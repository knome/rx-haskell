
-- rx-haskell by Michael Speer (c) 2009

-- import Debug.Trace (trace)

data RxOptions = RxOptions { rx_option_multiline   :: Bool ,
                             rx_option_ignore_case :: Bool }                             

data RxSetEntry = RxSetRange Char Char
                | RxSetChar  Char
                  deriving ( Show , Eq )

type RxSet = [ RxSetEntry ]

data RxRule a = RxMatch a          -- match a character
              | RxMatchAny         -- dot match , anything but newline
              | RxGoto Int         -- jump in rules
              | RxBack Int         -- push starting from given rule with current match onto backtrack stack
              | RxMatchStart       -- match at the beginning of the data , or after newline when in strings mode
              | RxMatchEnd         -- match at the end of the data , or before newline when in strings mode
              | PenDown Int        -- begin recording match info into a paren-group dropping any previous match
              | PenUp Int          -- stop recording match info for the given paren-group, LOGO ftw
              | RxMarkBack         -- place a marker into the list of backtrace options
              | RxPopBack          -- remove all backtrace entries upto and including marker ( used to implement '(?>' )
              | RxFailSet RxSet    -- accept any character not found within the set
              | RxMatchSet RxSet   -- accept any character found within the set
              | RxTrack            -- push a false boolean onto the consumption stack representing no character absorbed
              | RxPropagate        -- pop current propagation depth and one under it : push anding of these

              -- these aren't actually used yet, perhaps they won't be used at all
              | RxLookBehind       -- this will mean saving characters to match against and will likely be difficult to pull off
              | RxNonCapturing     -- this will mean being able to preform a search and simply failing or continuing once it matches without capturing anything ( used for lookahead assertion )
              | RxNonBacktracking  -- discards all backtracking information from a subpattern matched within it

              | RxOnStarveGoto Int -- conditional jump, only jumps when the flag indicating whether a character was consumed is false
              | RxSuccess          -- when this rule is encountered the regular expressions has performed a successful match
                deriving ( Show , Eq )

type RxRuleSet a = [ RxRule a ]

main = do
  testrun "(t|){3,}"  "ttttttttt"
  testrun "(t|){3,}?" "ttttttttt"

--  testrun "(a|b)+?$" "aabaabbbbaabababababaaab"
--  testrun "(a|b)+" "aabaabbbbaabababababaaab"

--  testrun "^(?>( *foo *)*)$" "foo foo foo foo foo foo foo foo foo foo foo foo fo"

--  this looks like it should capture but doesn't.
--  however, python does not capture in this instance either
--  testrun "(|(aa)*)*" "aaaaaaaaaaaaaaaaaa"

--  testrun "(w|a|()*)*?t" "wawt"
--  testrun "[0-9]{2}" "123abc"

--  print $ compile opts "[win]"
--  print $ compile opts "(?:abc){}"
--  print $ compile opts "(?:abc){0}"
--  print $ compile opts "(?:abc){1,}?"
--  print $ compile opts "(?:abc){2,}"
--  testrun "a{1,2}" "aa"
--  testrun "(?>a*)b" "aac"
--  testrun "<(.*?)>(?:(.)*)<.*>" "<b>hello world</b>"
--  testrun "he(ll)o" "hello"
--  testrun "^a$" "ab"
--  testrun "^( *foo *)*$" "foo foo foo foo foo"
--  testrun "^( *foo *)*$" "foo foo foo foo fo"

testrun pattern target = do
  print $ pattern
  print $ zip [0..] $ fst $ compile opts pattern
  print $ run (compile opts pattern) target
  putStrLn ""

--  print $ run (compile opts "^( *foo *)*$") "foo foo"
--  print $ compile opts "^( *foo *)*$"

{-
  print $ compile opts "wat"
  print $ compile opts "w(at)h"
  print $ compile opts "w(a|t)h"
  print $ compile opts "w(a|t)?h"
  print $ compile opts "w(a|t)??h"
  print $ compile opts{ rx_option_ignore_case = True } "w(a|t)??h"
-}

opts = RxOptions { rx_option_multiline   = False ,
                   rx_option_ignore_case = False }

-- returns list of rules and number of subgroups that will be matched
compile :: RxOptions -> String -> ( RxRuleSet Char , Int )
compile options pattern = let ( r , ralr , rp , np ) = eor options 0 0 ralr pattern
                          in
                            case rp of
                              [] -> -- trace (show np) $
                                    ( r ++ [ RxSuccess ] , np )
                              _  -> error "Unbalanced Parenthesis : Extraneous Closing Parenthesis"
    where
      -- eor :: options -> start rule -> on-success-goto-rule -> pattern -> ( ruleset , rule-after-last-rule , remaining-pattern )
      -- o     : options 
      -- sr    : start rule
      -- osgr  : on success goto rule
      -- p     : pattern
      -- r     : rules
      -- ralr  : rule after last rule
      -- rp    : remaining pattern
      -- rop   : remaining or pattern
      -- nr    : next rules
      -- nralr : next rule after last rule
      -- nrp   : next remaining pattern
      -- rap   : remaining after pattern
      -- sb    : start bump , amount to offset initial rule in preparation for prepending instructions
      -- np    : next parenthetical group identifier

      eor :: RxOptions -> Int -> Int -> Int -> String -> ( RxRuleSet Char , Int , String , Int )
      eor o np sr osgr p = let ( ~( r  , ralr  , rp , rnp ) ,
                                 ~( sb , ~( fr , fralr , fp , fnp ) ) ) = ( ear o np (sr + sb) p ,
                                                                            case rp of
                                                                              []        -> ( 0 , ( r , ralr , [] , rnp ) )
                                                                              (')':_)   -> ( 0 , ( r , ralr , rp , rnp ) )
                                                                              ('|':rop) -> ( 1 , let ( nr , nralr , nrp , nnp ) = eor o rnp (ralr + 1) osgr rop
                                                                                                 in
                                                                                                   ( [ RxBack (ralr + 1) ] ++ r ++ [ RxGoto osgr ] ++ nr , nralr , nrp , nnp ) ) )
                        in
                          ( fr , fralr , fp , fnp )
      
      -- ear :: options -> start rule -> pattern -> ( ruleset , rule-after-last-rule , remaining-pattern )
      ear :: RxOptions -> Int -> Int -> String -> ( RxRuleSet Char , Int , String , Int )
      ear o np sr p = let ( r , ralr , rp , rnp ) = erwr o np p sr
                      in
                        case rp of
                          []      -> ( r , ralr , [] , rnp )
                          (')':_) -> ( r , ralr , rp , rnp )
                          ('|':_) -> ( r , ralr , rp , rnp )
                          _       -> let ( nr , nralr , nrp , nnp ) = ear o rnp ralr rp
                                     in
                                       ( r ++ nr , nralr , nrp , nnp )
      
      -- erwr :: extract rule with repitition
      erwr :: RxOptions -> Int -> String -> Int -> ( RxRuleSet Char , Int , String , Int )
      erwr o np p sr = let x = \cs -> er o np cs p
                           ( ~( r , ralr , nrp , rnp ) ,
                             ~( sb , ~( fr , fralr , fp ) ) ) = ( x (sr + sb) ,
                                                                  -- TODO : ADD TRACK AND PROPAGATE INFORMATION HERE
                                                                  --  ANOTHER INSTRUCTION WILL BE NEEDED TO ASSERT TRUTH OR FALSENESS OF CURRENT PROPAGATOR 
                                                                  --    be careful with this, it shouldn't be like the general backtracking
                                                                  case nrp of
                                                                    ('?':'?':prp) -> ( 2 , ( [ RxBack (sr + sb) , RxGoto ralr ] ++ r , ralr , prp ) )
                                                                    ('?':prp)     -> ( 1 , ( [ RxBack ralr ] ++ r , ralr , prp ) )
                                                                    ('*':'?':prp) -> ( 3 , ( [ RxBack (sr + 2) , 
                                                                                               RxGoto (ralr + 4) ,
                                                                                               RxTrack ]
                                                                                             ++ r 
                                                                                             ++ 
                                                                                             [ RxOnStarveGoto (ralr + 3) , 
                                                                                               RxPropagate ,
                                                                                               RxGoto sr ,
                                                                                               RxPropagate ]
                                                                                           , ralr + 4
                                                                                           , prp ) )

                                                                    ('*':prp)     -> ( 2 , ( [ RxBack (ralr + 4) ,
                                                                                               RxTrack 
                                                                                             ] 
                                                                                             ++ r 
                                                                                             ++ 
                                                                                             [ RxOnStarveGoto (ralr + 3) ,
                                                                                               RxPropagate ,
                                                                                               RxGoto sr ,
                                                                                               RxPropagate ]
                                                                                           , ralr + 4
                                                                                           , prp ) )
                                                                    
                                                                    ('+':'?':prp) -> let ( ir , iralr , _ , _ ) = x sr
                                                                                     in
                                                                                       ( iralr + 3 - sr , ( ir
                                                                                                            ++ 
                                                                                                            [ RxBack (sr + sb - 1)  ,
                                                                                                              RxGoto (ralr + 4) ,
                                                                                                              RxTrack ] ++ 
                                                                                                            r ++ 
                                                                                                            [ RxOnStarveGoto (ralr + 3) ,
                                                                                                              RxPropagate ,
                                                                                                              RxGoto iralr ,
                                                                                                              RxPropagate ]
                                                                                                          , ralr + 4
                                                                                                          , prp ) )
                                                                    
                                                                    ('+':prp)     -> let ( ir , iralr , _ , _ ) = x sr
                                                                                     in
                                                                                       ( iralr + 2 - sr , ( ir ++ 
                                                                                                            [ RxBack (ralr + 4) ,
                                                                                                              RxTrack ] ++ 
                                                                                                            r ++ 
                                                                                                            [ RxOnStarveGoto (ralr + 3) ,
                                                                                                              RxPropagate ,
                                                                                                              RxGoto iralr ,
                                                                                                              RxPropagate ]
                                                                                                          , ralr + 4
                                                                                                          , prp ) )
                                                                    
                                                                    ('{':prp)     -> mkrange x prp sr
                                                                    _             -> ( 0 , ( r , ralr , nrp ) ) )
                       in
                         ( fr , fralr , fp , rnp )

      -- range followed by question mark is lazy range
      -- leading '{' is assumed clipped by caller
      rx_range = compile opts "((?>(?:[0-9])*))(?:(,)((?>(?:[0-9])*)))?\\}(\\?)?"

      erange p = let result = run rx_range p
                 in
                   -- trace (show $ rx_range) $
                   case result of
                     Nothing                             -> error "Malformed Range"
                     Just ( _ , submatches , remaining ) -> let vof y = case submatches !! y of
                                                                          [] -> -1
                                                                          _  -> read (submatches !! y) :: Int
                                                            in
                                                              ( not $ null $ submatches !! 3 , -- whether lazy
                                                                vof 0                        , -- minimum
                                                                if null $ submatches !! 1      -- maximum ; if there is a comma, infinite or integer bounded : otherwise equal to start
                                                                then
                                                                    vof 0
                                                                else
                                                                    vof 2                    ,
                                                                remaining                    ) -- pattern remaining
      
      -- do literal minimals, literal maximals, unbounded maximals
      mkrange x p sr = 
          let ( is_lazy , minm , maxm , postrange ) = erange p
              limm = if minm > 0
                     then minm
                     else 0
              limx = if minm < 1 
                     then (if maxm > -1
                           then maxm
                           else 0)
                     else (if maxm > -1
                           then (if maxm - minm >= 0
                                 then maxm - minm
                                 else 0)
                           else 0)
              ( lm_ru , lm_nr ) = foldl (\( r' , nr' ) _ -> let ( ir , iralr , _ , _ ) = x nr'
                                                            in
                                                              ( r' ++ ir , iralr ) )
                                        ( [] , sr )
                                        $ takeWhile (\n -> n < limm ) $ iterate (+1) 0
              ( lx_ru , lx_nr ) = foldl (\( r' , nr' ) _ -> let ( ir , iralr , _ , _ ) = x (nr' + (if is_lazy 
                                                                                                   then 2 
                                                                                                   else 1))
                                                            in
                                                              case is_lazy of
                                                                True -> ( r' ++ [ RxBack (nr' + 2) , RxGoto iralr ] ++ ir , iralr )
                                                                _    -> ( r' ++ [ RxBack iralr ] ++ ir , iralr ) )
                                        ( [] , lm_nr )
                                        $ takeWhile (\n -> n < limx ) $ iterate (+1) 0
              ( ux_ru , ux_nr ) = case -1 == maxm of
                                    False -> ( [] , lx_nr )
                                    True  -> let ( ir , iralr , _ , _ ) = x (lx_nr + (if is_lazy
                                                                                      then 3
                                                                                      else 2))
                                             in
                                               case is_lazy of
                                                 -- lx_nr is base
                                                 True  -> ( [ RxBack (lx_nr + 2) , 
                                                              RxGoto (iralr + 4) ,
                                                              RxTrack ] ++ 
                                                              ir ++ 
                                                            [ RxOnStarveGoto (iralr + 3) ,
                                                              RxPropagate ,
                                                              RxGoto lx_nr ,
                                                              RxPropagate ] 
                                                          , iralr + 4 )
                                                 
                                                 False -> ( [ RxBack (iralr + 4) ,
                                                              RxTrack ] ++
                                                            ir ++ 
                                                            [ RxOnStarveGoto (iralr + 3) ,
                                                              RxPropagate ,
                                                              RxGoto lx_nr ,
                                                              RxPropagate ]
                                                          , iralr + 4 )
          in
            ( lm_nr - sr , ( lm_ru ++ lx_ru ++ ux_ru , ux_nr , postrange ) )


      -- er :: extract rule
      er :: RxOptions -> Int -> Int -> String -> ( RxRuleSet Char , Int , String , Int )
      
      er o np sr ('?':rp)    = error "floating maybe operator ( ? )"
      er o np sr ('*':rp)    = error "floating glob operator ( * )"
      er o np sr ('+':rp)    = error "floating 1+ glob operator ( + )"

      er o np sr (p@(')':_)) = ( [] , sr , p , np ) -- catches empty group '()'

      er o np sr ('(':'?':':':rp) = let ( nr , nralr , nrp , nnp ) = eor o np sr nralr rp
                                    in
                                      case nrp of 
                                        (')':frp) -> ( nr , nralr , frp , nnp )
                                        _         -> error "Unbalanced Parenthesis on NonCapturing Group '(?:'"

      er o np sr ('(':'?':'>':rp) = let ( nr , nralr , nrp , nnp ) = eor o np (sr + 1) nralr rp
                                    in
                                      case nrp of
                                        (')':frp) -> ( [RxMarkBack] ++ nr ++ [RxPopBack] , nralr + 1 , frp , nnp )
                                        _         -> error "Unbalanced Parenthesis on Once-Only Group"


      er o np sr ('(':'?':_) = error "Unknown extension group '(?'"
      
      er o np sr ('(':rp)    = let ( nr , nralr , nrp , nnp ) = eor o (np + 1) (sr + 1) nralr rp
                               in
                                 case nrp of
                                   (')':frp) -> ( [ PenDown np ] ++ nr ++ [ PenUp np ] , nralr + 1 , frp , nnp )
                                   _         -> error "Unbalanced Parenthesis : Missing Close"
      
      er o np sr ('[':'^':rp) = eset o sr rp np True
      er o np sr ('[':rp)     = eset o sr rp np False
      
      er o np sr ('^':rp)    = ( [ RxMatchStart ]    , sr + 1 , rp , np )
      er o np sr ('$':rp)    = ( [ RxMatchEnd ]      , sr + 1 , rp , np )
      
      er (o@RxOptions{ rx_option_ignore_case = True }) np sr p = error "rx option ignore case not yet supported"
      er (o@RxOptions{ rx_option_multiline = True })   np sr p = error "rx option multiline not yet supported"
      
      er o np sr ('.':rp)    = ( [ RxMatchAny ]      , sr + 1 , rp , np )
      
      er o np sr ('\\':l:rp) = ( [ RxMatch l ]       , sr + 1 , rp , np )
      er o np sr (l:rp)      = ( [ RxMatch l ]       , sr + 1 , rp , np )
      er o np sr []          = ( [ RxGoto (sr + 1) ] , sr + 1 , [] , np ) -- goto one ahead , a noop
                               
      -- extract set '[a-zA-Z]'
      esetrange ('\\':a:'-':'\\':b:wat)              = ( RxSetRange a b , 5 ) : esetrange wat
      esetrange ('\\':a:'-':b:wat) | b /= ']'        = ( RxSetRange a b , 4 ) : esetrange wat
      esetrange ('\\':a:wat)                         = ( RxSetChar a    , 2 ) : esetrange wat
      esetrange (a:'-':'\\':b:wat) | a /= ']'        = ( RxSetRange a b , 4 ) : esetrange wat
      esetrange (a:'-':b:wat) | a /= ']' && b /= ']' = ( RxSetRange a b , 3 ) : esetrange wat
      esetrange (a:wat) | a /= ']'                   = ( RxSetChar a    , 1 ) : esetrange wat
      esetrange (']':wat)                            = []
      esetrange []                                   = error "Unterminated character set '[...]'"
      
      -- extract set
      eset o sr p np inverse = let ( set , sizes ) = unzip $ esetrange p
                               in
                                 case all (\r -> case r of
                                                   RxSetRange a b -> if a > b
                                                                     then error "First character in set range must be less than second"
                                                                     else if a == b
                                                                          then error "First character in set range must not be equal to the second"
                                                                          else True
                                                   _              -> True )
                                          set
                                 of
                                   True -> case sum sizes of
                                             0    -> error "Character sets must have at least one character or range in them.  '[]' is right out"
                                             size -> case inverse of
                                                       True  -> ( [ RxFailSet set  ] , sr + 1 , drop (1+size) p , np )
                                                       False -> ( [ RxMatchSet set ] , sr + 1 , drop (1+size) p , np )

type SubMatch = ( Bool , String )

type BackTrack = ( Bool , [Bool] , String ,[ SubMatch ] , RxRuleSet Char , String , Int )
data BtStackEntry = Bt BackTrack
                  | BtMark
                    deriving ( Eq )

run :: ( RxRuleSet Char , Int ) -> String -> Maybe ( String , [ String ] , String )
run re t = let ( rs , nsm ) = re 
               result = s True [False] [] [] (replicate nsm (False,[])) rs t 0
           in
             case result of
               Just ( rmatched , submatches , remaining ) -> Just ( reverse rmatched , map (reverse . snd) submatches , remaining )
               Nothing                                    -> Nothing
    where
      -- step at-start current-boundary-matched matches backtracks ruleset target current-rule
      back b = 
          -- trace ("going back") $
          case b of
            [] -> Nothing
            (BtMark:rb) -> back rb
            (Bt (_as , _cbm , _m , _sm , _rs , _t , _cr):rb) -> s _as _cbm _m rb _sm _rs _t _cr

      smpush :: Char -> SubMatch -> SubMatch
      smpush c (True,matches) = (True,c:matches)
      smpush _ inactive       = inactive

      s :: Bool -> [ Bool ] -> String -> [ BtStackEntry ] -> [ SubMatch ] -> RxRuleSet Char -> String -> Int -> 
           Maybe ( String , [ SubMatch ] , String )
      
      --  as :: at start , all matching patterns set this to false
      -- cbm :: consumed byte match - stack used to track whether a byte was actually absorbed or if the match was merely a boundary match
      --   m :: match - text matched by overall pattern
      --   b :: data stack used to implement backtracking
      --  sm :: submatches - text matched by various sbugroups, controlled via penup/pendown tokens
      --  rs :: rules - the rules this state machine is following
      --   t :: target string remaining
      --  cr :: current rule - index into rules
      
      s as cbm m b sm rs t cr = -- trace ("[m:"++(show m)++"][t:"++(show t)++"][#b:"++(show $ length b)++"][rs!!cr:"++(show $ rs !! cr)++"]") $ 
                                case rs !! cr of
                                  RxMatchStart -> case as of
                                                    True -> s as cbm m b sm rs t (cr + 1)
                                                    _    -> back b
                                  
                                  RxMatchEnd -> case t of
                                                  [] -> s as cbm m b sm rs t (cr + 1)
                                                  _ -> back b
                                  
                                  RxMatch v -> case ( t , cbm ) of
                                                 ( (h:rt) , (_:tpt) ) -> if v == h
                                                                         then
                                                                             s False (True:tpt) (h:m) b (map (smpush h) sm) rs rt (cr + 1) -- todo update sm
                                                                         else
                                                                             back b
                                                 _                    -> back b
                                  
                                  RxMatchAny -> case ( t , cbm ) of
                                                  ( (h:rt) , (_:tpt) ) -> s False (True:tpt) (h:m) b (map (smpush h) sm) rs rt (cr + 1)
                                                  _                    -> back b
                                  
                                  RxFailSet set -> case ( t , cbm ) of
                                                     ( (h:rt) , (_:tpt) ) -> case all (\r -> case r of
                                                                                               RxSetRange a b -> h < a || h > b
                                                                                               RxSetChar  a   -> h /= a )
                                                                                  set 
                                                                             of
                                                                               True  -> s False (True:tpt) (h:m) b (map (smpush h) sm) rs rt (cr + 1)
                                                                               False -> back b
                                                     _                    -> back b
                                  
                                  RxMatchSet set -> case ( t , cbm ) of
                                                      ( (h:rt) , (_:tpt) ) -> case any (\r -> case r of
                                                                                                RxSetRange a b -> h >= a && h <= b
                                                                                                RxSetChar  a   -> h == a )
                                                                                   set
                                                                              of
                                                                                True  -> s False (True:tpt) (h:m) b (map (smpush h) sm) rs rt (cr + 1)
                                                                                False -> back b
                                                      _                    -> back b
                                  
                                  RxGoto r -> s as cbm m b sm rs t r
                                  
                                  RxBack r -> s as cbm m (Bt (as,cbm,m,sm,rs,t,r):b) sm rs t (cr+1)
                                  
                                  RxMarkBack -> s as cbm m (BtMark:b) sm rs t (cr+1)
                                  
                                  RxPopBack -> s as cbm m ( tail $ dropWhile (/= BtMark) b) sm rs t (cr + 1)
                                  
                                  PenDown p -> let (pre , with) = splitAt p sm
                                                   post = tail with
                                               in
                                                 s as cbm m b (pre ++ [ (True,[]) ] ++ post) rs t (cr + 1)
                                  
                                  PenUp p -> let (pre , with) = splitAt p sm
                                                 (_,matches) = head with
                                                 post = tail with
                                             in
                                               s as cbm m b (pre ++ [ (False,matches) ] ++ post) rs t (cr + 1)

                                  RxTrack -> s as (False:cbm) m b sm rs t (cr + 1)
                                             
                                  -- inform the outer consumption tracking that it has consumed a character                                             
                                  RxPropagate -> case cbm of
                                                   (cbm_a:cbm_b:cbm_rs) -> s as ((cbm_a || cbm_b): cbm_rs) m b sm rs t (cr + 1) 
                                                   _                    -> error "character consumption propagation error"

                                  RxOnStarveGoto x -> case cbm of
                                                        (False:_) -> s as cbm m b sm rs t x
                                                        _         -> s as cbm m b sm rs t (cr + 1)
                                  
                                  RxSuccess -> Just ( m , sm , t )
