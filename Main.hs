
-- rx-haskell by Michael Speer (c) 2009

import Debug.Trace (trace)

data RxOptions = RxOptions { rx_option_multiline   :: Bool ,
                             rx_option_ignore_case :: Bool }                             

data RxRule a = RxMatch a         -- match a character
              | RxMatchAny        -- dot match , anything but newline
              | RxGoto Int        -- jump in rules
              | RxBack Int        -- push starting from given rule with current match onto backtrack stack
              | RxMatchStart      -- match at the beginning of the data , or after newline when in strings mode
              | RxMatchEnd        -- match at the end of the data , or before newline when in strings mode
              | RxLookBehind      -- this will mean saving characters to match against and will likely be difficult to pull off
              | RxNonCapturing    -- this will mean being able to preform a search and simply failing or continuing once it matches without capturing anything ( used for lookahead assertion )
              | RxNonBacktracking -- discards all backtracking information from a subpattern matched within it
              | PenDown Int       -- begin recording match info into a paren-group dropping any previous match
              | PenUp Int         -- stop recording match info for the given paren-group, LOGO ftw
              | RxMarkBack        -- place a marker into the list of backtrace options
              | RxPopBack         -- remove all backtrace entries upto and including marker ( used to implement '(?>' )
              | RxSuccess         -- when this rule is encountered the regular expressions has performed a successful match
                deriving ( Show , Eq )

type RxRuleSet a = [ RxRule a ]

main = do
  testrun "(?:a*)b" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaac"

--  testrun "<(.*?)>(?:(.)*)<.*>" "<b>hello world</b>"

--  testrun "he(ll)o" "hello"
--  testrun "^a$" "ab"
--  testrun "^( *foo *)*$" "foo foo foo foo foo"
--  testrun "^( *foo *)*$" "foo foo foo foo fo"

testrun pattern target = do
  print $ pattern
  print $ compile opts pattern
  print $ run (compile opts pattern) target
  putStrLn ""

--  print $ run (compile opts "^( *foo *)*$") "foo foo"
--  print $ compile opts "^( *foo *)*$"
--  print $ run (compile opts "^( *foo *)*$") "foo foo foo foo foo foo foo foo foo foo foo foo foo foo foo foo foo foo fo"

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
                              [] -> trace (show np) $
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
                                                                  case nrp of
                                                                    ('?':'?':prp) -> ( 2 , ( [ RxBack (sr + sb) , RxGoto ralr ] ++ r , ralr , prp ) )
                                                                    ('?':prp)     -> ( 1 , ( [ RxBack ralr ] ++ r , ralr , prp ) )
                                                                    ('*':'?':prp) -> ( 2 , ( [ RxBack (sr + sb) , RxGoto (ralr + 1) ] ++ r ++ [ RxGoto sr ] , ralr + 1 , prp ) )
                                                                    ('*':prp)     -> ( 1 , ( [ RxBack (ralr + 1) ] ++ r ++ [ RxGoto sr ] , ralr + 1 , prp ) )
                                                                    ('+':'?':prp) -> let ( ir , iralr , _ , _ ) = x sr
                                                                                     in
                                                                                       ( iralr + 2 - sr , ( ir ++ [ RxBack (sr + sb) , RxGoto (ralr + 1) ] ++ r ++ [ RxGoto iralr ], ralr + 1 , prp ) )
                                                                    ('+':prp)     -> let ( ir , iralr , _ , _ ) = x sr
                                                                                     in
                                                                                       ( iralr + 1 - sr , ( ir ++ [ RxBack (ralr + 1) ] ++ r ++ [ RxGoto iralr ] , ralr + 1 , prp ) )
                                                                    ('{':prp)     -> error "i dont know how to range"  -- range followed by question mark is lazy range
                                                                    _             -> ( 0 , ( r , ralr , nrp ) ) )
                       in
                         ( fr , fralr , fp , rnp )
      
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
      
      er o np sr ('[':rp)    = error "character ranges not yet supported"
      
      er o np sr ('^':rp)    = ( [ RxMatchStart ]    , sr + 1 , rp , np )
      er o np sr ('$':rp)    = ( [ RxMatchEnd ]      , sr + 1 , rp , np )
      
      er (o@RxOptions{ rx_option_ignore_case = True }) np sr p = error "rx option ignore case not yet supported"
      er (o@RxOptions{ rx_option_multiline = True })   np sr p = error "rx option multiline not yet supported"
      
      er o np sr ('.':rp)    = ( [ RxMatchAny ]      , sr + 1 , rp , np )
      
      er o np sr ('\\':l:rp) = ( [ RxMatch l ]       , sr + 1 , rp , np )
      er o np sr (l:rp)      = ( [ RxMatch l ]       , sr + 1 , rp , np )
      er o np sr []          = ( [ RxGoto (sr + 1) ] , sr + 1 , [] , np ) -- goto one ahead , a noop


type SubMatch = ( Bool , String )

type BackTrack = ( Bool , Bool , String ,[ SubMatch ] , RxRuleSet Char , String , Int )
data BtStackEntry = Bt BackTrack
                  | BtMark
                    deriving ( Eq )

run :: ( RxRuleSet Char , Int ) -> String -> Maybe ( Bool , String , [ String ] , String )
run re t = let ( rs , nsm ) = re 
               result = s True False [] [] (replicate nsm (False,[])) rs t 0
           in
             case result of
               Just ( success , rmatched , submatches , remaining ) -> Just ( success , reverse rmatched , map (reverse . snd) submatches , remaining )
               Nothing                                              -> Nothing
    where
      -- step at-start current-boundary-matched matches backtracks ruleset target current-rule
      back b = 
          trace ("going back") $
          case b of
            [] -> Nothing
            (BtMark:rb) -> back rb
            (Bt (_as , _cbm , _m , _sm , _rs , _t , _cr):rb) -> s _as _cbm _m rb _sm _rs _t _cr

      smpush :: Char -> SubMatch -> SubMatch
      smpush c (True,matches) = (True,c:matches)
      smpush _ inactive       = inactive

      s :: Bool -> Bool -> String -> [ BtStackEntry ] -> [ SubMatch ] -> RxRuleSet Char -> String -> Int -> 
           Maybe ( Bool , String , [ SubMatch ] , String )
      s as cbm m b sm rs t cr = trace ("[m:"++(show m)++"][t:"++(show t)++"][#b:"++(show $ length b)++"][rs!!cr:"++(show $ rs !! cr)++"]") $ 
                                case rs !! cr of
                                  RxMatchStart -> case as of
                                                    True -> s as True m b sm rs t (cr + 1)
                                                    _    -> back b

                                  RxMatchEnd -> case t of
                                                  [] -> s as True m b sm rs t (cr + 1)
                                                  _ -> back b
                               
                                  RxMatch v -> case t of
                                                 (h:rt) -> if v == h
                                                           then
                                                               s False False (h:m) b (map (smpush h) sm) rs rt (cr + 1) -- todo update sm
                                                           else
                                                               back b
                                                 _      -> back b
                                                           
                                  RxMatchAny -> case t of
                                                  (h:rt) -> s False False (h:m) b (map (smpush h) sm) rs rt (cr + 1)
                                                  _      -> back b
                                  
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

                                  RxSuccess -> Just ( True , m , sm , t )
