
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
              | RxSuccess         -- when this rule is encountered the regular expressions has performed a successful match
                deriving ( Show , Eq )

type RxRuleSet a = [ RxRule a ]

main = do
  testrun "^a$" "a"
  testrun "^a$" "ab"
  testrun "^( *foo *)*$" "foo foo foo foo foo"
  testrun "^( *foo *)*$" "foo foo foo foo fo"

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

compile :: RxOptions -> String -> RxRuleSet Char
compile options pattern = let ( r , ralr , rp ) = eor options 0 ralr pattern
                          in
                            r ++ [ RxSuccess ]
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
      
      eor :: RxOptions -> Int -> Int -> String -> ( RxRuleSet Char , Int , String )
      eor o sr osgr p = let ( ~( r  , ralr  , rp ) ,
                              ~( sb , ~( fr , fralr , fp ) ) ) = ( ear o (sr + sb) p ,
                                                                   case rp of
                                                                     []        -> ( 0 , ( r , ralr , []  ) )
                                                                     (')':rap) -> ( 0 , ( r , ralr , rap ) )
                                                                     ('|':rop) -> ( 1 , let ( nr , nralr , nrp ) = eor o (ralr + 1) osgr rop
                                                                                        in
                                                                                          ( [ RxBack (ralr + 1) ] ++ r ++ [ RxGoto osgr ] ++ nr , nralr , nrp ) )
                                                                     _         -> error "Unbalanced Parenthesis" )
                        in
                          ( fr , fralr , fp )
      
      -- ear :: options -> start rule -> pattern -> ( ruleset , rule-after-last-rule , remaining-pattern )
      ear :: RxOptions -> Int -> String -> ( RxRuleSet Char , Int , String )
      ear o sr p = let ( r , ralr , rp ) = erwr o p sr
                   in
                     case rp of
                       []      -> ( r , ralr , [] )
                       (')':_) -> ( r , ralr , rp )
                       ('|':_) -> ( r , ralr , rp )
                       _       -> let ( nr , nralr , nrp ) = ear o ralr rp
                                  in
                                    ( r ++ nr , nralr , nrp )
      
      -- erwr :: extract rule with repitition
      erwr :: RxOptions -> String -> Int -> ( RxRuleSet Char , Int , String )
      erwr o p sr = let x = \cs -> er o cs p
                        ( ~( r , ralr , nrp ) ,
                          ~( sb , ~( fr , fralr , fp ) ) ) = ( x (sr + sb) ,
                                                               case nrp of
                                                                 ('?':'?':prp) -> ( 2 , ( [ RxBack (sr + sb) , RxGoto ralr ] ++ r , ralr , prp ) )
                                                                 ('?':prp)     -> ( 1 , ( [ RxBack ralr ] ++ r , ralr , prp ) )
                                                                 ('*':'?':prp) -> ( 2 , ( [ RxBack (sr + sb) , RxGoto (ralr + 1) ] ++ r ++ [ RxGoto sr ] , ralr + 1 , prp ) )
                                                                 ('*':prp)     -> ( 1 , ( [ RxBack (ralr + 1) ] ++ r ++ [ RxGoto sr ] , ralr + 1 , prp ) )
                                                                 ('+':'?':prp) -> let ( ir , iralr , _ ) = x sr
                                                                                  in
                                                                                    ( iralr + 2 - sr , ( ir ++ [ RxBack (sr + sb) , RxGoto (ralr + 1) ] ++ r ++ [ RxGoto iralr ], ralr + 1 , prp ) )
                                                                 ('+':prp)     -> let ( ir , iralr , _ ) = x sr
                                                                                  in
                                                                                    ( iralr + 1 - sr , ( ir ++ [ RxBack (ralr + 1) ] ++ r ++ [ RxGoto iralr ] , ralr + 1 , prp ) )
                                                                 ('{':prp)     -> error "i dont know how to range"  -- range followed by question mark is lazy range
                                                                 _             -> ( 0 , ( r , ralr , nrp ) ) )
                    in
                      ( fr , fralr , fp )
      
      -- er :: extract rule
      er :: RxOptions -> Int -> String -> ( RxRuleSet Char , Int , String )

      er o sr ('?':rp)    = error "floating maybe operator ( ? )"
      er o sr ('*':rp)    = error "floating glob operator ( * )"
      er o sr ('+':rp)    = error "floating 1+ glob operator ( + )"
      
      er o sr ('(':rp)    = let ( nr , nralr , nrp ) = eor o sr nralr rp 
                            in
                              ( nr , nralr , nrp )

      er o sr ('[':rp)    = error "character ranges not yet supported"
      
      er o sr ('^':rp)    = ( [ RxMatchStart ]    , sr + 1 , rp )
      er o sr ('$':rp)    = ( [ RxMatchEnd ]      , sr + 1 , rp )
      
      er (o@RxOptions{ rx_option_ignore_case = True }) sr p = error "rx option ignore case not yet supported"
      er (o@RxOptions{ rx_option_multiline = True })   sr p = error "rx option multiline not yet supported"
      
      er o sr ('.':rp)    = ( [ RxMatchAny ]      , sr + 1 , rp )
      
      er o sr ('\\':l:rp) = ( [ RxMatch l ]       , sr + 1 , rp )
      er o sr (l:rp)      = ( [ RxMatch l ]       , sr + 1 , rp )
      er o sr []          = ( [ RxGoto (sr + 1) ] , sr + 1 , [] ) -- goto one ahead , a noop

run :: RxRuleSet Char -> String -> Maybe ( Bool , String , String )
run rs t = let result = s True False [] [] rs t 0
           in
             case result of
               Just ( success , rmatched , remaining ) -> Just ( success , reverse rmatched , remaining )
               Nothing                                 -> Nothing
    where
      -- step at-start current-boundary-matched matches backtracks ruleset target current-rule

      back b = 
          trace ("going back") $
          case b of
            [] -> Nothing
            ((_as , _cbm , _m , _rs , _t , _cr):rb) -> s _as _cbm _m rb _rs _t _cr

      s :: Bool -> Bool -> String -> [ ( Bool , Bool , String , RxRuleSet Char , String , Int ) ] -> RxRuleSet Char -> String -> Int -> Maybe ( Bool , String , String )
      s as cbm m b rs t cr = trace ("[m:"++(show m)++"][t:"++(show t)++"][#b:"++(show $ length b)++"][rs!!cr:"++(show $ rs !! cr)++"]") $ 
                             case rs !! cr of
                               RxMatchStart -> case as of
                                                 True -> s as True m b rs t (cr + 1)
                                                 _    -> back b

                               RxMatchEnd -> case t of
                                               [] -> s as True m b rs t (cr + 1)
                                               _ -> back b
                               
                               RxMatch v -> case t of
                                              (h:rt) -> if v == h
                                                        then
                                                            s False False (v:m) b rs rt (cr + 1)
                                                        else
                                                            back b
                                              _      -> back b

                               RxMatchAny -> case t of
                                               (h:rt) -> s False False (h:m) b rs rt (cr + 1)
                                               _      -> back b

                               RxGoto r -> s as cbm m b rs t r

                               RxBack r -> s as cbm m ((as,cbm,m,rs,t,r):b) rs t (cr+1)

                               RxSuccess -> Just ( True , m , t )
