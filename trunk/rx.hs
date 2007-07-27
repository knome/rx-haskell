-- rx : a regular expression engine for haskell
--    : (c) 2007 by michael speer , released GPL v2.0 license or later

import Maybe
import Array

-- get-function : gather a nodes worth of pattern from a pattern-string
--                returns the segment and the remaining pattern in a tuple
gf :: [Char] -> ( [Char] , [Char] )
gf ('(':ps)     = let ( segment , remaining ) = gpf [] ps
                 in ( '(':segment , remaining )
    where
      -- get-parenthesis'd fragment
      gpf :: [Char] -> [Char] -> ( [Char] , [Char] )
      gpf segment []       = ( segment , [] )
      gpf segment (')':ps) = ( segment++")" , ps )
      gpf segment ('(':ps) = let ( subsegment , remaining ) = gpf [] ps
                             in gpf ( segment ++ ('(':subsegment) ) remaining
      gpf segment (p:ps)   = gpf (segment ++ p:[]) ps
gf ('\\':p:ps)  = ( '\\':p:[] , ps )
gf ('?':'?':ps) = ( "??" , ps )
gf ('*':'?':ps) = ( "*?" , ps )
gf (p:ps)       = ( p:[] , ps )

-- list-functions : creates a list of function-pattern-segments from a regular expression
lfn :: [Char] -> [[Char]]
lfn []  = []
lfn pps = let ( fn , remaining ) = gf pps
          in fn : lfn remaining

-- postfix-to-prefix : moves all repitition characters to before their targets
--                     in addition running the pattern through this function
--                     ensures that the pattern is legal.
p2p :: [[Char]] -> [[Char]]
p2p []                 = []
p2p (('?':_):_)        = error "Misplaced repitition operator `?' "
p2p (('*':_):_)        = error "Misplaced repitition operator `*' "
p2p ("\\":_)           = error "Escape sequence targetting nothing"
p2p ((')':_):[])       = ")" : []                                          -- allows for a close-parum at end of pattern 
                                                                           -- later processing must test for this and throw error if it is unexpected ( eg top-level
p2p ((')':_):_)        = error "Unmatched terminating group marker , `)' " -- catches mid pattern erroneous close-para
p2p ("|":('?':_):_)    = error "Repitition operator `?' applied to procedural alternation operator `|' "
p2p (s1:s2@("??"):ps)  = ('?':'?': s1) : p2p ps
p2p (s1:s2@("?"):ps)   = ('?': s1) : p2p ps
p2p (s1:s2@("*?"):ps)  = ('*':'?': s1) : p2p ps
p2p (s1:s2@("*"):ps)   = ('*': s1) : p2p ps
p2p (s1:ps)            = s1 : p2p ps

-- group-split : break the contents of a parenthesized group into peices
--               build a current list of segments until | is encountered
--               then append the result of calling this again on the 
--               remainder
data PatternDepth = Top | Sub -- Pattern depth
gs :: PatternDepth -> [ [ Char ] ] -> [ [ Char ] ] -> [ [ [ Char ] ] ]
gs Top segments (")":[])   = error "Unmatched terminating group marker `)' at end of pattern"
gs Sub segments (")":[])   = gs Sub segments []
gs _   segments []         = if segments /= [] then
                                         segments : []
                                     else
                                         [""] : []
gs pd  segments ("|":rest) = segments : gs pd [] rest
gs pd  segments (s:rest)   = gs pd (segments++[s]) rest 

-- many to single nodes
m2s :: [ [ ( Maybe Char , Integer ) ] ] -> Integer -> ( ( Maybe Char , Integer ) , [ [ ( Maybe Char , Integer ) ] ] , Integer )
m2s (g@(ni:[]):gs) n = ( ni                  , gs  , n   ) -- if the first list is one long, pop it off
m2s ggs            n = ( ( Nothing , (n+1) ) , ggs , n+1 ) -- otherwise add a new member at the beginning to act as a pointer to it

-- or-extracted-nodes
oexn :: [ [ [ Char ] ] ] -> Integer -> Integer -> ( [ ( Maybe Char , Integer ) ] , [ [ ( Maybe Char , Integer ) ] ] , Integer )
oexn (g:[])    n l = let ( ~( ns , x ) ,
                           ~( ni' , ns' , x' ) ) = ( aexn g x' l ,
                                                     m2s ns n )
                     in ( [ ni' ] , ns' , x )

oexn (g:g':[]) n l = let ( ~( ns    , x            ) ,
                           ~( ni'   , ns'   , x'   ) ,
                           ~( ns''  , x''          ) ,
                           ~( ni''' , ns''' , x''' ) ) = ( aexn g x' l ,
                                                           m2s ns n ,
                                                           aexn g' x''' l ,
                                                           m2s ns'' x )
                     in
                       ( ni' : ni''' : [] , ns' ++ ns''' , (x''-1) )

oexn (g:gs)    n l = let ( ~( ns   , x          ) ,
                           ~( ni'  , ns'  , x'  ) ,
                           ~( ni'' , ns'' , x'' ) ) = ( aexn g x' l ,
                                                        m2s ns n ,
                                                        oexn gs x l )
                     in
                       ( ni' : ni'' , ns' ++ ns'' , (x''-1) )

-- and-extracted-nodes
aexn :: [ [ Char ] ] -> Integer -> Integer -> ( [ [ ( Maybe Char , Integer ) ] ] , Integer )
aexn (b:[]) n l = exn b n l 
aexn (b:bs) n l = let ( ~( ns  , x  ) ,
                        ~( ns' , x' ) ) = ( exn b n x ,
                                            aexn bs x l )
                  in
                    ( ns ++ ns' , x' )

-- subgroup
exn :: [ Char ] -> Integer -> Integer -> ( [ [ ( Maybe Char , Integer ) ] ] , Integer )
exn ('(':cs) n l = let ~( ni , ns , x ) = oexn (gs Sub [] $ p2p $ lfn cs ) n l
                   in
                     ( [ ni ] ++ ns , x )

-- non-greedy
exn ('?':'?':cs) n l = let ~( ni , ns , x ) = oexn (gs Top [] $ p2p $ lfn cs ) (n+1) x
                   in
                     ( [ [ ( Nothing , l ) , ( Nothing , (n+1) ) ] ] ++ [ ni ] ++ ns , x )

-- greedy
exn ('?':cs) n l = let ~( ni , ns , x ) = oexn (gs Top [] $ p2p $ lfn cs ) (n+1) x
                   in
                     ( [ [ ( Nothing , (n+1) ) , ( Nothing , l ) ] ] ++ [ ni ] ++ ns , x )

-- non-greedy
exn ('*':'?':cs) n l = let ~( ni , ns , x ) = oexn (gs Top [] $ p2p $ lfn cs ) (n+1) n
                   in
                     ( [ [ ( Nothing , l ) , ( Nothing , (n+1) ) ] ] ++ [ ni ] ++ ns , x )

-- greedy
exn ('*':cs) n l = let ~( ni , ns , x ) = oexn (gs Top [] $ p2p $ lfn cs ) (n+1) n
                   in
                     ( [ [ ( Nothing , (n+1) ) , ( Nothing , l ) ] ] ++ [ ni ] ++ ns , x )

exn (c:_)    n l = ( [ [ ( Just c , l ) ] ] , (n+1) )
exn []       n l = ( [ [ ( Nothing , l ) ] ] , (n+1) )

-- compile a regular expression into a DFA array
ruleset_compile pps = let ~( ni , ns , x ) = oexn (gs Top [] $ p2p $ lfn pps ) 1 x
                 in 
                   ( array ( 1 , x - 1 ) ( zip [1..] (ni : ns) ) , x )  

matches string pattern = let ( ruleset , endpos ) = ruleset_compile pattern
                         in match ruleset endpos [ ( 1 , string ) ]
    where
      match :: Array Integer [(Maybe Char,Integer)] -> Integer -> [( Integer , [Char] )] -> ( Bool , [Char] )
      match _       _      []                                  = ( False , [] )
      match ruleset endpos ((pos,remaining):_) | pos == endpos = ( True , remaining )
      match ruleset endpos current_partials                    = let new_partials = step ruleset endpos current_partials
                                                                 in match ruleset endpos new_partials
          where
            step :: Array Integer [(Maybe Char,Integer)] -> Integer -> [(Integer,[Char])] -> [(Integer,[Char])]
            step ruleset endpos []                         = []
            step ruleset endpos ((pos,remaining):partials) | pos == endpos = (pos , remaining) : step ruleset endpos partials
                                                           | otherwise     = let new_partials = test_rules (ruleset!pos) remaining
                                                                             in new_partials ++ step ruleset endpos partials
                where
                  test_rules :: [(Maybe Char,Integer)] -> [Char] -> [(Integer,[Char])]
                  test_rules []                         _          = []
                  test_rules ((Nothing,nextpos):rules)  ccs        | nextpos == endpos = (nextpos,ccs) : test_rules rules ccs
                                                                   | otherwise         = test_rules ((ruleset!nextpos)++rules) ccs
                  test_rules (((Just p),nextpos):rules) ccs@(c:cs) = if p == c 
                                                                     then 
                                                                         (nextpos,cs) : test_rules rules ccs
                                                                     else
                                                                         test_rules rules ccs
                  test_rules (_:rules)                  []         = test_rules rules []

(~=) = matches

main = let number = "(0|1|2|3|4|5|6|7|8|9)"
       in do
           print $ ruleset_compile number
           print $ "abcz" ~= "abc"
           print $ "aaaz" ~= "a*"
           print $ "abcz" ~= "abc"
           print $ "abcz" ~= "ab?c"
