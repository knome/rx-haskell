-- rx : a regular expression engine for haskell
--    : (c) 2007 by michael speer , released GPL v2.0 license or later

import System.Environment

import Directory
import Array
import Monad

-- these rules where initially modeled by Maybe Char, but required expanding to account for the presence of MatchAny
data Rule = Bypass     | -- used as a placeholder indicating the rules interpreter should move on to the next rule without consuming a target string member
            Match Char | -- used to indicate the rules interpreter should consume a member of the target string if it is the contained character, otherwise dropping the rule
            MatchAny     -- used to consume any character except for \n, if there is no character the rule is dropped

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
p2p (s1:s2@("+"):ps)   = ('+': s1) : p2p ps
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
m2s :: [ [ ( Rule , Int ) ] ] -> Int -> ( ( Rule , Int ) , [ [ ( Rule , Int ) ] ] , Int )
m2s (g@(ni:[]):gs) n = ( ni                 , gs  , n   ) -- if the first list is one long, pop it off
m2s ggs            n = ( ( Bypass , (n+1) ) , ggs , n+1 ) -- otherwise add a new member at the beginning to act as a pointer to it

-- or-extracted-nodes
oexn :: [ [ [ Char ] ] ] -> Int -> Int -> ( [ ( Rule , Int ) ] , [ [ ( Rule , Int ) ] ] , Int )
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
aexn :: [ [ Char ] ] -> Int -> Int -> ( [ [ ( Rule , Int ) ] ] , Int )
aexn []     n l = exn [] n l
aexn (b:[]) n l = exn b  n l 
aexn (b:bs) n l = let ( ~( ns  , x  ) ,
                        ~( ns' , x' ) ) = ( exn b n x ,
                                            aexn bs x l )
                  in
                    ( ns ++ ns' , x' )

-- subgroup
exn :: [ Char ] -> Int -> Int -> ( [ [ ( Rule , Int ) ] ] , Int )

exn ('(':cs) n l = let ~( ni , ns , x ) = oexn (gs Sub [] $ p2p $ lfn cs ) n l
                   in
                     ( [ ni ] ++ ns , x )

-- least from zero or one
exn ('?':'?':cs) n l = let ~( ni , ns , x ) = oexn (gs Top [] $ p2p $ lfn cs ) (n+1) x
                   in
                     ( [ [ ( Bypass , l ) , ( Bypass , (n+1) ) ] ] ++ [ ni ] ++ ns , x )

-- most from zero or one
exn ('?':cs) n l = let ~( ni , ns , x ) = oexn (gs Top [] $ p2p $ lfn cs ) (n+1) x
                   in
                     ( [ [ ( Bypass , (n+1) ) , ( Bypass , l ) ] ] ++ [ ni ] ++ ns , x )

-- least from zero or more
exn ('*':'?':cs) n l = let ~( ni , ns , x ) = oexn (gs Top [] $ p2p $ lfn cs ) (n+1) n
                   in
                     ( [ [ ( Bypass , l ) , ( Bypass , (n+1) ) ] ] ++ [ ni ] ++ ns , x )

-- most from zero or more
exn ('*':cs) n l = let ~( ni , ns , x ) = oexn (gs Top [] $ p2p $ lfn cs ) (n+1) n
                   in
                     ( [ [ ( Bypass , (n+1) ) , ( Bypass , l ) ] ] ++ [ ni ] ++ ns , x )

-- most from at least one
exn ('+':cs) n l = let ~( ni , ns , x ) = oexn (gs Top [] $ p2p $ lfn cs ) (n+2) (n+1)
                   in
                     ( [ [ ( Bypass , n+2 ) ] , [ ( Bypass , n+2 ) , ( Bypass , l) ] ] ++ [ ni ] ++ ns , x )
                     
exn ('.':cs) n l = ( [ [ ( MatchAny , l ) ] ] , (n+1) )
exn (c:_)    n l = ( [ [ ( Match c , l ) ] ]  , (n+1) )
exn []       n l = ( [ [ ( Bypass , l ) ] ]   , (n+1) )

-- compile a regular expression into a DFA array
ruleset_compile pps = let ~( ni , ns , x ) = oexn (gs Top [] $ p2p $ lfn pps ) 1 x
                 in 
                   ( array ( 1 , x - 1 ) ( zip [1..] (ni : ns) ) , x )  

matches string pattern = let ( ruleset , endpos ) = ruleset_compile pattern
                         in match ruleset endpos [ ( 1 , string ) ]
    where
      match :: Array Int [(Rule,Int)] -> Int -> [( Int , [Char] )] -> ( Bool , [Char] )
      match _       _      []                                  = ( False , [] )
      match ruleset endpos ((pos,remaining):_) | pos == endpos = ( True , remaining )
      match ruleset endpos current_partials                    = let new_partials = step ruleset endpos current_partials
                                                                 in match ruleset endpos new_partials
          where
            step :: Array Int [(Rule,Int)] -> Int -> [(Int,[Char])] -> [(Int,[Char])]
            step ruleset endpos []                         = []
            step ruleset endpos ((pos,remaining):partials) | pos == endpos = (pos , remaining) : step ruleset endpos partials
                                                           | otherwise     = let new_partials = test_rules (ruleset!pos) remaining
                                                                             in new_partials ++ step ruleset endpos partials
                where
                  test_rules :: [(Rule,Int)] -> [Char] -> [(Int,[Char])]
                  test_rules []                          _          = []
                  test_rules ((Bypass,nextpos):rules)    ccs        | nextpos == endpos = (nextpos,ccs) : test_rules rules ccs
                                                                    | otherwise         = test_rules ((ruleset!nextpos)++rules) ccs
                  test_rules ((MatchAny,nextpos) :rules) ccs@(c:cs) = (nextpos,cs) : test_rules rules ccs
                  test_rules (((Match p),nextpos):rules) ccs@(c:cs) | p == c = (nextpos,cs) : test_rules rules ccs
                                                                    | otherwise = test_rules rules ccs
                  test_rules (_:rules)                   []         = test_rules rules []

(~=) = matches

-- checks if any point of a string matches a regular expression
-- pattern -> target -> if_matches
match_in :: [Char] -> [Char] -> Bool
match_in pattern target = check ( ~= pattern ) target
    where
      check :: ( [Char] -> ( Bool , [Char] ) ) -> [Char] -> Bool
      check rxfn tts    | let ( b , _ ) = rxfn tts 
                          in b = True
      check rxfn []     = False
      check rxfn (_:ts) = check rxfn ts


-- foreach values ( value -> function-returning-monad -> anonymously-bound-together-monad
-- used to slingshot a monad across the results of applying a function to a list of values
-- literally it applies a function to each value generating a series of monads and uses an 
--   anonymous bind to stitch each together in turn
foreach :: (Monad m) => [b] -> (b -> m ()) -> m ()
foreach vs f = foldr (>>) (return ()) $ map f vs
--foreach vs f = foldl ( \s v -> s >> f v ) (return ()) vs

-- allow reversal of function application ordering for aesthetic purposes.
(#) v f = f v

main = let containing = \pattern lines -> filter ( \line -> match_in pattern line ) lines
       in
         getArgs >>= \args ->
             case args of
               ( pattern : files ) -> case files of
                                        -- if no files then parse stdin
                                        []     -> interact $ unlines . ( containing pattern ) . lines
                                        -- if only one file then parse it returning matching lines
                                        (_:[]) -> foreach files ( \file -> doesFileExist file >>= \existsp -> case existsp of
                                                                                                                True  -> readFile file >>= \content -> foreach ( lines content # containing pattern ) putStrLn
                                                                                                                False -> return () )
                                        -- if many files, parse them returning matching lines prepending each with the filename
                                        _      -> foreach files ( \file -> doesFileExist file >>= \existsp -> case existsp of
                                                                                                                True  -> readFile file >>= \content -> foreach ( lines content # containing pattern ) ( putStrLn . (++) ( file ++ ":" ) )
                                                                                                                False -> return () )
               _                   -> putStrLn "Syntax : hgrep <pattern> < searched > matching | hgrep <pattern> <searched-file> ... > matching"
