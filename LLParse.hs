-- -----------------------------
--
--  LL parser in Haskell (based on the LL parser in Scheme).
-- 
--  Written by Michael L. Scott for CSC 254, September 2004.
--  Translated to Haskell by Ryan Yates for CSC 254, September 2012.
--  Modified and extended, September 2005, 2006, 2008, 2009, 2011, and 2012.
--
--  To test this code, load it into GHCi and type, e.g.
--
--  > let prog = words "read a read b sum := a + b write sum write sum / 2 $$"
--  > parse (parseTable calcGrammar) prog
--
--  Note that the input program is a list of strings.
--
--  Note, also, that nothing in this file is input-language-specific,
--  other than sample grammars and inputs.  For the assignment you'll
--  need to add language-specific code to convert the parse tree into an
--  abstract syntax tree, to enforce semantic rules (if any), and to
--  interpret program input.
--
-- ------------------------------
module LLParse where

import Prelude hiding (last)
import Data.Char

import Control.Monad.Instances

--
-- This first section of the file contains utility routines that you may
-- find helpful.  I recommend you read all the routines carefully.
-- Understanding them (really, deeply understanding them) will help you
-- establish the mindset you need to write the rest of the code.
--

-- | Use the 'Ord' type class to quicksort a list.
sort :: Ord a => [a] -> [a]
sort []     = []
sort xs@[_] = xs
sort (x:xs) = sort as ++ (x : sort bs)
  where
    (as, bs) = partition x xs [] []
    partition _ [] as bs = (as, bs)
    partition e (c:cs) as bs
      | c < e     = partition e cs (c:as) bs
      | otherwise = partition e cs as (c:bs)

-- | Apply a function to the second entry in a pair.
second :: (b -> c) -> (a, b) -> (a, c)
second f (a, b) = (a, f b) -- Standard function found in Control.Arrow.

-- | Return list in which adjacent equal elements have been combined.
unique :: Eq a => [a] -> [a]
unique []     = []
unique xs@[_] = xs
unique (x:xs@(y:_)) 
  | x == y    = unique xs
  | otherwise = x : unique xs

-- | Sort (using the 'Ord' instance) and remove duplicates.
uniqueSort :: Ord a => [a] -> [a]
uniqueSort = unique . sort

-- | Return last element of list.
last :: [a] -> a
last [x] = x
last (_:xs) = last xs

-- | Return 'Just' the last element of list or 'Nothing'.
safeLast :: [a] -> Maybe a
safeLast []     = Nothing
safeLast [x]    = Just x
safeLast (_:xs) = safeLast xs

-- | Return 'Just' the tail of a list or 'Nothing'.
safeTail :: [a] -> Maybe [a]
safeTail []     = Nothing
safeTail (_:xs) = Just xs

-- | A 'Grammar' is a list of pairs of non-terminals and 
-- all their right-hand sides.
type Grammar = [(String, [[String]])]

-- | Return left-to-right fringe of tree as list.
gflatten :: Grammar -> [String]
gflatten [] = []
gflatten ((s,ps):ss) = s : concat ps ++ gflatten ss

startSymbol :: Grammar -> String
startSymbol ((s, _):_) = s

endMarker :: Grammar -> String
endMarker ((_, ps):_) = last (last ps)

-- | Return list of all nonterminals in grammar.
nonterminals :: Grammar -> [String]
nonterminals rs = map fst rs

-- | Return list of all symbols in grammar (no duplicates).
gsymbols :: Grammar -> [String]
gsymbols g = unique . sort . gflatten $ g

-- | Return list of all terminals in grammar.
terminals :: Grammar -> [String]
terminals g = filter (not . (`isNonterminal` g)) . gsymbols $ g

-- |  Does string s start with a letter and contain only letters and digits?
isIdentifier :: String -> Bool
isIdentifier [] = False
isIdentifier (c:cs)  = isAlpha c && all isAlphanumeric cs
  where isAlphanumeric c = isAlpha c || isDigit c

-- | Does string contain only digits?
isGNumber :: String -> Bool
isGNumber s = case readsInt s of
    [(n, [])] -> True
    _         -> False
  where
    readsInt = reads :: ReadS Int

-- | Convert symbols of L to pairs of strings, in which
-- the car of each pair is the parser's notion of terminal (e.g. "num")
-- and the cadr of each pair is the actual input token (e.g. "12345").
-- (This works only if parentheses in the input program are balanced.)
-- Note also that this code does not currently distinguish between
-- integer and real-number constants.
-- It also requires white space between any two adjacent symbols other
-- than parentheses.
tokenize :: [String] -> Grammar -> [(String, String)]
tokenize ss g = map h ss
  where 
    h t
      | isGNumber t      = ("num", t)
      | t `isTerminal` g && t /= "num"
                         = (t, t)
      | isIdentifier t   = ("id", t)
      | otherwise        = ("??", t)

-- | Return list of all productions in grammar.
-- Each is represented as a (lhs rhs) pair, where rhs is a list.
productions :: Grammar -> [(String, [String])]
productions g = [(s,p) | (s,ps) <- g, p <- ps]

-- | Is s a nonterminal?
isNonterminal :: String -> Grammar -> Bool
isNonterminal s g = elem s (nonterminals g)

-- | Is s a symbol in grammar?
isGSymbol :: String -> Grammar -> Bool
isGSymbol s g = elem s (gsymbols g)

-- | Is s a terminal in grammar?
isTerminal :: String -> Grammar -> Bool
isTerminal s g = isGSymbol s g && not (isNonterminal s g)

-- | Join lists together keeping only the unique elements.
union :: Ord a => [[a]] -> [a]
union = unique . sort . concat


-- Two equivalent versions of 'rightContext' are given for your edification.

-- | Return a list of pairs.
-- Each pair consists of a symbol A and a list of symbols beta
-- such that for some alpha, A -> alpha B beta.
rightContext' :: String -> Grammar -> [(String, [String])]
rightContext' b g = [(s, ps) | Just (s, ps) <- map h . productions $ g]
  where
    h (s, []) = Nothing  -- 'b' was not found.
    h (s, p:ps)
      | p == b    = Just (s, ps) -- We found 'b' now return 'beta'.
      | otherwise = h (s, ps)    -- keep looking.

-- | Return a list of pairs.
-- Each pair consists of a symbol A and a list of symbols beta
-- such that for some alpha, A -> alpha B beta.
rightContext :: String -> Grammar -> [(String, [String])]
rightContext b g = [(s, ps) | (s, Just ps) <- map (second h) . productions $ g]
  where
    h = safeTail . dropWhile (/= b)

-- Note: In a list comprehension any values that do not match the pattern
-- binding 's' and 'ps' will be ignored (as opposed to errors).  For example
--
--   ghci> [x | (Just x) <- [Nothing]]
--   []
--   ghci> let f (Just x) = x in f Nothing
--   *** Exception: Non-exhaustive patterns in function f
--


-- --------------------------------------------------------------
--
--  Here is our good friend the calculator language,
--  in the form expected by the parser generator.
--  We've also provided the sum-and-average program
--
--  Note that all symbols in the grammar are 'Strings'.
-- 
calcGrammar =
    [ ("P",  [["SL", "$$"]])
    , ("SL", [["S", "SL"], []])
    , ("S",  [["id", ":=", "E"], ["read", "id"], ["write", "E"]])
    , ("E",  [["T", "TT"]])
    , ("T",  [["F", "FT"]])
    , ("TT", [["ao", "T", "TT"], []])
    , ("FT", [["mo", "F", "FT"], []])
    , ("ao", [["+"], ["-"]])
    , ("mo", [["*"], ["/"]])
    , ("F",  [["id"], ["num"], ["(", "E", ")"]])
    ]

-- A program as a list of strings.
sumAndAve = [ "read", "a"
            , "read", "b"
            , "sum", ":=", "a", "+", "b"
            , "write", "sum"
            , "write", "sum"
            , "/", "2"
            , "$$"
            ]

-- --------------------------------------------------------------
--
--  Here is the extended calculator grammar, with if and while statements.
--  To demonstrate that the language is no longer a complete toy, we've
--  provided a (rather slow) program to compute the first N prime numbers.
--
--  Feel free to experiment with other grammars and inputs.
--
extendedCalcGrammar =
    [ ("P",  [["SL", "$$"]])
    , ("SL", [["S", "SL"], []])
    , ("S",  [ ["id", ":=", "E"], ["read", "id"], ["write", "E"]
             , ["if", "C", "SL", "end"], ["while", "C", "SL", "end"]
             ])
    , ("C",  [["E", "rn", "E"]])
    , ("rn", [["=="], ["!="], ["<"], [">"], ["<="], [">="]])
    , ("E",  [["T", "TT"]])
    , ("T",  [["F", "FT"]])
    , ("TT", [["ao", "T", "TT"], []])
    , ("FT", [["mo", "F", "FT"], []])
    , ("ao", [["+"], ["-"]])
    , ("mo", [["*"], ["/"]])
    , ("F",  [["id"], ["num"], ["(", "E", ")"]])
    ]

primes = words "read n                           \n\
               \cp := 2                          \n\
               \while n > 0                      \n\
               \    found := 0                   \n\
               \    cf1 := 2                     \n\
               \    cf1s := cf1 * cf1            \n\
               \    while cf1s <= cp             \n\
               \        cf2 := 2                 \n\
               \        pr := cf1 * cf2          \n\
               \        while pr <= cp           \n\
               \            if pr == cp          \n\
               \                found := 1       \n\
               \            end                  \n\
               \            cf2 := cf2 + 1       \n\
               \            pr := cf1 * cf2      \n\
               \        end                      \n\
               \        cf1 := cf1 + 1           \n\
               \        cf1s := cf1 * cf1        \n\
               \    end                          \n\
               \    if found == 0                \n\
               \        write cp                 \n\
               \        n := n - 1               \n\
               \    end                          \n\
               \    cp := cp + 1                 \n\
               \end                              \n\
               \$$"

-- --------------------------------------------------------------
--
--  Next comes the parser generator.
--  The main entry routine is 'parseTable', which takes a grammar as argument
--  (in the format shown above) and returns an LL(1) parse table as a result.
--  The table looks like the grammar, except that each RHS is replaced with a
--  (predict-Set, RHS) pair.  The computational heart of the algorithm is function
--  getKnowledge.
--
--  Much of the following employs a "Knowledge" data type.
--  It's a list of "KnowledgeEntry"s, one for each nonterminal,
--    in the same order those nonterminals appear in the grammar
--    (the order is important).

type ParseTable = [(String, [([String], [String])])]

data KnowledgeEntry = KnowledgeEntry
    { knowNonterminal :: String   -- ^ Nonterminal A [not needed computationally,
                                  -- but included for readability of output]
    , knowEpsilon     :: Bool     -- ^ Do we currently think A can -->* epsilon
    , knowFirst       :: [String] -- ^ (current guess at) FIRST(A)
    , knowFollow      :: [String] -- ^ (current guess at) Follow(A)
    }
  deriving (Show, Eq)

type Knowledge = [(String, KnowledgeEntry)]

-- | Return knowledge structure with empty FIRST and FOLLOW sets
-- and false gen-epsilon estimate for all symbols.
initialKnowledge :: Grammar -> Knowledge
initialKnowledge = map (\a -> (a, KnowledgeEntry a False [] [])) . nonterminals

-- | Return KnowledgeEntry for a given A.
symbolKnowledge :: String -> Knowledge -> Maybe KnowledgeEntry
symbolKnowledge = lookup

-- | Can w generate epsilon based on current estimates?
-- if w is a terminal, no
-- if w is a nonterminal, look it up
-- if w is an empty list, yes
-- if w is a non-empty list, "iterate" over elements
generatesEpsilon :: String -> Knowledge -> Grammar -> Bool
generatesEpsilon w k g 
    | w `isTerminal` g = False
    | otherwise        = maybe False knowEpsilon (symbolKnowledge w k)

-- | Return FIRST(w), based on current estimates.
-- if w is a terminal, return (w)
-- if w is a nonterminal, look it up
-- if w is an empty list, return []  (empty set)
-- if w is a non-empty list, "iterate" over elements
first :: [String] -> Knowledge -> Grammar -> [String]
first [] _ _ = []
first (w:ws) k g = helper w ++ if generatesEpsilon w k g 
                                 then first ws k g
                                 else []
  where
    helper w
      | w `isTerminal` g = [w]
      | otherwise        = maybe [] knowFirst (symbolKnowledge w k)

-- | Return FOLLOW(A), based on current estimates.
-- Simply look it up.
follow :: String -> Knowledge -> [String]
follow a k = maybe [] knowFollow (symbolKnowledge a k)

-- | Return knowledge structure for grammar.
-- Start with 'initialKnowledge grammar' and "iterate",
-- until the structure doesn't change.
-- Uses 'rightContext b grammar', for all nonterminals 'b',
-- to help compute follow sets.
getKnowledge :: Grammar -> Knowledge
getKnowledge g = helper (initialKnowledge g)
  where
    rcs = map (`rightContext` g) (nonterminals g) :: [[(String, [String])]]
    helper k | k == k'   = k
             | otherwise = helper k'
      where
        k' = zipWith3 update k g rcs
        update :: (String, KnowledgeEntry) -> (String, [[String]]) -> [(String, [String])] -> (String, KnowledgeEntry)
        update (_, KnowledgeEntry nt e kfirst kfollow) (_, ps) cs = 
            (nt, KnowledgeEntry
              nt
              (e || or (map gen ps))
              (union $ [kfirst, concatMap first' ps])
              (union $ [kfollow, concatMap first' (map snd cs), concatMap ff cs]))
          where
            first' s  = first s k g
            gen    ss = all (\s -> generatesEpsilon s k g) ss
            ff (s,w) 
              | gen w     = follow s k
              | otherwise = []

-- | Return parse table for grammar.
-- Uses the 'getKnowledge' function above.
parseTable :: Grammar -> ParseTable
parseTable g = map h g
  where
    k = getKnowledge g
    h (l, rs) = (l, map f rs)
      where
        f r = (union [first r k g, if all (\r -> generatesEpsilon r k g) r then follow l k else []], r)

-- | Double-index to find prediction (list of RHS symbols) for
-- nonterminal nt and terminal t.
-- Return 'Nothing' if not found.
parseLookup :: String -> String -> ParseTable -> Maybe [String]
parseLookup nt t table = maybe Nothing helper (lookup nt table)
  where
    helper []       = Nothing
    helper ((as,bs):ps)
      | t `elem` as = Just bs
      | otherwise   = helper ps

--
-- The main parse routine below returns a parse tree as a 'Right' value
-- (or a Left error message if the program is syntactically invalid).
-- To build that tree it employs a simplified version of the "attribute
-- stack" described in Section 4.5.2 (pages 54-57) of the PLP CD.
--
-- When it predicts A -> B C D, the parser pops A from the parse stack
-- and then, before pushing D, C, and B (in that order), it pushes a
-- number (in this case 3) indicating the length of the right hand side.
-- It also pushes A into the attribute stack.
--
-- When it matches a token, the parser pushes this into the attribute
-- stack as well.
--
-- Finally, when it encounters a number (say k) in the stack (as opposed
-- to a character string), the parser pops k+1 symbols from the
-- attribute stack, joins them together into a list, and pushes the list
-- back into the attribute stack.
--
-- These rules suffice to accumulate a complete parse tree into the
-- attribute stack at the end of the parse.
--
-- Note that everything is done functionally.  We don't really modify
-- the stacks; we pass new versions to a tail recursive routine.
--

-- | Extract grammar from a 'ParseTable', so we can invoke the various 
-- routines that expect a grammar as argument.
toGrammar :: ParseTable -> Grammar
toGrammar table = map (second (map snd)) table

-- A generic tree with n branches to hold the parse.
data Tree a = Node a (Forest a)
    deriving (Show, Eq)
type Forest a = [Tree a]
type ParseTree = Tree String
type AttributeStack = Forest String

-- | Pop n + 1 symbols off the attribute stack,
-- assemble into a production, and push back onto the stack.
reduceOneProd :: AttributeStack -> Int -> AttributeStack
reduceOneProd as n = h (1+n) as []
  where
    h 0 as     (Node p []:ps) = Node p (ps) : as
    h n (a:as) ps     = h (n-1) as (a:ps)

-- Distinguish between numbers on the stack and symbols.
data ParseStackEntry = PNum Int | PSym String
    deriving (Show, Eq)

-- | Main parsing function.
parse :: ParseTable -> [String] -> Either String ParseTree
parse table p = helper [PSym (startSymbol g)] (tokenize p g) []
  where
    g = toGrammar table

    die s = Left ("syntax error: " ++ s) -- We die on the first error

    helper [] [] (a:_)  = Right a
    helper [] _  _      = die "extra input beyond end of program"
    helper (PNum n:ps) ts as = 
        -- We've reached the end of a production.  Pop lhs and rhs
        -- symbols off astack, join into list, and push back into astack.
        helper ps ts (reduceOneProd as n)
    helper _      [] as = die "unexpected end of program"
    helper (PSym t:ps) ts'@((term,token):ts) as
        | t `isTerminal` g = 
            if t == term
              then helper ps ts (Node token []:as) -- note push of token into astack
              else die (concat ["expected ", t, "; saw ", token])
        | otherwise        =
            case parseLookup t term table of
              Just rhs -> 
                helper
                  (map PSym rhs ++ PNum (length rhs) : ps)
                  ts'
                  (Node t []:as) -- note push of lhs into astack
              Nothing  -> die (concat ["no prediction for ", t, " when seeing ", token])

-- --------------------------------------------------------------
--
-- Everything above this point in the file is complete and (I think)
-- usable as-is.  The rest of the file, from here down, is a skeleton
-- for the extra code you need to write.  It has been excised from my
-- working solution to the assignment.  You are welcome, of course, to
-- use a different organization if you prefer.  This is provided in the
-- hope you may find it useful.
--

-- First some types to represent the abstract syntax
type AST = [Statement]
type Ident = String
type Value = Integer

data Expr = Lit Value | Var Ident | Op String Expr Expr
  deriving (Show, Eq)

data Statement = Ident := Expr 
               | Read Ident 
               | Write Expr 
               | If Cond [Statement]
               | While Cond [Statement]
  deriving (Show, Eq)

data Cond = Cond String Expr Expr
  deriving (Show, Eq)

-- You will need to write code to map from the `ParseTree`
-- to the AST.  Where you see 'undefined' you will have
-- to fill in with an actual implementation.
toAstP :: ParseTree -> AST
toAstP (Node "P" fo) = toAstSL (head fo)  --Modified_ 

-- Replace the 'something' with a pattern match which will bind the
-- correct 's' and 'sl' so the RHS can be:  toAstS s : toAstSL sl
toAstSL :: ParseTree -> AST
toAstSL (Node "SL" (s:sl)) = toAstS s :toAstSL (head sl) {- toAstS s : toAstSL sl -}
toAstSL _ =[] 

toAstS :: ParseTree -> Statement
-- Here you will want a pattern match on each LHS matching
-- each RHS of the Statement data type.
toAstS (Node "S" [Node "read" _,Node x _]) = Read x 
toAstS (Node "S" [Node "write" _, e1@(Node "E" _)]) = Write (toAstE e1)
toAstS (Node "S" [Node "while" _, c1@(Node "C" _), sl1@(Node "SL" _), (Node "end" _)]) = While (toAstC c1) (toAstSL sl1)
toAstS (Node "S" [Node "if" _,    c1@(Node "C" _), sl1@(Node "SL" _), (Node "end" _)]) = If (toAstC c1) (toAstSL sl1)
toAstS (Node "S" [Node lit _ , (Node ":=" _) , e1@(Node "E" _ )]) = lit := (toAstE e1)


-- Handle "C"
toAstC :: ParseTree -> Cond
toAstC (Node "C" [ e1@(Node "E" _), ro@(Node "rn" [Node rnop []]), e2@(Node "E" _)] ) = Cond rnop (toAstE e1) (toAstE e2)

-- Handle "E""T""FT" 
toAstE :: ParseTree -> Expr
-- If F is Lit or F is Var
toAstE (Node "F" [Node x []])
	|isGNumber x = Lit (read x :: Integer)
	|isIdentifier x = Var x
-- If F is ( E )
toAstE (Node "F" [ (Node "(" []), ee@(Node "E" _), (Node ")" [])]) = toAstE ee
-- For E and T, convert the first nonterminal, 
-- give the output to the conversion routine for second nonterminal and return the correct AST
toAstE (Node "E" [ t@(Node "T" _), tt@(Node "TT" _) ]) = toAstETail (toAstE t) tt
toAstE (Node "T" [ f@(Node "F" _), ft@(Node "FT" _) ]) = toAstETail (toAstE f) ft 

-- The second function 'toAstETail' handles TT and FT
toAstETail :: Expr -> ParseTree -> Expr
--base cases for TT and FT
toAstETail e (Node "TT" []) = e
toAstETail e (Node "FT" []) = e
--nontrivial cases, bind the left child of tree with its parents and right sibling from a recursive call.
toAstETail e (Node "TT" [ (Node "ao" [Node binop []]) , t1, tt2 ]) = toAstETail (Op binop e (toAstE t1) ) tt2
toAstETail e (Node "FT" [ (Node "mo" [Node binop []]) , f1, ft2 ]) = toAstETail (Op binop e (toAstE f1) ) ft2

-- -----------------------------------------------------

-- Model the state of the calculator
data Environment = Env 
    { envValues :: [(String, Value)]
    , envInput  :: [String]
    , envOutput :: [String]
    }
  deriving (Show, Eq)

-- Memory

-- Be sure to understand this type!  Use 'Left' values to
-- indicate errors.
lookupEnv :: String -> Environment -> Either String Value
-- lookupEnv _ _ = undefined

-- if find no such var in list, return Left w/ error message.
lookupEnv var (Env [] _ _)= Left $ "Attempt to use uninitialized variable: " ++ var ++ ". Evaluation Aborted."
-- if find var, return its value
lookupEnv var (Env ((a,b):xs) ein eout) 
	| a == var = Right b
	| otherwise = lookupEnv var (Env xs ein eout)

updateEnv :: String -> Environment -> Value -> Environment
--updateEnv _ _ _ = undefined
updateEnv var (Env env ein eout) value = (Env (pil env var value)  ein eout)
	where
	--helper function pil for updating bindings
	pil:: [(String,Value)] -> String -> Value -> [(String,Value)]	
	pil [] var value = [(var,value)]	-- if first seen, add pair to end of list
	pil ((a,b):xs) var value 		-- if seen before, update var with new value 
		| a == var = (a,value):xs
		| otherwise = (a,b):(pil xs var value)

-- IO

-- readEnv
readEnv :: Environment -> Either String (Environment, Value)
-- read an empty input list means not enough argument is provided.
readEnv (Env env []  eout)  = Left "Not enough argument provided. Evaluation aborted."
-- read an input list with some more argument
readEnv (Env env (x:xs) eout)  
		| isGNumber x = Right $ ((Env env xs eout), (read x :: Integer)) -- Next input is number.
		| otherwise = Left $ "Non-numerical Input: "++ x		 -- Catch Non-numerical input.


-- writeEnv
writeEnv :: Environment -> String -> Environment
-- Put new output as head of output list.
-- This list will be reversed after evaluation of whole AST.
writeEnv (Env env ein eout) x =  (Env env ein (x:eout))
-- -------------------------------------------------------

-- The next two functions are complete and illustrate using
-- 'do' notation to handle errors without our writing explicit
-- handling of error cases.

-- Entry Point of Whole Program
interpret :: ParseTable -> [String] -> [String] -> Either String [String]
interpret table program input = do
    t <- parse table program
    let ast = toAstP t
    interpretAst ast input

-- Evaluate Abstract Syntax Tree
interpretAst :: AST -> [String] -> Either String [String]
interpretAst ast input = do
    (Env _ _ output) <- interpretSL ast (Env [] input [])
    Right $ reverse output

-- Evalueate Statement List 
interpretSL :: [Statement] -> Environment -> Either String Environment
-- Statement List base case when no more statment left: 
-- do nothing and return the current environment.
interpretSL [] env = Right env
-- Statement List:
-- Interprete the first statement, then interepret the rest of statment list with the updated Enviroment.
interpretSL (st:stml) env = do
	env2 <- interpretS st env
	interpretSL stml env2

-- Evaluate Statement
interpretS :: Statement -> Environment -> Either String Environment
-- Statement Read
interpretS (Read var) (Env env ein eout) = do 	
			((Env env2 ein2 eout2) , b) <- readEnv (Env env ein eout) 	-- read from Env
			Right (Env ((var,b):env) ein2 eout)	-- update bindings

-- Statement Write
interpretS (Write expr) env = do 
	value <- interpretE expr env       -- First Evaluate Expr
	Right (writeEnv env (show value))  -- Write to Output the value of Expr

-- Statement If
interpretS (If cond stmt) env = do
	b <- interpretCond cond env  		 -- First evaluate Cond
	case b of True -> interpretSL stmt env	 -- If Cond is True - Evaluate block return updated Env
	          False -> Right env		 -- If Cond is False - Do Nothing return current Env

-- Statement While
interpretS (While cond stmt) env = do		
	b <- interpretCond cond env			-- First evaluate Cond
	case b of True -> do				-- If Cond is True
			k <- interpretSL stmt env	-- 	evaluate block & return updated Env
		        interpretS (While cond stmt) k  -- 	evaluate While stmt with newly updated Env
		  False -> Right env			-- If Cond is False, return current Env

-- Statement Ident := Expr
interpretS (x := expr) env = do
	value <- interpretE expr env		-- First evaluate RHS Expr
	Right $ updateEnv x env value 		-- Update Env with new value 

-- Interpret Cond
interpretCond :: Cond -> Environment -> Either String Bool
interpretCond (Cond rop expr1 expr2) env = do
	e1<- interpretE expr1 env			-- Evaluate Expr 1
	e2<- interpretE expr2 env			-- Evaluate Expr 2
	case rop of "==" -> Right $ e1 == e2		-- Get Logical Value According to Different Logical Operator
		    "!=" -> Right $ e1 /= e2
		    ">=" -> Right $ e1 >= e2
		    ">"  -> Right $ e1 >  e2
		    "<"  -> Right $ e1 <  e2
		    "<=" -> Right $ e1 <= e2

-- Interpret Expr
interpretE :: Expr -> Environment -> Either String Value
-- Expr is Lit : Return value of LIt
interpretE (Lit x) env = Right x
-- Expr is Var : Look up from Env
interpretE (Var x) env = do 
		lookupEnv x env
-- Expr is (Op binop e1 e2)
interpretE (Op binop e1 e2) env =  do
		re1 <- (interpretE e1 env)  		-- Evaluate Expr 1
		re2 <- (interpretE e2 env)		-- Evaluate Expr 2
		-- Evaluate According to Different Binary Operator
	 	case binop of "+" -> Right $ re1 + re2
			      "-" -> Right $ re1 - re2
		              "*" -> Right $ re1 * re2
		              "/" -> 
				-- Catch Division by 0 Using Left
				case re2 of 0 -> Left  "Division by 0 detected. Evaluation Aborted."
				-- Otherwise return value after division
					    _ -> Right $ div re1 re2

-- -----------------------------------------------------
p=words "read n \n\
\i := 0 \n\
\sum := 0 \n\
\while i != n \n\
\read k \n\
\sum := sum + k \n\
\i := i + 1 \n\
\end \n\
\avg := sum / n \n\
\write avg \n\
\$$ "

pread = words "read n $$"
