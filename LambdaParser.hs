module N.LambdaParser where

import Data.List
import Data.Char
import Data.Maybe

----------------------------
        Parser Part		
----------------------------

newtype Parser a =  P (String -> [(a,String)])

instance Monad Parser where
	return v =  P (\inp -> [(v,inp)])
	p >>= f =  P (\inp -> case parse p inp of
		[]        -> []
		[(v,out)] -> parse (f v) out)

failure :: Parser a
failure = P (\inp -> [])

item :: Parser Char
item = P (\inp -> case inp of
	[] -> []
	(x:xs) -> [(x,xs)])
	
parse :: Parser a -> String -> [(a,String)]
parse (P p) inp = p inp

--choice
(+++) :: Parser a -> Parser a -> Parser a
p +++ q = P (\inp -> case parse p inp of
	[] -> parse q inp
	[(v,out)] -> [(v,out)])

--parser sat
sat :: (Char -> Bool) -> Parser Char
sat p = do x <- item; if (p x) then (return x) else failure

---using sat to define parser of primitives----
digit :: Parser Char
digit = sat isDigit
lower :: Parser Char
lower = sat isLower
upper :: Parser Char
upper = sat isUpper
letter :: Parser Char
letter = sat isAlpha
alphanum :: Parser Char
alphanum = sat isAlphaNum
char :: Char -> Parser Char
char x = sat (==x)

---using char to define a parser for string xs----
string :: String -> Parser String
string [] = return []
string (x:xs) = do char x; string xs; return (x:xs)

--many and many1 parsers
many :: Parser a -> Parser[a]
many p = many1 p +++ return[]
many1 :: Parser a -> Parser[a]
many1 p= do v <- p; vs <- many p; return (v:vs)

--using many and many1 to define parser for identifiers--
ident :: Parser String
ident = do x <- lower; xs <- many alphanum; return (x:xs)

nat :: Parser Int
nat = do xs <- many1 digit; return(read xs)

space :: Parser ()
space = do many (sat isSpace); return()

---handling Spacing and Tokens---
token :: Parser a -> Parser a
token p = do space; v <- p; space; return v

---using tokens to define parsers that ignore spacing around idetifiers---
identifier :: Parser String
identifier = token ident
natural :: Parser Int
natural = token nat
symbol :: String -> Parser String
symbol xs = token (string xs)

-----sample arithmetic parser
data AExp = Add AExp AExp
          | Mul AExp AExp
          | Num Int
          deriving Show

expr :: Parser AExp
expr = (do t <- term; symbol "+"; e <- expr; return (Add t e)) +++ term

term :: Parser AExp
term = (do f <- factor; symbol "*"; t <- term; return (Mul f t)) +++ factor

factor :: Parser AExp
factor = (do symbol "("; e <- expr; symbol ")"; return e) +++ number

number :: Parser AExp
number = do n <- natural; return (Num n)

parse_arith :: String -> AExp
parse_arith str = case parse expr str of
                           [(ast,[])] -> ast
                           [(_,out)]  -> error ("unused input " ++ out)
                           []         -> error "invalid input"

---------------------------------------
         Lambda Calculus Parser		
---------------------------------------
						   
type Ide = String

data LExp = Var Ide
	| App LExp LExp
	| Lam Ide LExp
	deriving Show

exprs :: Parser LExp
exprs = lam +++ app +++ var	+++ parenExprs

lam :: Parser LExp
lam = (do symbol "/"; i <- identifier; symbol"."; e <- exprs; return (Lam i e))

app :: Parser LExp
app = (do symbol "("; e1 <- exprs; e2 <- exprs; symbol ")"; return (App e1 e2))

parenExprs :: Parser LExp
parenExprs = (do symbol "("; e <- exprs; symbol ")"; return e)

var :: Parser LExp
var = (do vl <- identifier; return (Var vl))

parse_lc :: String -> LExp
parse_lc lcs = case parse exprs lcs of
						[(ast,[])] -> ast
						[(_,out)]  -> error ("unused input " ++ out)
						[]         -> error "invalid input"

data DBExp = Ind Int
	| Apply DBExp DBExp
	| Abs DBExp
	deriving Show

dbexprs :: Parser DBExp
dbexprs = abst +++ appl +++ ind	+++ parenDBExprs

abst :: Parser DBExp
abst = (do symbol "/"; symbol"."; e <- dbexprs; return (Abs e))

appl :: Parser DBExp
appl = (do symbol "("; e1 <- dbexprs; e2 <- dbexprs; symbol ")"; return (Apply e1 e2))

parenDBExprs :: Parser DBExp
parenDBExprs = (do symbol "("; e <- dbexprs; symbol ")"; return e)

ind :: Parser DBExp
ind = (do i <- natural; return (Ind i))

parse_dblc :: String -> DBExp
parse_dblc dblcs = case parse dbexprs dblcs of
						[(ast,[])] -> ast
						[(_,out)]  -> error ("unused input " ++ out)
						[]         -> error "invalid input"


-------------------------------------------
    	Functions of lambda Calculus	
-------------------------------------------

--instance Show LExp where
--    show = unparse

unparse :: LExp -> String
unparse (Var v) = v
unparse (Lam v exp) = "(/" ++ v ++ "." ++ unparse exp ++ ")"
unparse (App fun arg) = "(" ++ (unparse fun) ++ " " ++ (unparse arg) ++ ")"

fv :: LExp -> [Ide]
fv (Var v) = [v]
fv (App fun arg) = union (fv fun) (fv arg)
fv (Lam v exp) = delete v (fv exp)

-- substitute v with exp in exp'
subst :: (Ide, LExp) -> LExp -> LExp
subst s@(v, exp) exp'@(Var y)
    | v==y = exp
    | otherwise = exp'
subst s@(v, exp) exp'@(App fun arg) = App (subst s fun) (subst s arg)
subst s@(v, exp) exp'@(Lam y exp'')
    | v==y = exp'
    | y `notElem` (fv exp) = Lam y (subst s exp'')
    | otherwise = Lam z (subst s (subst (y, Var z) exp''))
	    where z = newIde (y: (fv exp))

-- generate a new Ide which does not appear in xs
newIde :: [Ide] -> Ide
newIde xs = concat xs

-- returns [exp] if reducible, [] otherwise
betaReduce :: LExp -> [LExp]
betaReduce (App (Lam v fun) arg) = [subst (v,arg) fun]
betaReduce _ = []

-- returns [exp] if reducible, [] otherwise
etaReduce :: LExp -> [LExp]
etaReduce (Lam v (App exp (Var y)))
    | (v==y) && (v `notElem` fv(exp)) = [exp]
    | otherwise = []
etaReduce _ = []

-------------------
     Reduction
-------------------
eval :: LExp -> LExp
eval (App t1 t2) =	case eval t1 of
						(Lam a u) -> eval (subst (a, eval(t2)) u)
						t         -> App t (eval t2)
eval t = t

byValue :: LExp -> LExp
byValue t = bodies (eval t)
    where bodies (Lam a t) = Lam a (byValue t)
          bodies (App t u) = App (bodies t) (bodies u)
          bodies t         = t

headNF :: LExp -> LExp		  
headNF (Lam a t) = Lam a (headNF t)
headNF (App t u) = 
    case headNF t of
      (Lam a t') -> headNF (subst (a, t') u)
      u'         -> App u' u
headNF t = t

byName :: LExp -> LExp
byName = args . headNF
    where args (Lam a t) = Lam a (args t)
          args (App t u) = App (args t) (byName u)
          args t         = t
		  
reduce :: String -> String
reduce x = unparse(byValue(parse_lc(x)))


--------------------------------------------------------------------
    Converting lambda calculus expression into de Bruijn Indices 
--------------------------------------------------------------------

env':: LExp -> [Ide]
env' (Var var) = []
env' (Lam var exp) = (var:(env' exp))
env' (App fun arg) = (env' fun) ++ (env' arg)

lc2db :: LExp -> DBExp
lc2db ids@(Var var) = db_it ids  (env' ids)
lc2db lams@(Lam var exp) = Abs (db_it  exp (env' lams))
lc2db apps@(App fun arg) =  Apply (lc2db fun) (lc2db arg)

env_pos :: Ide -> [Ide] -> Int
env_pos a [] = error ("unbound variable " ++ a)
env_pos a (x:xs)= if (findIndex (==a) (x:xs)) == Nothing
					then error ("unbound variable " ++ a)
					else fromJust(findIndex (==a) (x:xs))

db_it :: LExp -> [Ide] -> DBExp
db_it e [] = error ("unbound variable" ++ show(unparse(e)))
db_it (Var var) env = Ind (env_pos var env)
db_it (Lam var exp) env = Abs (db_it exp env)
db_it (App fun arg) env = Apply (db_it fun env) (db_it arg env)

unparse_db :: DBExp -> String
unparse_db (Ind num) = show(num)
unparse_db (Abs exp) = "(/" ++ unparse_db exp ++ ")"
unparse_db (Apply fun arg) = "(" ++ (unparse_db fun) ++ " " ++ (unparse_db arg) ++ ")"

con_lc_db :: String -> String
con_lc_db str = unparse_db $ lc2db $ parse_lc str

--------------------------------------------------
               Compilation Function 
--------------------------------------------------
data Ins = ACCESS Int
	| GRAB Char Ins
	| PUSH (Ins) Char Ins
	deriving Show

compile	:: DBExp -> Ins
compile (Ind num) = ACCESS num
compile (Abs exp) = GRAB (';') (compile(exp))
compile (Apply fun arg) = PUSH (compile(arg)) (';') (compile(fun))

-----------------------------------------------
              lifting operation 
-----------------------------------------------

lift :: Int -> Int -> DBExp -> DBExp
lift k n (Ind i)
	| i < k = Ind i
	| otherwise = Ind (n + i - 1)
lift k n (Abs exp) = Abs ( lift (k + 1) n exp)
lift k n (Apply fun arg) = Apply (lift k n fun) (lift k n arg)

----------------------------------------------
           Substitution Function 
----------------------------------------------

subs :: DBExp -> (Int, DBExp) -> DBExp
subs (Ind i) (k, exp)
	| (i < k) = Ind i
	| (i == k) = lift 0 k exp
	| (i > k) = Ind (i - 1)
subs (Abs e) (k, exp) = Abs (subs e (k + 1, exp))
subs (Apply fun arg) (k, exp) = Apply (subs fun (k, exp)) (subs arg (k, exp))


---------------------------------------------
        Beta Reduction in de Bruijn
---------------------------------------------

reduction :: DBExp -> DBExp
reduction (Apply m@(Abs x) n) = subs x (0, n)

evalDB :: DBExp -> DBExp
evalDB a@(Apply m@(Abs x) n) = evalDB(reduction(a))
evalDB a@(Abs x) = Abs (evalDB(x))
evalDB a@(Ind x) = a
evalDB a@(Apply m n) = a


---------------------------------------------
              Krivine Machine 
---------------------------------------------
type Envi = [(Int,Value)]
type Closure = (Ins,[Envi])
data Value = Nil
	| Pair Closure
	deriving Show
type Stack = [Closure]
type Code = [Ins]
type State = (Code, Envi, Stack)

initial :: Ins -> State
initial a = ([a], [], [])

interp :: State -> State
interp ([PUSH e x f],g,h) = ([f],g, push (pair e [g]) (h))
interp ([GRAB x a],c,d) = ([a],(0, (Pair (pop d))):(envi'' (c)), apop (d))
interp a@([ACCESS i],j,k) = ([(getIns' a)],getEnvi' a,k)

pair :: a -> b -> (a,b)
pair  a b = (a,b)

unpair :: (a,b) -> b
unpair (a,b) = b

unpair' :: (a,b) -> a
unpair' (a,b) = a

push :: Closure -> Stack -> Stack
push a b = a:b

pop :: Stack -> Closure
pop (x:xs) = x

apop :: Stack -> Stack
apop (x:xs) = xs

envi'' :: Envi -> Envi
envi'' [] = []
envi'' (x:xs) = (update(x)) ++ (envi''(xs))

update :: (Int,Value) -> Envi
update x@((a,val)) = [(a+1,val)]

notEmpty :: Envi -> Bool
notEmpty a
	| length (a) /= 0 = True
	| otherwise = False

access'' :: Int -> Envi -> Value
access'' x e
	| notEmpty(e) = (enviChecker x e) 
	
enviChecker :: Int -> Envi -> Value
enviChecker a (x:xs)
	| (enviCheckVal(a) (x)) = capture(x)
	| otherwise = enviChecker (a) (xs)

capture :: (Int,Value) -> Value
capture (a,b) = b
 
enviCheckVal :: Int -> (Int,Value) -> Bool
enviCheckVal x (a,b)
	| x == a = True
	| otherwise = False

getIns' :: State -> Ins
getIns' ([ACCESS i],a,b)
	| notEmpty (a) = getIns'' (access'' i a)
	
getIns'' :: Value -> Ins
getIns'' (Pair y) = unpair'(y)

getEnvi' :: State -> Envi
getEnvi' ([ACCESS i],a,b)
	| notEmpty (a) = getEnvi'' (access'' i a)
	
getEnvi'' :: Value -> Envi
getEnvi'' (Pair y) = merge(unpair(y))

merge :: [Envi] -> Envi
merge a
	| length(a) == 0 = []
merge (x:xs) = x ++ merge xs

evalKAM :: State -> State
evalKAM ([GRAB x a],c,d)
	| length (d) == 0 = ([GRAB x a],c,d)
	| otherwise = evalKAM(interp ([GRAB x a],c,d))
evalKAM psh@(([PUSH e x f],g,h)) = evalKAM(interp (psh))
evalKAM accss@(([ACCESS i],j,k)) = evalKAM(interp (accss))

evaluate :: Ins -> State
evaluate strm = evalKAM (initial (strm))
