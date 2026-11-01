\section{Tiny Weakest Precondition}
\begin{verbatim}
Copyright Andrew Buttefield (c) 2026

LICENSE: BSD3, see file LICENSE at tiny-wp root
\end{verbatim}
\begin{code}
module TinyWP (
  iamtinywp
)
where

import Data.List(intercalate,nub,intersperse)
import qualified Data.Map as M
import Data.Map(Map)

iamtinywp :: String
iamtinywp = "I am TinyWP!"

--import Debug.Trace
--dbg msg x = trace (msg++show x) x
\end{code}

\newpage
\subsection{Syntax}

\subsubsection{Variables, Names}

\begin{code}
type Var = String
type Name = String
\end{code}

\subsubsection{Substitutions}

\begin{code}
type Subs t = [(Var,t)]  -- [v1->t1,v2->t2,...,vn->tn]
\end{code}


\subsubsection{Expressions}

\begin{code}
data Expr
  = B Bool
  | I Int
  | V Var
  | F String [Expr]     -- function apply f(e1,e2,...,en)
  | S Expr (Subs Expr)  -- substitution e0[v1->e1,v2->e2,...,vn->en]
  deriving (Eq,Ord,Show,Read)
\end{code}


\subsubsection{Predicates}

\begin{code}
data Pred
  = T                   -- true
  | X                   -- false
  | A Expr              -- atomic predicate (e :: Bool)
  | P Name [Pred]       -- propositional operator  p(p1,p2,...,pn)  
  | Q Name Var Pred     -- quantifier    Q q @ p
  | R Pred (Subs Pred)  -- predicate replacement p0[v1->p1,v2->p2,...,vn->pn]
  deriving (Eq,Ord,Show,Read)
\end{code}

\subsubsection{Programs}

\begin{code}
data Prog
  = U -- undefined
  | II  -- skip
  | Prog ::: Prog
  | Var := Expr
  | Cond Expr Prog Prog
  | Loop Expr Prog
  deriving (Eq,Ord,Show,Read)
\end{code}

\newpage
\subsection{Weakest Precondition}

\begin{code}
wp :: Prog -> Pred -> Pred
wp II       p   =  p
wp (v := e) p   =  peSub p [(v,e)]
wp (p ::: q) r  =  wp p (wp q r)
wp prog r = P "and" [r,X] -- need time to thinks this through
\end{code}


\newpage
\subsection{Pretty-Printing}

We need to know sizes of text constructs and how things are logically nested.
We adopt the following ``sized string-tree'' data-structure to record this,
and some useful support functions.
\begin{code}
data SST -- Sized String-Tree
  = SST Int String [SST]
  deriving (Show,Read)


v2SST :: String -> SST
v2SST v = SST (length v) v []

sstlen :: SST -> Int
sstlen (SST len _ _)  =  len

onelineSST :: SST -> String
onelineSST (SST _ hdr ssts) = hdr ++ (concat $ map onelineSST ssts)

checkSST :: SST -> Int
checkSST sst@(SST len _ _) = len - length (onelineSST sst)

examine :: SST -> IO ()
examine sst = putStrLn $ unlines 
  [ ""
  , "==="
  , "Check: " ++ show (checkSST sst)
  , "OneLine:"
  , onelineSST sst
  , "---"
  , "Expr:"
  , show sst
  , "---"
  ]
\end{code}
The code below defines a standard instrumented rendering of an object,
assuming no width restrictions.

We will also want to know if a function is usually rendered using infix notation.
We provide a (partial) lookup table mapping function names to fixity information
(precedence,associativity):
\begin{code}
data FunRender 
  = Prefix  -- standard prefix function  f(e1,...,en)
  | Unary   -- prefix, with n=1
  | Binary  -- Infix, with n=2 only
  | LInfix  -- Left Infix    e op f op g   is  op(op(e,f),g)
  | RInfix  -- Right Infix    e op f op g   is  op(e,op(f,g))
  | Infix   -- Fully Infix   e op f op g   is  op(e,f,g)
  deriving (Eq,Show,Read)
type Infixes = Map String (Int,FunRender)

assocLkp :: Int -> Infixes -> String -> (Int,FunRender)
assocLkp tightest infixes str = case M.lookup str infixes of
  Nothing  ->  (tightest,Prefix)
  Just ia  ->  ia
\end{code}
If a name is not in the domain of the map then 
it is assumed to be a prefix function name.
For now we have a global map, 
but this may become a pretty-printing parameter at some future time.
The following is the fixity list from Haskell 2010.
\begin{verbatim}
infixr 0  $  $! `seq`
infixl 1  &  >>=  >>  >=>
infixr 2  ||
infixr 3  &&
infix 4   ==  /=  <  >  <=  >=  `elem`  `notElem`
infixl 4  <$  <$>  $>  <*  <*>  *>
infixl 5  .|.  :  ++
infixl 6  +  -
infixl 7  *  /  `div`  `mod`  .&.
infixr 8  **  ^  ^^
infixr 9  .
\end{verbatim}
\begin{code}
givenInfixes :: Infixes
givenInfixes = M.fromList
  [ ("or",(20,Infix))
  , ("and",(30,Infix))
  , ("not",(40,Unary))
  , ("eq",(40,Binary))
  , ("neq",(40,Binary))
  , ("lt",(40,Binary))
  , ("gt",(40,Binary))
  , ("le",(40,Binary))
  , ("ge",(40,Binary))
  , ("add",(60,Infix))
  , ("sub",(60,LInfix))
  , ("mul",(70,Infix))
  , ("dvd",(70,LInfix))
  , ("div",(70,LInfix))
  , ("mod",(70,LInfix))
  , ("exp",(80,RInfix))
  ]

givenTightest :: Int
givenTightest = maximum $ map fst $ M.elems givenInfixes

funrender :: String -> (Int,FunRender)
funrender = assocLkp givenTightest givenInfixes
\end{code}

\subsubsection{Expression Pretty-Printing}

Our standard rendering of atomic expressions produces one of the following forms
\begin{mathpar}
  T \and F \and 42 \and v 
\end{mathpar}
\begin{code}
expr2SST :: Expr -> SST
expr2SST (B b)     =  SST 1 (if b then "T" else "F") []
expr2SST (I i)     =  SST (length s) s [] where s = show i
expr2SST (V v)     =  SST (length v) v []
\end{code}
Our standard rendering of an function application 
produces one of the following forms
(here the $\oplus$ refers to 
the repetition of a single infix operator symbol)
:
\begin{mathpar}
  f(e_1,\dots,e_n) \and e_1 \oplus e_2 \oplus \dots \oplus e_n
\end{mathpar}
\begin{code}
expr2SST (F f [])  =  SST (length f+2) (f++"()") []
expr2SST (F f es)  --  f(e1,...,en)
  = case funrender f of
      fr@(_,Prefix)  ->  prefix2SST f es
      _              ->  prefix2SST f es -- temporary
\end{code}
Our standard rendering of substitution
produces the following forms
\begin{mathpar}
  e[e_1,...,e_n/x_1,...,x_n] \and e~\text{ if } n=0
\end{mathpar}
\begin{code}
expr2SST (S e [])  =  expr2SST e
expr2SST (S e subs) -- e[e1,...,en/]
  = let
      eSST@(SST sublen head eSSTs) = expr2SST e
      openSub = SST 1 "[" []
      sep = SST 1 "," []
      sub = SST 1 "/" []
      closeSub = SST 1 "]" []
      (targets,replacements) = unzip subs
      repSSTs = map expr2SST replacements
      tgtlist = intersperse sep $ map v2SST targets
      replist = intersperse sep repSSTs
      lengthS = sublen + 3 
              + (sum $ map sstlen replist)  + (sum $ map sstlen tgtlist)
    in SST lengthS head 
         (eSSTs++[openSub]++replist++[sub]++tgtlist++[closeSub])
\end{code}

Handling function rendering cases:
\begin{code}
prefix2SST :: String -> [Expr] -> SST
prefix2SST f es -- f(e1,...,en)
  = let
      flen = length f
      fname = SST flen f []
      openpar = SST 1 "(" []
      sep = SST 1 "," []
      sepcount = length args - 1  
      closepar = SST 1 ")" []
      args = map expr2SST es
      sstlist = intersperse sep args
      lengthF = flen + 2 + sepcount + sum (map sstlen args)
    in SST lengthF f ((openpar:sstlist)++[closepar])
\end{code}


\subsection*{DEPRECATED MATERIAL BELOW}

With pretty-printers we have an object to render, 
with a maximum width (\texttt{w}) we are allowed to use,
requiring us to use linebreaks in a pleasing manner.


For rendering, we then introduce the notion of a ``box'',
which is zero or more strings.
The idea is that we apply indentation at the box level.
We also have an intermediate structure 
where each string is annotated with its length.
\begin{code}
type Box = [String]
type SizedBox = [(Int,String)]

sizeBox :: Box -> SizedBox
sizeBox box = map (\ s -> (length s,s)) box

boxWidth :: Box -> Int
boxWidth = maximum . map length

indBox :: Int -> Box -> Box
indBox i box = map ((replicate i ' ')++) box

renderBox :: Box -> String
renderBox = reverse . strip . reverse . unlines

strip :: String -> String
-- removes zero or more initial newlines
strip "" = ""
strip str@(c:cs)
  | c == '\n'  =  strip cs
  | otherwise  =  str
\end{code}
Basically, our pretty-printer converts an object into a large \texttt{Box},
which they can render. 
The available width \texttt{w} is used by heuristics to best split the output 
over multiple lines.

\subsubsection{Syntax Pretty Printers}


\begin{code}
ppSub :: Int -> (Int -> t -> String) -> Subs t -> String
ppSub w ppt sub 
  = let (vs,ts) = unzip sub
    in "[" ++intercalate "," vs 
           ++ "/"
           ++ intercalate "," (map (ppt w) ts) ++ "]"

ppExpr :: Int -> Expr -> String
-- ppExpr w (B b)      =  if b then "T" else "F"
-- ppExpr w (I i)      =  show i
-- ppExpr w (V v)      =  v
ppExpr w (F f es)   =  ppFun w f es
ppExpr w (S e sub)  =  ppExpr w e ++ ppSub w ppExpr sub
ppExpr w expr = renderBox $ map snd $ ppE w expr

ppE :: Int -> Expr -> SizedBox
ppE _ (B b)  =  [(1,if b then "T" else "F")]
ppE _ (I i)  =  [(length s,s)] where s = show i
ppE _ (V v)  =  [(length v,v)]
ppE _ (F f [])  =  [(length f+2,f++"()")]
ppE w (F f es)
  =  let
       flen = length f
       fbox = [(flen,f)]
       esboxes = map (ppE w) es
     in concat (fbox:esboxes)
ppE w (S e sub) = [(19,"ppE w (S e sub) NYI")]

ppFun :: Int -> String -> [Expr] -> String
ppFun w f es  =  f ++ "("++intercalate "," (map (ppExpr w) es)++")"

ppPred :: Int -> Pred -> String
ppPred w = reverse . strip . reverse . unlines . ppPreds w

ppPreds :: Int -> Pred -> [String]
ppPreds w T     = ["T"]
ppPreds w X     = ["F"]
ppPreds w (A e) = [ppExpr w e]
ppPreds w (P p ps) = ppProp w p ps
ppPreds w (Q q x p) = [q++" "++x++" @ " ++ ppPred w p]
ppPreds w (R p sub) = [ppPred w p, ppSub w ppPred sub] 

ppProp :: Int -> Name -> [Pred] -> [String]
ppProp w p ps = [p++"("++intercalate "," (map (ppPred w) ps)++")"]

peSub :: Pred -> Subs Expr -> Pred
peSub p sub =  R p (mapsnd A sub)

mapsnd f [] = [] ; mapsnd f ((x,y):rest) = (x, f y):mapsnd f rest

ppProg :: Int -> Prog -> String
ppProg w =  reverse . strip . reverse . unlines . ppProgs w

ppProgs :: Int -> Prog -> [String]
ppProgs w U = ["U"]
ppProgs w II = ["II"]
ppProgs w (p ::: q) = ppProgs w p ++ [";"] ++ ppProgs w q
ppProgs w (v := e) = [ v ++ " := " ++ ppExpr w e ]
ppProgs w (Cond e p q) = ppProgs w p ++ ["<| "++ppExpr w e++" |>"] ++ ppProgs w q
ppProgs w (Loop e p) = [ppExpr w e ++ " *"] ++ ppProgs w p
\end{code}




