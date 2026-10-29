\section{Tiny Weakest Precondition}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2026

LICENSE: BSD3, see file LICENSE at tiny-wp root
\end{verbatim}
\begin{code}
module TinyWP (
  iamtinywp
)
where

import Data.List(intercalate,nub)

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
ppExpr w expr = renderBox $ map snd $ ppE w expr

-- ppExpr w (B b)      =  if b then "T" else "F"
-- ppExpr w (I i)      =  show i
-- ppExpr w (V v)      =  v
ppExpr w (F f es)   =  ppFun w f es
ppExpr w (S e sub)  =  ppExpr w e ++ ppSub w ppExpr sub

ppE :: Int -> Expr -> SizedBox
ppE _ (B b)  =  [(1,if b then "T" else "F")]
ppE _ (I i)  =  [(length s,s)] where s = show i
ppE _ (V v)  =  [(length v,v)]

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




