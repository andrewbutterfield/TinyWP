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

\subsubsection{Pretty-Printing Types}

We look at how we might layout composite things.
These are:
\begin{description}
\item[\texttt{F String [Expr]}]~\newline
f(e1,..,en)   or   e1 op e2 .. op en
\item[\texttt{S Expr (Subs Expr)}]~\newline 
e[e1,..,en/x1,..,xn]
\item[\texttt{A Expr            }]~\newline 
see above
\item[\texttt{P Name [Pred]     }]~\newline 
p1 pop p2 pop .. pop pn
\item[\texttt{Q Name Var Pred   }]~\newline 
quant v @ p
\item[\texttt{R Pred (Subs Pred)}]~\newline 
e[p1,..,pn/x1,..,xn]
\item[\texttt{Prog ::: Prog     }]~\newline 
p1 ; p2
\item[\texttt{Var := Expr       }]~\newline 
v := e
\item[\texttt{Cond Expr Prog Prog}]~\newline 
p1 <| e |> p2
\item[\texttt{Loop Expr Prog     }]~\newline 
c * p
\end{description}

We start with the notion of a ``box'',
which is zero or more strings, each of exactly the same length.
\begin{code}
type Box = [String]

invbox :: Box -> Bool
invbox [] = True
invbox box = length (nub $ map length box) == 1
\end{code}

\subsubsection{Syntax Pretty Printers}

\begin{code}
ppSub :: (t -> String) -> Subs t -> String
ppSub ppt sub 
  = let (vs,ts) = unzip sub
    in "[" ++intercalate "," vs 
           ++ "/"
           ++ intercalate "," (map ppt ts) ++ "]"

ppExpr :: Expr -> String
ppExpr (B b)      =  if b then "T" else "F"
ppExpr (I i)      =  show i
ppExpr (V v)      =  v
ppExpr (F f es)   =  ppFun f es
ppExpr (S e sub)  =  ppExpr e ++ ppSub ppExpr sub

ppFun :: String -> [Expr] -> String
ppFun f es  =  f ++ "("++intercalate "," (map ppExpr es)++")"

ppPred :: Pred -> String
ppPred  = reverse . strip . reverse . unlines . ppPreds

strip :: String -> String
-- removes zero or more initial newlines
strip "" = ""
strip str@(c:cs)
  | c == '\n'  =  strip cs
  | otherwise  =  str

ppPreds :: Pred -> [String]
ppPreds T     = ["T"]
ppPreds X     = ["F"]
ppPreds (A e) = [ppExpr e]
ppPreds (P p ps) = ppProp p ps
ppPreds (Q q x p) = [q++" "++x++" @ " ++ ppPred p]
ppPreds (R p sub) = [ppPred p, ppSub ppPred sub] 


ppProp :: Name -> [Pred] -> [String]
ppProp p ps = [p++"("++intercalate "," (map ppPred ps)++")"]

peSub :: Pred -> Subs Expr -> Pred
peSub p sub =  R p (mapsnd A sub)

mapsnd f [] = [] ; mapsnd f ((x,y):rest) = (x, f y):mapsnd f rest

ppProg :: Prog -> String
ppProg  =  reverse . strip . reverse . unlines . ppProgs

ppProgs :: Prog -> [String]
ppProgs U = ["U"]
ppProgs II = ["II"]
ppProgs (p ::: q) = ppProgs p ++ [";"] ++ ppProgs q
ppProgs (v := e) = [ v ++ " := " ++ ppExpr e ]
ppProgs (Cond e p q) = ppProgs p ++ ["<| "++ppExpr e++" |>"] ++ ppProgs q
ppProgs (Loop e p) = [ppExpr e ++ " *"] ++ ppProgs p
\end{code}




