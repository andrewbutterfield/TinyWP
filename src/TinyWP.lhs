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

vnames@[u,v,x,y,z] = ["u","v","x","y","z"]
[v_u,v_v,v_x,v_y,v_z] = map V vnames

unumbered@[u1,u2,u3,u4,u5] = map ((u++) . show) [1..5]
[v_u1,v_u2,v_u3,v_u4,v_u5] = map V unumbered

[i1,i2,i3,i4,i5] = map I [1..5]
[i10,i42,i99,i100,i1000] = map I [10,42,99,100,1000]

fnames@[f,g,h] = ["f","g","h"]

pqrs@[_P,_Q,_R,_S] = ["P","Q","R","S"]
[vP,vQ,vR,vS] = map V pqrs

bigExpr = S v_x [(u1,i42),(u2,F f [i99]),(u3,S vQ [(y,i1000)])]

bigFun = F f [F g [i42,i99],F h [vP,vQ,vR]]

bigVars = F f [V "abcdefg",V "gfedcba",V "hijklmno",V "pqrst"]
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

We will want to know if a function is usually rendered using infix notation.
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
assocLkp tightp infixes str = case M.lookup str infixes of
  Nothing  ->  (tightp,Prefix)
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

-- extreme precedences

givenLoosest, givenTightest :: Int
(givenLoosest,givenTightest)
  = (minimum precs,maximum precs) 
  where precs = map fst $ M.elems givenInfixes

loosep,tightp :: Int
loosep  =  0                   -- usual top-level precedence, no parentheses
tightp  =  givenTightest + 10  -- forces parentheses at top-level

funrender :: String -> (Int,FunRender)
funrender = assocLkp givenTightest givenInfixes

bigArith  =  F "mul" [ F "add" [i42,i99]
                     , F "add" [ F "mul" [i1,i2], F "mul" [i3,i4] ] ]
                    -- should be  (42+99)*(i1*i2+i3*i4)
\end{code}


Next, the notion of indented sized sub-strings:
\begin{code}
type Fragment = (Int,Int,String)
ind :: Fragment -> Int    ; ind (i,_,_) = i
len :: Fragment -> Int    ; len (_,l,_) = l
txt :: Fragment -> String ; txt (_,_,t) = t

indent :: Int -> Fragment -> Fragment 
indent iplus (i,l,t)  =  (i+iplus,l,t)

mkFragment :: String -> Fragment 
mkFragment str = (0,length str,str)

fuseF :: Fragment -> Fragment -> Fragment
fuseF (i1,l1,t1) (_,l2,t2) = (i1,l1+l2,t1++t2)

zeroF :: Fragment
zeroF = (0,0,"")

foldF :: [Fragment] -> Fragment
foldF = foldr fuseF zeroF

flattenF :: [Fragment] -> String
flattenF = concat . map txt

renderF :: Fragment -> String
renderF (i,_,t) = replicate i ' ' ++ t

renderFS :: [Fragment] -> String
renderFS = unlines . map renderF

putFrags :: [Fragment] -> IO ()
putFrags = putStrLn . renderFS

sizeF :: [Fragment] -> Int
sizeF = length . flattenF

-- some useful fragments
[lpar,rpar,comma] = map mkFragment ["(",")",","]
\end{code}

Now, the pretty printer:
\begin{code}
ppExpr :: Int -> Expr -> [Fragment]  -- indent,length,string
ppExpr _ (B b)  =  [(0,1,if b then "T" else "F")]
ppExpr _ (I i)  =  [(0,length s,s)] where s = show i
ppExpr _ (V x)  =  [(0,length x,x)]
ppExpr w (F f es)
  = case funrender f of
      _ -> ppPrefix w f es
ppExpr w (S e sub)  = [(0,14,"(ppExpr S NYI)")]
\end{code}

With \texttt{Prefix} we render as $f(e_1,\dots,e_2)$.
\begin{code}
ppPrefix :: Int -> String -> [Expr] -> [Fragment]
ppPrefix w f es 
  | w == 0 || size <= w  
    =  fname:lpar:intersperse comma (concat fargs) ++ [rpar]
  | flen <= w && allargs+sepcount <= w
    = [foldF [fname,lpar]] 
      ++ [foldF (map (indent 2 ) ((intersperse comma) (concat fargs)))]
      ++ [rpar]
  | otherwise  
    =  [foldF [fname,lpar]]
       ++ [(8,13,"ppPrefix-NYFi")]
       ++ [rpar]
  where
    flen    =  length f
    fname   =  (0,flen,f)
    fargs   =  map (ppExpr 0) es
    asizes  =  map len $ concat fargs
    sepcount = max 0 (length fargs - 1)
    size = flen + 2 + sum asizes + sepcount
    argsizes = map sizeF fargs
    sizes = (flen,argsizes)
    allargs = sum argsizes
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

\paragraph{Syntax Pretty Printers}


\begin{code}
ppSub :: Int -> (Int -> t -> String) -> Subs t -> String
ppSub w ppt sub 
  = let (vs,ts) = unzip sub
    in "[" ++intercalate "," vs 
           ++ "/"
           ++ intercalate "," (map (ppt w) ts) ++ "]"

xxExpr :: Int -> Expr -> String
-- xxExpr w (B b)      =  if b then "T" else "F"
-- xxExpr w (I i)      =  show i
-- xxExpr w (V v)      =  v
xxExpr w (F f es)   =  ppFun w f es
xxExpr w (S e sub)  =  xxExpr w e ++ ppSub w xxExpr sub
xxExpr w expr = renderBox $ map snd $ ppE w expr

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
ppFun w f es  =  f ++ "("++intercalate "," (map (xxExpr w) es)++")"

ppPred :: Int -> Pred -> String
ppPred w = reverse . strip . reverse . unlines . ppPreds w

ppPreds :: Int -> Pred -> [String]
ppPreds w T     = ["T"]
ppPreds w X     = ["F"]
ppPreds w (A e) = [xxExpr w e]
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
ppProgs w (v := e) = [ v ++ " := " ++ xxExpr w e ]
ppProgs w (Cond e p q) = ppProgs w p ++ ["<| "++xxExpr w e++" |>"] ++ ppProgs w q
ppProgs w (Loop e p) = [xxExpr w e ++ " *"] ++ ppProgs w p
\end{code}


