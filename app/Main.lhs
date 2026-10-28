\section{Main Program}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2026

LICENSE: BSD3, see file LICENSE at tiny-wp root
\end{verbatim}
\begin{code}
module Main(main) where

import TinyWP

--import Debug.Trace
--dbg :: Show a => [Char] -> a -> a  ; dbg msg x = trace (msg++show x) x
--pdbg :: Show a => [Char] -> a -> a ; pdbg nm x = dbg ('@':nm++":\n") x
\end{code}

\subsection{Version}

\begin{code}
progName :: [Char]     ; progName = "tiny-wp"
version :: [Char]      ; version = "0.0.1.0"
name_version :: [Char] ; name_version = progName++" "++version
\end{code}

\subsection{Mainline}

\begin{code}
main :: IO ()
main
  = do putStrLn name_version
       putStrLn iamtinywp
\end{code}
