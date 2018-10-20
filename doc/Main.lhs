\documentclass{article}

%include lhs2TeX.fmt
%include lhs2TeX.sty

%format -> = "\rightarrow"


\usepackage{cite}
\usepackage{epigraph}

\author{Juan Garc\'ia Garland}
\title{Reimplementaci\'on de \emph{AspectAG} basada en nuevas
       extensiones de Haskell
}

\setlength\parindent{0pt} % noindent in all file
\usepackage{geometry}
\geometry{margin=1in}
\usepackage{graphicx}

\begin{document}

\maketitle
\date

\newpage
\tableofcontents{}

\newpage


\section{Intro}
\section{Programaci\'on a nivel de tipos}
\subsection{Antes ({\tt MultiparamTypeClasses,
FunctionalDependencies, FlexibleInstances})}

%include ./src/Old.lhs

\newpage
\subsection{Ahora ({\tt TypeFamilies, DataKinds, GADTs ...})}

%include ./src/New.lhs

\newpage
\subsection{HList : Colecciones Heterogeneas Fuertemente tipadas}

%include ./src/HCols.lhs


\newpage
\section{AspectAG}

%include ./src/AGs.lhs



\section{Reimplementación de AAG}

%include ./src/AAG.lhs


\section{Comparaci\'on}


ambiguous types al final

monomorphism restriction

hack con las funciones semanticas


\newpage

\bibliography{bib}{}
\bibliographystyle{plain}


\end{document}
