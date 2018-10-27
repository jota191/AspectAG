\documentclass{article}

%include lhs2TeX.fmt
%include lhs2TeX.sty

%format -> = "\rightarrow"

\usepackage{cite}
\usepackage{epigraph}
\usepackage{color}   
\usepackage{hyperref}
\hypersetup{
    colorlinks=true,
    linktoc=all,  
    linkcolor=blue,
}

\author{Juan Garc\'ia Garland}
\title{Reimplementaci\'on de \emph{AspectAG} basada en nuevas
       extensiones de Haskell
}

\setlength\parindent{0pt} % noindent in all file
\usepackage{geometry}
%\geometry{margin=1in}
\usepackage{graphicx}

\begin{document}

\maketitle
\date

\newpage
\tableofcontents{}

\newpage


\section{Introducci\'on}

AspectAG [ref] es un EDSL (DSL embebido) desarrollado en Haskell que permite
la construcción modular de Gram\'aticas de Atributos. En AspectAG,
los fragmentos de una Gram\'atica de Atributos son definidos en forma
independiente y luego combinados a trav\'es del uso de operadores de
composici\'on que el propio EDSL provee. AspectAG se basa fuertemente en el
uso de registros extensibles, los cuales son implementados en t\'erminos
de HList [ref], una biblioteca de Haskell para la manipulaci\'on
de listas heterog\'eneas de forma fuertemente tipada.
HList est\'a implementada utilizando técnicas de programaci\'on a nivel
de tipos en las que los tipos son usados para representar ``valores''
a nivel de tipos y las clases de tipos son usadas para representar
``tipos'' y ``funcione'' en la manipulación a nivel de tipos. 

Desde el momento de la implementación original de AspectAG hasta ahora
la programación a nivel de tipos en Haskell ha tenido una evoluci\'on
importante, habi\'endose incorporado nuevas extensiones como
data promotion o polimorfismo de kinds, entre otras,
las cuales constituyen elementos fundamentales debido
a que permiten programar de forma “fuertemente tipada” a nivel de
tipos de la misma forma que cuando se programa a nivel de
valores en Haskell (algo que originalmente era imposible
o muy difícil de lograr). El uso de estas extensiones da
como resultado una programaci\'on a nivel de tipos más robusta y segura.
Sobre la base de estas extensiones, el planteo de este proyecto
es realizar una reimplementación de un subconjunto de AspectAG
que las tome en cuenta.
Esto implica una reimplementaci'on de las funcionalidades de AspectAG
y de las que sean necesarias de HList.

\paragraph{}
Estructura del documento:

En la secci\'on 2 [ref] se presenta un estudio de las
t\'ecnicas de programaci\'on a nivel de tipos 
y las extensiones
de haskell que provee el compilador GHC que las hacen posibles.
[TODO: redactar bien de aca en adelante]
Se desglosa entre las t\'ecnicas existentes previamente a la
implementaci\'on original de AspectAG, y las posteriores.
Se presentan
las estructuras de Listas Heterogeneas y Registros Heterogeneos que
implementa originalmente {\tt HList}, de las que depende AspectAG.

En la secci\'oin [ref] se presentan las gram\'aticas de atributos
y en particular la implementaci\'on (nueva) de AspectAG mediante un
ejemplo que introduce las primitivas importantes de la biblioteca.

En la secci\'on [ref] se presentan los detalles de la
implementaci\'on, que se basan en las t\'ecnicas de programaci\'on a
nivel de tipos modernas.

Finalmente [ref] se presenta una breve comparaci\'on que ilustra
las ventajas del uso de las t\'ecnicas modernas.

El c\'odigo fuente de la biblioteca y la documentaci\'on se encuentra
disponible en

\url{http://https://gitlab.fing.edu.uy/jpgarcia/AspectAG/}.

En la secci\'on te tests se implementan ejemplos de utilizaci\'on de
la biblioteca.



\section{Programaci\'on a nivel de tipos}
\subsection{T\'ecnicas antiguas}

%include ./src/Old.lhs

\newpage
\subsection{T\'ecnicas modernas}

%include ./src/New.lhs

\newpage
\subsection{HList : Colecciones Heterogeneas Fuertemente tipadas}

%include ./src/HCols.lhs


\newpage
\section{AspectAG}

%include ./src/AGs.lhs



\section{Reimplementación de AspectAG}

%include ./src/AAG.lhs


\section{Comparaci\'on}


ambiguous types al final

monomorphism restriction

hack con las funciones semanticas


\newpage

\bibliography{bib}{}
\bibliographystyle{plain}


\end{document}
