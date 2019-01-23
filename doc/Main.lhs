\documentclass{article}

%include lhs2TeX.fmt
%include lhs2TeX.sty

\usepackage{cite}
%\usepackage{epigraph}
\usepackage{color}   
\usepackage{hyperref}
\usepackage[utf8]{inputenc}

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
\geometry{margin=1in}
\usepackage{graphicx}

\date{}
\renewcommand{\contentsname}{\'Indice}



\begin{document}

\maketitle


\newpage
\tableofcontents{}

\newpage


\section{Introducci\'on}

AspectAG~\cite{Viera:2009:AGF:1596550.1596586}
es un lenguaje de dominio espec\'ifico embebido (EDSL)
desarrollado en Haskell que permite
la construcción modular de Gram\'aticas de Atributos. En AspectAG
los fragmentos de una Gram\'atica de Atributos son definidos en forma
independiente y luego combinados a trav\'es del uso de operadores de
composici\'on que el propio EDSL provee. AspectAG se basa fuertemente en el
uso de registros extensibles, los cuales son implementados en t\'erminos
de HList\cite{Kiselyov:2004:STH:1017472.1017488},
una biblioteca de Haskell que implementa la manipulaci\'on
de colecciones heterog\'eneas de forma fuertemente tipada.
HList est\'a implementada utilizando t\'ecnicas de programaci\'on a nivel
de tipos (los tipos son usados para representar valores
a nivel de tipos y las clases de tipos son usadas para representar
tipos y funciones en la manipulación a nivel de tipos).

Desde el momento de la implementaci\'on original de AspectAG hasta
la actualidad
la programaci\'on a nivel de tipos en Haskell ha tenido una evoluci\'on
importante, habi\'endose incorporado nuevas extensiones como
\emph{data promotion} o polimorfismo de kinds, entre otras,
las cuales constituyen elementos fundamentales debido
a que permiten programar de forma ``fuertemente tipada'' a nivel de
tipos de la misma forma que cuando se programa a nivel de
valores (algo que originalmente era imposible
o muy dif\'icil de lograr). El uso de estas extensiones permite
una programaci\'on a nivel de tipos m\'as robusta y segura.
Sobre la base de estas extensiones, implementamos un subconjunto
de la biblioteca original.

\paragraph{
Estructura del documento:
}

En la secci\'on \ref{typelevel} se presenta una breve rese\~na de las
t\'ecnicas de programaci\'on a nivel de tipos 
y las extensiones a Haskell que provee el compilador GHC
que las hacen posibles.
Se presentan
las estructuras de listas heterogeneas (\ref{hlist})
y registros heterogeneos (\ref{hrecord}) que
normalmente no ser\'ian implementables en un lenguaje fuertemente tipado
sin tipos dependientes.

En la secci\'on \ref{ags} se presentan las gram\'aticas de atributos
y en particular la implementaci\'on (nueva) de AspectAG mediante un
ejemplo que introduce las primitivas importantes de la biblioteca.

En la secci\'on \ref{impl} se presentan los detalles de la
implementaci\'on, que se basan en las t\'ecnicas de programaci\'on a
nivel de tipos modernas.

El c\'odigo fuente de la biblioteca y la documentaci\'on se encuentra
disponible en

\url{http://https://gitlab.fing.edu.uy/jpgarcia/AspectAG/}.

En el directorio {\tt /test} se implementan ejemplos de utilizaci\'on de
la biblioteca.

\newpage

\section{Programaci\'on a nivel de tipos en GHC Haskell}
\label{typelevel}
\subsection{Extensiones utilizadas}

\subsubsection{T\'ecnicas antiguas}
La biblioteca AspectAG presentada originalmente
en 2009, adem\'as de implementar un sistema de gram\'aticas de atributos
como un EDSL provee un buen ejemplo del uso de la
programaci\'on a nivel de tipos en Haskell.
La implementaci\'on utiliza fuertemente los registros extensibles que provee
la biblioteca HList. Ambas bibliotecas se basan en la combinaci\'on
de las extensiones {\tt MultiParamTypeClasses}
(hace posible la implementaci\'on de relaciones a nivel de tipos) con
{\tt FunctionalDependencies}~\cite{DBLP:conf/esop/Jones00}
(que permite expresar en particular
relaciones funcionales).\footnote{Adem\'as de otras relaciones de uso
extendido como {\tt FlexibleContexts}, {\tt FlexibleInstances}, etc}

\subsubsection{T\'ecnicas modernas}
Durante la d\'ecada pasada~\footnote{Algunas extensiones como
{\tt GADTS} o incluso {\tt TypeFamilies} ya exist\'ian en la \'epoca
de la publicaci\'on original de AspectAG, pero eran experimentales,
y de uso poco extendido.}
se han implementado m\'ultiples extensiones
en el compilador GHC que proveen herramientas para hacer la programaci\'on
a nivel de tipos m\'as expresiva. Las familias de tipos implementadas
en la extensi\'on
{\tt TypeFamilies}\cite{Chakravarty:2005:ATC:1047659.1040306, Chakravarty:2005:ATS:1090189.1086397, Sulzmann:2007:SFT:1190315.1190324}
nos permiten definir funciones a nivel
de tipos de una forma m\'as idiom\'atica que el estilo l\'ogico de la
programaci\'on orientada a relaciones por medio de clases y dependencias
funcionales. La extensi\'on
{\tt DataKinds}~\cite{Yorgey:2012:GHP:2103786.2103795}
implementa la \emph{data promotion} que provee la posibilidad de definir
tipos de datos -tipados- a nivel de tipos, introduciendo nuevos kinds.
Bajo el mismo trabajo Yorgey et al implementan la
extensi\'on {\tt PolyKinds} proveyendo polimorfismo a nivel de kinds.
Adem\'as la extensi\'on {\tt KindSignatures} permite anotar kinds a los
t\'erminos en el nivel de tipos. Con toda esta maquinaria Haskell cuenta
con un lenguaje a nivel de tipos casi tan expresivo como a nivel
de t\'erminos\footnote{no es posible, por ejemplo la aplicaci\'on parcial}.
La extensi\'on {\tt GADTs} combinada con las anteriores nos permite escribir
familias indizadas, como en los lenguajes dependientes.
{\tt TypeOperators}
habilita el uso de operadores como constructores de tipos.
El m\'odulo {\tt Data.Kind} exporta la notaci\'on {\tt Type} para
el kind {\tt *}. Esto fu\'e implementado originalmente con la extensi\'on
{\tt TypeInType}, que en las \'ultimas versiones del compilador es
equivalente a {\tt PolyKinds + DataKinds + KindSignatures}.


\subsection{Programando con tipos dependientes en Haskell}


Con todas estas extensiones combinadas, una declaraci\'on como

> data Nat = Zero | Succ Nat

se ``duplica'' a nivel de kinds ({\tt DataKinds}). Esto es, que
adem\'as de introducir los t\'erminos {\tt Zero} y {\tt Succ} de tipo
{\tt Nat}, y al propio tipo {\tt Nat} de kind {\tt *} la declaraci\'on
introduce los \emph{tipos}
{\tt Zero} y {\tt Succ} de kind {\tt Nat} (y al propio kind {\tt Nat}).
Luego es posible declarar, por ejemplo ({\tt GADTs}, {\tt KindSignatures})

> data Vec :: Nat -> Type -> Type where
>   VZ :: Vec Zero a
>   VS :: a -> Vec n a -> Vec (Succ n) a

y funciones seguras como:

> vTail :: Vec (Succ n) a -> Vec n a
> vTail (VS _ as) = as

> vZipWith :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
> vZipWith _ VZ VZ = VZ
> vZipWith f (VS x xs) (VS y ys)
>   = VS (f x y)(vZipWith f xs ys)

\newpage
o incluso:


> vAppend :: Vec n a -> Vec m a -> Vec (n + m) a
> vAppend (VZ) bs      = bs
> vAppend (VS a as) bs = VS a (vAppend as bs)

Es posible definir funciones puramene a nivel de tipos mediante familias
({\tt TypeFamilies}, {\tt TypeOperators}, {\tt DataKinds},
{\tt KindSignatures}) como la suma:

> type family (m :: Nat) + (n :: Nat) :: Nat
> type instance Zero + n = n
> type instance Succ m  + n = Succ (m + n) 

o mediante la notaci\'on alternativa, cerrada:

> type family (m :: Nat) + (n :: Nat) :: Nat where
>   (+) Zero     a = a
>   (+) (Succ a) b = Succ (a + b)

\subsection{Limitaciones}
\label{sec:limitaciones}

En contraste a lo que ocurre en los sistemas de tipos dependientes,
los lenguajes de t\'erminos y de tipos en Haskell
contin\'uan habitando mundos separados.
La correspondencia entre nuestra definici\'on de vectores
y las familias inductivas en los lenguajes de tipos dependientes no es tal.

Las ocurrencias de {\tt n} en los tipos de las funciones anteriores son
est\'aticas, y borradas en tiempo de
ejecuci\'on, mientras que en un lenguaje de tipos dependientes estos
par\'ametros son esencialmente
\emph{din\'amicos}~\cite{Lindley:2013:HPP:2578854.2503786}.
En las teor\'ias de tipos intensionales
una definici\'on como la suma ({\tt (+)}) declarada anteriormente
extiende el algoritmo de normalizaci\'on, de forma tal que el
compilador decidir\'a la igualdad de tipos seg\'un las formas
normales. Si dos tipos tienen la misma forma normal entonces los mismos
t\'erminos les habitar\'an.
Por ejemplo, los tipos  {\tt Vec (S (S Z) + n) a} y {\tt Vec (S (S n)) a}
tendr\'an los mismos habitantes.
Esto no va a ser cierto para tipos como
{\tt Vec (n + S (S Z)) a} y {\tt Vec (S (S n)) a}, aunque que los tipos
coincidan para todas las instancias concretas de {\tt n}.
Para expresar propiedades como la conmutatividad
se utilizan evidencias de las ecuaciones utilizando
\emph{tipos de igualdad proposicional}
(\emph{Propositional Types})~\cite{Lindley:2013:HPP:2578854.2503786}. 

En el sistema de tipos de Haskell, sin embargo la igualdad de tipos
es puramente sint\'actica. Los tipos \break
{\tt Vec (n + S (S Z)) a} y {\tt Vec (S (S n)) a} {\bf no} son el mismo
tipo, y no poseen los mismos habitantes.
La definici\'on de una familia de tipos axiomatiza {\tt (+)} para la igualdad
proposicional de Haskell. Cada ocurrencia de {\tt (+)} debe estar soportada
con evidencia expl\'icita derivada de estos axiomas.
Cuando el compilador traduce desde el lenguaje externo al lenguaje del kernel,
busca generar evidencia mediante heur\'isticas de resoluci\'on de
restricciones.
La evidencia sugiere que el \emph{constraint solver} computa agresivamente,
y esta es la raz\'on por la cual la funci\'on {\tt vAppend} definida
anteriormente compila y funciona correctamente.

Sin embargo, funciones como:

> vchop :: Vec (m + n) x -> (Vec m x, Vec n x)

resultan imposibles de definir si no tenemos la informaci\'on de
{\tt m} o {\tt n} en tiempo de ejecuci\'on (intuitivamente,
ocurre que ``no sabemos donde partir el vector'').

Por otra parte la funci\'on:

< vtake :: Vec (m + n) x -> Vec m x

tendr\'ia un problema m\'as sutil. Incluso asuminedo que tuvieramos forma
de obtener {\tt m} en tiempo
de ejecuci\'on, no es posible para el verificador de tipos aceptar
la definici\'on.
No hay forma de deducir {\tt n} a partir del tipo del tipo {\tt m + n}
sin la informaci\'on de que {\tt (+)} es una funci\'on inyectiva, lo cual
el verificador es incapaz de deducir.


\newpage

\subsection{Singletons y Proxies}
\label{sec:sings}

Existen dos \emph{hacks} para resolver los problemas planteados
anteriormente.

\subsubsection{Singletons}

Si pretendemos implementar {\tt vChop} cuyo tipo
podemos escribir m\'as expl\'icitamente como 

> vChop :: forall (m n :: Nat). Vec (m + n) x -> (Vec m x, Vec n x)

necesitamos hacer
referencia expl\'icita a {\tt m} para decidir donde cortar el vector.
Como en Haskell el cuantificador universal solo se refiere
a objetos est\'aticos (los lenguajes de tipos y t\'erminos est\'an
separados), esto no es posible directamente.
Un tipo \emph{singleton}\cite{Eisenberg:2012:DTP:2430532.2364522}
en el contexto de Haskell, es un {\tt GADT}
que replica datos est\'aticos a nivel de t\'erminos.

> data SNat :: Nat -> * where
>   SZ :: SNat Zero
>   SS :: SNat n -> SNat (Succ n)

Existe por cada tipo {\tt n} de kind {\tt Nat}, un \'unico
\footnote{Formalmente esto no es cierto, si consideramos las posibles
ocurrecias de $\bot$, la unicidad es cierta
para t\'erminos totalmente definidos}
t\'ermino de tipo {\tt SNat n}. Sobre estos t\'erminos podemos
hacer \emph{pattern matching}, e impl\'icitamente decidimos seg\'un
la informaci\'on del tipo.

Estamos en condiciones de implementar {\tt vChop}:

> vChop :: SNat m -> Vec (m + n) x -> (Vec m x, Vec n x)
> vChop SZ xs            = (VZ, xs)
> vChop (SS m) (VS x xs) = let (ys, zs) = vChop m xs
>                          in (VS x ys, zs)


La biblioteca {\tt singleton}\cite{libsingleton}
provee la generaci\'on autom\'atica
de instancias de tipos singleton y otras utilidades.


\subsubsection{Proxies}

An\'alogamente para definir {\tt vTake} es necesario el valor de
{\tt m} en tiempo
de ejecuci\'on para conocer
cuantos elementos extraer, pero una funci\'on de tipo

> vTake :: SNat m -> Vec (m + n) x -> Vec m x

no ser\'a implementable. Es necesaria la informaci\'on tambi\'en
de {\tt n} en tienpo de compilaci\'on,
pero no as\'i una representaci\'on de {\tt n}
en tiempo de ejecuci\'on. El natural
{\tt n} es est\'atico pero estamos obligados a proveer
un valor testigo expl\'icito para asistir al verificador de tipos que es
incapaz de deducir la inyectividad de la suma.

Consideramos la definici\'on:

> data Proxy :: k -> * where
>   Proxy :: Proxy a

Proxy es un tipo que no contiene datos, pero contiene un par\'ametro
\emph{phantom} de tipo arbitrario (de hecho, de kind arbitrario).
El uso de un proxy va a resolver el problema de {\tt vTake}, indicando
simplemente que la ocurrencia del proxy tiene la informaci\'on del tipo
{\tt n} en el vector.

La siguiente implementaci\'on de vTake compila y funciona correctamente:

> vTake :: SNat m -> Proxy n -> Vec (m + n) x -> Vec m x
> vTake SZ _ xs            = VZ
> vTake (SS m) n (VS x xs) = VS x (vTake m n xs)

Durante la implementaci\'on de AspectAG y sus dependencias haremos uso
intensivo de estas t\'ecnicas.



\newpage
\subsection{HList : Colecciones Heterogeneas Fuertemente tipadas}
\label{hlist}

%include ./src/HCols.lhs


\newpage
\section{Gram\'aticas de atributos y AspectAG}
\label{ags}

%include ./src/AGs.lhs


\newpage
\section{Reimplementaci\'on de AspectAG}
\label{impl}

A continuaci\'on presentamos algunos de los aspectos m\'as importantes
de la implementaci\'on de la biblioteca.

%include ./src/AAG.lhs

\newpage
\section{Conclusi\'on}
%include ./src/Conc.lhs

\newpage

\bibliography{bib}{}
\bibliographystyle{plain}


\end{document}
