%if False

> {-# LANGUAGE TypeInType,
>              GADTs,
>              KindSignatures,
>              TypeOperators,
>              TypeFamilies,
>              MultiParamTypeClasses,
>              FlexibleInstances,
>              FlexibleContexts,
>              StandaloneDeriving,
>              UndecidableInstances,
>              FunctionalDependencies,
>              ConstraintKinds,
>              ScopedTypeVariables,
>              PolyKinds#-}

> import Data.Kind
> import New
> import GHC.TypeLits (TypeError, ErrorMessage(Text, (:$$:)))

%endif

% \subsubsection{Listas Heterogeneas}

La biblioteca HList\cite{Kiselyov:2004:STH:1017472.1017488} provee
operaciones para crear y manipular colecciones heterogeneas fuertemente
tipadas (donde el largo y el tipo de los elementos se conocen en tiempo
de compilaci\'on). Estas son \'utiles para
implementar registros heterogeneos (extensibles), variantes,
productos y coproductos indizados por tipos, entre otras estructuras.
HList es un buen ejemplo
de aplicaci\'on de la programaci\'on a nivel de tipos usando
las t\'ecnicas antiguas.
La implementaci\'on original de AspectAG hace uso intensivo de estas
versiones de la biblioteca.
HList sigue desarroll\'andose a medida de que nuevas extensiones se
a\~naden al lenguaje Haskell. % de hecho a GHC...
En lugar de reimplementar AspectAG dependiendo de nuevas versiones de HList
decidimos reescribir desde cero todas las funcionalidades necesarias,
por los siguientes motivos:

\begin{itemize}
\item
  HList es una biblioteca experimental, que no pretende
  ser utilizada como dependencia de desarrollos de producci\'on
  por lo que constantemente cambia
  su interfaz sin ser compatible hacia atr\'as. Implementar
  hoy dependiendo de HList implica depender posiblemente de una versi\'on
  desactualizada (e incompatible con la liberaci\'on corriente) en poco tiempo.
\item
  Cuando programamos a nivel de tipos el lenguaje no provee fuertes
  mecanismos de modularizaci\'on, dado que no fue dise\~nado para
  este prop\'osito. Es com\'un que por ejemplo, se fugue informaci\'on en los
  mensajes de error sobre las estructuras de datos utilizadas.
  La implementaci\'on basada en HList filtrar\'ia
  errores de HList, que no utilizan el mismo vocabulario que nuestro
  EDSL. La imposibilidad de modularizar nos obliga a que si pretendemos
  tener estructuras distinguibles por sus nombres mnem\'onicos tenemos
  que reimplementarlas. Buscar mejores soluciones a esta complicaci\'on
  es parte de la investigaci\'on en el \'area, e idea de trabajo futuro.
\item
  HList no es necesariamente adecuada si queremos tipar todo lo fuertemente
  posible.
  Por ejemplo, en la implementaci\'on que realizamos,
  una de las estructuras a utilizar es esencialmente un
  registro que contiene registros.
  Usando tipos de datos a medida podemos programar
  una soluci\'on elegante donde esto queda expresado correctamente
  a nivel de kinds. La biblioteca AspectAG orginal implementa
  el registro externo como un registro de HList,
  no forzando en el tipado que los campos sean efectivamente registros.
\item
  Por inter\'es acad\'emico. Reescribir funcionalidades de HList
  (de hecho, varias veces,
  un subconjunto mayor al necesario para AspectAG)
  fu\'e la forma de dominar las t\'ecnicas
  de programaci\'on a nivel de tipos.
  Esto no es una raz\'on en si para efectivamente depender de
  una nueva implementaci\'on en lugar de la implementaci\'on moderna de
  HList, pero a los argumentos anteriores se le suma el hecho de que
  reimplementar no significa un costo: ya lo hicimos. 
\end{itemize}

Una lista (o m\'as en general una colecci\'on)
heterogenea es tal si contiene valores de distintos tipos.
Existen varios enfoques para construir colecciones heterogeneas en
Haskell\cite{HColsWiki}.
Nos interesan en particular las implementaciones que son fuertemente tipadas,
donde se conoce
est\'aticamente el tipo de cada miembro.

Existen variantes para definir HList.
Las versiones m\'as antiguas (sobre las que se implement\'o originalmente
AspectAG) utilizan la siguiente representaci\'on, isomorfa a pares anidados:

< data HCons a b = HCons a b
< data HNil = HNil

El inconveniente de esta
implementaci\'on es que es posible
construir tipos sin sentido como {\tt HCons Bool Char}, lo cual puede
solucionarse mediante el uso de clases, como es usual en
el enfoque antig\"uo de la programaci\'on a nivel de tipos.
En versiones posteriores HList utiliz\'o un GADT, y en las
\'ultimas versiones se utiliza una \emph{data family}\footnote{
  Una \emph{data family} es una construcci\'on
  que provee la extensi\'on {\tt TypeFamilies}, no hacemos uso de
  las mismas en nuestra implementaci\'on.
}.
En la documentaci\'on de la biblioteca HList
se fundamenta cual es la ventaja de cada representaci\'on. Dado que el GADT y
la data Family son pr\'acticamente equivalentes
(de hecho en nuestra implementaci\'on se pueden cambiar una por la otra),
preferimos el GADT por ser la soluci\'on m\'as clara.

\newpage
El tipo de datos {\tt HList} tiene la siguiente definici\'on: 

> data HList (l :: [Type]) :: Type  where
>   HNil  :: HList '[]
>   HCons :: x -> HList xs -> HList (x ': xs)

La extensi\'on {\tt DataKinds} promueve las listas con una notaci\'on
conveniente similar a la utilizada a nivel de valores.
En la definici\'on anterior se utiliza
la versi\'on promovida de listas como \'indice del tipo de datos.
{\tt HNil} es un valor de tipo {\tt HList '[]}, mientras que {\tt HCons}
construye un valor de tipo {\tt HList (x ': xs)} a partir de un valor de tipo
{\tt x} y una lista de tipo {\tt HList xs}.

A modo de ejemplo, un habitante posible del kind {\tt [Type]} es
{\tt '[Bool, Char]}. Luego {\tt HList [Bool, Char]} es un tipo
(de kind {\tt Type})
habitado por ejemplo por {\tt HCons True (HCons 'c' HNil)}.


Es intuitivo definir, por ejemplo las versiones seguras
de {\tt head} o {\tt tail}:

> hHead :: HList (x ': xs) -> x
> hHead (HCons x _) = x

> hTail :: HList (x ': xs) -> HList xs
> hTail (HCons _ xs) = xs

No es posible compilar expresiones como {\tt hHead HNil},
dado que el verificador de tipos de GHC inferir\'a que es imposible
satisfacer la restricci\'on {\tt (x ': xs) $\sim$ '[]}.



Para concatenar dos listas
primero definimos la concatenaci\'on a nivel de tipos:

> type family (xs :: [Type]) :++ ( ys :: [Type]) :: [Type]
> type instance '[]       :++ ys = ys
> type instance (x ': xs) :++ ys = x ': (xs :++ ys)

Y luego a nivel de t\'erminos:

> hAppend :: HList xs -> HList ys -> HList (xs :++ ys)
> hAppend HNil ys = ys
> hAppend (HCons x xs) ys = HCons x (hAppend xs ys)

Una alternativa es definir la familia como un tipo indizado:
\footnote{\'Esta es una tercer forma de definir familias de tipos,
adem\'as de la notaci\'on abierta o cerrada.
}

> class HAppend xs ys where
>   type HAppendR xs ys :: [Type]
>   chAppend :: HList xs -> HList ys -> HList (HAppendR xs ys)
 
> instance HAppend '[] ys where
>   type HAppendR '[] ys = ys
>   chAppend HNil ys = ys

> instance (HAppend xs ys) => HAppend (x ': xs) ys where
>   type HAppendR (x ': xs) ys = x ': (HAppendR xs ys)
>   chAppend (HCons x xs) ys = HCons x (chAppend xs ys)


Si intentamos a modo de ejemplo
programar una funci\'on que actualiza la $n$-\'esima entrada en
una lista heterogenea
(eventualmente cambiando el tipo del dato en esa posici\'on),
estamos claramente ante una funci\'on de tipos dependientes (el tipo
del resultado depende de $n$). \'Este es el escenario donde ser\'an
necesarios {\tt Proxies} y/o {\tt Singletons}.

Una definici\'on posible:
\footnote{asumamos que el $n$ es menor al largo de la lista,
lo cual podr\'iamos tambi\'en forzar est\'aticamente}

< type family UpdateAtNat (n :: Nat)(x :: Type)(xs :: [Type]) :: [Type]
< type instance UpdateAtNat Zero     x (y ': ys) = x ': ys
< type instance UpdateAtNat (Succ n) x (y ': ys) = y ': UpdateAtNat n x ys

< updateAtNat :: SNat n -> x -> HList xs -> HList (UpdateAtNat n x xs)
< updateAtNat SZ y (HCons _ xs) = HCons y xs
< updateAtNat (SS n) y (HCons x xs) = HCons x (updateAtNat n y xs)


\subsection{Registros Heterogeneos Extensibles}
\label{hrecord}

AspectAG requiere de registros heterogeneos extensibles fuertemente
tipados, esto es,
colecciones etiqueta-valor, heterogeneas, donde adem\'as las etiquetas
est\'en dadas por tipos. Adem\'as de
de HList, existen otros proyectos de implementaciones
de registros heterogeneos en Haskell,
como Vinil\cite{libvinyl}, CTRex\cite{libCTRex}, entre otros \cite{HColsWiki}.

El enfoque original de HList para implementar registros
es utilizar una lista heterogenea,
donde cada entrada es del tipo {\tt Tagged l v}, definido como

< data Tagged l v = Tagged v

Esta definici\'on no es satisfactoria si pretendemos utilizar todo el poder
de las nuevas extensiones de Haskell. Por ejemplo
no se est\'a utilizando la posibilidad de tipar (en el lenguaje de tipos)
que nos provee la
promoci\'on de datos. HList implementa predicados como typeclasses
para asegurar que todos los miembros son de tipo {\tt Tagged} cuando la
buena formaci\'on
podr\'ia expresarse directamente en el kind.
Adem\'as las etiquetas de HList
son de kind {\tt Type}, cuando en realidad nunca
requieren estar habitadas a nivel de valores.

En su lugar, utilizaremos la siguiente implementaci\'on:

> data Record :: forall k . [(k,Type)] -> Type where
>   EmptyR :: Record '[]
>   ConsR  :: LabelSet ( '(l, v) ': xs) =>
>    Tagged l v -> Record xs -> Record ( '(l,v) ': xs)

Un registro es una lista con m\'as estructura, a nivel de tipos
es una lista de pares. Usamos la promoci\'on de listas y de pares
a nivel de tipos. Para agregar un campo,
requerimos un valor de tipo {\tt Tagged l v}
definido como:

> data Tagged (l :: k) (v :: Type) where
>   Tagged :: v -> Tagged l v

{\tt Tagged} es polim\'orfico en el kind de las etiquetas.
La restricci\'on {\tt Labelset} garantiza que las etiquetas no se repitan,
su implementaci\'on se explica a continuaci\'on.


\subsection{Predicados sobre tipos}

Si bien las extensiones modernas nos permiten adoptar
el estilo funcional en la programaci\'on a nivel de
tipos, el estilo de programaci\'on ``l\'ogica'' por medio de clases
sigue siendo adecuado para codificar predicados.
Una lista de pares promovida satisface el predicado {\tt LabelSet}
si las primeras componentes son \'unicas. As\'i, la lista
de pares representa un mapeo, o registro indizado por las primeras
componentes. El predicado se implementa a la prolog, aunque usamos
el poder de las extensiones modernas para tipar fuertemente los
functores.

> class LabelSet (l :: [(k,k2)])
> instance LabelSet '[]         -- empty set
> instance LabelSet '[ '(x,v)]  -- singleton set


> instance ( HEqK l1 l2 leq
>          , LabelSet' '(l1,v1) '(l2,v2) leq r)
>         => LabelSet ( '(l1,v1) ': '(l2,v2) ': r)

> class LabelSet' l1v1 l2v2 (leq::Bool) r
> instance ( LabelSet ( '(l2,v2) ': r)
>          , LabelSet ( '(l1,v1) ': r)
>          ) => LabelSet' '(l1,v1) '(l2,v2) False r

donde {\tt HEqK l1 l2 False} es instancia solo si {\tt l1}
y {\tt l2} son probables distintos. Para ello
se utiliza la igualdad sobre kinds que implementa el m\'odulo
{\tt Data.Type.Equality}. 

Notar que podr\'iamos tambi\'en codificar el predicado como una funci\'on
booleana a nivel de tipos, luego se propaga como una restricci\'on 
con el valor que queremos ({\tt Labelset l} $\sim$ {\tt True}).

Tambi\'en podr\'ia utilizarse
una familia de tipos para construir la constraint {\tt LabelSet}
(haciendo uso de la extensi\'on {\tt ConstraintKinds}).

En general, la programaci\'on mediante
clases es siempre sustituible por familias de tipos,
pero no parece natural en este caso.
