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

\subsubsection{Listas Heterogeneas}

En \cite{Kiselyov:2004:STH:1017472.1017488} se presenta un buen ejemplo
de aplicaci\'on de las t\'ecnicas de programaci\'on a nivel de tipos, usando
las t\'ecnicas antiguas.
La implementaci\'on original de AspectAG hace uso intensivo de estas
versiones de la biblioteca.
HList sigue desarrollandose a medida de que nuevas caracter\'isticas se
a\~naden al lenguaje.
En lugar de reimplementar AspectAG dependiendo de nuevas versiones de HList,
decidimos reescribir desde cero todas las funcionalidades necesarias,
por distintos motivos:

\begin{itemize}
\item
  HList es una biblioteca experimental, que no pretende
  ser utilizada como dependencia de desarrollos de producci\'on
  por lo que constantemente cambia
  su interfaz sin ser compatible hacia atr\'as. Implementar
  hoy dependiendo de HList implica depender posiblemente de una versi\'on
  antigua y distinta de la versi\'on final en poco tiempo.
\item
  Cuando programamos a nivel de tipos el lenguaje no provee fuertes
  mecanismos de modularizaci\'on, dado que no fu\'e dise\~nado para
  este prop\'osito. Es com\'un que se fugue implementaci\'on
  con los mensajes de error. Y la implementaci\'on basada en HList va a
  filtrar errores de HList, que no utilizan los mismo t\'erminos que
  la jerga de nuestro DSL.
  Si bien proveemos una soluci\'on al manejo
  de errores, no es necesariamente exhaustiva.
  La biblioteca AspectAG utiliza m\'ultiples estructuras isomorfas a
  Registros heterogeneos,
  y dentro del propio desarrollo de la misma result\'o m\'as c\'omodo
  trabajar con estructuras con sus nombres mnem\'onicos.
\item
  HList no es necesariamente adecuada si queremos tipar todo lo fuertemente
  posible.
  Por ejemplo, en la implementaci\'on
  vamos a utilizar una estructura que es esencialmente un
  Registro de Registros. Usando tipos de datos a medida podemos programar
  una soluci\'on elegante donde esto queda expresado correctamente
  a nivel de kinds. La alternativa de implementar el Registro externo
  como un Registro de HList
  ofusca al interno, tratandolo como un tipo "plano".
\item
  Por inter\'es acad\'emico. Reescribir HList (varias veces, un subconjunto
  mayor al necesario para AspectAG) fu\'e la forma de dominar las t\'ecnicas
  de programaci\'on a nivel de tipos.
  Esto no es una raz\'on en si para efectivamente depender de
  una nueva implementaci\'on en lugar de la implementaci\'on moderna de
  HList, pero a los argumentos anteriores se le suma el hecho de que
  reimplementar no significa un costo: ya lo hicimos. 
\end{itemize}

Una lista (o \'as en general una colecci\'on)
heterogenea es tal si contiene valores de distintos tipos.
Existen varios enfoques para construir colecciones heterogeneas en Haskell,
REF: https://wiki.haskell.org/Heterogenous\_collections
Nos interesan en particular las que son fuertemente tipadas, se conoce
est\'aticamente el tipo de cada miembro (del mismo modo en el que
conoc\'iamos los largos en la implementaci\'on de vectores).

Existen variantes para definir HList
(incluso considerando las t\'ecnicas modernas)
REF:
https://hackage.haskell.org/package/HList-0.5.0.0/docs/Data-HList-HList.html

Las versiones m\'as antiguas (y sobre estas se implement\'o originalmente
AspectAG) utilizan la siguiente representaci\'on, isomorfa a pares anidados:

< data HCons a b = HCons a b
< data HNil = HNil

El inconveniente de esta
representaci\'on es que podemos
construir tipos sin sentido como {\tt HCons Bool Char}.

En versiones posteriores HList utiliz\'o un GADT, y en las
\'ultimas versiones se utiliza una data Family.

En la documentaci\'on de la biblioteca
se explicita cual es la ventaja de cada representaci\'on. Dado que el GADT y
la data Family son pr\'acticamente equivalentes
(de hecho en nuestra implementaci\'on se pueden cambiar una por la otra),
preferimos el GADT por ser la soluci\'on m\'as clara.

> data HList (l :: [Type]) :: Type  where
>   HNil  :: HList '[]
>   HCons :: x -> HList xs -> HList (x ': xs)

Es intuitivo definir funciones en este contexto, por ejemplo

> hHead :: HList (x ': xs) -> x
> hHead (HCons x _) = x

> hTail :: HList (x ': xs) -> HList xs
> hTail (HCons _ xs) = xs


si queremos concatenar dos listas,
primero definimod la concatenaci\'on a nivel de tipos:

> type family (xs :: [Type]) :++ ( ys :: [Type]) :: [Type]
> type instance '[]       :++ ys = ys
> type instance (x ': xs) :++ ys = x ': (xs :++ ys)

A nivel de t\'erminos:

> hAppend :: HList xs -> HList ys -> HList (xs :++ ys)
> hAppend HNil ys = ys
> hAppend (HCons x xs) ys = HCons x (hAppend xs ys)

Una alternativa es usar la familia cerrada:

> class HAppend xs ys where
>   type HAppendR xs ys :: [Type]
>   chAppend :: HList xs -> HList ys -> HList (HAppendR xs ys)
 
> instance HAppend '[] ys where
>   type HAppendR '[] ys = ys
>   chAppend HNil ys = ys

> instance (HAppend xs ys) => HAppend (x ': xs) ys where
>   type HAppendR (x ': xs) ys = x ': (HAppendR xs ys)
>   chAppend (HCons x xs) ys = HCons x (chAppend xs ys)


Consideramos por ejemplo la funci\'on reverse:

> type family Reverse (l::[Type]) :: [Type]
> type instance Reverse '[]       = '[]
> type instance Reverse (x ': xs) = Reverse xs :++ '[x]

Si intentemos programar una funci\'on que actualiza la $n$-\'esima entrada en
una lista heterogenea, incluso eventualmente cambiando el tipo.
Intuitivamente deber\'ia tener el tipo:

< updateAtNat :: Nat -> x -> HList xs -> HList xs'

Donde {\tt xs'} depende de x y del {\bf valor} del natural del tipo {\tt Nat}.
Evidentemente esto no es posible, y necesitamos el natural a nivel de tipos.

La soluci\'on es usar Proxys, o singletons
(en este caso singleton es m\'as adecuado, vamos a hacer pattern Matching
sobre el natural as\'i que lo necesitamos en runtime)

< type family UpdateAtNat (n :: Nat)(x :: Type)(xs :: [Type]) :: [Type]
< type instance UpdateAtNat Zero     x (y ': ys) = x ': ys
< type instance UpdateAtNat (Succ n) x (y ': ys) = y ': UpdateAtNat n x ys

< updateAtNat :: SNat n -> x -> HList xs -> HList (UpdateAtNat n x xs)
< updateAtNat SZ y (HCons _ xs) = HCons y xs
< updateAtNat (SS n) y (HCons x xs) = HCons x (updateAtNat n y xs)




\subsection{Registros Heterogeneos}
\label{sec:hrecord}

AspectAG requiere de \emph{Records} heterogeneos, esto es, colecciones
etiqueta-valor, heterogeneas, donde adem\'as las claves est\'en dadas
por tipos, y no por valores.

El enfoque de HList para implementarles era utilizar una lista Heterogenea,
donde cada entrada era del tipo {\tt Tagged l v}, definido como

< Tagged l v = Tagged v

Esto no es satisfactorio con las herramientas modernas,
no se est\'a utilizando la posibilidad de tipar que nos provee la
promoci\'on de datos. HList implementa predicados como typeclasses
para asegurar que todos los miembros son de tipo {\tt Tagged} cuando
podr\'ia expresarse en el kind.
Adem\'as las etiquetas son de kind {\tt Type}, cuando en realidad nunca
requieren estar habitadas a nivel de valores. AspectAG genera etiquetas
utilizando metaprogramaci\'on con Template Haskell [REF], mientras
podr\'ia usarse simplemente data promotion.

En su lugar se propone la siguiente implementaci\'on:

> data Record :: forall k . [(k,Type)] -> Type where
>   EmptyR :: Record '[]
>   ConsR  :: LabelSet ( '(l, v) ': xs) =>
>    Tagged l v -> Record xs -> Record ( '(l,v) ': xs)

Un registro es una lista con m\'as estructura, el
vac\'io es an\'alogo a la lista vac\'ia, 
para agregar un campo, requerimos un valor de tipo {\tt Tagged l v}
definido como:

> data Tagged (l :: k) (v :: Type) where
>   Tagged :: v -> Tagged l v

Tagged es polimorfico en el kind de las etiquetas. Notar que
para construir un valor hay que anotar el tipo de {\tt l} o utilizar
un {\tt constructor inteligente} que use un proxy
(o en la jerga de AspectAG, una etiqueta).

< tag :: Label l -> v -> Tagged l v

La restricci\'on Labelset garantiza que las etiquetas no se repitan,
y se explica en la secci\'on siguiente.


\subsubsection{Predicados sobre tipos}

A pesar de que las extensiones modernas nos permiten adoptar
el estilo funcional en la programaci\'on a nivel de
tipos, el estilo l\'ogico sigue siendo adecuado para codificar predicados.
\footnote{Podr\'iamos tambi\'en codificar la funci\'on
booleana a nivel de tipos, luego se propaga como una restricci\'on 
con el calor que queremos, pero no parece natural.
}
Una lista heterogenea de pares satisface el predicado {\tt LabelSet}
si y solo si las primeras componentes son \'unicas. As\'i, la lista
de pares representa un mapeo.

Se implementa a la prolog:

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
