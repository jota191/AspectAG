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

En la biblioteca HList\cite{Kiselyov:2004:STH:1017472.1017488}
se presenta un buen ejemplo
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
  antigua y distinta de la versi\'on corriente en poco tiempo.
\item
  Cuando programamos a nivel de tipos el lenguaje no provee fuertes
  mecanismos de modularizaci\'on, dado que no fue dise\~nado para
  este prop\'osito. Es com\'un que por ejemplo, se fugue implementaci\'on
  con los mensajes de error. La implementaci\'on basada en HList filtrar\'ia
  errores de HList, que no utilizan el mismo vocabulario que nuestro
  EDSL. La imposibilidad de modularizar nos obliga a que si pretendemos
  tener estructuras distinguibles por sus nombres mnem\'onicos tenemos
  que reimplementarlas. Buscar mejores soluciones a esta complicaci\'on
  es parte de la investigaci\'on en el \'area, e idea de trabajo futuro.
\item
  HList no es necesariamente adecuada si queremos tipar todo lo fuertemente
  posible.
  Por ejemplo, en la implementaci\'on
  una de las estructuras a utilizar es esencialmente un
  registro que contiene registros.
  Usando tipos de datos a medida podemos programar
  una soluci\'on elegante donde esto queda expresado correctamente
  a nivel de kinds. La alternativa de implementar el registro externo
  como un registro de HList trata al interno como un tipo plano.
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
Haskell\cite{HColsWiki}
Nos interesan en particular las que son fuertemente tipadas, donde se conoce
est\'aticamente el tipo de cada miembro.

Existen variantes para definir HList
Las versiones m\'as antiguas (y sobre estas se implement\'o originalmente
AspectAG) utilizan la siguiente representaci\'on, isomorfa a pares anidados:

< data HCons a b = HCons a b
< data HNil = HNil

El inconveniente de esta
representaci\'on es que podemos
construir tipos sin sentido como {\tt HCons Bool Char}, lo cual puede
solucionarse mediante el uso de clases, como es usual en
el enfoque antig\"uo de la programaci\'on a nivel de tipos.

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


Para, por ejemplo concatenar dos listas,
primero definimos la concatenaci\'on a nivel de tipos:

> type family (xs :: [Type]) :++ ( ys :: [Type]) :: [Type]
> type instance '[]       :++ ys = ys
> type instance (x ': xs) :++ ys = x ': (xs :++ ys)

Y luego a nivel de t\'erminos:

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


Si intentemos, por ejemplo
programar una funci\'on que actualiza la $n$-\'esima entrada en
una lista heterogenea
(eventualmente cambiando el tipo del dato en esa posici\'on),
estamos claramente ante una funci\'on de tipos dependientes (el tipo
de salida depende de $n$). \'Este es el escenario donde ser\'an
necesarios {\tt Proxies} y\o {\tt Singletons}.

< type family UpdateAtNat (n :: Nat)(x :: Type)(xs :: [Type]) :: [Type]
< type instance UpdateAtNat Zero     x (y ': ys) = x ': ys
< type instance UpdateAtNat (Succ n) x (y ': ys) = y ': UpdateAtNat n x ys

< updateAtNat :: SNat n -> x -> HList xs -> HList (UpdateAtNat n x xs)
< updateAtNat SZ y (HCons _ xs) = HCons y xs
< updateAtNat (SS n) y (HCons x xs) = HCons x (updateAtNat n y xs)


\subsection{Registros Heterogeneos}
\label{sec:hrecord}

AspectAG requiere de registros heterogeneos, esto es, colecciones
etiqueta-valor, heterogeneas, donde adem\'as las claves est\'en dadas
por tipos.
El enfoque original de HList para implementarles es utilizar una lista
Heterogenea,
donde cada entrada era del tipo {\tt Tagged l v}, definido como

< Tagged l v = Tagged v

Consideramos que no es satisfactorio si pretendemos utilizar todo el poder
de las t\'ecnicas modernas.
No se est\'a utilizando la posibilidad de tipar que nos provee la
promoci\'on de datos. HList implementa predicados como typeclasses
para asegurar que todos los miembros son de tipo {\tt Tagged} cuando
podr\'ia expresarse directamente en el kind.
Adem\'as las etiquetas de HList
son de kind {\tt Type}, cuando en realidad nunca
requieren estar habitadas a nivel de valores.

En su lugar se propone la siguiente implementaci\'on:

> data Record :: forall k . [(k,Type)] -> Type where
>   EmptyR :: Record '[]
>   ConsR  :: LabelSet ( '(l, v) ': xs) =>
>    Tagged l v -> Record xs -> Record ( '(l,v) ': xs)

Un registro es una lista con m\'as estructura, a nivel de tipos
es una lista de pares, usamos la promoci\'on de listas y de pares
a nivel de tipos. Para agregar un campo,
requerimos un valor de tipo {\tt Tagged l v}
definido como:

> data Tagged (l :: k) (v :: Type) where
>   Tagged :: v -> Tagged l v

Tagged es polimorfico en el kind de las etiquetas.
La restricci\'on Labelset garantiza que las mismas no se repitan,
su implementaci\'on se explica a contunuaci\'on.


\subsubsection{Predicados sobre tipos}

Si bien las extensiones modernas nos permiten adoptar
el estilo funcional en la programaci\'on a nivel de
tipos, el estilo l\'ogico sigue siendo adecuado para codificar predicados.
Una lista promovida de pares satisface el predicado {\tt LabelSet}
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
con el valor que queremos. En general, la programaci\'on mediante
clases es siempre sustituible por familias,  
pero no parece natural en este caso.
