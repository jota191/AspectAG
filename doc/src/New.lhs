%if False

> {-# LANGUAGE DataKinds            #-} --
> {-# LANGUAGE FlexibleContexts     #-} --
> {-# LANGUAGE GADTs                #-}  -- 
> {-# LANGUAGE KindSignatures       #-}  --
> {-# LANGUAGE RankNTypes           #-} --
> -- {-# LANGUAGE ScopedTypeVariables  #-} 
> {-# LANGUAGE TypeFamilies         #-} -- 
> {-# LANGUAGE TypeOperators        #-} --
> {-# LANGUAGE FlexibleInstances     #-} --
> {-# LANGUAGE UndecidableInstances  #-}
> {-# LANGUAGE MultiParamTypeClasses #-}--
> {-# LANGUAGE PolyKinds #-}             --

> module New where
> import Prelude hiding ((+))

%endif



\subsubsection{DataKinds} (7.4.1)
El desarrollo del concepto de datatype promotion
~\cite{Yorgey:2012:GHP:2103786.2103795}
es un importante salto de expresividad. En lugar de tener un sistema
de kinds en donde solamente se logra expresar la aridad de los tipos,
pueden \emph{promoverse} datatypes adecuados.

Con la extensi\'on {\tt -XDataKinds}, cada declaraci\'on de tipos como

> data Nat = Zero | Succ Nat deriving (Show, Eq, Ord)

> Zero     + n = n
> (Succ m) + n = Succ (m + n)

se duplica a nivel de Kinds.

Adem\'as de introducir los t\'erminos {\tt Zero} y {\tt Succ} de tipo
{\tt Nat}, y al propio tipo {\tt Nat } de kind {\tt *}, introduce
los TIPOS {\tt Zero} y {\tt Succ} de Kind {\tt Nat} (y al propio kind Nat).

El kind {\tt *} pasa entonces a ser el de los tipos habitados, y cada vez que
declaramos un tipo promovible se introducen tipos no habitados del nuevo kind.


En el ejemplo de la secci\'on anterior, el tipo {\tt Vec}ten\'ia kind
{\tt * $\rightarrow$ * $\rightarrow$ *} por lo que {\tt Vec Bool Char}
era un tipo v\'alido.
Con DataKinds podemos construir: (+KindSignatures para anotar)

> data Vec :: Nat -> * -> * where
>   VZ :: Vec Zero a
>   VS :: a -> Vec n a -> Vec (Succ n) a

\subsubsection{{\tt GHC.TypeLits}}

intro del modulo

Usando el m\'odulo
{\tt GHC.TypeLits}, podemos escribir: (+TypeOperators)

< data Vec :: Nat -> * -> * where
<   VZ :: Vec 0 a
<   VS :: a -> Vec n a -> Vec (n+1) a


\subsubsection{Sintaxis promovida (DataKinds + TypeOperators)} (7.4.1)

\subsubsection{XPolyKinds}

\subsubsection{TypeFamilies} (6.8.1)

La introduccion de la extensi\'on typefamilies es previa a DataKinds, y
PolyKinds.
decidimos presentarla en este orden para introducir ejemplos interesantes
con el kind Nat.

INTRO

Algunas definiciones posibles:

> type family (m :: Nat) :+ (n :: Nat) :: Nat
> type instance Zero :+ n = n
> type instance Succ m  :+ n = Succ (m :+ n) 

{REF to THIS}



\subsubsection{Programando con tipos dependientes}



Utilizando esta representaci\'on, podemos programar funciones seguras,
de forma an\'aloga a como las escribir\'iamos en lenguajes de tipos
dependientes
como por ejemplo:

> vHead :: Vec (Succ n) a -> a
> vHead (VS a _) = a

> vTail :: Vec (Succ n) a -> Vec n a
> vTail (VS _ as) = as

Intentar compilar la expresi\'on {\tt vHead VZ} retorna un error
de compilaci\'on: 

< error:
<     . Couldn't match type  ''Zero' with ''Succ n0'
<       Expected type: Vec ('Succ n0) a
<         Actual type: Vec 'Zero a
<     . In the first argument of 'vHead', namely 'VZ'
<       In the expression: vHead VZ


> vZipWith :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
> vZipWith _ VZ VZ = VZ
> vZipWith f (VS x xs) (VS y ys)
>   = VS (f x y)(vZipWith f xs ys)

< vZipWith (+) (VS 3 VZ) (VS 4 (VS 3 VZ)) 
< error:
<     . Couldn't match type ''Succ 'Zero' with ''Zero'
<       Expected type: Vec ('Succ 'Zero) c
<         Actual type: Vec ('Succ ('Succ 'Zero)) c
<     . In the third argument of 'vZipWith', namely '(VS 4 (VS 3 VZ))'
<       In the expression: vZipWith (+) (VS 3 VZ) (VS 4 (VS 3 VZ))
<       In an equation for 'it':

Otro ejemplo:


[TODO]: explicar por que funciona, (Hasochism) 

> vAppend :: Vec n a -> Vec m a -> Vec (n :+ m) a
> vAppend (VZ) bs      = bs
> vAppend (VS a as) bs = VS a (vAppend as bs)



COMENTAR TOTALIDAD, safety

MAS EJEMPLOS?


\subsubsection{Limitaciones}

A diferencia de lo que ocurre en implementaciones de lenguajes con tipos
dependientes, los lenguajes de t\'erminos y de tipos en Haskell
contin\'uan habitando mundos separados.

La correspondencia entre nuestra definici\'on de vectores
y las familias inductivas en los lenguajes de tipos dependientes no es tal.

El {\tt n} en el tipo de Haskell es est\'atico, y borrado en tiempo de
ejecuci\'on, mientras que en un lenguaje de tipos dependientes es
esencialmente \emph{din\'amico} ~\cite{Lindley:2013:HPP:2578854.2503786}.

En las teor\'ias de tipos intensionales
una definici\'on como la de la type family
{HACER REF} extiende el algoritmo de normalizaci\'on, de forma tal que el
\emph{ type checker} decidir\'a la igualdad de tipos seg\'un las formas
normales. Si dos tipos tienen la misma forma normal entonces los mismos
t\'erminos les habitar\'an.

Por ejemplo {\tt Vec (S (S Z) :+ n) a} y {\tt Vec (S (S n)) a} tendr\'an
los mismos habitantes.

Esto no va a ser cierto para tipos como
{\tt Vec (n :+ S (S Z)) a} y {\tt Vec (S (S n)) a}, aunque que los tipos
coincidan para todas las instancias concretas de {\tt n}.
Para expresar propiedades como la conmutatividad
se utilizan evidencias de las ecuaciones utilizando
\emph{tipos de igualdad proposicional}\footnote{Propositional Types}.
~\cite{Lindley:2013:HPP:2578854.2503786}. [buscar mejor referencia]

En el sistema de tipos de Haskell sin embargo, la igualdad de tipos
es puramente sint\'actica.
{\tt Vec (n :+ S (S Z)) a} y {\tt Vec (S (S n)) a} {\bf no} son el mismo
tipo, y no tienen los mismos habitantes.

La definici\'on como [REF a TF] axiomatiza {\tt :+} para la igualdad
proposicional de Haskell. Cada ocurrencia de {\tt :+} debe estar soportada
con evidencia expl\'icita derivada de estos axiomas.

Cuando GHC traduce desde el lenguaje externo al lenguaje del kernel,
busca generar evidencia mediante heur\'isticas de resoluci\'on de
restricciones.

La evidencia sugiere que el \emph{constraint solver} computa agresivamente,
y esta es la raz\'on por la cual la funci\'on {\tt vAppend} compila
y funciona correctamente.

Sin embargo, supongamos que queremos definir la funci\'on:

< vchop :: Vec (m :+ n) x -> (Vec m x, Vec n x)

No es posible definirla si no tenemos {\tt m} o {\tt n} en tiempo
de ejecuci\'on.

Por otra parte la funci\'on:

< vtake :: Vec (m :+ n) x -> Vec m x

tiene un problema m\'as sutil. Incluso teniendo {\tt m} en tiempo
de ejecuci\'on, no es posible para el type checker tiparla: no hay
forma de deducir {\tt n} a partir del tipo del par\'ametro.
El type checker es incapaz de deducir que {\tt :+} es inyectiva.


\subsubsection{Singletons y Proxies}
\label{sec:sings}

Existen dos \emph{hacks}, para resolver los problemas planteados en la 
secci\'on anterior.

\paragraph{Singletons}

Para codificar {\tt vChop}, que podemos escribir de tipo

< vChop :: forall (m n :: Nat). Vec (m :+ n) x -> (Vec m x, Vec n x)

si explicitamos los par\'ametros naturales, necesitamos hacer
referencia expl\'icita a {\tt m} para decidir donde cortar.
Como en Haskell el cuantificador $\forall$ dependiente solo habla
de objetos est\'aticos (los lenguajes de tipos y t\'erminos est\'an
separados), esto no es posible directamente.

Un tipo \emph{singleton}, en el contexto de Haskell, es un GADT
que replica datos est\'aticos a nivel de t\'erminos.

> data SNat :: Nat -> * where
>   SZ :: SNat Zero
>   SS :: SNat n -> SNat (Succ n)

Existe por cada tipo {\tt n} de kind {\tt Nat}, {\bf un}
\footnote{Formalmente esto no es cierto, si consideramos el valor $\bot$}
valor de tipo {\tt SNat n}.

$\Pi $ types

Podemos implementar {\tt vChop}:

> vChop :: SNat m -> Vec (m :+ n) x -> (Vec m x, Vec n x)
> vChop SZ xs            = (VZ, xs)
> vChop (SS m) (VS x xs) = let (ys, zs) = vChop m xs
>                          in (VS x ys, zs)

\paragraph{Proxies}

An\'alogamente para definir {\tt vTake} necesitamos {\tt m} en tiempo
de ejecuci\'on. Consideramos la implementaci\'on:


< vTake :: SNat m -> Vec (m :+ n) x -> Vec m x
< vTake SZ xs     = SZ
< vTake (SS x xs) = -- (no es necesario para activar el error)

Obtenemos un error de tipos:

< . Couldn't match type 'm :+ n' with 'm :+ n0'
<   Expected type: SNat m -> Vec (m :+ n) x -> Vec m x
<   Actual type: SNat m -> Vec (m :+ n0) x -> Vec m x
<   NB: ':+' is a type function, and may not be injective
<   The type variable 'n0' is ambiguous
< . In the ambiguity check for 'vtake'

Notar que esta vez no es necesaria una representaci\'on de {\tt n}
en tiempo de ejecuci\'on. {\tt n} es est\'atico pero necesitamos que sea
expl\'icito.

Consideramos la definici\'on (que requiere la extensi\'on PolyKinds):

> data Proxy :: k -> * where
>   Proxy :: Proxy a

Proxy es un tipo que no contiene datos, pero contiene un par\'ametro
\emph{phantom} de tipo arbitrario (de hecho, de kind arbitrario).

Historicamente, el constructor de tipos no polim\'orfico
{\tt Proxy :: * -> *} funcionaba
como una alternativa segura a {\tt undefined :: a},
(usando expresiones como {\tt Proxy :: Proxy a}).

Con polimorfismo de kinds podemos construir proxys aplicando el constructor
a habitantes de cualquier kind, en particular {\tt Nat}.

El uso de un proxy va a resolver el problema de {\tt vTake}, indicando
simplemente que la ocurrencia del proxy tiene el mismo tipo que el {\tt n}
en el vector [explicar esto bien]

La siguiente implementaci\'on de vTake funciona:

> vTake :: SNat m -> Proxy n -> Vec (m :+ n) x -> Vec m x
> vTake SZ _ xs            = VZ
> vTake (SS m) n (VS x xs) = VS x (vTake m n xs)

[ver bien aca si no vale la pena explicar el caso recursivo]


%if False

> v1 = VS 3 (VS 4 VZ)
> v2 = VS 9 (VS 5 VZ)


> instance Show a => Show (Vec n a) where
>   show VZ = "[]"
>   show (VS a as) = show a ++ ":" ++ show as

%endif
