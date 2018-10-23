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



\subsubsection{DataKinds} 
El desarrollo del concepto de datatype promotion
~\cite{Yorgey:2012:GHP:2103786.2103795}, que se introduce en  GHC en su
versi\'on {\tt 7.4.1} con la extensi\'on {\tt DataKinds}
es un importante salto de expresividad. En lugar de tener un sistema
de kinds en donde solamente se logra expresar la aridad de los tipos,
pueden \emph{promoverse} ciertos tipos de datos (con ciertas limitaciones,
por ejemplo inicialmente no es posible promover {\tt GADTs}).
Con la extensi\'on habilidata, cada declaraci\'on de tipos como 

> data Nat = Zero | Succ Nat

se ``duplica'' a nivel de kinds, esto es, 
adem\'as de introducir los t\'erminos {\tt Zero} y {\tt Succ} de tipo
{\tt Nat}, y al propio tipo {\tt Nat } de kind {\tt *}, la declaraci\'on
introduce los \emph{tipos}
{\tt Zero} y {\tt Succ} de Kind {\tt Nat} (y al propio kind Nat).
El kind {\tt *} ya no es el \'unico kind unario existente, y pasa a ser
un kind especial: el de los tipos habitados.  Cada vez que
declaramos un tipo promovible se introducen tipos no habitados del nuevo kind.


En el ejemplo de la secci\'on anterior, el tipo {\tt Vec}ten\'ia kind
{\tt * $\rightarrow$ * $\rightarrow$ *} por lo que {\tt Vec Bool Char}
era un tipo v\'alido.
Con DataKinds podemos construir: (Utilizando adem\'as, la extensi\'on
{\tt KindSignatures} para anotar el kind de {\tt Vec}).


> data Vec :: Nat -> * -> * where
>   VZ :: Vec Zero a
>   VS :: a -> Vec n a -> Vec (Succ n) a


[LISTAS PROMOVIDAS]

\subsubsection{TypeFamilies} (6.8.1)

[REFS: https://wiki.haskell.org/GHC/Typefamilies]

ndexed type families are a new GHC extension to facilitate type-level
programming.
Type families are a generalisation of associated data types (Associated Types
with Class, M. Chakravarty, G. Keller, S. Peyton Jones, and S. Marlow.
In Proceedings of ``The 32nd Annual ACM SIGPLAN-SIGACT Symposium on
Principles of Programming Languages (POPL'05'', pages 1-13, ACM Press, 2005)
and associated type synonyms
(``Type Associated Type Synonyms''. M. Chakravarty,
G. Keller, and S. Peyton Jones. In Proceedings of ``The Tenth ACM SIGPLAN
International Conference on Functional Programming'', ACM Press, pages 241-253,
2005). Type families themselves are described in the paper ``Type Checking with
Open Type Functions'', T. Schrijvers, S. Peyton-Jones, M. Chakravarty, and M.
Sulzmann, in Proceedings of ``ICFP 2008: The 13th ACM SIGPLAN International
Conference on Functional Programming'', ACM Press, pages 51-62, 2008.
Type families essentially provide type-indexed data types and named functions
on types, which are useful for generic programming and highly parameterised l
ibrary interfaces as well as interfaces with enhanced static information,
much like dependent types. They might also be regarded as an alternative to
functional dependencies, but provide a more functional style of type-level
programming than the relational style of functional dependencies.
INTRO

Las \emph{Typefamilies} permiten definir funciones a nivel de tipos, por
ejemplo

> type family (m :: Nat) + (n :: Nat) :: Nat
> type instance Zero + n = n
> type instance Succ m  + n = Succ (m :+ n) 

\label{sec:tf}

Es el equivalente de la funci\'on

> Zero     + n = n
> (Succ m) + n = Succ (m + n)

definida a nivel de valores.

Entonces, el {\bf tipo} {\tt (Succ Zero) + (Succ Zero)} denota, y reduce a
{\tt Succ (Succ Zero)}.

\subsubsection{Azucar sint\'actica}

En la definici\'on anterior se utilizan algunas extensiones m\'as para
lograr una sintaxis tan limpia.
La extensi\'on {\tt TypeOperators} (implementada desde GHC {\tt 6.8.1})
habilita el uso de simbolos operadores como constructores de tipos.
Por ejemplo, podemos definir

> data a + b = Left a | Right b

O como en la definici\'on anterior, la type family {\tt (+)}, sin
contar con {\tt TypeOperators} deber\'iamos definir la familia de tipos
como

> type family Add m n ...


La extensi\'on {\tt KindSignatures} por otra parte
permite anotar los kinds (del mismo
modo que anotamos los tipos en funciones a nivel de valores), tanto para
documentar como para desambiguar en ciertos casos.

Podemos ir m\'as all\'a, el m\'odulo {\tt GHC.TypeLits}
({\tt base-4.12.0.0}) declara Naturales y Caracteres a nivel de tipos
con una sintaxis como la usual.

Importando el m\'odulo, es c\'odigo legal, por ejemplo:

< data Vec :: Nat -> * -> * where
<   VZ :: Vec 0 a
<   VS :: a -> Vec n a -> Vec (n+1) a


\subsubsection{Sintaxis promovida (DataKinds + TypeOperators)} (7.4.1)

\subsubsection{Polimorfismo de Kinds}

Yorgey et al. [REF] introducen el polimorfismo a nivel de kinds, que en GHC
corresponde a la extensi\'on {\tt PolyKinds} implementada a partir de la
versi\'on {\tt 7.4.1} del compilador. Con la extensi\'on habilidada
es posible implementar funciones a nivel de tipos polim\'orficas.
Por ejemplo:

> type family Length (list :: '[a]) :: Nat where
>   Length '[]       = 'Zero
>   Length (x ': xs) = 'Succ (Length xs)


[hay que unificar la notacion, aca escribo TF cerrada antes abierta,
uso todos los constructores promovidos con ' , etc]





\subsubsection{Programando con tipos dependientes}

[explicar mejor aca]
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
\label{sec:limitaciones}

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
~\ref{sec:tf} extiende el algoritmo de normalizaci\'on, de forma tal que el
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
