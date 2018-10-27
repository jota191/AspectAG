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
El desarrollo del concepto de datatype
promotion~\cite{Yorgey:2012:GHP:2103786.2103795},
que se introduce en  GHC en su
versi\'on {\tt 7.4.1} con la extensi\'on {\tt DataKinds}
es un importante salto de expresividad. En lugar de tener un sistema
de kinds en donde solamente se logra expresar la aridad de los tipos,
pueden \emph{promoverse} ciertos tipos de datos (con ciertas limitaciones,
por ejemplo inicialmente no es posible promover {\tt GADTs}).
Con la extensi\'on cada declaraci\'on de tipos como 

> data Nat = Zero | Succ Nat

se ``duplica'' a nivel de kinds. Esto es, 
adem\'as de introducir los t\'erminos {\tt Zero} y {\tt Succ} de tipo
{\tt Nat}, y al propio tipo {\tt Nat} de kind {\tt *} la declaraci\'on
introduce los \emph{tipos}
{\tt Zero} y {\tt Succ} de Kind {\tt Nat} (y al propio kind Nat).
El kind {\tt *} ya no es el \'unico unario existente, y pasa a ser
uno m\'as, aunque particular: el de los tipos habitados.
Cada vez que declaramos un tipo promovible se introducen tipos no
habitados del nuevo kind promovido.


En el ejemplo de la secci\'on anterior, el tipo {\tt Vec} ten\'ia kind
{\tt * -> * -> *} por lo que {\tt Vec Bool Char}
era un tipo v\'alido.
Con DataKinds podemos construir: (Utilizando adem\'as, la extensi\'on
{\tt KindSignatures} para anotar el kind de {\tt Vec}).

> data Vec :: Nat -> * -> * where
>   VZ :: Vec Zero a
>   VS :: a -> Vec n a -> Vec (Succ n) a

Cuando programamos con la extensi\'on habilitada por defecto se promueven
algunos tipos b\'asicos, en particular las listas. Por ejemplo
{\tt [Bool, Char, Int]} es un tipo de kind {\tt [*]}, o
{\tt [Succ Zero, Zero]} es un tipo de kind {\tt [Nat]}. Cuando existe
ambig\"edad (y en particular en ciertos contextos es necesario)
los constructores promovidos pueden escribirse precedidos por un car\'acter
apostrofe, por ejemplo {\tt '[ 'Succ 'Zero, 'Zero]}
es el tipo de kind {\tt [Nat]} que antes..


\subsubsection{TypeFamilies} (6.8.1)

Las \emph{Type families} o familias de tipos indizadas,
son una extensi\'on para facilitar la programaci\'on a nivel de tipos.
\footnote{}


----------------------------------------
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

------------------------------------------

Las {type families} proveen tipos indizados por tipos y funciones
sobre los mismos que son \'utiles en programaci\'on gen\'erica o interfaces
provistas con informaci\'on est\'atica de tipado,
del mismo modo que con interfaces de tipos dependientes.
Pueden considerarse una alternativa a las dependencias funcionales, pero
proveen un estilo m\'as \emph{idiom\'atico} de programaci\'on en el
contexto de haskell, dado que codificar familias de tipos se asemeja
a la programaci\'on funcional en t\'erminos,
a diferencia del enfoque relacional o l\'ogico de las
dependencias funcionales.
La siguiente definici\'on implementa la suma a nivel de tipos:

> type family (m :: Nat) + (n :: Nat) :: Nat
> type instance Zero + n = n
> type instance Succ m  + n = Succ (m :+ n) 

\label{sec:tf}

Es el equivalente de la funci\'on

> (+) :: Nat -> Nat -> Nat
> Zero     + n = n
> (Succ m) + n = Succ (m + n)

definida a nivel de valores.

Entonces, el {\bf tipo} {\tt (Succ Zero) + (Succ Zero)} denota, y reduce a
{\tt Succ (Succ Zero)}.

Existe una notaci\'on alternativa, cerrada:

> type family (m :: Nat) + (n :: Nat) :: Nat where
>   (+) Z     a = a
>   (+) (S a) b = S (a + b)

En ambos casos la anotaci\'on de los kinds podr\'ia omitirse.


\subsubsection{Azucar sint\'actica}

En la definici\'on anterior se utilizan algunas extensiones m\'as para
lograr una sintaxis tan limpia.
La extensi\'on {\tt TypeOperators} (implementada desde GHC {\tt 6.8.1})
habilita el uso de simbolos operadores como constructores de tipos.
Por ejemplo, podemos definir

> data a + b = Left a | Right b

En la secci\'on anterior definimos la  type family {\tt (+)}. Sin
contar con la extensi\'on {\tt TypeOperators}
deber\'iamos definir la familia de tipos como

> type family Add m n ...


La extensi\'on {\tt KindSignatures} por otra parte
permite anotar los kinds (del mismo
modo que anotamos los tipos en funciones a nivel de valores), tanto para
documentar como para desambiguar en ciertos casos.

Podemos ir m\'as all\'a con la notaci\'on, el m\'odulo {\tt GHC.TypeLits}
({\tt base-4.12.0.0}) declara Naturales y Caracteres a nivel de tipos
con una sintaxis como la usual.

Importando el m\'odulo, es c\'odigo legal, por ejemplo:

< data Vec :: Nat -> * -> * where
<   E    :: Vec 0 a
<   (:<) :: a -> Vec n a -> Vec (n+1) a

Y {\tt 'e':<'4':<E } una expresi\'on de tipo {\tt Vec 2 Char}

\subsubsection{Polimorfismo de Kinds}

Yorgey et al. [REF] introducen el polimorfismo a nivel de kinds, que en GHC
corresponde a la extensi\'on {\tt PolyKinds} implementada a partir de la
versi\'on {\tt 7.4.1} del compilador. Con la extensi\'on habilidada
es posible implementar funciones a nivel de tipos polim\'orficas.
Por ejemplo:

> type family Length (list :: '[a]) :: Nat where
>   Length '[]       = 'Zero
>   Length (x ': xs) = 'Succ (Length xs)


\subsubsection{Programando con tipos dependientes}

[explicar mejor aca]
Utilizando esta representaci\'on, podemos programar funciones seguras,
de forma an\'aloga a como las escribir\'iamos en lenguajes de tipos
dependientes
como por ejemplo:

> vHead :: Vec (Succ n) a -> a
> vHead (VS a _) = a

Intentar compilar la expresi\'on {\tt vHead VZ} retorna un error
de compilaci\'on: 

< error:
<     . Couldn't match type  ''Zero' with ''Succ n0'
<       Expected type: Vec ('Succ n0) a
<         Actual type: Vec 'Zero a
<     . In the first argument of 'vHead', namely 'VZ'
<       In the expression: vHead VZ


Otros ejemplos, pueden ser:

> vTail :: Vec (Succ n) a -> Vec n a
> vTail (VS _ as) = as


> vZipWith :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
> vZipWith _ VZ VZ = VZ
> vZipWith f (VS x xs) (VS y ys)
>   = VS (f x y)(vZipWith f xs ys)

O incluso:

> vAppend :: Vec n a -> Vec m a -> Vec (n :+ m) a
> vAppend (VZ) bs      = bs
> vAppend (VS a as) bs = VS a (vAppend as bs)


\subsubsection{Limitaciones}
\label{sec:limitaciones}

A diferencia de lo que ocurre en implementaciones de lenguajes con tipos
dependientes, los lenguajes de t\'erminos y de tipos en Haskell
contin\'uan habitando mundos separados.
La correspondencia entre nuestra definici\'on de vectores
y las familias inductivas en los lenguajes de tipos dependientes no es tal.

Las ocurrencias de {\tt n} los tipos de las funciones anteriores son
est\'aticas, y borradas en tiempo de
ejecuci\'on, mientras que en un lenguaje de tipos dependientes estos
par\'ametros son esencialmente
\emph{din\'amicos}~\cite{Lindley:2013:HPP:2578854.2503786}.
En las teor\'ias de tipos intensionales
una definici\'on como la familia en 
~\ref{sec:tf} extiende el algoritmo de normalizaci\'on, de forma tal que el
compilador decidir\'a la igualdad de tipos seg\'un las formas
normales. Si dos tipos tienen la misma forma normal entonces los mismos
t\'erminos les habitar\'an.
Por ejemplo, los tipos  {\tt Vec (S (S Z) :+ n) a} y {\tt Vec (S (S n)) a}
tendr\'an los mismos habitantes.
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

La definici\'on como ~\ref{sec:tf} axiomatiza {\tt :+} para la igualdad
proposicional de Haskell. Cada ocurrencia de {\tt :+} debe estar soportada
con evidencia expl\'icita derivada de estos axiomas.
Cuando GHC traduce desde el lenguaje externo al lenguaje del kernel,
busca generar evidencia mediante heur\'isticas de resoluci\'on de
restricciones.

La evidencia sugiere que el \emph{constraint solver} computa agresivamente,
y esta es la raz\'on por la cual la funci\'on {\tt vAppend} definida
anteriormente compila y funciona correctamente.

Sin embargo, dada la funci\'on:

> vchop :: Vec (m + n) x -> (Vec m x, Vec n x)

resulta imposible definirla si no tenemos la informaci\'on de
{\tt m} o {\tt n} en tiempo de ejecuci\'on (intuitivamente,
ocurre que ``no sabemos donde partir el vector'').

Por otra parte la funci\'on:

< vtake :: Vec (m + n) x -> Vec m x

tiene un problema m\'as sutil. Incluso asuminedo que tuvieramos forma
de obtener {\tt m} en tiempo
de ejecuci\'on, no es posible para el verificador de tipos aceptarla.
No hay forma de deducir {\tt n} a partir del tipo del tipo {\tt m + n}
sin la informaci\'on de que {\tt (+)} es una funci\'on inyectiva, lo cual
el verificador de tipos es incapaz de deducir.


\subsubsection{Singletons y Proxies}
\label{sec:sings}

Existen dos \emph{hacks}, para resolver los problemas planteados en la 
secci\'on anterior.

\paragraph{Singletons}

Si pretendemos implementar {\tt vChop} cuyo tipo
podemos escribir m\'as expl\'icitamente como 

> vChop :: forall (m n :: Nat). Vec (m + n) x -> (Vec m x, Vec n x)

necesitamos hacer
referencia expl\'icita a {\tt m} para decidir donde cortar.
Como en Haskell el cuantificador $\forall$ dependiente solo habla
de objetos est\'aticos (los lenguajes de tipos y t\'erminos est\'an
separados), esto no es posible directamente.

Un tipo \emph{singleton}, en el contexto de Haskell, es un {\tt GADT}
que replica datos est\'aticos a nivel de t\'erminos.

> data SNat :: Nat -> * where
>   SZ :: SNat Zero
>   SS :: SNat n -> SNat (Succ n)

Existe por cada tipo {\tt n} de kind {\tt Nat}, {\bf un}
\footnote{Formalmente esto no es cierto, si consideramos el valor $\bot$}
valor de tipo {\tt SNat n}.

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

Consideramos la definici\'on:

> data Proxy :: k -> * where
>   Proxy :: Proxy a

Proxy es un tipo que no contiene datos, pero contiene un par\'ametro
\emph{phantom} de tipo arbitrario (de hecho, de kind arbitrario).

Historicamente, el constructor de tipos no polim\'orfico
{\tt Proxy :: * -> *} funcionaba
como una alternativa segura a {\tt undefined :: a}, como las usadas en
la secci\'on [REF]
(usando expresiones como {\tt Proxy :: Proxy a}).

Gracias al polimorfismo de kinds podemos construir proxys aplicando
el constructor
a habitantes de cualquier kind, en particular {\tt Nat}.
El uso de un proxy va a resolver el problema de {\tt vTake}, indicando
simplemente que la ocurrencia del proxy tiene la informaci\'on del tipo
{\tt n} en el vector.

La siguiente implementaci\'on de vTake es funcional:

> vTake :: SNat m -> Proxy n -> Vec (m :+ n) x -> Vec m x
> vTake SZ _ xs            = VZ
> vTake (SS m) n (VS x xs) = VS x (vTake m n xs)
