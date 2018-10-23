%if False

> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE FunctionalDependencies #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE GADTs #-}


%endif 

\subsubsection{Typeclasses y Typeclasses Multiparametro}


Haskell posee un sistema de \emph{TypeClasses} 
originalmente pensado para proveer polimorfismo ad-hoc
~\cite{Hall:1996:TCH:227699.227700}.
Una interpretaci\'on usual es que una \emph{Typeclass}
es como un predicado sobre tipos.
Cuando las \emph{TypeClasses} fueron introducidas fueron consideradas una
caracter\'istica experimental, por lo que tuvieron un dise\~no conservador
~\cite{type-classes-an-exploration-of-the-design-space}.

Las \emph{Typeclasses} son una extensi'on al sistema de tipos de
Hindley-Milner que es originalmente decidible. Para garantizar la decibilidad
del sistema de tipos en el dise\~no original se restringieron las instancias
que se pueden definir. En particular todas las declaraciones deben ser de la
forma {\tt T a1 a2 ... an} en donde {\tt a1 ... an} son variables de tipo
distintas, y lo mismo vale para los contextos. En la
pr\'actica existen muchos casos de uso interesantes en que
estas restricciones no permiten construir, y que usualmente no causan
que la compulaci\'on diverja.
Las extensiones de GHC {\tt FlexibleInstances} y {\tt FlexibleContexts} que
se implementan a partir de la versi\'on {\tt 6.8.1} de GHC
eliminan algunas de \'estas restricciones y son ampliamente utilzadas.


Por otro lado, la
limitaci\'on original a clases monopar\'ametro es arbitraria, y del mismo
modo en que una clase monopar\'ametro es un subconjunto de tipos,
podemos interpretar una case multipar\'ametro como una
relaci\'on entre tipos.
A partir de la versi\'on {\tt 6.8.1} de GHC, se provee la
extensi\'on {\tt MultiParamTypeclasses}, con la cual
es posible programar typeclasses multipar\'ametro. 

Existen m\'ultiples usos de las clases multipar\'ametro y no pretendemos
ser exhaustivos en este documento. Uno inmediato es implementar relaciones
como por ejemplo el isomorfismo:

> classs Iso a b where
>   iso :: a -> b
>   osi :: b -> a

En donde como es usual, es responsabilidad del programador que
{\tt iso . osi = id} y {\tt osi . iso = id}.
En ~\cite{type-classes-an-exploration-of-the-design-space} se presentan
m\'ultiples ejemplos. Un caso de uso muy usual es la sobrecarga con
par\'ametro restringidos, por ejemplo en la implementaci\'on de colecciones:

> class Eq e => Collection c e where
>   insert :: c -> e -> c
>   member :: c -> e -> Bool
>   ...

Los tipos  {\tt c} y {\tt e} est\'an relacionados en el sentido de que la
colecci\'on (una estructura de tipo {\tt c}) contiene elementos de tipo
{\tt e}.

Por ejemplo, una implementaci\'on con listas:

> instance Eq a => Collection [a] a where
>   insert = flip (:)
>   member = flip elem
>   ...

Supongamos que la clase {\tt Collection} tiene adem\'as un m\'etodo de tipo:

>  empty  :: c -> Bool

Obtenemos un error de compilaci\'on:

>  error:
>     . Could not deduce (Collection c e0)
>       from the context: Collection c e
>         bound by the type signature for:
>                    empty :: forall c e. Collection c e => c -> Bool
>         at Col.hs:8:3-21
>       The type variable 'e0' is ambiguous


Notar que si bien el tipo {\tt e} est\'a un\'ivocamente determinado por
{\tt c} en cualquier instancia razonable, el compilador no puede deducir
esto, por lo que en cada ocurrencia de {\tt empty} el tipo {\tt e} no puede
determinarse y ser\'a ambig\':uo.


\subsubsection{Dependencias Funcionales}

La soluci\'on a problemas similares al planteado en la secci\'on anterior
fu\'e tomada de las bases de datos relacionales
~\cite{DBLP:conf/esop/Jones00}.
Una dependencia funcional restringe las instancias de una clase
multipar\'ametro.

En una declaraci\'on como por ejemplo:

> class (...) => C a b c | a -> b

Cada par de instancias de {\tt C} que coincidan en {\tt a} {\bf deben}
coincidir en {\tt b}, de lo contrario el compilador reportar\'a un error.
Con la extensi\'on adem\'as el type checker se extiende de forma tal que
una vez que se resuelva la ocurrencia de {\tt a}, podr\'a resolverse la
de {\tt b} seg\'un la \'unica posibilidad.

As\'i, por ejemplo la siguiente implementaci\'on de colecciones es legal,
(y \'util):

> class Eq e => Collection c e | c -> e where
>   insert :: c -> e -> c
>   member :: c -> e -> Bool
>   empty  :: c -> Bool
>   ...

> instance Eq a => Collection [a] a where
>   insert = flip (:)
>   member = flip elem
>   empty  = null 
>   ... 


\subsubsection{Programaci\'on a nivel de tipos}

Tempranamente era sabido que el lenguaje a nivel de tipos es isomorfo
al lenguaje a nivel de valores, en el sentido de que la definici\'on

> data Zero
> data Succ n

introduce constructores a nivel de tipos con aridad cero y uno, del mismo
modo que la definici\'on:

> data Nat = Zero
>          | Succ Nat

los introduce a nivel de valores (con la salvedad de que a nivel de tipos,
los constructores solo tienen en su \emph{kind} informaci\'on
de la aridad; no est\'an fuertemente tipados).
Como se argument\'o anteriormente la extensi\'on de clases multipar\'ametro
vino a eliminar una restricci\'on de dise\~no, y las dependencias
funcionales a resolver un problema con ellas. Pero la comunidad es creativa
y los entusiastas no tardaron en darse cuenta de que \'estas extensiones
agregaban la posibilidad de expresar computaciones en tiempo de compilaci\'on,
abusando del sistema de tipos~\cite{Hallgren00funwith}.
Las clases multiparametro definen relaciones sobre tipos, que combinadas con
las dependencias funcionales permiten esencialmente expresar funciones sobre
los mismos, y \emph{decidir} una resoluci\'on a nivel del typechecker es
fundamentalmente computar con \'el.


\subsubsection{Ejemplo: Naturales a Nivel de tipos}

Considremos por ejemplo la siguiente implementaci\'on de los naturales
unarios, como tipo inductivo:

> data Nat = Zero
>          | Succ Nat

\'Esta definici\'on introduce los constructores
{\tt Zero :: Nat} y {\tt Succ :: Nat -> Nat}.
Podemos entonces construir t\'erminos de tipo {\tt Nat} de la forma

< n0 = Zero 
< n4 = Succ $ Succ $ Succ $ Zero 

O definir funciones por \emph{pattern matching} de la siguiente manera:

> add :: Nat -> Nat -> Nat
> add n Zero     = n
> add n (Succ m) = Succ (add n m)

Por otra parte la definici\'on a nivel de tipos:

> data Zero
> data Succ n

tambi\'en introduce constructores (de tipos) {\tt Zero :: *}
y {\tt Succ :: * -> *}
An\'alogamente podemos implementar la suma a nivel de tipos de la siguiente
manera:

> class Add m n smn | m n -> smn where
>   tAdd :: m -> n -> smn

> instance Add Zero m m
>   where tAdd = undefined

> instance Add n m k => Add (Succ n) m (Succ k)
>   where tAdd = undefined

Ahora el t\'ermino:

> u3 = tAdd (undefined :: Succ (Succ Zero))(undefined :: Succ Zero)

tiene tipo {\tt Succ (Succ (Succ Zero))}, que es computado gracias a la
dependencia funcional.


\paragraph{Programaci\'on l\'ogica y Programaci\'on con clases}

\'Este tipo de programaci\'on se asemeja a la programaci\'on l\'ogica.

En Prolog[REF] escribir\'iamos:


< add(0,X,X) :-
<     nat(X).
< add(s(X),Y,s(Z)) :-
<     add(X,Y,Z).

Sin embargo, programar relaciones funcionales con Typeclasses difiere
respecto a programar en Prolog, dado que el type checker de GHC no realiza
backtracking al resolver una instancia. 

Cuando tenemos una sentencia de la forma:

< class (A x, B x) => C x

y GHC debe probar {\tt C a}, primero el typechecker \emph{matchea}
su objetivo con la \emph{cabeza} {\tt C x},
agregando las restricci\'on {\tt x $\sim$ a}, y
{\bf luego} pasa a probarse el contexto. Si se falla habr\'a un error
de compilaci\'on se abortar\'a.

En Prolog es v\'alido:

< c(X) :- a(X), b(X)
< c(X) :- d(X), e(X)

Si se trata de probar {\tt c(X)} y fallan {\tt a(X)} o {\tt b(X)},
el int\'erprete hace \emph{bactracking} y busca una prueba de
la alternativa. En haskell la traducci\'on del programa anterior
ni siquiera es legal (GHC retorna error por \emph{Overlapping Instances}).

En particular entonces no podemos decidir la implementaci\'on de las
operaciones de una clase a partir de la
resoluci\'on de un contexto u otro.
Esto sigue siendo relevante cuando programamos con las t\'ecniicas modernas
y existe una soluci\'on sistem\'atica que ilustraremos m\'as adelante.

\subsubsection{Completitud (de Turing)}

Con estas t\'ecnicas se pueden realizar computaciones sofisticadas
en tiempo de compilaci\'on~\cite{parker:tlii}~\cite{McBride2002FakingIS},
y puede demostrarse que de hecho, que las t\'ecnicas para definir
computaciones en tiempo de compilaci\'on con estas extensiones tienen
el poder de expresividad de un lenguaje Turing Completo,
lo cual queda demostrado al codificar, por ejemplo un calculo de
combinadores SKI ~\cite{OlegSKI}.


\subsubsection{Tipado a nivel de Tipos}

En el ejemplo anterior los constructores {\tt Zero} y {\tt Succ} tienen kinds
{\tt *} y {\tt * -> *}.
Nada impide entonces construir instancias patol\'ogicas de tipos como
{\tt Succ Bool}, o {\tt Succ (Succ (Maybe Int))}.

El lenguaje a nivel de tipos es entonces escencialmente no tipado.
Una soluci\'on al problema de las instancias inv\'alidas es programar un
predicado (una nueva clase) que indique cu\'ando un tipo representa un
natural a nivel de tipos, y requerirla como contexto cada vez que se
quiere asegurar que solo se puedan construir instancias v\'alidas, as\'i:

> class TNat a
> instance TNat Zero
> instance TNat n => TNat (Succ n)

Por ejemplo la funci\'on {\tt add} entonces puede definirse como:

< class (TNat m, TNat n, TNat smn) => Add m n smn | m n -> smn where
<   tAdd :: m -> n -> smn


\subsubsection{Aplicaciones}

La mayor utilidad de estas t\'ecnicas no pasa por
realizar computaciones de prop\'osito general en nivel de tipos, sino por
codificar chequeos de propiedades que nuestro programa debe cumplir
(en tiempo de compilaci\'on), como
se hace usualmente con lenguajes de tipos dependientes aunque con algunas
limitaciones, pero tambi\'en con algunas ventajas.
McBride~\cite{McBride2002FakingIS} discute la aplicaci\'on usual de vectores
(listas indizadas por su largo). Como ejemplos m\'as complejos
podemos citar a la biblioteca HList
~\cite{Kiselyov:2004:STH:1017472.1017488} de colecciones heterogeneas
fuertemente tipadas, la propia biblioteca AspectAG
~\cite{Viera:2009:AGF:1596550.1596586} que vamos a reimplementar,
o bases de datos fuertemente tipadas~\cite{Silva:2006:STR:1159842.1159846}.

A modo de ejemplo consideremos el cl\'asico ejemplo de tipo de datos
dependiente: Las listas indizadas por su tama\~no.


[TODO] Esto requiere GADTs, GADTs se introduce en ghc 6.8.1
igual que FunctionalDependencies

> data Vec a n where
>   VZ :: Vec a Zero
>   VS :: a -> Vec a n -> Vec a (Succ n)


Por ejemplo, la funci\'on:

> safeHead :: (TNat n) =>  Vec a (Succ n) -> a
> safeHead (VS a _) = a

aplicada a un vector vac\'io no compilar\'a.

< <interactive>:3:10: error:
<     - Couldn't match type 'Zero' with 'Succ n0'
<       Expected type: Vec a (Succ n0)
<         Actual type: Vec a Zero
<     - In the first argument of 'safeHead', namely 'VZ'
<       In the expression: safeHead VZ
<       In an equation for 'it': it = safeHead VZ

La implementaci\'on de funciones no triviales sobre vectores
(por ejemplo {\tt reverse}, {\tt take}, {\tt chop}) son complejas y requieren
desarrollar algunos \emph{hacks}. Esencialmente con estas t\'ecnicas
antiguas de programaci\'on a nivel de tipos tenemos que resolver
todas las limitaciones presentadas en la secci\'on \ref{sec:limitaciones},
y m\'as. La biblioteca HList~\cite{Kiselyov:2004:STH:1017472.1017488} es
una recopilaci\'on exhaustiva de estas t\'ecnicas. A los efectos de este
documento no nos interesa ser exhaustivos con esto [redactar mejor esto].