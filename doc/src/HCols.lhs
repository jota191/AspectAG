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
  HList es una biblioteca experimental, en constante cambio, que no pretende
  ser una fuente estable de dependencias, y que constantemente cambia
  su interfaz sin ser compatible hacia atr\'as. Implementar
  hoy dependiendo de HList implica depender posiblemente de una versi\'on
  antigua y distinta de la versi\'on final en poco tiempo.
\item
  Cuando programamos a nivel de tipos el lenguaje no provee fuertes
  mecanismos de modularizaci\'on. Es com\'un que se fugue implementaci\'on
  con los mensajes de error. Y la implementaci\'on basada en HList va a
  filtrar errores de HList, que no utilizan los mismo t\'erminos que
  la jerga de nuestro DSL.
  Si bien proveemos una soluci\'on al manejo
  de errores [TODO: REF], no es necesariamente exhaustiva.
  La biblioteca AspectAG utiliza m\'ultiples estructuras isomorfas a Records,
  y dentro del propio desarrollo de la misma result\'o m\'as c\'omodo
  trabajar con estructuras con sus nombres mnem\'onicos.
\item
  HList no es necesariamente adecuada si queremos tipar todo lo fuertemente
  posible.
  Por una parte es restrictiva. Por ejemplo, en la implementaci\'on
  vamos a utilizar una estructura que es esencialmente un
  Record de Records. Usando tipos de datos a medida podemos programar
  una soluci\'on elegante donde esto queda expresado correctamente
  en el kind. Implementando el Record externo como un Record de HList
  ofusca al interno, tratandolo como un tipo "plano".
  Por otra parte es muy general (se implementan varias veces las mismas
  funcionalidades para comparar)
\item
  Por inter\'es acad\'emico. Reescribir HList (varias veces, un subconjunto
  mayor al necesario para AspectAG) fu\'e la forma de dominar las t\'ecnicas.

  { ``?`C\'omo se aprende a programar?
    Con leer mucho c\'odigo y escribir mucho c\'odigo." \\[5pt]
    \rightline{{\rm --- Richard Stallman}}
  }

  Esto no es una raz\'on en si para efectivamente depender de
  una nueva implementaci\'on en lugar de la implementaci\'on moderna de
  HList, pero a los argumentos anteriores se le suma que no
  requerimos de mayor costo.
\end{itemize}

\paragraph{Definici\'on}

Una lista (o \'as en general una colecci\'on)
heterogenea es tal si contiene valores de distintos tipos.
En haskell el tipo {\tt [a]} va a ser un contenedor de valores de tipo
{\tt a}.

Por ejemplo

< hlist = "foo" : True : []

conduce a un error de tipos.
Existen varios enfoques para construir colecciones heterogeneas en Haskell,
REF: https://wiki.haskell.org/Heterogenous\_collections

A nosotros nos interesan las que son fuertemente tipadas, se conoce
est\'aticamente el tipo de cada miembro (an\'alogamente al largo en la
implementaci\'on de vectores).

Existen variantes para definir HList
(incluso considerando las t\'ecnicas modernas)
REF:
https://hackage.haskell.org/package/HList-0.5.0.0/docs/Data-HList-HList.html

Las versiones m\'as antiguas (y sobre estas se implement\'o originalmente
AAG) utilizan la siguiente representaci\'on:

< data HCons a b = HCons a b
< data HNil = HNil

As\'i por ejemplo

< HCons "4" (HCons True HNil) :: HCons [Char] (HCons Bool HNil)

Es una lista heterogenea bien tipada. El inconveniente de esta
representaci\'on (adem\'as de la verborragia) es que podemos
construir tipos sin sentido como {\tt HCons Bool Char}.
Notar que esta implementaci\'on es an\'aloga a los naturales de
2.1.3 [TODO: PONER BIEN REF], y podemos resolver el problema
y "clausurar" las listas con una typeclass an\'aloga a {\tt TNat}.
... O sacar partido de las nuevas extensiones.

En versiones posteriores HList utiliz\'o un GADT, y en las
\'ultimas versiones se utiliza una data Family.

En
https://hackage.haskell.org/package/HList-0.5.0.0/docs/Data-HList-HList.html

se explicita cual es la ventaja de cada representaci\'on. Dado que el GADT y
la data Family son pr\'acticamente equivalentes
(de hecho en nuestra implementaci\'on se pueden cambiar una por la otra),
preferimos el GADT por ser la soluco\'on m\'as clara y elegante.

> data HList (l :: [Type]) :: Type  where
>   HNil  :: HList '[]
>   HCons :: x -> HList xs -> HList (x ': xs)

Por ejemplo

> boolStrChar = HCons True $ HCons "foo" $ HCons 't' HNil

es un t\'ermino v\'alido de tipo {\tt HList '[Bool, [Char], Integer]}


Una posible definici\'on de la instancia {\tt Show}

> instance Show (HList '[]) where
>   show _ = "[]"

> instance (Show x, Show (HList xs)) => Show (HList (x ': xs))  where
>   show (HCons e l) = let tsl = tail (show l)
>                      in "[" ++show e ++ if tsl == "]"
>                                         then "]"
>                                         else  "," ++ tsl



Podemos definir Head o Tail seguras:

> hHead :: HList (x ': xs) -> x
> hHead (HCons x _) = x

> hTail :: HList (x ': xs) -> HList xs
> hTail (HCons _ xs) = xs

Supongamos que queremos concatenar dos listas:

< hAppend :: HList xs -> HList ys -> HList ?? -- oops

Definimos la concatenaci\'on a nivel de tipos:

> type family (xs :: [Type]) :++ ( ys :: [Type]) :: [Type]
> type instance '[]       :++ ys = ys
> type instance (x ': xs) :++ ys = x ': (xs :++ ys)

A nivel de t\'erminos:

> hAppend :: HList xs -> HList ys -> HList (xs :++ ys)
> hAppend HNil ys = ys
> hAppend (HCons x xs) ys = HCons x (hAppend xs ys)

Una alternativa:

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

< *Main> :kind! Reverse ('[Bool, [Char], Integer])
< Reverse ('[Bool, [Char], Integer]) :: [*]
< = '[Integer, [Char], Bool]

> hReverse :: HList xs -> HList (Reverse xs)
> hReverse HNil = HNil
> hReverse (HCons x xs) = hAppend (hReverse xs) (HCons x HNil)

Intentemos programar una funci\'on que actualiza la $n$-\'esima entrada en
una lista heterogenea, incluso eventualmente cambiando el tipo.
Intuitivamente deber\'ia tener el tipo:

< updateAtNat :: Nat -> x -> HList xs -> HList xs'

Donde {\tt xs'} depende de x y del {\bf valor} del natural del tipo {\tt Nat}.
Evidentemente esto no es posible, y necesitamos el natural a nivel de tipos.

La soluci\'on es usar Proxys, o singletons
(en este caso singleton es m\'as adecuado, vamos a hacer pattern Matching
sobre el natural as\'i que lo necesitamos en runtime)
Una segunda firma candidata es entonces:

< updateAtNat :: SNat n -> x -> HList xs -> HList xs'

Que por supuesto a\'un no funciona porque no hay relaci\'on entre n, x xs y xs'.

Programemos el update a nivel de tipos:

< type family UpdateAtNat (n :: Nat)(x :: Type)(xs :: [Type]) :: [Type]
< type instance UpdateAtNat Zero     x (y ': ys) = x ': ys
< type instance UpdateAtNat (Succ n) x (y ': ys) = y ': UpdateAtNat n x ys


< *Main> :kind! UpdateAtNat Zero (Maybe Int) '[Bool, [Char], Integer]
< UpdateAtNat Zero (Maybe Int) '[Bool, [Char], Integer] :: [*]
< = '[Maybe Int, [Char], Integer]
< *Main> :kind! UpdateAtNat (Succ Zero) (Maybe Int) '[Bool, [Char], Integer]
< UpdateAtNat (Succ Zero) (Maybe Int) '[Bool, [Char], Integer] :: [*]
< = '[Bool, Maybe Int, Integer]
< *Main> :kind! UpdateAtNat (Succ (Succ (Succ Zero))) (Maybe Int) '[Bool, [Char], Integer]
< UpdateAtNat (Succ (Succ (Succ Zero))) (Maybe Int) '[Bool, [Char], Integer] :: [*]
< = Bool : [Char] : Integer : UpdateAtNat 'Zero (Maybe Int) '[]


Ahora la vers\'on final:

< updateAtNat :: SNat n -> x -> HList xs -> HList (UpdateAtNat n x xs)
< updateAtNat SZ y (HCons _ xs) = HCons y xs
< updateAtNat (SS n) y (HCons x xs) = HCons x (updateAtNat n y xs)


Que pasa si intentamos actualizar un \'indice que no existe?
por ejemplo al evaluar

< updateAtNat (SS (SS(SS SZ))) '5' mylist

El t\'ermino de hecho est\'a bien tipado,

< updateAtNat (SS (SS(SS SZ))) '5' mylist
<   :: HList (Bool : [Char] : Integer : UpdateAtNat 'Zero Char '[])

Podr\'amos trabajar con \'el, no podemos por ejemplo imprimirle:

< <interactive>:36:1: error:
<     . No instance for (Show (HList (UpdateAtNat 'Zero Char '[])))
<         arising from a use of 'print'
<     . In a stmt of an interactive GHCi command: print it

Si nuestro objetivo es que nuestros programas sean confiables, rechazar la
compilaci\'on de programas incorrectos siempre que sea posible,
esas expresiones deber\'ian estar {\bf mal tipadas}.

\subsubsection{Programando con restricciones}

Para resolver el problema con {\tt updateAtNat } deber\'iamos {\bf  limitar}
las instancias monom\'orficas v\'alidas de:

< updateAtNat2 :: forall (n::Nat) (x :: Type) (xs :: [Type]).
<                 SNat n -> x -> HList xs -> HList (UpdateAtNat n x xs)

Esto es justamente lo que podemos hacer con una typeclass
(Predicar sobre los tipos).

Consideramos la siguiente definici\'on alternativa:

> class UpdateAtNat (n :: Nat) (y :: Type) (xs :: [Type]) where
>   type UpdateAtNatR n y xs :: [Type]
>   updateAtNat :: SNat n -> y -> HList xs -> HList (UpdateAtNatR n y xs)

> instance UpdateAtNat Zero y (x ': xs) where
>   type UpdateAtNatR Zero y (x ': xs) = (y ': xs)
>   updateAtNat SZ y (HCons _ xs) = HCons y xs

> instance UpdateAtNat n y xs
>   => UpdateAtNat (Succ n) y (x ': xs) where
>   type UpdateAtNatR (Succ n) y (x ': xs) =  x ': UpdateAtNatR n y xs
>   updateAtNat (SS n) y (HCons x xs) = HCons x (updateAtNat n y xs)

Funciona correctamente para los \'indices v\'alidos, por ejemplo
 {\tt updateAtNat (SS (SS SZ)) True boolStrChar} reduce a
{\tt [True,"foo",True]}, pero si evaluamos:

< updateAtNat (SS (SS (SS SZ))) True boolStrChar

Obtenemos un error de compilaci\'on, como quer\'iamos:

< <interactive>:32:1: error:
<     . No instance for (UpdateAtNat 'Zero Bool '[])
<         arising from a use of 'updateAtNat'
<     . In the expression: updateAtNat (SS (SS (SS SZ))) True boolStrChar
<       In an equation for 'it':
<           it = updateAtNat (SS (SS (SS SZ))) True boolStrChar

En la reimplementaci\'on de AspectAG este estilo de programaci\'on
ser\'a ampliamente usado.

[TODO: tambien se puede presentar aca la version con dependencia funcional,
para explicar por que es util y que no necesariamente significa un paso atras
talvez hay que usar un ejemplo mejor..]


\subsubsection{Manejo de Errores}

El error de compilaci\'on tal y como lo aprecia el programador en la secci\'on
anterior es bastante enga\~noso. Mucho m\'as a\'un si consideramos
c\'odigo complicado. "{\tt No instance for (UpdateAtNat 'Zero Bool '[]) }" no
nos dice nada sobre la lista original.

Kyselyov et al ~\cite{Kiselyov:2004:STH:1017472.1017488} proponen una
soluci\'on (en el a\~no 2004). [TODO Mover esto arriba?]

En lugar de la definici\'on antigua:

> class Fail e
> data PositionOutOfBound

< instance Fail (PositionOutOfBound) => UpdateAtNat n x '[] where
<   type UpdateAtNatR n x '[] = '[]
<   updateAtNat = undefined

Que conduce al error "{\tt No instance for (Fail PositionOutOfBound)}"



Podemos recurrir al m\'odulo {\tt GHC.TypeLits}.
\footnote{{\tt TypeError} tambi\'en es una typefamily (polykinded) y
  funciona como una versi\'on promovida de {\tt error :: [Char] -> a},
  Podr\'iamos tambi\'en operar sobre la TypeFamily (la primer implementaci\'on)
  y evitar el uso de Typeclasses en este caso.
}

EXPLICAR MAS

> instance TypeError (Text "Type Error ----" :$$:
>                     Text "From the use of 'UpdateAtNat' :" :$$:
>                     Text "Position Out of Bound" :$$:
>                     Text "Perhaps your list is too short?")
>   => UpdateAtNat n x '[] where
>   type UpdateAtNatR n x '[] = '[] -- unreachable
>   updateAtNat = undefined

La compilaci\'on produce un error mucho m\'as legible:

< <interactive>:10:1: error:
<     . Type Error ----
<       From the use of 'UpdateAtNat' :
<       Position Out of Bound
<       Perhaps your list is too short?
<     . In the expression: updateAtNat (SS (SS (SS SZ))) True boolStrChar


\subsubsection{Logic vs Functional}

Supongamos que queremos codificar:

< getByType :: x -> HList xs




\subsection{Records Heterogeneos}

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

Un record es una lista con m\'as estructura.
Notar que el record vac\'io es an\'alogo a la lista vac\'ia.
Para agregar un campo, requerimos un valor de tipo {\tt Tagged l v}
definido como:

> data Tagged (l :: k) (v :: Type) where
>   Tagged :: v -> Tagged l v

Tegged es polimorfico en el kind de las etiquetas. Notar que
para construir un valor hay que anotar el tipo de {\tt l} o utilizar
un {\tt constructor inteligente} que use un proxy
(o en la jerga de AspectAG, una etiqueta).

< tag :: Label l -> v -> Tagged l v

La restricci\'on Labelset garantiza que las etiquetas no se repitan,
y se explica en la secci\'on siguiente.




\subsubsection{M\'as Restricciones}

Las typeclasses, entendidas como predicados sobre tipos

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

> instance TypeError (Text "LabelSet Error:" :$$:
>                     Text "Duplicated Label on Record" :$$:
>                    Text "On fields:" :$$: ShowType l1 :$$:
>                    Text " and " :$$: ShowType l1 )
>           => LabelSet' l1 l2 True r
