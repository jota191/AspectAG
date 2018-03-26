
\documentclass{article}
\usepackage{amsmath,amssymb}
\usepackage{framed}

\newcommand{\key}[1]{\ensuremath{\operatorname{\bf #1}}}
\title{Typed Heterogeneous Collections}

\author{Juan Pablo García Garland}
\date{}

%include lhs2TeX.fmt
%include lhs2TeX.sty


\begin{document}
\maketitle

\section{Introduction}

El objetivo sera programar un subconjunto de las utlidades que
provee la biblioteca HList.

En particular, queremos programar Records fuertemente tipados, es decir,
listas de pares indice-valor, en donde los indices seran tipos.
El type checker probara parte de la
especificacion (por ejemplo, la no repeticion de los indices).

El fin ultimo, es obtener una estructura que usaremos para implementar
mapeos (funciones) en la implementación de AAG. Por ejemplo, una
\emph{Atribución} es una mapeo entre nombres de atributos (indices)
y valores.


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
>              ScopedTypeVariables#-}

> module HList.HList where
> import Data.Kind
> import Data.Type.Equality (type (==))

La idea es que el modulo sea lo mas autocontenido posible,
para evitar generar dependencias medio tiviales.

En particular, reimplemento Proxy y LVPair.



\section{Listas heterogeneas}

Definimos el tipo de las listas heterogeneas, dependientes (cuyo largo y tipo
de los elementos se conoce en tiempo de compilacion), como una
\emph{type family}.

Declaramos que HList es una familia de tipos indizada por las listas a nivel
de tipos (promovidas, usamos Datakinds):

< data family HList (l::[Type])

Inductivamente, definimos

< data instance HList '[] = HNil
< data instance HList (x ': xs) = x `HCons` HList xs


Puede definirse como un GADT (por ahora uso esto, al menos
hasta ahora las implementaciones son intercambiables).

> data HList (l :: [Type]) :: Type  where
>   HNil :: HList '[]
>   HCons :: x -> HList xs -> HList (x ': xs)


En el paper original de AAG, la implementacion de las listas heterogeneas
se basa en HList 0.2.x. En donde se utilizaba la tecnica antigua de definir
tipos de datos para cada constructor, y efectuar la clausura con una
Typeclass.
Esta implementacion con GADTs utiliza el estado del arte (ghc8, TypeInType
no es estrictamente necesario, podriamos no haber anotado los tipos),
y difiere de la que usa la biblioteca HList en
su version 0.4.2.0 (ultimo release) ,que usa una type family)



\section{Extendiendo colecciones}


Declaramos HExtend, para modelar la extension de colecciones.

Esto difiere respecto a la implementacion que hace la biblioteca
HList.

La idea es que al reimplementar AspectAG, voy a tipar (*kindear) cosas
que estan hechas a "la antigua".

Por ejemplo definir

< data Fam (c :: [Type]) (p::[Type]) :: Type where
<   Fam :: Record c -> Record p -> Fam c p

En lugar de

< data Fam c p = Fam c p

La clase HExtend de HList, tiene par\'ametros de kind Type (HExtend e l),
por lo que la siguiente definici\'on:

< syndef :: (HExtend (Att att val) sp,
<            sp' ~ HExtendR (Att att val) sp)
<           => Label att -> val -> (Fam ic sp -> Fam ic sp')

no compila (sp tiene kind [Type], pero en la clase HExtend tiene kind Type)

Entonces implemento la interfaz de colecciones extensibles as\'i:

(tipando todo, y tengo que explicitar como parametro el wrapper que usa
la coleccion (HList, Record, etc)).

> class HExtend (w :: [Type] -> Type ) (e :: Type) (l::[Type]) where
>   type HExtendR w e l :: [Type]
>   (.*.) :: e -> w l -> w (HExtendR w e l)
> infixr 2 .*.

TODO: Al hacer explicito al wrapper HExtendR queda trvial,
(hago siempre Type level Cons). Esto creo que se puede simplificar
y no usar el tipo indizado, habria que refactorear


En HList 0.2.x, esto se modelaba con una Typeclass
multiparametro.


La idea es que cada instancia de esta clase introduce una regla de extension
para alguna estructura, en donde en el tipado se restringe para asegurar buena
formacion. En el caso de los Records, se controlara no repetir etiquetas.
Se introduce ademas la azucar sintactica del operador infijo $.*.$ .

El caso mas simple de extension se da en las listas planas, en donde
no existen las restricciones (a una lista puedo agregarle cualquier cosa):


> instance HExtend HList e xs where
>   type HExtendR HList e xs = (e ': xs)
>   (.*.) = HCons



\section{Records extensibles}

Definimos el tipo para los records. Un record es basicamente una lista
wrapeada:

> newtype Record (r :: [Type]) = Record (HList r)

En donde los elementos son del tipo:

> newtype Tagged l v = Tagged { unTagged :: v }
>                    deriving (Show, Eq)

Algunas funciones utiles:

> labelLVPair :: Tagged l v -> Label l
> labelLVPair _ = Label

> valueLVPair :: Tagged l v -> v
> valueLVPair = unTagged

> newLVPair :: Label l -> v -> Tagged l v
> newLVPair _ = Tagged


Es decir, cada entrada de la lista tiene un habitante de Tagged l v, que
es un contenedor de un valor de tipo v, indizado por el \emph{tipo} l.

El tipo l es un phantom type. Las etiquetas por lo tanto solo existen
en tiempo de compilacion.


Esta implementacion es mucho
mas segura que la original, al ser tipada,
gracias a los DataKinds. Se requiere que el
parametro tenga kind [Type]


El siguiente paso es programar la extension de los records, de forma tal
que esten bien formados. Explotamos la expresividad de los tipos de Haskell.

Un record debe cumplir:
\begin{itemize}
\item
  Que todos los elementos de la lista sean pares Etiqueta-Valor
\item
  Que no existan etiquetas repetidas
\end{itemize}

La tecnica consiste en especificar estos predicados como Typeclasses,
y luego requerirlos como contexto en los smart constructors.

La clase {\tt{ HAllTagged }} predica sobre las listas que tienen todos OBsus
elementos como pares Etiqueta-Valor (i.e. del tipo Tagged).

Definimos la clase:

> class HAllTaggedLV (ps :: [Type])

> instance HAllTaggedLV '[]
> instance (HAllTaggedLV xs, x ~ Tagged t v)
>    => HAllTaggedLV (x ': xs)

Esto es, La lista vacia es Taggeada, y si a una lista Taggeada le agregamos
un elemento Taggeado, obtenemos una lista Taggeada.

La clase {\tt{ HLabelSet }} predica sobre los conjuntos de etiquetas que
no contienen elementos repetidos.



> class HLabelSet (l :: [Type])
> instance HLabelSet '[]
> instance HLabelSet '[x]
> instance ( HEqK l1 l2 leq
>          , HLabelSet' l1 l2 leq r
>          ) => HLabelSet (l1 ': l2 ': r)

> class HLabelSet' l1 l2 (leq::Bool) r
> instance ( HLabelSet (l2 ': r)
>          , HLabelSet (l1 ': r)
>          ) => HLabelSet' l1 l2 False r
> instance ( Fail (DuplicatedLabel l1) ) => HLabelSet' l1 l2 True r

> class DuplicatedLabel l

> class (HLabelSet (LabelsOf ps), HAllTaggedLV ps) => HRLabelSet (ps :: [*])
> instance (HLabelSet (LabelsOf ps), HAllTaggedLV ps) => HRLabelSet (ps :: [*])


>
> type family LabelsOf (ls :: [*]) :: [*]
> type instance LabelsOf '[] = '[]
> type instance LabelsOf (Label l ': r)  = Label l ': LabelsOf r
> type instance LabelsOf (Tagged l v ': r) = Label l ': LabelsOf r

Smart Constructor:

> mkRecord :: (HRLabelSet r ) => HList r -> Record r
> mkRecord = Record


Finalmente definimos la interfaz de extension de los Registros:

> instance ( HRLabelSet (e ': r)
>          , HAllTaggedLV (e ': r))
>   => HExtend Record e r where
>   type HExtendR Record e r = (e ': r)
>   e .*. (Record r) = mkRecord (HCons e r)


> emptyRecord = mkRecord HNil


Actualizando una etiqueta:


Codificamos el la relacion SameLength,

en donde dos listas estan

relacionadas sii tienen el mismo largo.

Se usara como contexto de funciones que

mantengan largos de listas en su

especificacion:

> class SameLength (es1 :: [k]) (es2 :: [m])
> instance (es2 ~ '[]) => SameLength '[] es2
> instance (SameLength xs ys, es2 ~ (y ': ys)) => SameLength (x ': xs) es2

Para Actualizar el valor de una etiqueta, requerimos una funcion de tipo,
por ejemplo {\tt{ Label l -> v -> record r -> record r' }}.
Como es polimorfica por todos lados usamos una  typeclass:


< class HasField (l::k) (r::[Type]) (v::Type) | l r -> v where
<     hLookupByLabel:: Label l -> Record r -> v



Intuitivamente podemos encontrar el campo en la cabeza,
o en la cola de la lista.
Queremos entonces programar dos posibles generadores de instancias:

< instance HasField l (Record ((Tagged l v) ': tail)) v where
<   hLookupByLabel l (Record (HCons lv tail)) = unTagged lv

< instance HasField l (Record tail) v
<   => HasField l (Record (t ': tail)) v where
<   hLookupByLabel l (Record (HCons lv tail)) = hLookupByLabel l (Record tail)

Sin embargo aparece un problema, esto no funciona (overlapping Instances).

< ghci> hLookupByLabel (Label:: Label Label1) myHR

El problema es que en realidad cualquier record que matchee con la cabeza de
la primer instancia, matchea con la cabeza de la segunda.
Estamos haciendo que el contexto de la instancia decida sobre que
declaracion usar
(si no estoy mal esta es la gran diferencia entre las typeclasses y una
 maquina de prolog).

Es conocida una tecnica para resolver esto:
https://wiki.haskell.org/GHC/AdvancedOverlap

(en el paper de AAG est\'a bien la referencia que es a Oleg Kiselyov)


> class HasField (l::k) (r :: [Type]) v | l r -> v where
>    hLookupByLabel:: Label l -> Record r -> v


> instance (HEqK l l1 b, HasField' b l (Tagged l1 v1 ': r) v)
>     => HasField l (Tagged l1 v1 ': r) v where
>     hLookupByLabel l (Record r) =
>              hLookupByLabel' (Proxy::Proxy b) l r


> --instance Fail (FieldNotFound l)
> -- =>HasField l (Record '[])(FieldNotFound l) where
> --    hLookupByLabel _ _
> --      = error "Data.HList.Record.HasField: Fail instances should not exist"


> class HasField' (b::Bool) (l :: k) (r::[*]) v | b l r -> v where
>     hLookupByLabel':: Proxy b -> Label l -> HList r -> v

> instance HasField' True l (Tagged l v ': r) v where
>    hLookupByLabel' _ _ (HCons (Tagged v) _) = v
> instance HasField l r v => HasField' False l (fld ': r) v where
>    hLookupByLabel' _ l (HCons _ r) = hLookupByLabel l (Record r)

---------------------------------------------------------------------------------
Syntactic sugar:

> infixr 9 #
> (#) :: HasField l r v => Record r -> Label l -> v
> (#) = flip hLookupByLabel


> data Proxy a = Proxy




{-

> class HEq (x :: k) (y :: k) (b :: Bool) | x y -> b

-- | Equality for types that may have different kinds. This definition
-- allows operations on @Record [Tagged \"x\" a, Tagged 2 b]@ to work
-- as expected.

> type HEqK (x :: k1) (y :: k2) (b :: Bool) = HEq (Proxy x) (Proxy y) b



> instance ((Proxy x == Proxy y) ~ b) => HEq x y b

-}



HFindLabel:

>
> class HFindLabel (l :: Type) (r :: [Type]) (n :: Nat) where
>     getIndex :: Label l -> Record r -> Proxy n-> Nat


> instance HFindLabel l (Tagged l v ': r) Zero where
>     getIndex _ _ _= Zero
>
> instance (Reify n, HFindLabel l r n)
>   => HFindLabel l (x ': r) (Succ n) where
>     getIndex _ _ _= Succ (reify (Proxy :: Proxy n))
>

> class HUpdateAtHNat (n :: Nat) v (r :: [Type]) where
>   type HUpdateAtHNatR (n :: Nat) v (r :: [Type]) :: [Type]
>   hUpdateAtHNat :: Proxy n -> v -> HList r -> HList (HUpdateAtHNatR n v r)

> instance HUpdateAtHNat Zero v (x ': xs) where
>   type HUpdateAtHNatR Zero v (x ': xs) = v ': xs
>   hUpdateAtHNat Proxy v (HCons _ xs) = HCons v xs

> instance HUpdateAtHNat n v r
>   => HUpdateAtHNat (Succ n) v (x ': r) where
>     type HUpdateAtHNatR (Succ n) v (x ': r) = x ': (HUpdateAtHNatR n v r)
>     hUpdateAtHNat (Proxy :: Proxy (Succ n)) v (HCons x xs)
>       = HCons x $ hUpdateAtHNat (Proxy :: Proxy n) v xs

> type family HUpdateAtHNatR' (n :: Nat) v (r :: [Type]) :: [Type]
> type instance HUpdateAtHNatR' Zero v (x ': xs) = v ': xs
> type instance HUpdateAtHNatR' (Succ n) v (x ': xs)
>   = x ': HUpdateAtHNatR' n v xs


> class
>     HUpdateAtLabel (l :: k) (v :: Type) (r :: [Type]) (r' :: [Type])
>           | l v r -> r', l r' -> v where
>     hUpdateAtLabel :: SameLength r r'=>
>       Label l -> v -> Record r -> Record r'

> instance (HUpdateAtLabel2 l v r r',
>         HasField l r' v) =>
>         HUpdateAtLabel l v r r' where
>     hUpdateAtLabel = hUpdateAtLabel2

> class HUpdateAtLabel2 (l :: k) (v :: Type) (r :: [Type]) (r' :: [Type])
>         | l r v -> r' where
>     hUpdateAtLabel2 :: Label l -> v -> Record r -> Record r'

> class HUpdateAtLabel1 (b :: Bool)(l :: k)(v ::Type)(r ::[Type])(r' :: [Type])
>         | b l v r -> r' where
>     hUpdateAtLabel1 :: Proxy b -> Label l -> v -> Record r -> Record r'

> instance HUpdateAtLabel1 True l v (Tagged l e ': xs) (Tagged l v ': xs) where
>     hUpdateAtLabel1 _b _l v (Record (e `HCons` xs)) =
>       Record (e{ unTagged = v } `HCons` xs)

> instance HUpdateAtLabel2 l v xs xs'
>   => HUpdateAtLabel1 False l v (x ': xs) (x ': xs') where
>     hUpdateAtLabel1 _b l v (Record (x `HCons` xs))
>       = case hUpdateAtLabel2 l v (Record xs) of
>         Record xs' -> Record (x `HCons` xs')


> instance (HEqK l l' b, HUpdateAtLabel1 b l v (Tagged l' e ': xs) xs')
>     => HUpdateAtLabel2 l v (Tagged l' e ': xs) xs' where
>     hUpdateAtLabel2 = hUpdateAtLabel1 (Proxy :: Proxy b)



> instance Fail (FieldNotFound l) => HUpdateAtLabel2 l v '[] '[] where
>     hUpdateAtLabel2 _ _ r = r

> class Fail a
> class FieldNotFound a


HUpdateAtLabel es un wrapper de HUpdateAtlabel2,
agregando la precondicion HasField.

HUpdateAtLabel1 agrega un parametro de kind Bool que indica si se esta
actualizando la cabeza o no.




Test membership en type level:


> class HMember (e1 :: k) (l :: [k]) (b :: Bool) | e1 l -> b
> instance HMember e1 '[] False
> instance (HEq e1 e b, HMember' b e1 l br) => HMember  e1 (e ': l) br

> class HMember' (b0 :: Bool) (e1 :: k) (l :: [k]) (b :: Bool) | b0 e1 l -> b
> instance HMember' True e1 l True
> instance (HMember e1 l br) => HMember' False e1 l br

> hMember :: HMember e l b => e -> HList l -> Proxy b
> hMember _ _ = undefined


> testHMember :: HMember e l True => e -> Record l -> ()
> testHMember _ _ = ()


> class HasLabel (l :: k)(r :: [Type])(b :: Bool)| l r -> b where {}
> instance HasLabel l' '[] False
> instance (HEq l lp b, HasLabel l r b', Or b b' ~ b'')
>   => HasLabel l (Tagged lp vp ': r) b''


> hasLabel :: HasLabel l r b => l -> Record r -> Proxy b
> hasLabel = undefined

> hasLabel2 :: HasLabel l r b => Label l -> Record r -> Proxy b
> hasLabel2 = undefined

TODO: esta duplicado porque en el modulo AspectAG necesito una u otra,
luego hay que refactorear en lo posible y usar uno solo de estos

\section{tests}

> myrH = (Label :: Label Label1) .=. "v1" .*.
>        (Label :: Label Label2) .=. '2'  .*. HNil
> myr = mkRecord myrH
> myHR = (Label :: Label Label1) .=. "v1" .*.
>        (Label :: Label Label2) .=. '2'  .*.
>        (Label :: Label Label4) .=. False .*.
>        (Label :: Label Label3) .=. Zero  .*.emptyRecord


> t1 = hUpdateAtLabel (Label :: Label Label1) Zero myHR


\section{Boilerplate}


> data Label1
> data Label2
> data Label3
> data Label4
> data Label5

> data Nat = Zero | Succ Nat deriving Show

> type family Or (a :: Bool)(b :: Bool) :: Bool where
>   Or True  _ = True
>   Or False b = b


> class Reify (n :: Nat) where
>   reify :: Proxy n -> Nat

> instance Reify Zero where
>   reify _ = Zero
> instance Reify n => Reify (Succ n) where
>   reify (Proxy :: Proxy (Succ n)) = Succ (reify (Proxy :: Proxy n))

> singHR = (Label :: Label Label1) .=. "v1" .*. emptyRecord


> infixr 4 .=.

> (.=.) :: Label l -> v -> Tagged l v
> l .=. v = newLVPair l v



> instance Show (HList '[]) where
>     show _ = "H[]"

> instance (Show e, Show (HList l)) => Show (HList (e ': l)) where
>     show (HCons x l) = let 'H':'[':s = show l
>                        in "H[" ++ show x ++
>                                   (if s == "]" then s else "," ++ s)


> data Label l = Label


> deriving instance (Eq (HList r)) => Eq (Record r)
> deriving instance (Ord (HList r)) => Ord (Record r)
> deriving instance (Show (HList r)) => Show (Record r)


Aplicacion de funciones




ver HList FakePrelude para mejorar esto
el valor de retorno se podria modelar se con una dataFamily,
Oleg et al en la version moderna de HList igual no lo hacen para no perder
poder en la inferencia, habria que probar si para la aplicacion en AAG
es necesario esto, sino conviene ir por el otro lado.
TODO: reimplementar con el indexed type y ver si anda

HECHO:

> {-
> class Apply f a where
>   type ApplyR f a :: Type
>   apply :: f -> a -> ApplyR f a


una posible instancia trivial:

> instance Apply (x -> y) x where
>   type ApplyR (x -> y) x = y
>   apply f x = f x
> -}

Aca hay algo interesante para ver cuando tenga tiempo.

Considerar:

< class Apply f a r | f a -> r where
<   apply :: f -> a r

Y luego las instancias

< instance Apply (x -> y) x y

< instance (x ~ x', y ~ y') =>  Apply (x' -> y') x y

Ver como funciona la inferencia aca

por ejemplo en la expresion <<apply id True>>
(Seguramente en el primero hay que anotar tipos y en el segundo no)


\end{document}


