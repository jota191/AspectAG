%if False

> {-# LANGUAGE DataKinds,
>              TypeOperators,
>              PolyKinds,
>              GADTs,
>              TypeInType,
>              RankNTypes,
>              StandaloneDeriving,
>              FlexibleInstances,
>              FlexibleContexts,
>              ConstraintKinds,
>              MultiParamTypeClasses,
>              FunctionalDependencies,
>              UndecidableInstances,
>              ScopedTypeVariables,
>              TypeFamilies
> #-}

> import Data.Kind 
> import Data.Type.Equality (type (==))
> import Data.Proxy

%endif

An attribution will be a map from attribute names to attribute values,
where names are labels purely phantom.
So we must code strongly type heterogeneous records.

TODO:

\begin{itemize}
  \item  explain why Attribution and not Record
  \item  explain why a fresh implementation instead of doing it over lists
\end{itemize}

Since attributions must be a map, we must ensure that
instances doesn't repeat labels. This kind of predicate can be encoded
by typeclasses, and encoded doing a sort of logic programming.
While we prefer a Functional style in this implementation, using more recent
extensions to ghc like typefamilies and dataKinds, instead of the old fashioned
logic style of type level programming, for tasks like this, where we implement
predicates, it makes more sense to do it this way.

LabelSet is a monoparameter typeclass, working as a predicate
over a promoted list of pairs, where first elements are the labels. {\tt l} is
an instance of {\tt LabelSet} when no labels are repeated.

First we define equality on types:



> class HEq (x :: k) (y :: k) (b :: Bool) | x y -> b
> type HEqK (x :: k1) (y :: k2) (b :: Bool) = HEq (Proxy x) (Proxy y) b
> instance ((Proxy x == Proxy y) ~ b) => HEq x y b

TODO: explain better this

%if False

> class LabelSet (l :: [(k,Type)])
> instance LabelSet '[] -- empty set
> instance LabelSet '[ '(x,v)] -- singleton set

> instance ( HEqK l1 l2 leq
>          , LabelSet' '(l1,v1) '(l2,v2) leq r)
>         => LabelSet ( '(l1,v1) ': '(l2,v2) ': r)

> class LabelSet' l1v1 l2v2 (leq::Bool) r
> instance ( LabelSet ( '(l2,v2) ': r)
>          , LabelSet ( '(l1,v1) ': r)
>          ) => LabelSet' '(l1,v1) '(l2,v2) False r

> instance ( Fail (DuplicatedLabel l1) ) => LabelSet' l1 l2 True r

> class Fail l
> class DuplicatedLabel l

%endif

TODO: explain how the selection of the instance is done

We are ready to define Attributions.

> data Attribution :: forall k . [(k,Type)] -> Type where
>   EmptyAtt :: Attribution '[]
>   ConsAtt  :: LabelSet ( '(att, val) ': atts) =>
>    Attribute att val -> Attribution atts -> Attribution ( '(att,val) ': atts)
                                                  
> newtype Attribute label value = Attribute { getVal :: value }
>                               deriving (Eq, Ord,Show)


%if False
Some boilerplate to show Attributes and Attributions

> instance Show (Attribution '[]) where
>   show _ = "«»"

> instance (Show val, Show (Attribution atts)) =>
>          Show (Attribution  ( '(att,val) ': atts ) ) where
>   show (ConsAtt att atts) = let tail = show atts
>                             in "«" ++ show (getVal att) ++ "," ++ drop 1 tail 

%endif


%if False

Some tests:
TODO: move this..

> data Label1; data Label2; data Label3
> att1 = Attribute 3   :: Attribute Label1 Int 
> att2 = Attribute '4' :: Attribute Label2 Char
> att3 = Attribute '4' :: Attribute Label3 Char

> test1 = ConsAtt att2 EmptyAtt
> -- test2 = ConsAtt att2 test1 does not compile because of label duplication
> test2 = ConsAtt att1 test1
> test3 = ConsAtt att3 test2


test2 = (Proxy :: Proxy 'True ,True) .*. (Proxy :: Proxy 'False,'r') .*. EmptyR
  :: HRecord '[ '( 'True ,Bool), '( 'False ,Char)]


%endif


--- HasField

> data Label l = Label

> class HasField (l::k) (r :: [(k,Type)]) v | l r -> v where
>    hLookupByLabel:: Label l -> Attribution r -> v

> instance (HEqK l l1 b, HasField' b l ( '(l1,v1) ': r) v)
>     => HasField l ( '(l1,v1) ': r) v where
>     hLookupByLabel l (r :: Attribution ( '(l1,v1) ': r)) =
>          hLookupByLabel' (Proxy::Proxy b) l r

> 
> class HasField' (b::Bool) (l :: k) (r::[(k,Type)]) v | b l r -> v where
>     hLookupByLabel':: Proxy b -> Label l -> Attribution r -> v

> instance HasField' True l ( '(l,v) ': r) v where
>    hLookupByLabel' _ _ (ConsAtt (Attribute v) _) = v
> instance HasField l r v => HasField' False l ( '(l2,v2) ': r) v where
>    hLookupByLabel' _ l (ConsAtt _ r) = hLookupByLabel l r
 

UpdateAtLabel


> class UpdateAtLabel (l :: k) (v :: Type) (r :: [(k,Type)]) where
>   type UpdateAtLabelR l v r :: [(k,Type)]
>   updateAtLabel :: Label l -> v -> Attribution r
>                 -> Attribution (UpdateAtLabelR l v r)

> instance (HEqK l l' True) => UpdateAtLabel l v '[ '(l',v' )] where
>   type UpdateAtLabelR l v '[ '(l',v' )] = '[ '(l,v)]
>   updateAtLabel Label v (ConsAtt _ EmptyAtt) = ConsAtt (Attribute v) EmptyAtt

> {-

Since we have to decide 

> class UpdateAtLabel' (b::Bool) (l :: k) (v :: Type) (r :: [(k,Type)]) where
>   type UpdateAtLabelR' b l v r :: [(k,Type)]
>   updateAtLabel :: Proxy b -> Label l -> v -> Attribution r
>                 -> Attribution (UpdateAtLabelR l v r)

> -}
