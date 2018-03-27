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
>              UndecidableInstances#-}

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

> class HLabelSet (l :: [(k,Type)])
> instance HLabelSet '[] -- empty set
> instance HLabelSet '[ '(x,v)] -- singleton set

> instance ( HEqK l1 l2 leq
>          , HLabelSet' '(l1,v1) '(l2,v2) leq r)
>         => HLabelSet ( '(l1,v1) ': '(l2,v2) ': r)

> class HLabelSet' l1v1 l2v2 (leq::Bool) r
> instance ( HLabelSet ( '(l2,v2) ': r)
>          , HLabelSet ( '(l1,v1) ': r)
>          ) => HLabelSet' '(l1,v1) '(l2,v2) False r

> instance ( Fail (DuplicatedLabel l1) ) => HLabelSet' l1 l2 True r

> class Fail l
> class DuplicatedLabel l

%endif

TODO: explain how the selection of the instance is done

We are ready to define Attributions.

> data Attribution :: forall k . [(k,Type)] -> Type where
>   EmptyAtt :: Attribution '[]
>   ConsAtt  :: HLabelSet ( '(att, val) ': atts) =>
>    Attribute att val -> Attribution atts -> Attribution ( '(att,val) ': atts)
                                                  
> newtype Attribute label value = Attribute { getVal :: value }
>                               deriving (Eq, Ord)



%if False

Some tests:

> data Label1; data Label2; data Label3
> --field1


> test1 = ConsAtt (Attribute 'e' :: Attribute Label1 Char) EmptyAtt

test2 = (Proxy :: Proxy 'True ,True) .*. (Proxy :: Proxy 'False,'r') .*. EmptyR
  :: HRecord '[ '( 'True ,Bool), '( 'False ,Char)]


%endif












