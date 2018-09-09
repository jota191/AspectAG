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

> module Attribution where

> import Data.Kind 
> import Data.Type.Equality
> import Data.Proxy
> import Errors
> import Eq
> import Attribute
> import TPrelude
> import TagUtils

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


REFERENCE TO EQ MODULE

LABELSET MOVED TO TPRELUDE

We are ready to define Attributions.

> data Attribution :: forall k . [(k,Type)] -> Type where
>   EmptyAtt :: Attribution '[]
>   ConsAtt  :: LabelSet ( '(att, val) ': atts) =>
>    Attribute att val -> Attribution atts -> Attribution ( '(att,val) ': atts)
                                                  


%if False
Some boilerplate to show Attributes and Attributions

> instance Show (Attribution '[]) where
>   show _ = "«»"

> instance (Show val, Show (Attribution atts)) =>
>          Show (Attribution  ( '(att,val) ': atts ) ) where
>   show (ConsAtt att atts) = let tail = show atts
>                             in "«" ++ show (getVal att) ++ "," ++ drop 1 tail 

%endif

--- HasField

> class HasFieldAtt (l::k) (r :: [(k,Type)]) v | l r -> v where
>    lookupByLabelAtt:: Label l -> Attribution r -> v

> instance (HEqK l l1 b, HasFieldAtt' b l ( '(l1,v1) ': r) v)
>     => HasFieldAtt l ( '(l1,v1) ': r) v where
>     lookupByLabelAtt l (r :: Attribution ( '(l1,v1) ': r)) =
>          lookupByLabelAtt' (Proxy::Proxy b) l r

> 
> class HasFieldAtt' (b::Bool) (l :: k) (r::[(k,Type)]) v | b l r -> v where
>     lookupByLabelAtt':: Proxy b -> Label l -> Attribution r -> v

> instance HasFieldAtt' True l ( '(l,v) ': r) v where
>    lookupByLabelAtt' _ _ (ConsAtt (Attribute v) _) = v
> instance HasFieldAtt l r v => HasFieldAtt' False l ( '(l2,v2) ': r) v where
>    lookupByLabelAtt' _ l (ConsAtt _ r) = lookupByLabelAtt l r
 

UpdateAtLabel

I attempt to code an indexed type implementation, where the resulting Type
function of the parameters.
I could code the type function over the type level,
the problem is when I do this on a type class to code ter level computations.
Since we decide from the context (HEqK ) the returned boolean must be a
parameter of UpdateAtLabelR, but since it's purely on the context,
it is free on the RHS...

The fundep implementation is needed..

> class UpdateAtLabelAtt (l :: k)(v :: Type)(r :: [(k,Type)])(r' :: [(k,Type)])
>    | l v r -> r' where
>   updateAtLabelAtt :: Label l -> v -> Attribution r -> Attribution r'

So we need an auxiliary class with an extra parameter to decide if we update
on the head of r or not

> class UpdateAtLabelAtt' (b::Bool)(l::k)(v::Type)(r::[(k,Type)])(r'::[(k,Type)])
>     | b l v r -> r'  where
>   updateAtLabelAtt' :: Proxy b -> Label l -> v -> Attribution r -> Attribution r'



> instance (HEqK l l' b, UpdateAtLabelAtt' b l v ( '(l',v')': r) r')
>  -- note that if pattern over r is not written this does not compile
>        => UpdateAtLabelAtt l v ( '(l',v') ': r) r' where
>   updateAtLabelAtt = updateAtLabelAtt' (Proxy :: Proxy b)


> instance (LabelSet ( '(l,v') ': r), LabelSet ( '(l,v) ': r) ) =>
>          UpdateAtLabelAtt' 'True l v ( '(l,v') ': r) ( '(l,v) ': r) where
>   updateAtLabelAtt' _ (l :: Label l) v (att `ConsAtt` atts)
>     = (Attribute v :: Attribute l v) `ConsAtt` atts

> 
> instance ( UpdateAtLabelAtt l v r r', LabelSet  ( a ': r' ) ) =>
>          UpdateAtLabelAtt' False l v ( a ': r) ( a ': r') where
>   updateAtLabelAtt' (b :: Proxy False) (l :: Label l) (v :: v)
>     (ConsAtt att xs :: Attribution ( a ': r))
>     = case (updateAtLabelAtt l v xs) of
>         xs' -> ConsAtt att xs' :: Attribution( a ': r')

> instance Fail (FieldNotFound l) => UpdateAtLabelAtt l v '[] '[] where
>     updateAtLabelAtt _ _ r = r

Sugar:

> infixr 2 .*.
> (.*.) :: LabelSet ('(att, val) : atts) =>
>     Attribute att val -> Attribution atts -> Attribution ('(att, val) : atts)
> (.*.) = ConsAtt
