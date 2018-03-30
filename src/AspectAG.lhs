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
>              AllowAmbiguousTypes,
>              UnicodeSyntax#-}


> module AspectAG where

> import HList
> import Attribution
> import Record
> import Attribute
> import Data.Kind
> import Data.Tagged
> import TPrelude

In each node of the grammar, the \emph{Fam} contains a single attribution
fot the parent, and a collection (Record) of attributions for the children:

> data Fam (c::[(k,Type)])(p :: [(k,Type)]) :: Type where
>   Fam :: Record c -> Attribution p -> Fam c p

Note that we could actually improve the kinding here, It is not clear if
we'll have benefits of type safety and it is certainly non-straightforward
to do it, so for now this will be the implementation.


> type Chi ch atts = Tagged ch atts

-- TODO ? : I could use Chi in records instead of this..

Rules, aka definition of attribution computations
Rules are defined as a mapping from an input family to an output family,
the added arity is for make them composable


> type Rule sc ip ic sp ic' sp'
>   = Fam sc ip -> (Fam ic sp -> Fam ic' sp')


> ext :: Rule sc ip ic' sp' ic'' sp''
>     -> Rule sc ip ic sp ic' sp'
>     -> Rule sc ip ic sp ic'' sp''

> (f `ext` g) input = f input . g input


The function 'syndef' adds the definition of a synthesized attribute.
It takes a label 'att' representing the name of the new attribute, 
a value 'val' to be assigned to this attribute, and it builds a function which 
updates the output constructed thus far.


> syndef  :: LabelSet ( '(att,val) ': sp) =>
>     Label att -> val -> (Fam ic sp -> Fam ic ( '(att,val) ': sp))
> syndef latt val (Fam ic sp) = Fam ic (latt .=. val .*. sp)


> synmod  ::  UpdateAtLabelAtt att val sp sp'
>        =>  Label att -> val -> Fam ic sp -> Fam ic sp'
> synmod att v (Fam ic sp) = Fam ic (updateAtLabelAtt att v sp)

