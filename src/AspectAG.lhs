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
>              ScopedTypeVariables
> #-}


> module AspectAG where

> import HList
> import Attribution
> import Record
> import Attribute
> import Data.Kind
> import Data.Tagged
> import TPrelude
> import Data.Proxy
> import ChildAtts

In each node of the grammar, the \emph{Fam} contains a single attribution
fot the parent, and a collection (Record) of attributions for the children:

> data Fam (c::[(k,[(k,Type)])]) (p :: [(k,Type)]) :: Type where
>   Fam :: ChAttsRec c  -> Attribution p -> Fam c p

Note that we could actually improve the kinding here, It is not clear if
we'll have benefits of type safety and it is certainly non-straightforward
to do it, so for now this will be the implementation.

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


mch --> memnership of chld
mnts--> membership of nonterminals

> -- TODO this pv is a pair label-value, I should improve the typing
> --at type level, Attribute, Tagged and that kind of stuff can be improved
> class SingleDef (mch::Bool)(mnts::Bool) att pv (ic ::[(k,[(k,Type)])])
>                  (ic' ::[(k,[(k,Type)])]) | mch mnts att pv ic -> ic' where
>   singledef :: Proxy mch -> Proxy mnts -> Label att -> pv -> ChAttsRec ic
>                -> ChAttsRec ic'


> instance ( HasChild lch ic och
>          , UpdateAtChild lch ( '(att,vch) ': och) ic ic'
>          , LabelSet ( '(att, vch) ': och))
>   => SingleDef True True att (TaggedChAtt lch vch) ic ic' where
>   singledef _ _ att pch ic =
>     updateAtChild (Label :: Label lch) ( att .=. vch .*. och) ic
>     where lch = labelTChAtt pch
>           vch = unTaggedChAtt pch
>           och = hLookupByChild lch ic


> class Defs att (nts :: [Type]) (vals :: [(k,Type)])
>            (ic :: [(k,[(k,Type)])]) (ic' :: [(k,[(k,Type)])]) where
>   defs :: Label att -> HList nts -> Record vals -> ChAttsRec ic
>        -> ChAttsRec ic'

> instance Defs att nts '[] ic ic where
>   defs _ _ _ ic = ic

> 
> instance
>   ( Defs att nts vs ic ic'
>   , HasLabelChildAttsRes (lch,t) ic' ~ mch
>   , HMemberRes t nts ~ mnts
>   , SingleDef mch mnts att (Tagged (lch,t) vch) ic ic') =>
>   Defs att nts ( '((lch,t), vch) ': vs) ic ic' where
>   defs att nts (ConsR pch vs) ic =
>     singledef mch mnts att pch ic'
>     where ic'  = defs att nts vs ic
>           lch  = labelLVPair pch :: Label (lch,t)
>           mch  = hasLabelChildAtts lch ic'
>           mnts = hMember (sndLabel lch) nts

> labelLVPair :: Tagged (k1,k2) v -> Label (k1,k2)
> labelLVPair _ = Label

> sndLabel :: Label (a,b) -> Label b
> sndLabel _ = undefined
