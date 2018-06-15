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
> import TagUtils

In each node of the grammar, the \emph{Fam} contains a single attribution
fot the parent, and a collection (Record) of attributions for the children:

> data Fam (c::[(k,[(k,Type)])]) (p :: [(k,Type)]) :: Type where
>   Fam :: ChAttsRec c  -> Attribution p -> Fam c p

Rules, aka definition of attribution computations
Rules are defined as a mapping from an input family to an output family,
the added arity is for make them composable


> type Rule sc ip ic sp ic' sp'
>   = Fam sc ip -> (Fam ic sp -> Fam ic' sp')


> ext :: Rule sc ip ic' sp' ic'' sp''
>     -> Rule sc ip ic  sp  ic'  sp'
>     -> Rule sc ip ic  sp  ic'' sp''

> (f `ext` g) input = f input . g input


The function 'syndef' adds the definition of a synthesized attribute.
It takes a label 'att' representing the name of the new attribute, 
a value 'val' to be assigned to this attribute, and it builds a function which 
updates the output constructed thus far.


----------------------------------------------------------------------------

> syndef  :: LabelSet ( '(att,val) ': sp) =>
>     Label att -> val -> (Fam ic sp -> Fam ic ( '(att,val) ': sp))
> syndef latt val (Fam ic sp) = Fam ic (latt .=. val .*. sp)


> synmod  ::  UpdateAtLabelAtt att val sp sp'
>        =>  Label att -> val -> Fam ic sp -> Fam ic sp'
> synmod att v (Fam ic sp) = Fam ic (updateAtLabelAtt att v sp)

----------------------------------------------------------------------------


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
>   => SingleDef True True att (Tagged lch vch) ic ic' where
>   singledef _ _ att pch ic =
>     updateAtChild (Label :: Label lch) ( att .=. vch .*. och) ic
>     where lch = labelTChAtt pch
>           vch = unTaggedChAtt pch
>           och = hLookupByChild lch ic


> class Defs att (nts :: [Type]) (vals :: [(k,Type)])
>            (ic :: [(k,[(k,Type)])]) (ic' :: [(k,[(k,Type)])])
>           | att nts vals ic -> ic' where
>   defs :: Label att -> HList nts -> Record vals -> ChAttsRec ic
>        -> ChAttsRec ic'

> instance Defs att nts '[] ic ic where
>   defs _ _ _ ic = ic

> -- TODO: duplicated context
> instance ( Defs att nts vs ic ic'
>          , HasLabelChildAttsRes (lch,t) ic' ~ mch
>          , HasLabelChildAtts (lch,t) ic'
>          , HMemberRes t nts ~ mnts
>          , HMember t nts
>          , SingleDef mch mnts att (Tagged (lch,t) vch) ic' ic'')
>     => Defs att nts ( '((lch,t), vch) ': vs) ic ic'' where
>   defs att nts (ConsR pch vs) ic = singledef mch mnts att pch ic' 
>       where ic'  = defs att nts vs ic         -- :: ChAttsRec ic'
>             lch  = labelLVPair pch            -- :: Label (lch,t)
>             mch  = hasLabelChildAtts lch ic'  -- :: Proxy mch
>             mnts = hMember (sndLabel lch) nts -- :: Proxy mnts


----------------------------------------------------------------------------

> inhdef :: Defs att nts vals ic ic'
>   => Label att -> HList nts -> Record vals -> (Fam ic sp -> Fam ic' sp)
> inhdef att nts vals (Fam ic sp) = Fam (defs att nts vals ic) sp

----------------------------------------------------------------------------


Aspects: Aspects are record that have a rule for each production:
-- TODO: use specialized datatypes?

> type Aspect = Record


Let a Type for the fields:

> type Prd prd rule = Tagged prd rule

> labelPrd (Tagged v :: Tagged l v)= Label :: Label l 
> rulePrd (Tagged v)= v


Lets define the combination of aspects. When labels are only present once,
the new aspect has a copy of the field. In the other hand, when a lebel is
repeated, rules are combined with the function ext.

> -- here we are using a less kinded types than before
> class Com (r₁ :: [(k,Type)]) (r₂ :: [(k, Type)]) (r₃ :: [(k,Type)])
>   | r₁ r₂ -> r₃ where
>   (.+.) :: Aspect r₁ ->  Aspect r₂ ->  Aspect r₃

Since we'll need to decide what to do depending on context, we use the
usual technique:


> class ComSingle (b::Bool) (prd :: k) (rule :: Type) (r₁ :: [(k,Type)])
>                 (r₂ :: [(k,Type)]) | b prd rule r₁ -> r₂ where
>   comSingle :: Proxy b -> Prd prd rule -> Aspect r₁ -> Aspect r₂

The boolean parameter is the indicator of prd being a label in the record.

> instance (LabelSet ('(prd, rule) : r₁))
>    => ComSingle 'False prd rule r₁ ( '(prd,rule) ': r₁) where
>   comSingle _ prd asp = prd `ConsR` asp

> 
> instance (UpdateAtLabelRec prd (Rule sc ip ic' sp' ic'' sp'') r₁ r₂
>          , HasFieldRec prd r₁ (Rule sc ip ic'' sp'' ic'' sp''))
>   => ComSingle 'True prd (Rule sc ip ic' sp' ic'' sp'') r₁ r₂ where
>   comSingle _ f r = updateAtLabelRec l (oldR `ext` newR) r
>     where l    = labelPrd f
>           oldR = hLookupByLabelRec l r
>           newR = rulePrd f
> 


Now we implement Com, by induction over the first Aspect.

> instance Com '[] r₂ r₂ where
>   _ .+. r = r

> instance ( Com r₁ r₂ r'
>          , HasLabelRecRes prd r₂ ~ b
>          , HasLabelRec prd r₂
>          , ComSingle b prd rule r' r₃)
>   => Com ( '(prd, rule) ': r₁) r₂ r₃ where
>      (pr `ConsR` r₁) .+. r₂ = let r'  = r₁ .+. r₂
>                                   b   = hasLabelRec (labelPrd pr) r₂
>                                   r₃   = comSingle b pr r'
>                               in  r₃

----------------------------------------------------------------------------

[(k1, [(k1, *)])] -> [(k2, [(k2, *)])]

> class Empties (fc :: [(k,Type)])
>               (ec :: [(k, [(k, Type)])]) | fc -> ec where
>   empties :: Record fc -> ChAttsRec ec

> instance Empties '[] '[] where
>   empties (EmptyR) = EmptyCh

> instance ( Empties fcr ecr
>          , LabelSet ( '(lch, '[]) ': ecr)) --TODO ver como remover esto
>   => Empties ( '(lch,fch)': fcr ) ( '(lch, '[])': ecr) where
>   empties (ConsR pch fcr)
>     = let lch = labelTChAtt pch -- TODO: name
>       in  ConsCh (TaggedChAttr lch EmptyAtt) (empties fcr)

----------------------------------------------------------------------------


> data Val

> class Kn (fc :: [(k, Type)])
>          (ic :: [(k, [(k, Type)])])
>          (sc :: [(k, [(k, Type)])]) | fc -> sc ic where
>   kn :: Record fc -> ChAttsRec ic -> ChAttsRec sc

> instance Kn '[] '[] '[] where
>   kn _ _ = EmptyCh

 
> instance ( Kn fc ic sc
>          , LabelSet ('(lch, fc2scl) ': sc)
>          , fc2icl ~ Fc2ic l
>          , fc2scl ~ Fc2sc l
>          , l ~ (Attribution fc2icl -> Attribution fc2scl))
>   =>  Kn ( '(lch , l {-Attribution ich -> Attribution sch)-}) ': fc)
>          ( '(lch , fc2icl) ': ic)
>          ( '(lch , fc2scl) ': sc) where
>   kn (ConsR pfch fcr) (ConsCh pich icr)
>    = let scr = kn fcr icr
>          lch = labelTChAtt pfch    :: Label lch-- TODO: name
>          fch = unTagged pfch       :: l
>          ich = unTaggedChAttr pich -- :: Attribution ich
>      in ConsCh (TaggedChAttr lch (fch ich)) scr


> type family Fc2ic a ::  [(k,Type)]
> type instance Fc2ic (Attribution '[] -> Attribution '[ '(v, Int)]) = '[]
> type instance Fc2ic (Attribution ich -> Attribution sch) = ich

> type family Fc2sc a ::  [(k,Type)]
> type instance Fc2sc (Attribution '[] -> Attribution '[ '(v, Int)])
>   = '[ '(v,Int)]
> type instance Fc2sc (Attribution ich -> Attribution sch) = sch


-- > instance ( Kn fc ic sc
-- >          , LabelSet ('(lch, sch) ': sc))
-- >   =>  Kn ( '(lch , Attribution '[] -> Attribution '[ '(Val, a)]) ': fc)
-- >          ( '(lch , '[ '(Val, a)] ) ': ic)
-- >          ( '(lch , '[] ) ': sc) where
-- >   kn (ConsR pfch fcr) (ConsCh pich icr)
-- >    = undefined
-- > --     let scr = kn fcr icr
-- > --         lch = labelTChAtt pfch -- TODO: name
-- > --         fch = unTagged pfch
-- > --         ich = unTaggedChAttr pich
-- > --     in ConsCh (TaggedChAttr lch (fch ich)) scr

----------------------------------------------------------------------------

Now we code the actual knit function:

> knit :: ( Empties fc ec
>         , Kn fc ic sc )
>   => Rule sc ip ec '[] ic sp
>      -> Record fc -> Attribution ip -> Attribution sp
> knit rule fc ip
>   = let ec          = empties fc
>         (Fam ic sp) = rule (Fam sc ip) (Fam ec EmptyAtt)
>         sc          = kn fc ic
>     in  sp

