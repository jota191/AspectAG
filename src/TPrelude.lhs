

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

> module TPrelude where
> import Errors
> import Data.Kind
> import Eq
> import Data.Type.Equality

> type family If (cond:: Bool) (thn :: k) (els :: k) :: k where
>   If 'True  thn els = thn
>   If 'False thn els = els


> class LabelSet (l :: [(k,k2)])
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


TODO: explain how the selection of the instance is done



> type family HMember (e::k)(l ::[k]) :: Bool where
>   HMember k '[] = 'False
>   HMember k ( k' ': l) = If (k==k') 'True (HMember k l)

> type family HasLabel (l::k) (lst :: [(k,Type)]) :: Bool where
>   HasLabel l '[] = 'False
>   HasLabel l ( '(k,v) ': tail) = If (l == k) 'True (HasLabel l tail)

