

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
> import GHC.TypeLits
> import Data.Proxy

> type family If (cond:: Bool) (thn :: k) (els :: k) :: k where
>   If 'True  thn els = thn
>   If 'False thn els = els

> type family Or (l :: Bool)(r :: Bool) :: Bool where
>   Or False b = b
>   Or True b  = 'True

> type family And (l :: Bool)(r :: Bool) :: Bool where
>   And False b = False
>   And True b  = b


> type family Not (l :: Bool) :: Bool where
>   Not False = True
>   Not True  = False

-- > type family IsLabelSet (r :: [(k,k')]) :: Bool
-- > type instance IsLabelSet '[]             = True
-- > --type instance IsLabelSet '[ '(l,v)]      = True
-- > type instance IsLabelSet ( '(l,v) ': r)
-- >   = And (Not (OccursLabel l r)) (IsLabelSet r)

-- > type family OccursLabel (l :: k) (r :: [(k,k')]) :: Bool
-- > type instance OccursLabel l '[] = False
-- > type instance OccursLabel l ( '(l2,v) ': r ) = Or (l == l2)(OccursLabel l r)


-- > --FIXME: this is not polykinded
-- > type family (===) l v :: Bool 
-- > -- type instance x === y = x == y
-- > type instance x === y = Proxy x == Proxy y

> class LabelSet (l :: [(k,k2)])
> --instance (IsLabelSet xs ~ True) => LabelSet xs

> instance LabelSet '[] -- empty set
> instance LabelSet '[ '(x,v)] -- singleton set

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
> 

Reference:
https://hackage.haskell.org/package/base-4.11.1.0/docs/GHC-TypeLits.html

TODO: explain how the selection of the instance is done
TODO: 


> type family HMemberT (e::k)(l ::[k]) :: Bool where
>   HMemberT k '[] = 'False
>   HMemberT k ( k' ': l) = If (k==k') 'True (HMemberT k l)

> type family HasLabelT (l::k) (lst :: [(k,Type)]) :: Bool where
>   HasLabelT l '[] = 'False
>   HasLabelT l ( '(k,v) ': tail) = If (l == k) 'True (HasLabelT l tail)
> 

