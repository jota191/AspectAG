

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

> module HList where
> import Eq
> import TPrelude
> import Data.Type.Equality
> import Data.Kind

> import Data.Proxy
> import Attribute

> data HList (l :: [Type]) :: Type  where
>   HNil :: HList '[]
>   HCons :: x -> HList xs -> HList (x ': xs)

> class HMember (t :: Type) (l :: [Type]) where
>   type HMemberRes t l :: Bool
>   hMember :: Label t -> HList l -> Proxy (HMemberRes t l)

> instance HMember t '[] where
>   type HMemberRes t '[] = 'False
>   hMember _ _ = Proxy


> instance HMember t (t' ': ts) where
>   type HMemberRes t (t' ': ts) = Or (t == t') (HMemberRes t ts)
>   hMember _ _ = Proxy


Tests

> l1 = HCons "hola" $ HCons True HNil 
> t1 = hMember (Label :: Label Bool) l1
> t2 = hMember (Label :: Label Char) l1
> t3 = hMember (Label :: Label [Char]) l1
