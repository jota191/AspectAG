

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

> data HList (l :: [Type]) :: Type  where
>   HNil :: HList '[]
>   HCons :: x -> HList xs -> HList (x ': xs)


