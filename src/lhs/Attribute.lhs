
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

> module Attribute where

> import Data.Kind 
> import Data.Type.Equality
> import Data.Proxy
> import Errors
> import Eq
> import TagUtils

> newtype Attribute l value = Attribute { getVal :: value }
>                           deriving (Eq, Ord,Show)
>

> infixr 4 .=.

> (.=.) :: Label l -> v -> Attribute l v
> Label .=. v = Attribute v
