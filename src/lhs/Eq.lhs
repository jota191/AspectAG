

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

> module Eq where

> import Data.Kind 
> import Data.Type.Equality
> import Data.Proxy

First we define equality on types:


> class HEq (x :: k) (y :: k) (b :: Bool) | x y -> b
> type HEqK (x :: k1) (y :: k2) (b :: Bool) = HEq (Proxy x) (Proxy y) b
> instance ((Proxy x == Proxy y) ~ b) => HEq x y b

TODO: explain better this

