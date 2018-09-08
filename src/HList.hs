{-|
Module      : HList
Description : Heterogeneous Lists for AAG, inspired on HList
Copyright   : (c) Juan García Garland, 2018 
License     : LGPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX

Implementation of strongly typed heterogeneous lists.
-}

{-# LANGUAGE TypeInType,
             GADTs,
             KindSignatures,
             TypeOperators,
             TypeFamilies,
             MultiParamTypeClasses,
             FlexibleInstances,
             FlexibleContexts,
             StandaloneDeriving,
             UndecidableInstances,
             FunctionalDependencies,
             ConstraintKinds,
             ScopedTypeVariables#-}

module HList where
import Eq
import TPrelude
import Data.Type.Equality
import Data.Kind
import TagUtils
import Data.Proxy


-- |Heterogeneous lists are implemented as a GADT
data HList (l :: [Type]) :: Type  where
  HNil :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)


-- | HMember is a test membership function.
--Since we are in Haskell the value level function computes with the evidence 
class HMember (t :: Type) (l :: [Type]) where
  type HMemberRes t l :: Bool
  hMember :: Label t -> HList l -> Proxy (HMemberRes t l)

instance HMember t '[] where
  type HMemberRes t '[] = 'False
  hMember _ _ = Proxy

instance HMember t (t' ': ts) where
  type HMemberRes t (t' ': ts) = Or (t == t') (HMemberRes t ts)
  hMember _ _ = Proxy


-- | No other functionality is needed for AAG
