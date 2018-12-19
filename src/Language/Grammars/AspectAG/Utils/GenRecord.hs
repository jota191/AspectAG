
{-# LANGUAGE DataKinds,
             TypeOperators,
             PolyKinds,
             GADTs,
             TypeInType,
             RankNTypes,
             StandaloneDeriving,
             FlexibleInstances,
             FlexibleContexts,
             ConstraintKinds,
             MultiParamTypeClasses,
             FunctionalDependencies,
             UndecidableInstances,
             ScopedTypeVariables,
             TypeFamilies,
             InstanceSigs,
             AllowAmbiguousTypes
#-}

module Language.Grammars.AspectAG.Utils.GenRecord where

import Data.Kind 
import Data.Type.Equality
import Data.Proxy
import Language.Grammars.AspectAG.Utils.TPrelude
import Data.Tagged hiding (unTagged)
import Language.Grammars.AspectAG.Utils.TagUtils
import GHC.TypeLits


----- only for testing

import Language.Grammars.AspectAG.Utils.Attribute

-----

-- * Definition 

-- | REC is a generic definition parametrized by the datatype used to build
-- fields. 
data REC :: forall k k'. (k -> k' -> Type) -> [(k,k')] -> Type where
  EmptyR :: REC field '[]
  ConsR  :: LabelSet ( '(l,v) ': r) =>
            field l v -> REC field r -> REC field ( '(l,v) ': r)


-- * Pretty constructors

infixr 2 .*.
(.*.) :: LabelSet ( '(l, v) ': r) =>
    field l v -> REC field r -> REC field ( '(l,v) ': r)
(.*.) = ConsR

-- * destructors

-- | A getter, also a predicate

class HasField (l :: k) (r :: [(k,k')]) field where
  type LookupByLabel field l r :: Type
  (##) :: Label l -> REC field r -> LookupByLabel field l v
