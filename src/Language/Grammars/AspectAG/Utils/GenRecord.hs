
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
             InstanceSigs
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

data REC :: forall k k'. (k -> k' -> Type) -> [(k,k')] -> Type where
  EmptyR :: REC field '[]
  ConsR  :: LabelSet ( '(l,t) ': rs) =>
            field l t -> REC field rs -> REC field ( '(l,t) ': rs)


-- type Attribution = REC Attribute 
