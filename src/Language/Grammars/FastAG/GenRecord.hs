{-|
Module      : Language.Grammars.AspectAG.GenRecord
Description : Record library, this will be eventually forked out
              from AAG codebase and used as a standalone library, depending on it
Copyright   : (c) Juan García Garland, Marcos Viera, 2019
License     : GPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX
-}

{-# OPTIONS_GHC -fno-warn-missing-methods #-}

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
             AllowAmbiguousTypes,
             TypeApplications,
             PatternSynonyms
#-}

module Language.Grammars.FastAG.GenRecord where

import Prelude hiding (lookup)
import Data.Kind
--import Data.Type.Equality hiding ((==))
import Data.Proxy
import Language.Grammars.FastAG.TPrelude

import GHC.TypeLits


type family a == b where
  a == b = Equal a b

-- * Pretty constructors

infixr 2 .*.
(.*.) :: LabelSet ( '(l, v) ': r) =>
    TagField c l v -> Rec c r -> Rec c ( '(l,v) ': r)
(.*.) = ConsRec

-- * destructors

-- | A getter, also a predicate
-- class HasField (l :: k) (r :: [(k, k')]) field where
--   type LookupByLabel field l r :: Type
--   (#) :: REC field r -> Label l -> LookupByLabel field l v


tailRec :: Rec c ( '(l,v) ': r) -> Rec c r
tailRec (ConsRec _ t) = t

data Rec (c :: k) (r :: [(k', k'')]) :: Type where
  EmptyRec :: Rec c '[]
  ConsRec  :: -- LabelSet ( '(l,v) ': r) =>
              TagField c l v -> Rec c r -> Rec c ( '(l,v) ': r)

data TagField (cat :: k) (l :: k') (v :: k'') where
  TagField :: Label c -> Label l -> WrapField c v -> TagField c l v

untagField :: TagField c l v -> WrapField c v
untagField (TagField lc lv v) = v

type family    WrapField (c :: k')  (v :: k) -- = ftype | ftype c -> v


----------------------------LOOKUP---------------------------------------------
class Lookup (c :: Type) (l :: k) (r :: [(k,k')]) where
  type LookupR c l r :: Type
  lookup :: Label l -> Rec c r -> LookupR c l r

class Lookup' (cmp :: Ordering) (c :: Type) (l :: k) (r :: [(k,k')]) where
  type LookupR' cmp c l r :: Type
  lookup' :: Label cmp -> Label l -> Rec c r -> LookupR' cmp c l r

instance
  Lookup' (CMP l l') c l ( '(l', v) : r)
  => Lookup c l ( '(l', v) ': r) where
  type LookupR c l ( '(l', v) ': r) = LookupR' (CMP l l') c l ( '(l', v) ': r)
  lookup = lookup' (Label @ (CMP l l'))

instance
  Lookup c l r
  => Lookup' 'LT c l ( '(l', v) : r) where
  type LookupR' 'LT c l ( '(l', v) : r) = LookupR c l (r)
  lookup' cmp l (ConsRec _ r) = lookup l r

instance
  Lookup' 'EQ c l ( '(l, v) : r) where
  type LookupR' 'EQ c l ( '(l, v) : r) = WrapField c v
  lookup' cmp l (ConsRec lv r) = untagField lv


----------------------------UPDATE---------------------------------------------
class Update (c :: Type) (l :: k) (v :: k') (r :: [(k, k')]) where
  type UpdateR c l v r :: Type
  update :: Label l -> WrapField c v -> Rec c r -> UpdateR c l v r

class Update' (cmp :: Ordering)
              (c :: Type) (l :: k) (v :: k') (r :: [(k, k')]) where
  type UpdateR' cmp c l v r :: Type
  update' :: Label cmp -> Label l -> WrapField c v -> Rec c r
          -> UpdateR' c l v r



{-
  Node: We cannot encode the dependency {ftype, c} -> v since
  TypeFamilyDependencies does not support this general
  dependencies. So from (WrapField c v) we can't infer c.
-}


-- Extend
-- Update
-- Lookup
