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
             TypeApplications,
             PatternSynonyms,
             TypeFamilyDependencies
#-}

--              AllowAmbiguousTypes,


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
(.*.) :: (Extend c l v r, a ~ WrapField c v)
 => TagField c l v -> Rec c r -> Rec c (ExtendR c l v r)
((TagField (labelc :: Label c) (labell :: Label l) (v :: a)) :: TagField c l v ) .*. (r :: Rec c r)
  = extend labell (Proxy @v) v r


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

type family    WrapField (c :: k')  (v :: k) = ftype -- | ftype -> c

{-
  Node: We cannot encode the dependency {ftype, c} -> v since
  TypeFamilyDependencies does not support this general
  dependencies. So from (WrapField c v) we can't infer c.
-}

type family UnWrap t :: k -- (t :: [(k,k')]) :: k'
type instance UnWrap (Rec c (r :: [(k, k')])) = r


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
  => Lookup' 'GT c l ( '(l', v) : r) where
  type LookupR' 'GT c l ( '(l', v) : r) = LookupR c l r
  lookup' cmp l (ConsRec _ r) = lookup l r

instance
  Lookup' 'EQ c l ( '(l, v) : r) where
  type LookupR' 'EQ c l ( '(l, v) : r) = WrapField c v
  lookup' cmp l (ConsRec lv r) = untagField lv


----------------------------UPDATE---------------------------------------------
class Update (c :: Type) (l :: k) (v :: k') (r :: [(k, k')]) where
  type UpdateR c l v r :: [(k, k')]
  update :: Label l -> Proxy v -> WrapField c v -> Rec c r
         -> Rec c (UpdateR c l v r)

class Update' (cmp :: Ordering)
              (c :: Type) (l :: k) (v :: k') (r :: [(k, k')]) where
  type UpdateR' cmp c l v r :: [(k, k')]
  update' :: Proxy cmp -> Label l -> Proxy v -> WrapField c v -> Rec c r
          -> Rec c (UpdateR' cmp c l v r)

instance Update' (CMP l l') c l v ( '(l' , v') ': r) =>
  Update c l v ( '(l' , v') ': r) where
  type UpdateR  c l v ( '(l' , v') ': r)
    = UpdateR' (CMP l l') c l v ( '(l' , v') ': r)
  update l _ (f :: WrapField c v) r
    = update' (Proxy @(CMP l l')) l (Proxy @v) f r

instance Update c l v r =>
  Update' 'GT c l v ( '(l' , v') ': r) where
  type UpdateR' 'GT c l v ( '(l' , v') ': r)
    = '(l' , v') ': UpdateR c l v r
  update' Proxy l Proxy f (ConsRec x xs)
    = ConsRec x $ (update l (Proxy @v) f xs)


instance
  Update' 'EQ c l v ( '(l , v') ': r) where
  type UpdateR' 'EQ c l v ( '(l , v') ': r)
    = '(l, v) ': r
  update' _ l _ f (ConsRec x xs)
    = ConsRec (TagField Label l f) xs

----------------------------EXTEND---------------------------------------------
class Extend (c :: Type) (l :: k) (v :: k') (r :: [(k, k')]) where
  type ExtendR c l v r :: [(k, k')]
  extend :: Label l -> Proxy v -> WrapField c v -> Rec c r
         -> Rec c (ExtendR c l v r)

class Extend' (cmp :: Ordering )(c :: Type) (l :: k) (v :: k') (r :: [(k, k')])
 where
  type ExtendR' cmp c l v r :: [(k, k')]
  extend' :: Proxy cmp -> Label l -> Proxy v -> WrapField c v -> Rec c r
          -> Rec c (ExtendR c l v r)

instance
  Extend c l v '[] where
  type ExtendR c l v '[]
    =  '(l, v) ': '[]
  extend l _ f EmptyRec
    = ConsRec (TagField Label l f) EmptyRec



instance Extend' (CMP l l') c l v ( '(l', v') : r) =>
  Extend c l v ( '(l', v') ': r) where
  type ExtendR c l v ( '(l', v') ': r)
    =  ExtendR' (CMP l l') c l v ( '(l', v') ': r)
  extend l _ (f :: WrapField c v) r
    = extend' (Proxy @(CMP l l')) l (Proxy @v) f r

instance ( Extend c l v r
         , Rec c (ExtendR c l v ('(l', v') : r))
           ~ Rec c ( '(l', v') : ExtendR c l v r)
         ) =>
  Extend' 'GT c l v ( '(l', v') ': r) where
  type ExtendR' 'GT c l v ( '(l', v') ': r)
    = '(l', v') ': ExtendR c l v r
  extend' cmp l _ f (ConsRec x xs)
    = ConsRec x (extend l (Proxy @v) f xs)

instance Rec c (ExtendR c l v ('(l', v') : r))
        ~ Rec c ('(l, v) : '(l', v') : r) =>
  Extend' 'LT c l v ( '(l', v') ': r) where
  type ExtendR' 'LT c l v ( '(l', v') ': r)
    = ( '(l, v) ': '(l', v') ': r)
  extend' cmp l _ f r
    = ConsRec (TagField Label l f) r
