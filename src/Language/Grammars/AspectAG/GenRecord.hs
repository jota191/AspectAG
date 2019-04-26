
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
             TypeApplications
#-}

module Language.Grammars.AspectAG.GenRecord where

import Data.Kind 
import Data.Type.Equality
import Data.Proxy
import Language.Grammars.AspectAG.TPrelude
import Data.Tagged hiding (unTagged)
import Language.Grammars.AspectAG.TagUtils
import GHC.TypeLits

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
class HasField (l :: k) (r :: [(k, k')]) field where
  type LookupByLabel field l r :: Type
  (#) :: REC field r -> Label l -> LookupByLabel field l v


tailRec :: REC field ( '(l,v) ': r) -> REC field r
tailRec (ConsR _ t) = t

data Rec :: forall k k'. (k -> k' -> Type) -> [(k,k')] -> Type where
  EmptyRec :: Rec field '[]
  ConsRec  :: LabelSet ( '(l,v) ': r) =>
              field l v -> Rec field r -> Rec field ( '(l,v) ': r)


data OpLookup (f  :: k -> k' -> Type)
              (l  :: k)
              (r  :: [(k, k')]) :: Type
 where
   OpLookup :: Label l -> Proxy f -> Rec f r -> OpLookup f l r


data OpLookup'  (b  :: Bool)
                (f  :: k -> k' -> Type)
                (l  :: k)
                (r  :: [(k, k')]) :: Type
 where
   OpLookup' :: Proxy b -> Label l -> Proxy f -> Rec f r -> OpLookup' b f l r


--type family Demote (op :: Type) :: Constraint
--type instance Demote (Lookup l f r) = HasField l r f

class Require (op   :: Type) --todo: ?
              (ctx  :: [Symbol])  where
   type ReqR op
   req :: Proxy ctx -> ReqR op

type family Lookup (f :: k -> k' -> Type) (l :: k) (r :: [(k, k')]) :: Type


-------------------------------------------------------------------------------
instance ( Require' (l1 == l2) (OpLookup f l1 ( '(l2 , v) ': r)) ctx
         , ReqR' (l1 == l2) (OpLookup f l1 ( '(l2 , v) ': r))
         ~ (Label l1 -> Rec f r -> Lookup f l1 ('(l2, v) : r)))
  => Require (OpLookup f l1 ( '(l2 , v) ': r)) ctx where
  type ReqR (OpLookup f l1 ( '(l2 , v) ': r)) = Label l1 -> Rec f r
         -> Lookup f l1 ( '(l2 , v) ': r)
  req p l r = req' (Proxy @ (l1 == l2)) p l r

-- instance Require (OpLookup' b f l r) ctx where
--   type ReqR (OpLookup' b f l r) = Proxy b -> Label l -> Rec f r -> Lookup f l r
--   req p b l r = undefined

class Require' (b    :: Bool)
               (op   :: Type) --todo: ?
               (ctx  :: [Symbol])  where
   type ReqR' b op
   req' :: Proxy b -> Proxy ctx -> ReqR' b op




-- class ReqLookup (f   :: k -> k' -> Type)
--                 (l   :: k)
--                 (r   :: [(k, k')])
--                 (ctx :: [Symbol]) where
--   type ReqLR f l r :: Type
--   reqLookup :: Proxy ctx -> Label l -> Rec f r -> ReqLR f l r

-- class ReqLookup' (b :: Bool)
--                  (f   :: k -> k' -> Type)
--                  (l   :: k)
--                  (r   :: [(k, k')])
--                  (ctx :: [Symbol]) where
--   type ReqLR' b f l r :: Type
--   reqLookup' :: Proxy ctx -> Proxy b -> Label l -> Rec f r -> ReqLR' f l r

-- instance RecLookup' (l == l') f l ( '(l', v) ': r) ctx
--   => RecLookup f l ( '(l', v) ': r) ctx where
--   type ReqLR f l ( '(l', v) ': r) = ReqLR' (l == l') l ( '(l', v) ': r)
--   reqLookup ctx l r = reqLookup' ctx (Proxy @ (l == l')) l r 
