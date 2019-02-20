{-|
Module      : Language.Grammars.AspectAG.Attribution
Description : Maps from attribute names to attribute values
Copyright   : (c) Juan García Garland, 2018 
License     : LGPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX

Used to build attributions, which are mappings from labels to values.
This module implements dependent functions using functional dependencies
and using type families. The latter approach is the one we actually use.

-}

{-# LANGUAGE DataKinds,
             TypeOperators,
             PolyKinds,
             GADTs,
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
             TypeApplications
#-}

module Language.Grammars.AspectAG.Attribution  where

-- (
--   (*.),
--   lookupByLabelAtt,

--                                                     )where

import Data.Kind 
import Data.Type.Equality
import Data.Proxy
import GHC.TypeLits

import Language.Grammars.AspectAG.GenRecord

import Language.Grammars.AspectAG.Attribute
import Language.Grammars.AspectAG.TPrelude
import Language.Grammars.AspectAG.TagUtils


-- -- | Internal representation, isomorphic to a 'Record'
-- data Attribution :: forall k . [(k,Type)] -> Type where
--   EmptyAtt :: Attribution '[]
--   ConsAtt  :: LabelSet ( '(att, val) ': atts) =>
--    Attribute att val -> Attribution atts -> Attribution ( '(att,val) ': atts)

-- | An attribution is a record constructed from attributes
type Attribution = REC Attribute 

-- * Pretty constructors

-- | Extending
infixr 2 *.
(*.) :: LabelSet ('(att, val) : atts) =>
    Attribute att val -> Attribution atts
      -> Attribution ('(att, val) : atts)
(*.) = ConsR

-- | Empty
emptyAtt :: Attribution '[]
emptyAtt = EmptyR

-- * operations

-- | A getter, also works as a predicate. 'HasFieldAttF' is actually used.
class HasFieldAtt (l::k) (r :: [(k,Type)]) v | l r -> v where
   lookupByLabelAtt:: Label l -> Attribution r -> v

instance (HEqK l l1 b, HasFieldAtt' b l ( '(l1,v1) ': r) v)
  => HasFieldAtt l ( '(l1,v1) ': r) v where
  lookupByLabelAtt l (r :: Attribution ( '(l1,v1) ': r)) =
       lookupByLabelAtt' (Proxy::Proxy b) l r

class HasFieldAtt' (b::Bool) (l :: k) (r::[(k,Type)]) v | b l r -> v where
  lookupByLabelAtt':: Proxy b -> Label l -> Attribution r -> v

instance HasFieldAtt' True l ( '(l,v) ': r) v where
  lookupByLabelAtt' _ _ (ConsR (Attribute v) _) = v
instance HasFieldAtt l r v => HasFieldAtt' False l ( '(l2,v2) ': r) v where
  lookupByLabelAtt' _ l (ConsR _ r) = lookupByLabelAtt l r

-- | Error instance

-- instance TypeError (Text "NoFieldError")
--   => HasFieldAtt l '[] t where {}  



-- | Type Family Version of HasFieldAtt

class HasFieldAttF (l::k) (r :: [(k,Type)]) where
  type LookupByLabelAttFR l r :: Type
  lookupByLabelAttF:: Label l -> Attribution r -> LookupByLabelAttFR l r

class HasFieldAttF' (b :: Bool) (l::k) (r :: [(k,Type)]) where
  type LookupByLabelAttFR' b l r :: Type
  lookupByLabelAttF' :: Proxy b -> Label l -> Attribution r
                     -> LookupByLabelAttFR' b l r
  
instance (HasFieldAttF' (l==l1) l ( '(l1,v) ': r))
  => HasFieldAttF l ( '(l1,v) ': r) where
  type LookupByLabelAttFR l ( '(l1,v) ': r)
    = LookupByLabelAttFR' (l==l1) l ( '(l1,v) ': r)
  lookupByLabelAttF l r = lookupByLabelAttF' (Proxy :: Proxy (l == l1)) l r


instance HasFieldAttF' True l ( '(l, v) ': r) where
  type LookupByLabelAttFR' 'True l ( '(l, v) ': r) = v
  lookupByLabelAttF' _ _ (ConsR (Attribute a) _) = a

instance (HasFieldAttF l r)
  => HasFieldAttF' 'False l ( '(l1,v) ': r) where
  type LookupByLabelAttFR' 'False l ( '(l1,v) ': r) = LookupByLabelAttFR l r
  lookupByLabelAttF' _ l (ConsR _ r) = lookupByLabelAttF l r


  
{-
 This is a nice piece of code, for that reason I keep it here.

type family LookupByLabelAttFR (l::k) (r ::[(k,Type)]) :: Type where
  LookupByLabelAttFR l '[]
    = TypeError (Text "No attribution named " :$$:
                  ShowType l :$$: Text " found")
  LookupByLabelAttFR l ( '(m, t) ': xs)
    = If (l == m) t (LookupByLabelAttFR l xs)

It shows why Indexed TF are better than open/closed ones in this kind
of funcion.

lookupByLabelAttF :: Label l -> Attribution ( '(l2, v) ': r)
                 -> LookupByLabelAttFR l ( '(l2, v) ': r)
lookupByLabelAttF l r = lookupByLabelAttF' (Proxy @ (l == l2)) l r

Proxy @ (l == l2) does not compile since l and l2 are free. To have
access to them we need to annotate types everywhere, on the class we
use (Proxy:: Proxy b) even when b is only binded on the LHS of the class
definition!!

proxy = Proxy

lookupByLabelAttF' :: Proxy 'True -> Label l -> Attribution ( '(l, v) ': r)
                 -> LookupByLabelAttFR l ( '(l, v) ': r)
-- lookupByLabelAttF' l (ConsR (Attribute v) _) = v
-}

-- | Pretty lookup
infixl 3 #.
(#.)  :: (HasFieldAttF l r)
   => Attribution r -> Label l -> LookupByLabelAttFR l r
c #. l = lookupByLabelAttF l c


-- | Update an attribution at a Label, putting an attribute v.
--Note that not only the value but also the type at the position could
--be updated. 'UpdateAtLabelAttF' is actually used
class UpdateAtLabelAtt (l :: k)(v :: Type)(r :: [(k,Type)])(r' :: [(k,Type)])
   | l v r -> r' where
  updateAtLabelAtt :: Label l -> v -> Attribution r -> Attribution r'


class UpdateAtLabelAtt' (b::Bool)(l::k)(v::Type)(r::[(k,Type)])(r'::[(k,Type)])
    | b l v r -> r'  where
  updateAtLabelAtt' :: Proxy b -> Label l -> v->Attribution r -> Attribution r'


instance (HEqK l l' b, UpdateAtLabelAtt' b l v ( '(l',v')': r) r')
 -- note that if pattern over r is not written this does not compile
  => UpdateAtLabelAtt l v ( '(l',v') ': r) r' where
  updateAtLabelAtt = updateAtLabelAtt' (Proxy :: Proxy b)


instance (LabelSet ( '(l,v') ': r), LabelSet ( '(l,v) ': r) )
  => UpdateAtLabelAtt' 'True l v ( '(l,v') ': r) ( '(l,v) ': r) where
  updateAtLabelAtt' _ (l :: Label l) v (att `ConsR` atts)
    = (Attribute v :: Attribute l v) `ConsR` atts


instance ( UpdateAtLabelAtt l v r r', LabelSet  ( a ': r' ) ) =>
         UpdateAtLabelAtt' False l v ( a ': r) ( a ': r') where
  updateAtLabelAtt' (b :: Proxy False) (l :: Label l) (v :: v)
    (ConsR att xs :: Attribution ( a ': r))
    = case (updateAtLabelAtt l v xs) of
        xs' -> ConsR att xs' :: Attribution( a ': r')



-- TODO: implement type error
--instance Fail (FieldNotFound l) => UpdateAtLabelAtt l v '[] '[] where
--    updateAtLabelAtt _ _ r = r



-- instance Show (Attribution '[]) where
--   show _ = "«»"

-- instance (Show val, Show (Attribution atts)) =>
--          Show (Attribution  ( '(att,val) ': atts ) ) where
--   show (ConsAtt att atts) = let tail = show atts
--                             in "«" ++ show (getVal att) ++ "," ++ drop 1 tail 

-- | Type family implementation of update 
class UpdateAtLabelAttF (l :: k) (v :: Type) (r :: [(k,Type)]) where
  type UpdateAtLabelAttFR l v r :: [(k,Type)]
  updateAtLabelAttF :: Label l -> v -> Attribution r
                    -> Attribution (UpdateAtLabelAttFR l v r)  

-- | Auxiliar function, with equality proof explicit
class UpdateAtLabelAttF' (b :: Bool) (l :: k) (v :: Type)
                                       (r :: [(k, Type)]) where
  type UpdateAtLabelAttFR' b l v r :: [(k,Type)]
  updateAtLabelAttF' :: Proxy b -> Label l -> v -> Attribution r
                     -> Attribution (UpdateAtLabelAttFR' b l v r)  


-- | Call the auxiliar function making te (in)equality evidence
-- of head and to-update index explicit 
instance (UpdateAtLabelAttF' (l==l2) l v ( '(l2, v2) ': r))
  => UpdateAtLabelAttF l v ( '(l2, v2) ': r) where
  type UpdateAtLabelAttFR l v ( '(l2, v2) ': r)
    = UpdateAtLabelAttFR' (l==l2) l v ( '(l2, v2) ': r)
  updateAtLabelAttF l v r = updateAtLabelAttF' (Proxy @ (l==l2)) l v r

-- | When the first label matches
instance (LabelSet ('(l, v) : r))
  => UpdateAtLabelAttF' 'True l v ( '(l2,v2) ': r) where
  type UpdateAtLabelAttFR' 'True l v ( '(l2,v2) ': r) = ( '(l,v) ': r)
  updateAtLabelAttF' _ l v (_ `ConsR` r) = l =. v *. r 

-- | When the first label does not match
instance ( LabelSet ( '(l2,v2) ': UpdateAtLabelAttFR l v r)
         , UpdateAtLabelAttF l v r)
  => UpdateAtLabelAttF' 'False l v ( '(l2,v2) ': r) where
  type UpdateAtLabelAttFR' 'False l v ( '(l2,v2) ': r)
    = '(l2,v2) ': UpdateAtLabelAttFR l v r
  updateAtLabelAttF' _ l v (lv `ConsR` r) = lv *. (updateAtLabelAttF l v r) 

-- | Error instance
type NoAttToUpdate l r
  = Text "No attribute of name '" :<>: ShowType l :<>: Text "'":$$:
          Text "to update on Attribution: " :<>: ShowType r

instance UpdateAtLabelAttF l v '[] where
  type UpdateAtLabelAttFR l v '[] = TypeError (NoAttToUpdate l '[])
  updateAtLabelAttF = undefined

{-

Here, either conflicting fam decls or a warning, anyways, the error is the
same than in actual implementation
instance {-# OVERLAPS #-} TypeError (NoAttToUpdate l r)
  => UpdateAtLabelAttF l v r where
  type UpdateAtLabelAttFR l v r = '[] -- TypeError (NoAttToUpdate l r)
  updateAtLabelAttF = undefined
-}
