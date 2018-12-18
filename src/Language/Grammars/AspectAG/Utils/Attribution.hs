{-|
Module      : Language.Grammars.AspectAG.Utils.Attribution
Description : Maps from attribute names to attribute values
Copyright   : (c) Juan García Garland, 2018 
License     : LGPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX

Used to build attributions, which are mappings from labels to values
-}

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
             TypeFamilies
#-}

module Language.Grammars.AspectAG.Utils.Attribution  where

-- (
--   (*.),
--   lookupByLabelAtt,

--                                                     )where

import Data.Kind 
import Data.Type.Equality
import Data.Proxy

import Language.Grammars.AspectAG.Utils.GenRecord

import Language.Grammars.AspectAG.Utils.Attribute
import Language.Grammars.AspectAG.Utils.TPrelude
import Language.Grammars.AspectAG.Utils.TagUtils


-- -- | Internal representation, isomorphic to a 'Record'
-- data Attribution :: forall k . [(k,Type)] -> Type where
--   EmptyAtt :: Attribution '[]
--   ConsAtt  :: LabelSet ( '(att, val) ': atts) =>
--    Attribute att val -> Attribution atts -> Attribution ( '(att,val) ': atts)

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

-- | A getter, also works as a predicate
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


-- | Pretty lookup
-- | Pretty lookup
infixl 2 #.
(#.)  :: (HasFieldAtt l r v)
   => Attribution r -> Label l -> v
c #. l = lookupByLabelAtt l c

--UpdateAtLabel
--I attempt to code an indexed type implementation, where the resulting Type
--function of the parameters.
--I could code the type function over the type level,
--the problem is when I do this on a type class to code ter level computations.
--Since we decide from the context (HEqK ) the returned boolean must be a
--parameter of UpdateAtLabelR, but since it's purely on the context,
--it is free on the RHS...
--The fundep implementation is needed..


-- | Update an attribution at a Label, putting an attribute v.
--Note that not only the value but also the type at the position could
--be updated
class UpdateAtLabelAtt (l :: k)(v :: Type)(r :: [(k,Type)])(r' :: [(k,Type)])
   | l v r -> r' where
  updateAtLabelAtt :: Label l -> v -> Attribution r -> Attribution r'

--So we need an auxiliary class with an extra parameter to decide if we update
--on the head of r or not

class UpdateAtLabelAtt' (b::Bool)(l::k)(v::Type)(r::[(k,Type)])(r'::[(k,Type)])
    | b l v r -> r'  where
  updateAtLabelAtt' :: Proxy b -> Label l -> v->Attribution r -> Attribution r'



instance (HEqK l l' b, UpdateAtLabelAtt' b l v ( '(l',v')': r) r')
 -- note that if pattern over r is not written this does not compile
       => UpdateAtLabelAtt l v ( '(l',v') ': r) r' where
  updateAtLabelAtt = updateAtLabelAtt' (Proxy :: Proxy b)


instance (LabelSet ( '(l,v') ': r), LabelSet ( '(l,v) ': r) ) =>
         UpdateAtLabelAtt' 'True l v ( '(l,v') ': r) ( '(l,v) ': r) where
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
