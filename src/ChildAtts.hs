{-|
Module      : ChildAtts
Description : Maps from child names to attributions
Copyright   : (c) Juan García Garland, 2018 
License     : LGPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX

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

module ChildAtts where

import Data.Kind 
import Data.Type.Equality
import Data.Proxy
import Attribute
import TPrelude
import TagUtils
import Attribution

-- | * Constructors


-- | The record of attribution fot the children, strongly kinded
data ChAttsRec :: forall k k' . [(k , [(k',Type)])] -> Type where
  EmptyCh :: ChAttsRec '[]
  ConsCh  :: LabelSet ( '(l, v) ': xs) =>
   TaggedChAttr l v -> ChAttsRec xs -> ChAttsRec ( '(l,v) ': xs)

-- | Pretty constructors
infixr 2 .*
(.*) :: LabelSet ('(ch, attrib) : attribs) =>
  TaggedChAttr ch attrib -> ChAttsRec attribs -> ChAttsRec ('(ch, attrib) : attribs)
(.*) = ConsCh

-- | no child
emptyChild :: ChAttsRec '[]
emptyChild = EmptyCh

-- |** This are the tag utils for tag attributions of the childred

-- TODO: move this?

-- | Tags a Label (labels of children) to an attribution
data TaggedChAttr (l::k) (v :: [(k',Type)]) :: Type where
  TaggedChAttr :: Label l -> Attribution v -> TaggedChAttr l v


-- | Pretty constructor for tagging a child
infixr 4 .=
(.=) :: Label l -> Attribution v -> TaggedChAttr l v
(.=) = TaggedChAttr

-- | To get the atribution
unTaggedChAttr :: TaggedChAttr l a -> Attribution a
unTaggedChAttr (TaggedChAttr _ a) = a

-- | To get the label
labelChAttr :: TaggedChAttr l a -> Label l
labelChAttr _ = Label

                                                 
-- |* Lookup

-- | Haschild is like HasField
class HasChild (l::k) (r :: [(k ,[(k,Type)])]) v | l r -> v where
   lookupByChild :: Label l -> ChAttsRec r -> Attribution v

instance (HEqK l l1 b, HasChild' b l ( '(l1,v1) ': r) v)
    => HasChild l ( '(l1,v1) ': r) v where
    lookupByChild l (r :: ChAttsRec ( '(l1,v1) ': r)) =
         lookupByChild' (Proxy::Proxy b) l r

class HasChild' (b::Bool) (l :: k) (r::[(k,[(k,Type)])]) v | b l r -> v where
    lookupByChild':: Proxy b -> Label l -> ChAttsRec r -> Attribution v

instance HasChild' True l ( '(l,v) ': r) v where
   lookupByChild' _ _ (ConsCh lv _) = unTaggedChAttr lv
instance HasChild l r v => HasChild' False l ( '(l2,v2) ': r) v where
   lookupByChild' _ l (ConsCh _ r) = lookupByChild l r

-- | Pretty lookup
infixl 2 .#
(.#)  :: (HasChild l r v) => ChAttsRec r -> Label l ->  Attribution v
c .# l = lookupByChild l c

-- |* Update

-- | updates an attribution at a child, this is the implementation of
--UpdateAtLabel for children
class UpdateAtChild (l :: k)(v :: [(k,Type)])
      (r :: [(k,[(k,Type)])])(r' :: [(k,[(k,Type)])])
   | l v r -> r' where
  updateAtChild :: Label l -> Attribution v -> ChAttsRec r -> ChAttsRec r'

--So we need an auxiliary class with an extra parameter to decide if we update
--on the head of r or not

class UpdateAtChild' (b::Bool)(l::k)(v::[(k,Type)])
      (r::[(k,[(k,Type)])])(r'::[(k,[(k,Type)])])
    | b l v r -> r'  where
  updateAtChild' :: Proxy b -> Label l -> Attribution v -> ChAttsRec r -> ChAttsRec r'



instance (HEqK l l' b, UpdateAtChild' b l v ( '(l',v')': r) r')
 -- note that if pattern over r is not written this does not compile
       => UpdateAtChild l v ( '(l',v') ': r) r' where
  updateAtChild = updateAtChild' (Proxy :: Proxy b)


instance (LabelSet ( '(l,v') ': r), LabelSet ( '(l,v) ': r) ) =>
         UpdateAtChild' 'True l v ( '(l,v') ': r) ( '(l,v) ': r) where
  updateAtChild' _ (l :: Label l) newattrib (attrib `ConsCh` attribs)
    = (TaggedChAttr l newattrib) `ConsCh` attribs


instance ( UpdateAtChild l v r r', LabelSet  ( a ': r' ) ) =>
         UpdateAtChild' False l v (a ': r) (a ': r') where
  updateAtChild' (b :: Proxy False) (l :: Label l) v
    (ConsCh attrib xs :: ChAttsRec ( a ': r))
    = case (updateAtChild l v xs) of
        xs' -> ConsCh attrib xs' :: ChAttsRec (a ': r')


-- TODO: Type errors
--instance Fail (FieldNotFound l) => UpdateAtChild l v '[] '[] where
--    updateAtChild _ _ r = r



-- |*  Predicates

-- | To decide label membership, returning a certificate
class HasLabelChildAtts (e :: k)(r :: [(k,[(k,Type)])]) where
  type HasLabelChildAttsRes (e::k)(r :: [(k,[(k,Type)])]) :: Bool
  hasLabelChildAtts
   :: Label e -> ChAttsRec r -> Proxy (HasLabelChildAttsRes e r)

instance HasLabelChildAtts e '[] where
  type HasLabelChildAttsRes e '[] = 'False
  hasLabelChildAtts _ _ = Proxy

instance HasLabelChildAtts k ( '(k' ,v) ': ls) where
  type HasLabelChildAttsRes k ( '(k' ,v) ': ls)
      = Or (k == k') (HasLabelChildAttsRes k ls)
  hasLabelChildAtts _ _ = Proxy





-- | Some boilerplate to show Attributes and Attributions
instance Show (ChAttsRec '[]) where
  show _ = "{}"

instance (Show (Attribution v), Show (ChAttsRec xs)) =>
         Show (ChAttsRec ( '(l,v) ': xs ) ) where
  show (ConsCh lv xs) = let tail = show xs
                            in "{" ++ show (unTaggedChAttr lv) ++
                               "," ++ drop 1 tail 
