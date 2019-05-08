
{-|
Module      : Language.Grammars.AspectAG.ChildAtts
Description : Maps from child names to attributions
Copyright   : (c) Juan García Garland, 2018 
License     : LGPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX

Yet another specialized record. Mappings from Children to their attributions.
This module implements dependent functions using functional dependencies
and using type families. The latter approach is the one we actually use.

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
             TypeFamilies,
             PatternSynonyms,
             TypeApplications
#-}

module Language.Grammars.AspectAG.ChildAtts where

import Data.Kind 
import Data.Type.Equality
import Data.Proxy
import Language.Grammars.AspectAG.Attribute
import Language.Grammars.AspectAG.TPrelude
import Language.Grammars.AspectAG.TagUtils
import Language.Grammars.AspectAG.Attribution
import Language.Grammars.AspectAG.GenRecord
import GHC.TypeLits

-- | * Constructors


-- | The record of attribution fot the children, strongly kinded
-- data ChAttsRec :: forall k k' . [(k , [(k',Type)])] -> Type where
--   EmptyCh :: ChAttsRec '[]
--   ConsCh  :: LabelSet ( '(l, v) ': xs) =>
--    TaggedChAttr l v -> ChAttsRec xs -> ChAttsRec ( '(l,v) ': xs)

-- type ChAttsRec = REC TaggedChAttr


-- | Pattern synonyms, since now we implement ChAttsRec as a generic record,
-- this allows us to recover pattern matching
pattern EmptyCh :: ChAttsRec prd '[]
pattern EmptyCh = EmptyRec
pattern ConsCh :: (LabelSet ( '( 'Chi ch prd nt, v) ': xs)) =>
  TaggedChAttr prd ( 'Chi ch prd nt) v -> ChAttsRec prd xs
                         -> ChAttsRec prd ( '( 'Chi ch prd nt,v) ': xs)
pattern ConsCh h t = ConsRec h t

-- | Pretty constructors
infixr 2 .*
(.*) :: LabelSet ('(ch, attrib) ':  attribs) =>
  TaggedChAttr prd ch attrib -> ChAttsRec prd attribs
    -> ChAttsRec prd ('(ch, attrib) ': attribs)
(.*) = ConsRec

-- | no child
emptyCh :: ChAttsRec prd '[]
emptyCh = EmptyRec

-- |** This are the tag utils for tag attributions of the childred

-- TODO: move this?

-- | Tags a Label (labels of children) to an attribution
--data TaggedChAttr (l :: (k,Type)) (v :: [(k,Type)]) :: Type where
--  TaggedChAttr :: Label l -> Attribution v -> TaggedChAttr l v


-- | Pretty constructor for tagging a child
infixr 4 .=
(.=) :: Label l -> WrapField (ChiReco prd) v -> TaggedChAttr prd l v
(.=) = TaggedChAttr

-- | To get the atribution
unTaggedChAttr :: TaggedChAttr prd l v -> WrapField (ChiReco prd) v
unTaggedChAttr (TaggedChAttr _ a) = a


-- | To get the label
--labelChAttr :: TaggedChAttr l a -> Label l
--labelChAttr _ = Label

                                                 
-- |* Lookup

-- | Haschild is a predicate that implements a lookup at term level
-- class HasChild (l::(k,Type)) (r :: [((k,Type) ,[(k,Type)])]) v | l r -> v where
--    lookupByChild :: Label l -> ChAttsRec r -> Attribution v

-- instance (HEqK l l1 b, HasChild' b l ( '(l1,v1) ': r) v)
--     => HasChild l ( '(l1,v1) ': r) v where
--     lookupByChild l (r :: ChAttsRec ( '(l1,v1) ': r)) =
--          lookupByChild' (Proxy::Proxy b) l r

-- class HasChild' (b::Bool) (l :: (k,Type)) (r::[((k,Type),[(k,Type)])]) v | b l r -> v where
--     lookupByChild':: Proxy b -> Label l -> ChAttsRec r -> Attribution v

-- instance HasChild' True l ( '(l,v) ': r) v where
--    lookupByChild' _ _ (ConsRec lv _) = unTaggedChAttr lv
-- instance HasChild l r v => HasChild' False l ( '(l2,v2) ': r) v where
--    lookupByChild' _ l (ConsRec _ r) = lookupByChild l r


-- | HaschildF is the type family version of HasChild

-- class HasChildF (l::(k,Type)) (r :: [((k,Type) ,[(k,Type)])]) where
--   type LookupByChildFR l r :: [(k,Type)]
--   lookupByChildF :: Label l -> ChAttsRec r -> Attribution (LookupByChildFR l r)

-- class HasChildF' (b :: Bool) (l::(k,Type)) (r :: [((k,Type) ,[(k,Type)])]) where
--   type LookupByChildFR' b l r :: [(k,Type)]
--   lookupByChildF' :: Proxy b -> Label l -> ChAttsRec r
--     -> Attribution (LookupByChildFR' b l r)

-- instance (HasChildF' (l==l1) l ( '(l1,v) ': r)) =>
--   HasChildF l ( '(l1,v) ': r) where
--   type LookupByChildFR l ( '(l1,v) ': r)
--     =  LookupByChildFR' (l == l1) l ( '(l1,v) ': r)
--   lookupByChildF l r = lookupByChildF' (Proxy :: Proxy (l == l1)) l r

-- instance
--   HasChildF' 'True l ( '(l,v) ': r) where
--   type LookupByChildFR' 'True l ( '(l,v) ': r) = v
--   lookupByChildF' _ _ (ConsRec lv _) = unTaggedChAttr lv

-- instance (HasChildF l r) => 
--   HasChildF' 'False l ( '(l1,v) ': r) where
--   type LookupByChildFR' 'False l ( '(l1,v) ': r) = LookupByChildFR l r
--   lookupByChildF' _ l (ConsRec _ r) = lookupByChildF l r

-- | Pretty lookup,
--infixl 8 .#
--(.#)  :: (HasChildF l r, LookupByChildFR l r ~ v) =>
--         ChAttsRec r -> Label l ->  Attribution v
--c .# l = lookupByChildF l c

infixl 8 .#
(.#)
  :: Require (OpLookup (ChiReco prd) w r) '[] =>
     Rec (ChiReco prd) r -> Label w -> ReqR (OpLookup (ChiReco prd) w r)
(chi :: Rec (ChiReco prd) r) .# l = req (Proxy @ '[]) (OpLookup @_ @(ChiReco prd) l chi)

-- lookupCtx
--   :: Require (OpLookup ChiReco w r) ctx =>
--      Proxy ctx -> Rec ChiReco r -> Label w -> ReqR (OpLookup ChiReco w r)
--lookupCtx (p :: Proxy ctx) chi l = req p (OpLookup @_ @ChiReco l chi)

-- |* Update

-- | updates an attribution at a child, this is the implementation of
--   UpdateAtLabel for children, using functional dependencies
-- class UpdateAtChild (l :: (k,Type))(v :: [(k,Type)])
--       (r :: [((k,Type),[(k,Type)])])(r' :: [((k,Type),[(k,Type)])])
--    | l v r -> r' where
--   updateAtChild :: Label l -> Attribution v -> ChAttsRec r -> ChAttsRec r'

-- --So we need an auxiliary class with an extra parameter to decide if we update
-- --on the head of r or not

-- class UpdateAtChild' (b::Bool)(l::(k,Type))(v::[(k,Type)])
--       (r::[((k,Type),[(k,Type)])])(r'::[((k,Type),[(k,Type)])])
--     | b l v r -> r'  where
--   updateAtChild' :: Proxy b -> Label l -> Attribution v -> ChAttsRec r
--                  -> ChAttsRec r'

-- instance (HEqK l l' b, UpdateAtChild' b l v ( '(l',v')': r) r')
--  -- note that if pattern over r is not written this does not compile
--        => UpdateAtChild l v ( '(l',v') ': r) r' where
--   updateAtChild = updateAtChild' (Proxy :: Proxy b)


-- instance (LabelSet ( '(l,v') ': r), LabelSet ( '(l,v) ': r) ) =>
--          UpdateAtChild' 'True l v ( '(l,v') ': r) ( '(l,v) ': r) where
--   updateAtChild' _ (l :: Label l) newattrib (attrib `ConsRec` attribs)
--     = (TaggedChAttr l newattrib) .*. attribs


-- instance ( UpdateAtChild l v r r', LabelSet  ( a ': r' ) ) =>
--          UpdateAtChild' False l v (a ': r) (a ': r') where
--   updateAtChild' (b :: Proxy False) (l :: Label l) v
--     (ConsRec attrib xs :: ChAttsRec ( a ': r))
--     = case (updateAtChild l v xs) of
--         xs' -> attrib .*. xs' :: ChAttsRec (a ': r')


-- -- TODO: Type errors
-- --instance Fail (FieldNotFound l) => UpdateAtChild l v '[] '[] where
-- --    updateAtChild _ _ r = r


-- | updates an attribution at a child, this is the implementation of
--   UpdateAtLabel for children, using type families
class UpdateAtChildF (l :: (k,Type))(v :: [(k,Type)])(r :: [((k,Type),[(k,Type)])]) where
  type UpdateAtChildFR l v r :: [((k,Type),[(k,Type)])]
  updateAtChildF :: Label l -> Attribution v -> ChAttsRec prd r
                 -> ChAttsRec prd (UpdateAtChildFR l v r)

class UpdateAtChildF' (b :: Bool)
                      (l :: (k,Type))(v :: [(k,Type)])
                      (r :: [((k,Type),[(k,Type)])]) where
  type UpdateAtChildFR' b l v r :: [((k,Type),[(k,Type)])]
  updateAtChildF' :: Proxy b -> Label l -> Attribution v -> ChAttsRec prd r
                 -> ChAttsRec prd (UpdateAtChildFR' b l v r)


instance (LabelSet ( '(l,v') ': r), LabelSet ( '(l,v) ': r)) =>
  UpdateAtChildF' 'True l v ( '(l,v') ': r) where
  type UpdateAtChildFR' 'True l v ( '(l,v') ': r) = ( '(l,v) ': r)
  updateAtChildF' Proxy l natbtn (oatbtn `ConsRec` atbtns)
    = l .= natbtn .* atbtns

instance (UpdateAtChildF l v r, LabelSet (a ': (UpdateAtChildFR l v r))) => 
  UpdateAtChildF' 'False l v (a ': r) where
  type UpdateAtChildFR' 'False l v (a ': r) = a ': (UpdateAtChildFR l v r)
  updateAtChildF' b l v (ConsRec atbtn atbtns)
    = case (updateAtChildF l v atbtns) of
        atbtns' -> atbtn .* atbtns'

instance (UpdateAtChildF' (l==l') l v ( '(l',v')': r)) =>
  UpdateAtChildF l v ( '(l',v') ': r)  where
  type UpdateAtChildFR l v ( '(l',v') ': r)
    = UpdateAtChildFR' (l == l') l v ( '(l',v')': r)
  updateAtChildF = updateAtChildF' (Proxy :: Proxy (l==l'))






-- |*  Predicates

-- | To decide label membership, returning a certificate
class HasLabelChildAtts (e :: (k,Type))(r :: [((k,Type),[(k,Type)])]) where
  type HasLabelChildAttsRes (e::(k,Type))(r :: [((k,Type),[(k,Type)])]) :: Bool
  hasLabelChildAtts
   :: Label e -> ChAttsRec prd r -> Proxy (HasLabelChildAttsRes e r)

instance HasLabelChildAtts e '[] where
  type HasLabelChildAttsRes e '[] = 'False
  hasLabelChildAtts _ _ = Proxy

instance HasLabelChildAtts k ( '(k' ,v) ': ls) where
  type HasLabelChildAttsRes k ( '(k' ,v) ': ls)
      = Or (k == k') (HasLabelChildAttsRes k ls)
  hasLabelChildAtts _ _ = Proxy





-- | Some boilerplate to show Attributes and Attributions
instance Show (ChAttsRec prd '[]) where
  show _ = "{}"

instance (Show (WrapField (ChiReco prd) v), Show (ChAttsRec prd xs)) =>
         Show (ChAttsRec prd ( '(l,v) ': xs ) ) where
  show (ConsRec lv xs) = let tail = show xs
                       in "{" ++ show (unTaggedChAttr lv) ++
                          "," ++ drop 1 tail 
