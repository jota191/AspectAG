{-|
Module      : Language.Grammars.AspectAG.Record
Description : Strongly typed heterogeneous records,
              using polykinded phantom labels as indexes.
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
             TypeFamilies,
             InstanceSigs
#-}

module Language.Grammars.AspectAG.Record where

import Data.Kind 
import Data.Type.Equality
import Data.Proxy
import Language.Grammars.AspectAG.TPrelude
import Data.Tagged hiding (unTagged)
import Language.Grammars.AspectAG.TagUtils
import GHC.TypeLits
import Language.Grammars.AspectAG.GenRecord

-- * Constructors


-- ** Internal representation

-- | A Record is a map from labels to values. Labels must be unique,
--so we use a proof of 'LabelSet' as an implicit parameter to construct a new
--instance

-- data Record :: forall k . [(k,Type)] -> Type where
--   EmptyR :: Record '[]
--   ConsR  :: LabelSet ( '(l, v) ': xs) =>
--    Tagged l v -> Record xs -> Record ( '(l,v) ': xs)


type Record = REC Tagged

-- ** Exported
-- | Pretty constructors

-- | For the empty Record
emptyRecord :: Record '[]
emptyRecord = EmptyR



-- * Getting

-- | get a field indexed by a label
class HasFieldRec (l::k) (r :: [(k,Type)]) where
  type LookupByLabelRec l r :: Type
  lookupByLabelRec:: Label l -> Record r -> LookupByLabelRec l r


instance (HasFieldRec' (l == l2) l ( '(l2,v) ': r)) =>
  HasFieldRec l ( '(l2,v) ': r) where
  type LookupByLabelRec l ( '(l2,v) ': r)
    = LookupByLabelRec' (l == l2) l ( '(l2,v) ': r)
  lookupByLabelRec :: Label l -> Record ( '(l2,v) ': r)
                    -> LookupByLabelRec l ( '(l2,v) ': r)
  lookupByLabelRec l r
    = lookupByLabelRec' (Proxy :: Proxy (l == l2)) l r 

class HasFieldRec' (b::Bool) (l::k) (r :: [(k,Type)]) where
  type LookupByLabelRec' b l r :: Type
  lookupByLabelRec' ::
     Proxy b -> Label l -> Record r -> LookupByLabelRec' b l r

-- | Operator for lookup
infixl 3 .#.
(.#.)  :: (HasFieldRec l r)
   => Record r -> Label l -> (LookupByLabelRec l r)
c .#. l = lookupByLabelRec l c

-- | Since the typechecker cannot decide an instance dependent of the context,
--but on the head, an auxiliary class with an extra parameter to decide
--if we update on the head of r or not is used
instance HasFieldRec'    'True l ( '(l, v) ': r) where
  type LookupByLabelRec' 'True l ( '(l, v) ': r) = v
  lookupByLabelRec' _ _ (ConsR lv _) = unTagged lv

instance (HasFieldRec l r )=>
  HasFieldRec' 'False l ( '(l2, v) ': r) where
  type LookupByLabelRec' 'False l ( '(l2, v) ': r) = LookupByLabelRec l r
  lookupByLabelRec' _ l (ConsR _ r) = lookupByLabelRec l r


type NoFieldFound l
  = Text "Type Error : No Field found on Record:" :$$:
    Text "(Possibly, in some aspect there are productions " :<>:
    Text "where the attribute is undefined)" :$$:
    Text "No Field of type " :<>: ShowType l
    :<>: Text " on Record"

-- | Error instance:
instance TypeError (NoFieldFound l)
  => HasFieldRec l '[] where
  type LookupByLabelRec l '[] = ()
  lookupByLabelRec = undefined



-- * Updating

-- | updating the value on a label, possibly changing the type of the index,
-- fundep version
class UpdateAtLabelRec (l :: k)(v :: Type)(r :: [(k,Type)])(r' :: [(k,Type)])
   | l v r -> r' where
  updateAtLabelRec :: Label l -> v -> Record r -> Record r'


instance (HEqK l l' b, UpdateAtLabelRec' b l v ( '(l',v')': r) r')
 -- note that if pattern over r is not written this does not compile
       => UpdateAtLabelRec l v ( '(l',v') ': r) r' where
  updateAtLabelRec = updateAtLabelRec' (Proxy :: Proxy b)

-- | Again, the usual hack 
class UpdateAtLabelRec' (b::Bool)(l::k)(v::Type)(r::[(k,Type)])(r'::[(k,Type)])
    | b l v r -> r'  where
  updateAtLabelRec' :: Proxy b -> Label l -> v -> Record r -> Record r'

instance (LabelSet ( '(l,v') ': r), LabelSet ( '(l,v) ': r) ) =>
         UpdateAtLabelRec' 'True l v ( '(l,v') ': r) ( '(l,v) ': r) where
  updateAtLabelRec' _ (l :: Label l) v (att `ConsR` atts)
    = (Tagged v :: Tagged l v) `ConsR` atts

instance ( UpdateAtLabelRec l v r r', LabelSet  ( a ': r' ) ) =>
         UpdateAtLabelRec' False l v ( a ': r) ( a ': r') where
  updateAtLabelRec' (b :: Proxy False) (l :: Label l) (v :: v)
    (ConsR att xs :: Record ( a ': r))
    = case (updateAtLabelRec l v xs) of
        xs' -> ConsR att xs' :: Record( a ': r')

-- | Type family version of update
class UpdateAtLabelRecF (l :: k)(v :: Type)(r :: [(k,Type)]) where
  type UpdateAtLabelRecFR l v r :: [(k,Type)]
  updateAtLabelRecF :: Label l -> v -> Record r
                    -> Record (UpdateAtLabelRecFR l v r)

class UpdateAtLabelRecF' (b :: Bool)(l :: k)(v :: Type)(r :: [(k,Type)]) where
  type UpdateAtLabelRecFR' b l v r :: [(k,Type)]
  updateAtLabelRecF' :: Proxy b -> Label l -> v -> Record r
                    -> Record (UpdateAtLabelRecFR' b l v r)

instance (UpdateAtLabelRecF' (l == l') l v ( '(l',v') ': r)) => 
  UpdateAtLabelRecF l v ( '(l',v') ': r) where
  type UpdateAtLabelRecFR l v ( '(l',v') ': r)
    = UpdateAtLabelRecFR' (l == l') l v ( '(l',v') ': r)
  updateAtLabelRecF = updateAtLabelRecF' (Proxy :: Proxy (l == l'))

instance (LabelSet ( '(l, v) ': r)) => 
  UpdateAtLabelRecF' 'True l v ( '(l, v') ': r) where
  type UpdateAtLabelRecFR' 'True l v ( '(l, v') ': r) = ( '(l, v) ': r)
  updateAtLabelRecF' _ (l :: Label l) v (att `ConsR` atts)
    = (Tagged v :: Tagged l v) .*. atts

instance ( UpdateAtLabelRecF l v r
         , LabelSet ( '(l', v') ': UpdateAtLabelRecFR l v r)) => 
  UpdateAtLabelRecF' 'False l v ( '(l', v') ': r) where
  type UpdateAtLabelRecFR' 'False l v ( '(l', v') ': r)
    = '(l', v') ': UpdateAtLabelRecFR l v r
  updateAtLabelRecF' _ l v (ConsR x xs)
    = x .*. updateAtLabelRecF l v xs



-- | No field on record, On AAG usually appears when an aspect was not
-- defined in all its required labels
instance TypeError
  ( Text "Type Error : No Field found on Record:" :$$:
    Text "(Possibly, in some aspect there are productions " :<>:
    Text "where the attribute is undefined)" :$$:
    Text "No Field of type " :<>: ShowType l
    :<>: Text " on Record" )
  => UpdateAtLabelRec l v '[] '[] where
  updateAtLabelRec _ _ r = r




-- * Predicates

-- | Boolean membership, at type level
class HasLabelRec (e :: k)(r ::[(k,Type)]) where
  type HasLabelRecRes (e::k)(r ::[(k,Type)]) :: Bool
  hasLabelRec :: Label e -> Record r -> Proxy (HasLabelRecRes e r)

instance HasLabelRec e '[] where
  type HasLabelRecRes e '[] = 'False
  hasLabelRec _ _ = Proxy

instance HasLabelRec  k ( '(k' ,v) ': ls) where
  type HasLabelRecRes k ( '(k' ,v) ': ls)
      = Or (k == k') (HasLabelRecRes k ls)
  hasLabelRec _ _ = Proxy



-- | Show instance, used for debugging
instance Show (Record '[]) where
  show _ = "{}"

instance (Show v, Show (Record xs)) =>
         Show (Record ( '(l,v) ': xs ) ) where
  show (ConsR lv xs) = let tail = show xs
                       in "{" ++ show (unTagged lv)
                          ++ "," ++ drop 1 tail




