
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

module Language.Grammars.FastAG.RecordInstances where

-- import Language.Grammars.AspectAG.Require
import Language.Grammars.FastAG.GenRecord
import Language.Grammars.FastAG.TPrelude
import GHC.TypeLits
import Data.Kind
import Data.Proxy
import Prelude hiding (lookup)

data Att   = Att Symbol Type               -- deriving Eq
data Prod  = Prd Symbol NT                  --deriving Eq
data Child = Chi Symbol Prod (Either NT T)  --deriving Eq
data NT    = NT Symbol                      --deriving Eq
data T     = T Type                        -- deriving Eq


type instance
  CMP ('Att a _) ('Att b _) = CmpSymbol a b
type instance
  CMP ('Prd a _) ('Prd b _) = CmpSymbol a b
type instance
  CMP ('Chi a _ _) ('Chi b _ _) = CmpSymbol a b

-- type instance  ShowT ('Att l t)   = Text  "Attribute " :<>: Text l
--                                                        :<>: Text ":"
--                                                        :<>: ShowT t 
-- type instance  ShowT ('Prd l nt)  = ShowT nt :<>: Text "::Production "
--                                              :<>: Text l
-- type instance  ShowT ('Chi l p s) = ShowT p :<>:  Text "::Child " :<>: Text l 
--                                             :<>:  Text ":" :<>: ShowT s
-- type instance  ShowT ('Left l)    = ShowT l
-- type instance  ShowT ('Right r)   = ShowT r
-- type instance  ShowT ('NT l)      = Text "Non-Terminal " :<>: Text l
-- type instance  ShowT ('T  l)      = Text "Terminal " :<>: ShowT l



-- | * Records

-- | datatype definition
type Record        = Rec Reco

-- | index type
data Reco

-- | field type
type instance  WrapField Reco     (v :: Type) = v

-- -- | Type level show utilities
-- type instance ShowRec Reco         = "Record"
-- type instance ShowField Reco       = "field named "



-- | ** Pattern Synonyms
pattern EmptyR :: Rec Reco '[]
pattern EmptyR = EmptyRec :: Rec Reco '[]
pattern ConsR :: (LabelSet ( '(l,v ) ': xs))
  => Tagged l v -> Rec Reco xs -> Rec Reco ( '(l,v ) ': xs) 
pattern ConsR lv r = ConsRec lv r


type Tagged = TagField Reco
pattern Tagged :: v -> Tagged l v
pattern Tagged v = TagField Label Label v



-- ** Constructors

-- | Pretty Constructor
infixr 4 .=.
(.=.) :: Label l -> v -> Tagged l v
l .=. v = Tagged v

-- | For the empty Record
emptyRecord :: Record '[]
emptyRecord = EmptyR

unTagged :: Tagged l v -> v
unTagged (TagField _ _ v) = v

-- * Destructors
-- | Get a label
label :: Tagged l v -> Label l
label _ = Label

-- | Same, mnemonically defined
labelTChAtt :: Tagged l v -> Label l
labelTChAtt _ = Label


-- | Show instance, used for debugging
instance Show (Record '[]) where
  show _ = "{}"

instance (Show v, Show (Record xs), (LabelSet ('(l, v) : xs))) =>
         Show (Record ( '(l,v) ': xs ) ) where
  show (ConsR lv xs) = let tail = show xs
                       in "{" ++ show (unTagged lv)
                          ++ "," ++ drop 1 tail



-- | * Attribution
-- | An attribution is a record constructed from attributes

-- | datatype implementation
type Attribution (attr :: [(Att,Type)]) =  Rec AttReco attr

-- | index type
data AttReco

-- | field type
type instance  WrapField AttReco  (v :: Type) = v

-- -- | type level utilities
-- type instance ShowRec AttReco      = "Attribution"
-- type instance ShowField AttReco       = "attribute named "

-- | Pattern Synonyms
pattern EmptyAtt :: Attribution '[]
pattern EmptyAtt = EmptyRec
pattern ConsAtt :: LabelSet ( '(att, val) ': atts) =>
    Attribute att val -> Attribution atts -> Attribution ( '(att,val) ': atts)
pattern ConsAtt att atts = ConsRec att atts

-- | Attribute

type Attribute (l :: Att) (v :: Type) = TagField AttReco l v
pattern Attribute :: v -> TagField AttReco l v
pattern Attribute v = TagField Label Label v

-- ** Constructors
-- | A pretty constructor for an attribute 
infixr 4 =.

(=.) :: Label l -> v -> Attribute l v
Label =. v = Attribute v


-- | Extending
infixr 2 *.
(*.) ::  (Extend AttReco att val atts) =>
      Attribute att val -> Attribution atts
      -> Attribution (ExtendR AttReco att val atts)
lv *. r = case lv of
            TagField _ l v -> extend l Proxy v r


att1 :: Label ('Att "a" Bool)
att1 = Label

att2 :: Label ('Att "aa" Bool)
att2 = Label

att3 :: Label ('Att "ab" Bool)
att3 = Label

reco = (att3 =. False) *. (att2 =. True) *.(att1 =. True) *. emptyAtt  

-- | Empty
emptyAtt :: Attribution '[]
emptyAtt = EmptyRec


-- ** Destructors
infixl 7 #.

(#.) :: Lookup AttReco l r => 
  Attribution r -> Label l -> LookupR AttReco l r
(attr :: Attribution r) #. (l :: Label l)
  = lookup l attr



-- * Children
-- | operations for the children

-- | datatype implementation
type ChAttsRec prd (chs :: [(Child,[(Att,Type)])])
   = Rec (ChiReco prd) chs

-- | index type
data ChiReco (prd :: Prod)

-- | Field type
type instance  WrapField (ChiReco prd) v
  = Attribution v

-- -- | Type level Show utilities
-- type instance ShowRec (ChiReco a)     = "Children Map"
-- type instance ShowField (ChiReco a)   = "child labelled "

-- ** Pattern synonyms

-- |since now we implement ChAttsRec as a generic record, this allows us to
--   recover pattern matching
pattern EmptyCh :: ChAttsRec prd '[]
pattern EmptyCh = EmptyRec
pattern ConsCh :: (LabelSet ( '( 'Chi ch prd nt, v) ': xs)) =>
  TaggedChAttr prd ( 'Chi ch prd nt) v -> ChAttsRec prd xs
                         -> ChAttsRec prd ( '( 'Chi ch prd nt,v) ': xs)
pattern ConsCh h t = ConsRec h t

-- | Attributions tagged by a child
type TaggedChAttr prd = TagField (ChiReco prd)
pattern TaggedChAttr :: Label l -> WrapField (ChiReco prd) v
                     -> TaggedChAttr prd l v
pattern TaggedChAttr l v
  = TagField (Label :: Label (ChiReco prd)) l v


-- ** Constructors
-- | Pretty constructor for tagging a child
infixr 4 .=
(.=) :: Label l -> WrapField (ChiReco prd) v -> TaggedChAttr prd l v
(.=) = TaggedChAttr

-- | Pretty constructors
infixr 2 .*
(.*) :: Extend (ChiReco prd) ch attrib attribs => 
  TaggedChAttr prd ch attrib -> ChAttsRec prd attribs
   -> ChAttsRec prd (ExtendR (ChiReco prd) ch attrib attribs)
tch .* r = case tch of
             TaggedChAttr l (v :: Attribution attrib) -> extend l (Proxy @attrib) v r


-- | empty
emptyCh :: ChAttsRec prd '[]
emptyCh = EmptyRec

-- ** Destructors
unTaggedChAttr :: TaggedChAttr prd l v -> WrapField (ChiReco prd) v
unTaggedChAttr (TaggedChAttr _ a) = a

labelChAttr :: TaggedChAttr prd l a -> Label l
labelChAttr _ = Label

infixl 8 .#
(.#) :: Lookup (ChiReco prd) c r =>
     Rec (ChiReco prd) r -> Label c -> LookupR (ChiReco prd) c r
(chi :: Rec (ChiReco prd) r) .# (l :: Label c)
  = lookup l chi



-- * Productions

data PrdReco

type instance  WrapField PrdReco (rule :: Type)
  = rule

type Aspect (asp :: [(Prod, Type)]) = Rec PrdReco asp
-- type instance ShowRec PrdReco      = "Aspect"
-- type instance ShowField PrdReco       = "production named "


{-
  -}
