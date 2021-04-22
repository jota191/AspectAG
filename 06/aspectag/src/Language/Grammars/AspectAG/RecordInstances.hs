
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
             PatternSynonyms,
             PartialTypeSignatures
#-}

module Language.Grammars.AspectAG.RecordInstances where

import Data.Type.Require
import Data.GenRec
import GHC.TypeLits
import Data.Kind
import Data.Proxy

data Att   = Att Symbol Type                -- deriving Eq
data Prod  = Prd Symbol NT                  -- deriving Eq
data Child = Chi Symbol Prod (Either NT T)  -- deriving Eq
data NT    = NT Symbol                      -- deriving Eq
data T     = T Type                         -- deriving Eq

prdFromChi :: Label (Chi nam prd tnt) -> Label prd
prdFromChi _ = Label


instance OrdType Att where
   type Cmp ('Att a _) ('Att b _)
     = CmpSymbol a b

instance OrdType Prod where 
  type Cmp ('Prd a _) ('Prd b _)
    = CmpSymbol a b

instance OrdType Child where
  type Cmp ('Chi a _ _) ('Chi b _ _) = CmpSymbol a b


type instance  ShowTE ('Att l t)   =
  Text "(" :<>:
  Text l   :<>:
  Text ":" :<>:
  ShowTE t :<>:
  Text ")"
type instance  ShowTE ('Prd l nt)  =
  Text "(" :<>:
  Text l   :<>:
  Text " of " :<>:
  ShowTE nt :<>:
  Text ")"

type instance  ShowTE ('Chi l p s) =
  Text "Child " :<>:
  Text l  :<>:
  Text " of producion " :<>:
  ShowTE p
  
type instance  ShowTE ('Left l)    = ShowTE l
type instance  ShowTE ('Right r)   = ShowTE r
type instance  ShowTE ('NT l)      = Text "Non-Terminal " :<>: Text l
type instance  ShowTE ('T  l)      = Text "Terminal " :<>: ShowTE l

type instance ShowLabel l = FromEM (ShowTE l)

-- | * Records

-- | datatype definition
type Record        = Rec Reco

-- | index type
data Reco

-- | field type
type instance  WrapField Reco     (v :: Type) = v

-- | Type level show utilities
type instance ShowRec Reco         = "Record"
type instance ShowField Reco       = "field"


type Tagged = TagField Reco
pattern Tagged :: v -> Tagged l v
pattern Tagged v = TagField Label Label v


-- ** Constructors

-- -- | Pretty Constructor
-- infixr 4 .=.
-- (.=.) :: Label l -> v -> Tagged l v
-- l .=. v = Tagged v

-- -- | For the empty Record
-- emptyRecord :: Record '[]
-- emptyRecord = EmptyRec

-- unTagged :: Tagged l v -> v
-- unTagged (TagField _ _ v) = v

-- -- * Destructors
-- -- | Get a label
-- label :: Tagged l v -> Label l
-- label _ = Label

-- -- | Same, mnemonically defined
-- labelTChAtt :: Tagged l v -> Label l
-- labelTChAtt _ = Label


-- -- | Show instance, used for debugging
-- instance Show (Record '[]) where
--   show _ = "{}"

-- instance (Show v, Show (Record xs)) =>
--          Show (Record ( '(l,v) ': xs ) ) where
--   show (ConsRec lv xs) = let tail = show xs
--                          in "{" ++ show (unTagged lv)
--                             ++ "," ++ drop 1 tail



-- | * Attribution
-- | An attribution is a record constructed from attributes

-- | datatype implementation
type Attribution (attr :: [(Att,Type)]) =  Rec AttReco attr

-- | index type
data AttReco

-- | field type
type instance  WrapField AttReco  (v :: Type) = v

-- | type level utilities
type instance ShowRec AttReco      = "Attribution"
type instance ShowField AttReco       = "attribute"

-- | Pattern Synonyms
-- pattern EmptyAtt :: Attribution '[]
-- pattern EmptyAtt = EmptyRec
-- pattern ConsAtt :: LabelSet ( '(att, val) ': atts) =>
--     Attribute att val -> Attribution atts -> Attribution ( '(att,val) ': atts)
-- pattern ConsAtt att atts = ConsRec att atts

-- | Attribute

type Attribute (l :: Att) (v :: Type) = TagField AttReco l v
pattern Attribute :: v -> TagField AttReco l v
pattern Attribute v = TagField Label Label v

-- ** Constructors
-- | Apretty constructor for an attribute 
infixr 4 =.

(=.) :: Label l -> v -> Attribute l v
Label =. v = Attribute v


-- | Extending
infixr 2 *.
-- (*.) :: Attribute att val -> Attribution atts
--       -> Attribution (ReqR (OpExtend AttReco att val atts) ctx)
(l :: Attribute att val) *. (r :: Attribution atts) = l .*. r

-- | Empty
emptyAtt :: Attribution '[]
emptyAtt = EmptyRec

-- ** Destructors
infixl 7 #.

(#.) ::
  ( msg ~ '[Text "looking up attribute " :<>: ShowTE l :$$:
            Text "on " :<>: ShowTE r
           ]
  , Require (OpLookup AttReco l r) msg
  )
  => Attribution r -> Label l -> ReqR (OpLookup AttReco l r)
(attr :: Attribution r) #. (l :: Label l)
  = let prctx = Proxy @ '[Text "looking up attribute " :<>: ShowTE l :$$:
                          Text "on " :<>: ShowTE r
                         ]
    in req prctx (OpLookup @_ @(AttReco) l attr)


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

-- | Type level Show utilities
type instance ShowRec (ChiReco a)     = "Children Map"
type instance ShowField (ChiReco a)   = "child labelled "

-- ** Pattern synonyms

-- |since now we implement ChAttsRec as a generic record, this allows us to
--   recover pattern matching
-- pattern EmptyCh :: ChAttsRec prd '[]
-- pattern EmptyCh = EmptyRec
-- pattern ConsCh :: (LabelSet ( '( 'Chi ch prd nt, v) ': xs)) =>
--   TaggedChAttr prd ( 'Chi ch prd nt) v -> ChAttsRec prd xs
--                          -> ChAttsRec prd ( '( 'Chi ch prd nt,v) ': xs)
-- pattern ConsCh h t = ConsRec h t

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
(tch :: TaggedChAttr prd ch attrib) .* (chs :: ChAttsRec prd attribs) = tch .*. chs
-- TODO: error instances if different prds are used?

-- | empty
emptyCh :: ChAttsRec prd '[]
emptyCh = EmptyRec

-- ** Destructors
unTaggedChAttr :: TaggedChAttr prd l v -> WrapField (ChiReco prd) v
unTaggedChAttr (TaggedChAttr _ a) = a

labelChAttr :: TaggedChAttr prd l a -> Label l
labelChAttr _ = Label

infixl 8 .#
(.#) ::
  (  c ~ ('Chi ch prd nt)
  ,  ctx ~ '[Text "looking up " :<>: ShowTE c :$$:
            Text "on " :<>: ShowTE r :$$:
            Text "producion: " :<>: ShowTE prd
           ]
  , Require (OpLookup (ChiReco prd) c r) ctx
  ) =>
     Rec (ChiReco prd) r -> Label c -> ReqR (OpLookup (ChiReco prd) c r)
(chi :: Rec (ChiReco prd) r) .# (l :: Label c)
  = let prctx = Proxy @ '[Text "looking up " :<>: ShowTE c :$$:
                          Text "on " :<>: ShowTE r :$$:
                          Text "producion: " :<>: ShowTE prd
                         ]
    in req prctx (OpLookup @_ @(ChiReco prd) l chi)



-- * Productions

data PrdReco

type instance  WrapField PrdReco (rule :: Type)
  = rule

type Aspect (asp :: [(Prod, Type)]) = Rec PrdReco asp
type instance ShowRec PrdReco       = "Aspect"
type instance ShowField PrdReco     = "production named "
