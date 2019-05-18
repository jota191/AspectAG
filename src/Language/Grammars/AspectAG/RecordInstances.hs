
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

module Language.Grammars.AspectAG.RecordInstances where

import Language.Grammars.AspectAG.Require
import Language.Grammars.AspectAG.GenRecord
import Language.Grammars.AspectAG.TPrelude
import GHC.TypeLits
import Data.Kind
import Data.Proxy

data Att   = Att Symbol Type
data Prod  = Prd Symbol NT
data Child = Chi Symbol Prod (Either NT T)
data NT    = NT Symbol
data T     = T Type




type instance  ShowT ('Att l t)   = Text  "Attribute " :<>: Text l
                                                       :<>: Text ":"
                                                       :<>: ShowT t 
type instance  ShowT ('Prd l nt)  = ShowT nt :<>: Text "::Production "
                                             :<>: Text l
type instance  ShowT ('Chi l p s) = ShowT p :<>:  Text "::Child " :<>: Text l 
                                            :<>:  Text ":" :<>: ShowT s
type instance  ShowT ('Left l)    = ShowT l
type instance  ShowT ('Right r)   = ShowT r
type instance  ShowT ('NT l)      = Text "Non-Terminal " :<>: Text l
type instance  ShowT ('T  l)      = Text "Terminal " :<>: ShowT l



-- | * Records

-- | datatype definition
type Record        = Rec Reco

-- | index type
data Reco

-- | field type
type instance  WrapField Reco     (v :: Type) = v

-- | Type level show utilities
type instance ShowRec Reco         = "Record"
type instance ShowField Reco       = "field named "



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
type Attribution   = Rec AttReco

-- | index type
data AttReco

-- | field type
type instance  WrapField AttReco  (v :: Type) = v

-- | type level utilities
type instance ShowRec AttReco      = "Attribution"
type instance ShowField AttReco       = "attribute named "

-- | Pattern Synonyms
pattern EmptyAtt :: Attribution '[]
pattern EmptyAtt = EmptyRec
pattern ConsAtt :: LabelSet ( '(att, val) ': atts) =>
    Attribute att val -> Attribution atts -> Attribution ( '(att,val) ': atts)
pattern ConsAtt att atts = ConsRec att atts

-- | Attribute

type Attribute        = TagField AttReco
pattern Attribute :: v -> TagField AttReco l v
pattern Attribute v = TagField Label Label v

-- ** Constructors
-- | Apretty constructor for an attribute 
infixr 4 =.

(=.) :: Label l -> v -> Attribute l v
Label =. v = Attribute v


-- | Extending
infixr 2 *.
(*.) :: LabelSet ('(att, val) : atts) =>
    Attribute att val -> Attribution atts
      -> Attribution ('(att, val) : atts)
(*.) = ConsRec

-- | Empty
emptyAtt :: Attribution '[]
emptyAtt = EmptyRec

-- ** Destructors
infixl 7 #.

(#.) ::
  ( msg ~ '[Text "looking up attribute " :<>: ShowT l :$$:
            Text "on " :<>: ShowT r
           ]
  , Require (OpLookup AttReco l r) msg
  )
  => Rec AttReco r -> Label l -> ReqR (OpLookup AttReco l r)
(attr :: Attribution r) #. (l :: Label l)
  = let prctx = Proxy @ '[Text "looking up attribute " :<>: ShowT l :$$:
                          Text "on " :<>: ShowT r
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
type instance  WrapField (ChiReco prd)  (v :: [(k, Type)])
  = Attribution v

-- | Type level Show utilities
type instance ShowRec (ChiReco a)     = "Children Map"
type instance ShowField (ChiReco a)   = "child labelled "

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
(.*) :: LabelSet ('(ch, attrib) ':  attribs) =>
  TaggedChAttr prd ch attrib -> ChAttsRec prd attribs
    -> ChAttsRec prd ('(ch, attrib) ': attribs)
(.*) = ConsRec

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
  ,  ctx ~ '[Text "looking up " :<>: ShowT c :$$:
            Text "on " :<>: ShowT r :$$:
            Text "producion: " :<>: ShowT prd
           ]
  , Require (OpLookup (ChiReco prd) c r) ctx
  ) =>
     Rec (ChiReco prd) r -> Label c -> ReqR (OpLookup (ChiReco prd) c r)
(chi :: Rec (ChiReco prd) r) .# (l :: Label c)
  = let prctx = Proxy @ '[Text "looking up " :<>: ShowT c :$$:
                          Text "on " :<>: ShowT r :$$:
                          Text "producion: " :<>: ShowT prd
                         ]
    in req prctx (OpLookup @_ @(ChiReco prd) l chi)



-- * Productions

data PrdReco

type instance  WrapField PrdReco (rule :: Type)
  = rule

type Aspect (asp :: [(Prod, Type)]) = Rec PrdReco asp
type instance ShowRec PrdReco      = "Aspect"
type instance ShowField PrdReco       = "production named "
