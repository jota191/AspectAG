
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

data ChiReco (prd :: Prod)
data AttReco
data Reco
data PrdReco

type instance  WrapField Reco     (v :: Type)
  = v
type instance  WrapField AttReco  (v :: Type)
  = v
type instance  WrapField (ChiReco prd)  (v :: [(k, Type)])
  = Attribution v
type instance  WrapField PrdReco (rule :: Type)
  = rule




type Aspect (asp :: [(Prod, Type)]) = Rec PrdReco asp

type Attribute        = TagField AttReco


labelChAttr :: TaggedChAttr prd l a -> Label l
labelChAttr _ = Label

type instance ShowRec (ChiReco a)  = "Children Map"
type instance ShowRec AttReco      = "Attribution"
type instance ShowRec Reco         = "Record"
type instance ShowRec PrdReco      = "Aspect"

type instance ShowField (ChiReco a)   = "child labelled "
type instance ShowField AttReco       = "attribute named "
type instance ShowField Reco          = "field named "
type instance ShowField PrdReco       = "production named "


type instance  ShowT ('Att l t)   = ShowT t :<>: Text  "::Attribute " :<>: Text l
type instance  ShowT ('Prd l nt)  = ShowT nt :<>: Text "::Production " :<>: Text l
type instance  ShowT ('Chi l p s) = ShowT p :<>:  Text "::Child " :<>: Text l 
                                     :<>:  Text ":" :<>: ShowT s
type instance  ShowT ('NT l)      = Text "Non-Terminal " :<>: Text l
type instance  ShowT ('T  l)      = Text "Terminal " :<>: ShowT l

type Tagged = TagField Reco
unTagged :: Tagged l v -> v
unTagged (TagField _ _ v) = v

pattern Tagged :: v -> Tagged l v
pattern Tagged v = TagField Label Label v

-- | Get the label of a Tagged value, restricted to the case
--when labels are a pair, for safety, since this function is used
--on that context
labelLVPair :: Tagged '(k1,k2) v -> Label '(k1,k2)
labelLVPair _ = Label

-- |Get the first member of a pair label, as a label 
sndLabel :: Label '(a,b) -> Label b
sndLabel _ = undefined

-- |Untag a value 
unTaggedChAtt :: Tagged l v -> v
unTaggedChAtt (Tagged v) = v

-- |Untag a value, different names to use on diferent contexts,
--in a future iteration possibly We'll have different Types of tag
--unTagged :: Tagged l v -> v
--unTagged (Tagged v) = v


-- | Get a label
label :: Tagged l v -> Label l
label _ = Label

-- | Same, mnemonically defined
labelTChAtt :: Tagged l v -> Label l
labelTChAtt _ = Label

-- | Pretty Constructor
infixr 4 .=.
(.=.) :: Label l -> v -> Tagged l v
l .=. v = Tagged v


-- | * Records

type Record        = Rec Reco

pattern EmptyR :: Rec Reco '[]
pattern EmptyR = EmptyRec :: Rec Reco '[]
pattern ConsR :: (LabelSet ( '(l,v ) ': xs))
  => Tagged l v -> Rec Reco xs -> Rec Reco ( '(l,v ) ': xs) 
pattern ConsR lv r = ConsRec lv r

-- ** Exported
-- | Pretty constructors
-- | For the empty Record
emptyRecord :: Record '[]
emptyRecord = EmptyR

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
--type Attribution = Rec AttrRec
type Attribution   = Rec AttReco

-- | Pattern Synonyms
pattern EmptyAtt :: Attribution '[]
pattern EmptyAtt = EmptyRec
pattern ConsAtt :: LabelSet ( '(att, val) ': atts) =>
    Attribute att val -> Attribution atts -> Attribution ( '(att,val) ': atts)
pattern ConsAtt att atts = ConsRec att atts

-- | Attribute
pattern Attribute :: v -> TagField AttReco l v
pattern Attribute v = TagField Label Label v

-- ** Pretty constructors
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

-- | Pretty lookup
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

-- | * Children
-- | Pattern synonyms, since now we implement ChAttsRec as a generic record,
-- this allows us to recover pattern matching
type ChAttsRec prd = Rec (ChiReco prd)
pattern EmptyCh :: ChAttsRec prd '[]
pattern EmptyCh = EmptyRec
pattern ConsCh :: (LabelSet ( '( 'Chi ch prd nt, v) ': xs)) =>
  TaggedChAttr prd ( 'Chi ch prd nt) v -> ChAttsRec prd xs
                         -> ChAttsRec prd ( '( 'Chi ch prd nt,v) ': xs)
pattern ConsCh h t = ConsRec h t


type TaggedChAttr prd = TagField (ChiReco prd)
pattern TaggedChAttr :: Label l -> WrapField (ChiReco prd) v
                     -> TaggedChAttr prd l v
pattern TaggedChAttr l v
  = TagField (Label :: Label (ChiReco prd)) l v

-- | Pretty constructor for tagging a child
infixr 4 .=
(.=) :: Label l -> WrapField (ChiReco prd) v -> TaggedChAttr prd l v
(.=) = TaggedChAttr

-- | To get the atribution
unTaggedChAttr :: TaggedChAttr prd l v -> WrapField (ChiReco prd) v
unTaggedChAttr (TaggedChAttr _ a) = a

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
