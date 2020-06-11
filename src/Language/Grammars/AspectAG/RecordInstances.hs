
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
             PartialTypeSignatures,
             TemplateHaskell,
             InstanceSigs,
             EmptyCase
#-}

module Language.Grammars.AspectAG.RecordInstances where

import Data.GenRec
import Data.Type.Require
import GHC.TypeLits
import Data.Kind
import Data.Proxy
import GHC.TypeLits
import Data.Type.Bool
-- import Data.Type.Equality
import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.Ord
import Data.Singletons.Prelude.Eq
import Data.Singletons.CustomStar

data Att   = Att Symbol Type               -- deriving Eq
data Prod  = Prd Symbol NT                  -- deriving Eq
data Child = Chi Symbol Prod (Either NT T)  -- deriving Eq
data NT    = NT Symbol                      -- deriving Eq
data T     = T Type                         -- deriving Eq

prdFromChi :: Sing (Chi nam prd tnt) -> Sing prd
prdFromChi _ = undefined -- Label

data instance Sing (att :: Att) where
  SAtt :: Sing s -> Sing t ->  Sing ('Att s t)
data instance Sing (prod :: Prod) where
  SPrd :: Sing s -> Sing nt -> Sing ('Prd s nt)
data instance Sing (child :: Child) where
  SChi :: Sing s -> Sing prd -> Sing (tnt :: Either NT T)
       -> Sing ('Chi s prd tnt)
data instance Sing (nt :: NT) where
  SNT :: Sing s -> Sing ('NT s)
data instance Sing (nt :: T) where
  ST :: Sing t -> Sing ('T t)


$(singletonStar [''Bool, ''Maybe, ''Either, ''Char, ''Int])
$(singEqInstances [''Att, ''Prod, ''Child, ''NT, ''T])
$(singOrdInstances [''Att, ''Prod, ''Child, ''NT, ''T])



type instance  ShowTE ('Att l t)   = Text  "Attribute " :<>: Text l
                                                        :<>: Text ":"
                                                        :<>: ShowTE t 
type instance  ShowTE ('Prd l nt)  = ShowTE nt :<>: Text "::Production "
                                              :<>: Text l
type instance  ShowTE ('Chi l p s) = ShowTE p :<>:  Text "::Child " :<>: Text l 
                                            :<>:  Text ":" :<>: ShowTE s
type instance  ShowTE ('Left l)    = ShowTE l
type instance  ShowTE ('Right r)   = ShowTE r
type instance  ShowTE ('NT l)      = Text "Non-Terminal " :<>: Text l
type instance  ShowTE ('T  l)      = Text "Terminal " :<>: ShowTE l



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



-- ** Constructors

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
type instance ShowField AttReco       = "attribute named "

-- | Pattern Synonyms
-- pattern EmptyAtt :: Attribution '[]
-- pattern EmptyAtt = EmptyRec
-- pattern ConsAtt :: LabelSet ( '(att, val) ': atts) =>
--     Attribute att val -> Attribution atts -> Attribution ( '(att,val) ': atts)
-- pattern ConsAtt att atts = ConsRec att atts

-- | Attribute

type Attribute (l :: Att) (v :: Type) = TagField AttReco l v
--pattern Attribute :: v -> TagField AttReco l v
--pattern Attribute v = TagField Proxy (SAtt SSym undefined) v

-- ** Constructors
-- | Apretty constructor for an attribute 
infixr 4 =.

(=.) :: Sing l -> v -> Attribute l v
sing =. v = TagField Proxy sing v


{-

before: 
(*.)
  :: Attribute att val -> Attribution atts
     -> Attribution (ReqR (OpExtend AttReco att val atts) ctx)

after:
(*.)
  :: Attribute att val
     -> Attribution atts -> Rec AttReco (Extend AttReco att val atts)
λ>

-}

-- | Extending
infixr 2 *.
-- (*.) :: Attribute att val -> Attribution atts
--       -> Attribution (ReqR (OpExtend AttReco att val atts) ctx)
(l :: Attribute att val) *. (r :: Attribution atts) = l .*. r

-- | Empty
emptyAtt :: Attribution '[]
emptyAtt = EmptyRec

-- -- ** Destructors
infixl 7 #.
(attr :: Attribution r) #. (l :: Label l) =
  attr # l




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

-- -- ** Pattern synonyms

-- -- |since now we implement ChAttsRec as a generic record, this allows us to
-- --   recover pattern matching
-- -- pattern EmptyCh :: ChAttsRec prd '[]
-- -- pattern EmptyCh = EmptyRec
-- -- pattern ConsCh :: (LabelSet ( '( 'Chi ch prd nt, v) ': xs)) =>
-- --   TaggedChAttr prd ( 'Chi ch prd nt) v -> ChAttsRec prd xs
-- --                          -> ChAttsRec prd ( '( 'Chi ch prd nt,v) ': xs)
-- -- pattern ConsCh h t = ConsRec h t

-- -- | Attributions tagged by a child
type TaggedChAttr prd = TagField (ChiReco prd)
pattern TaggedChAttr :: Sing l -> WrapField (ChiReco prd) v
                     -> TaggedChAttr prd l v
pattern TaggedChAttr l v
  = TagField (Proxy :: Proxy (ChiReco prd)) l v


-- -- ** Constructors
-- -- | Pretty constructor for tagging a child
infixr 4 .=
(.=) :: Sing l -> WrapField (ChiReco prd) v -> TaggedChAttr prd l v
(.=) = TaggedChAttr

-- -- | Pretty constructors
infixr 2 .*
(tch :: TaggedChAttr prd ch attrib) .* (chs :: ChAttsRec prd attribs) = tch .*. chs
-- -- TODO: error instances if different prds are used?

-- -- | empty
emptyCh :: ChAttsRec prd '[]
emptyCh = EmptyRec

-- -- ** Destructors
unTaggedChAttr :: TaggedChAttr prd l v -> WrapField (ChiReco prd) v
unTaggedChAttr (TaggedChAttr _ a) = a

labelChAttr :: TaggedChAttr prd ('Chi s p tnt) a -> Sing ('Chi s p tnt)
labelChAttr (TagField proxy s _)= s

-- infixl 8 .#
-- (.#) ::
--   (  c ~ ('Chi ch prd nt)
--   ,  ctx ~ '[Text "looking up " :<>: ShowTE c :$$:
--             Text "on " :<>: ShowTE r :$$:
--             Text "producion: " :<>: ShowTE prd
--            ]
--   , Require (OpLookup (ChiReco prd) c r) ctx
--   ) =>
--      Rec (ChiReco prd) r -> Label c -> ReqR (OpLookup (ChiReco prd) c r)
(chi :: Rec (ChiReco prd) r) .# (l :: Label c) =
  chi # l

--   = let prctx = Proxy @ '[Text "looking up " :<>: ShowTE c :$$:
--                           Text "on " :<>: ShowTE r :$$:
--                           Text "producion: " :<>: ShowTE prd
--                          ]
--     in req prctx (OpLookup @_ @(ChiReco prd) l chi)



-- -- * Productions

data PrdReco

type instance  WrapField PrdReco (rule :: Type) = rule

type Aspect (asp :: [(Prod, Type)]) = Rec PrdReco asp
type instance ShowRec PrdReco       = "Aspect"
type instance ShowField PrdReco     = "production named "
