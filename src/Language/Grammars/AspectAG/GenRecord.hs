
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

module Language.Grammars.AspectAG.GenRecord where

import Data.Kind 
import Data.Type.Equality
import Data.Proxy
import Language.Grammars.AspectAG.TPrelude
-- import Data.Tagged hiding (unTagged)
import Language.Grammars.AspectAG.TagUtils
import GHC.TypeLits

-- * Definition 

-- | REC is a generic definition parametrized by the datatype used to build
-- fields. 
-- data REC :: forall k k'. (k -> k' -> Type) -> [(k,k')] -> Type where
--   EmptyR :: REC field '[]
--   ConsR  :: LabelSet ( '(l,v) ': r) =>
--             field l v -> REC field r -> REC field ( '(l,v) ': r)


-- * Pretty constructors

infixr 2 .*.
(.*.) :: LabelSet ( '(l, v) ': r) =>
    TagField c l v -> Rec c r -> Rec c ( '(l,v) ': r)
(.*.) = ConsRec

-- * destructors

-- | A getter, also a predicate
-- class HasField (l :: k) (r :: [(k, k')]) field where
--   type LookupByLabel field l r :: Type
--   (#) :: REC field r -> Label l -> LookupByLabel field l v


tailRec :: Rec c ( '(l,v) ': r) -> Rec c r
tailRec (ConsRec _ t) = t

data Rec (c :: k) (r :: [(k', k'')]) :: Type where
  EmptyRec :: Rec c '[]
  ConsRec  :: LabelSet ( '(l,v) ': r) =>
              TagField c l v -> Rec c r -> Rec c ( '(l,v) ': r)

data TagField (cat :: k) (l :: k') (v :: k'') where
  TagField :: Label c -> Label l -> WrapField c v -> TagField c l v

untagField :: TagField c l v -> WrapField c v
untagField (TagField lc lv v) = v

type family    WrapField (c :: k')  (v :: k) -- = ftype | ftype c -> v
type instance  WrapField Reco    (v :: Type) = v
type instance  WrapField AttReco  (v :: Type) = v
type instance  WrapField (ChiReco prd)  (v :: [(k, Type)]) = Attribution v
type instance  WrapField PrdReco  (rule :: Type) = rule

data Att   = Att Symbol Type
data Prod  = Prd Symbol NT
data Child = Chi Symbol Prod (Either NT T)
data NT    = NT Symbol
data T     = T Type

data ChiReco (prd :: Prod); data AttReco; data Reco; data PrdReco

type Attribution   = Rec AttReco
type ChAttsRec prd = Rec (ChiReco prd)
type Record        = Rec Reco

type Aspect (asp :: [(Prod, Type)]) = Rec PrdReco asp

type Attribute     = TagField AttReco
type TaggedChAttr prd = TagField (ChiReco prd)

type Tagged = TagField Reco
unTagged :: Tagged l v -> v
unTagged (TagField _ _ v) = v

pattern Tagged :: v -> Tagged l v
pattern Tagged v = TagField Label Label v

  {-Attribution, but again the injectivity problem-}
pattern TaggedChAttr :: Label l -> WrapField (ChiReco prd) v -> TaggedChAttr prd l v
pattern TaggedChAttr l v
  = TagField (Label :: Label (ChiReco prd)) l v


labelChAttr :: TaggedChAttr prd l a -> Label l
labelChAttr _ = Label

-- lookup ignorando el contexto para pegarlo directamente en Repmin con la nueva
-- implementacion



--infixl 8 .##

--(.##)
--  :: Require (OpLookup ChiReco w r) '[] =>
--     Rec ChiReco r -> Label w -> ReqR (OpLookup ChiReco w r)
--chi .## l = req (Proxy @ '[]) (OpLookup @_ @ChiReco l chi)



field1  :: TagField Reco L1 Bool
field1  =  TagField Label Label False
field2  :: TagField Reco L2 Char
field2  =  TagField Label Label '4'
data L1 
data L2
data L3
data L4
type Re = Rec Tagged
r1 = field1 `ConsRec` (field2 `ConsRec` EmptyRec)



{-
Node:
We cannot encode the dependency {ftype, c} -> v since TypeFamilyDependencies
does not support this general dependencies. So from (WrapField c v) we
can't infer c.

-}



-- class WrapFieldC (t :: Type)  (v :: k) where
--   type WrapField' t v :: Type
--   wrapfield :: WrapField' t v -> 


data OpLookup (c :: Type)
              (l  :: k)
              (r  :: [(k, k')]) :: Type where
  OpLookup :: Label l -> Rec c r -> OpLookup c l r

data OpLookup' (b  :: Bool)
               (c  :: Type)
               (l  :: k)
               (r  :: [(k, k')]) :: Type where
  OpLookup' :: Proxy b -> Label l -> Rec c r -> OpLookup' b c l r


class Require (op   :: Type)
              (ctx  :: [ErrorMessage])  where
   type ReqR op :: k
   req :: Proxy ctx -> op -> ReqR op

instance (Require (OpLookup' (l == l') c l ( '(l', v) ': r)) ctx)
  => Require (OpLookup c l ( '(l', v) ': r)) ctx where
  type ReqR (OpLookup c l ( '(l', v) ': r))
    = ReqR (OpLookup' (l == l') c l ( '(l', v) ': r))
  req ctx (OpLookup l r) = req ctx (OpLookup' (Proxy @ (l == l')) l r)

instance Require (OpLookup' 'True c l ( '(l, v) ': r)) ctx where
  type ReqR (OpLookup' 'True c l ( '(l, v) ': r)) = WrapField c v
  req Proxy (OpLookup' Proxy Label (ConsRec f _)) = untagField f

instance (Require (OpLookup c l r) ctx)
  => Require (OpLookup' False c l ( '(l', v) ': r)) ctx where
  type ReqR (OpLookup' False c l ( '(l', v) ': r)) = ReqR (OpLookup c l r)
  req ctx (OpLookup' Proxy l (ConsRec _ r)) = req ctx (OpLookup l r)

                                            


instance (TypeError (Text "Error: " :<>: m :$$:
                     Text "from context: " :<>: ShowCTX ctx))
  => Require (OpError m) ctx where {}

data OpError (m :: ErrorMessage) where {}


type family ShowCTX (ctx :: [ErrorMessage]) :: ErrorMessage where
  ShowCTX '[] = Text ""
  ShowCTX (m ': ms) = m :$$: ShowCTX ms


type family ShowEM (m :: ErrorMessage) :: ErrorMessage


instance
  Require (OpError (Text "field not Found on " :<>: Text (ShowRec c)
                     :$$: Text "looking up the " :<>: Text (ShowField c)
                           :<>: ShowT l
                          )) ctx
  => Require (OpLookup c l ( '[] :: [(k,k')])) ctx where
  type ReqR (OpLookup c l ('[] :: [(k,k')])  ) = ()
  req = undefined

type family ShowRec c :: Symbol
type instance ShowRec (ChiReco a)  = "Children Map"
type instance ShowRec AttReco      = "Attribution"
type instance ShowRec Reco         = "Record"
type instance ShowRec PrdReco      = "Aspect"

type family ShowField c :: Symbol
type instance ShowField (ChiReco a)   = "child labelled "
type instance ShowField AttReco       = "attribute named "
type instance ShowField Reco          = "field named "
type instance ShowField PrdReco       = "production named "


instance (Require (OpError (Text "field not Found on " :<>: Text (ShowRec c)
                    :$$: Text "updating the " :<>: Text (ShowField c)
                     :<>: ShowT l)) ctx)
  => Require (OpUpdate c l v '[]) ctx where 
  type ReqR (OpUpdate c l v ('[] )  ) = '[]
  req = undefined


type family ShowT (t :: k) :: ErrorMessage  where
  ShowT ('Att l t)   = ShowT t :<>: Text  "::Attribute " :<>: Text l
  ShowT ('Prd l nt)  = ShowT nt :<>: Text "::Production " :<>: Text l
  ShowT ('Chi l p s) = ShowT p :<>:  Text "::Child " :<>: Text l 
                                     :<>:  Text ":" :<>: ShowT s
  ShowT ('NT l)      = Text "Non-Terminal " :<>: Text l
  ShowT ('T  l)      = Text "Terminal " :<>: ShowT l
  ShowT t            = ShowType t



  
-- | update

data OpUpdate (c  :: Type)
              (l  :: k)
              (v  :: k')
              (r  :: [(k, k')]) :: Type where
  OpUpdate :: Label l -> WrapField c v -> Rec c r
           -> OpUpdate c l v r

data OpUpdate' (b  :: Bool)
               (c  :: Type)
               (l  :: k)
               (v  :: k')
               (r  :: [(k, k')]) :: Type where
  OpUpdate' :: Proxy p -> Label l -> WrapField c v ->  Rec c r
           -> OpUpdate' b c l v r

{- Look at the comment above, WrapField c v is not enough to recover
v, that's why we use an extra proxy

update: Instead of the proxy, I use TypeApplications below

-}

instance (Require (OpUpdate' (l == l') c l v ( '(l', v') ': r) ) ctx )
  => Require (OpUpdate c l v ( '(l', v') ': r) ) ctx where
  type ReqR (OpUpdate c l v ( '(l', v') ': r) )
    = ReqR (OpUpdate' (l == l') c l v ( '(l', v') ': r) )
  req ctx (OpUpdate l f r)
    = (req @(OpUpdate' (l == l') _ _ v _ )) -- v is explicity instantiated 
       ctx (OpUpdate' (Proxy @(l == l')) l f r)


instance ( LabelSet ( '(l, v) ': r)
         , LabelSet ( '(l, v') ': r))
  => Require (OpUpdate' 'True c l v ( '(l, v') ': r)) ctx where
  type ReqR (OpUpdate' 'True c l v ( '(l, v') ': r))
    = Rec c ( '(l, v) ': r)
  req ctx (OpUpdate' proxy label field (ConsRec tgf r))
    = ConsRec (TagField Label label field) r

-- instance ( Require (OpUpdate c l v r) ctx
--          , ConsFam l' v' (ReqR (OpUpdate c l v r)) ~ Rec c ( '(l', v') : r0)
--          , ReqR (OpUpdate c l v r) ~ Rec c r0
--          , LabelSet ( '(l', v') : r0)
--          )
--   => Require (OpUpdate' 'False c l v ( '(l',v') ': r)) ctx where
--   type ReqR (OpUpdate' 'False c l v ( '(l',v') ': r))
--     = ConsFam l' v' (ReqR (OpUpdate c l v r))
--   req ctx (OpUpdate' _ l f (ConsRec field r))
--     = ConsRec field $ (req @(OpUpdate _ _ v r)) ctx (OpUpdate l f r)

{- to manipulate cons at type level in a generic way -}
---type family ConsFam (l :: k) (v :: k') r
---type instance ConsFam l v (Rec c r) = Rec c ( '(l,v) ': r)


instance ( Require (OpUpdate c l v r) ctx
         , UnWrap (ReqR (OpUpdate c l v r)) ~ r0
         , LabelSet ( '(l', v') : r0)
         , ReqR (OpUpdate c l v r) ~ Rec c r0)
  => Require (OpUpdate' 'False c l v ( '(l',v') ': r)) ctx where
  type ReqR (OpUpdate' 'False c l v ( '(l',v') ': r))
    = Rec c ( '(l',v') ': (UnWrap (ReqR (OpUpdate c l v r))))
  req ctx (OpUpdate' _ l f (ConsRec field r))
    = ConsRec field $ (req @(OpUpdate _ _ v r)) ctx (OpUpdate l f r)



type family UnWrap t :: [(k,k')]
type instance UnWrap (Rec c r) = r



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


data OpExtend (c :: Type)
              (l  :: k)
              (v  :: k')
              (r  :: [(k, k')]) :: Type where
  OpExtend :: Label l -> WrapField c v -> Rec c r
           -> OpExtend c l v r

data OpExtend' (b :: Bool)
               (c :: Type)
               (l  :: k)
               (v  :: k')
               (r  :: [(k, k')]) :: Type where
  OpExtend' :: Proxy b -> Label l -> WrapField c v -> Rec c r
           -> OpExtend' b c l v r


instance (LabelSetF ( '(l, v) ': r) ~ 'True)
  => Require (OpExtend' True  c l v r) ctx where
  type ReqR (OpExtend' True c l v r) = Rec c ( '(l, v) ': r)
  req ctx (OpExtend' _ l f r) = ConsRec (TagField (Label @c) l f) r


instance ( LabelSetF ( '(l, v) ':  r) ~ b
         , Require (OpExtend' b c l v r) ctx)
  => Require (OpExtend c l v r) ctx where
  type ReqR (OpExtend c l v r)
    = ReqR (OpExtend' (LabelSetF ( '(l, v) ': r)) c l v r)
  req ctx (OpExtend l v r)
    = req @(OpExtend' (LabelSetF ( '(l, v) ': r)) _ _ v _ )
      ctx (OpExtend' Proxy l v r) 

instance Require (OpError (Text "Duplicated Labels on " :<>: Text (ShowRec c)
                          :$$: Text "on the " :<>: Text (ShowField c)
                           :<>: ShowT l
                          )) ctx
  => Require (OpExtend' False c l v (r :: [(k, k')])) ctx where
  type ReqR (OpExtend' False c l v r) = Rec c (r :: [(k, k')])
  req ctx (OpExtend' p l v r) = undefined


lookupCtx'
  :: Require (OpLookup c w r) ctx =>
     Proxy ctx -> Rec c r -> Label w -> ReqR (OpLookup c w r)
lookupCtx' (p :: Proxy ctx) chi l = req p (OpLookup @_ l chi)



type family HasLabel (l :: k) (r :: [(k, k')]) :: Bool where
  HasLabel l '[] = False
  HasLabel l ( '(l', v) ': r) = Or (l == l') (HasLabel l r)



