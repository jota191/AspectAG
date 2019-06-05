
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
import Language.Grammars.AspectAG.Require

import GHC.TypeLits



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

{-
Node:
We cannot encode the dependency {ftype, c} -> v since TypeFamilyDependencies
does not support this general dependencies. So from (WrapField c v) we
can't infer c.

-}


data OpLookup (c :: Type)
              (l  :: k)
              (r  :: [(k, k')]) :: Type where
  OpLookup :: Label l -> Rec c r -> OpLookup c l r

data OpLookup' (b  :: Bool)
               (c  :: Type)
               (l  :: k)
               (r  :: [(k, k')]) :: Type where
  OpLookup' :: Proxy b -> Label l -> Rec c r -> OpLookup' b c l r




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




instance
  Require (OpError (Text "field not Found on " :<>: Text (ShowRec c)
                     :$$: Text "looking up the " :<>: Text (ShowField c)
                           :<>: ShowT l
                          )) ctx
  => Require (OpLookup c l ( '[] :: [(k,k')])) ctx where
  type ReqR (OpLookup c l ('[] :: [(k,k')])  ) = ()
  req = undefined

type family ShowRec c :: Symbol
type family ShowField c :: Symbol

instance (Require (OpError (Text "field not Found on " :<>: Text (ShowRec c)
                    :$$: Text "updating the " :<>: Text (ShowField c)
                     :<>: ShowT l)) ctx)
  => Require (OpUpdate c l v '[]) ctx where
  type ReqR (OpUpdate c l v ('[] )  ) = Rec c '[]
  req = undefined

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


instance (Require (OpUpdate' (l == l') c l v ( '(l', v') ': r) ) ctx )
  => Require (OpUpdate c l v ( '(l', v') ': r) ) ctx where
  type ReqR (OpUpdate c l v ( '(l', v') ': r) )
    = ReqR (OpUpdate' (l == l') c l v ( '(l', v') ': r) )
  req ctx (OpUpdate l f r)
    = (req @(OpUpdate' (l == l') _ _ v _ ))
       ctx (OpUpdate' (Proxy @(l == l')) l f r)


instance ( LabelSet ( '(l, v) ': r)
         , LabelSet ( '(l, v') ': r))
  => Require (OpUpdate' 'True c l v ( '(l, v') ': r)) ctx where
  type ReqR (OpUpdate' 'True c l v ( '(l, v') ': r))
    = Rec c ( '(l, v) ': r)
  req ctx (OpUpdate' proxy label field (ConsRec tgf r))
    = ConsRec (TagField Label label field) r


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



data OpNonEmpty (c :: Type) (r :: [(k, k')]) where
  OpNonEmpty :: Rec c r -> OpNonEmpty c r


instance Require (OpNonEmpty c ( '(l, v) ': r)) ctx where
  type ReqR (OpNonEmpty c ( '(l, v) ': r)) = ()
  req = undefined
