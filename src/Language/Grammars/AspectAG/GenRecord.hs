{-|
Module      : Language.Grammars.AspectAG.GenRecord
Description : Record library, this will be eventually forked out
              from AAG codebase and used as a standalone library, depending on it
Copyright   : (c) Juan García Garland, Marcos Viera, 2019
License     : GPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX
-}

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
import Data.Proxy
import Language.Grammars.AspectAG.Label
import Language.Grammars.AspectAG.Require
import Language.Grammars.AspectAG.TPrelude (LabelSet)

import GHC.TypeLits


type family a == b where
  a == b = Equal a b


-- | Record data structure for generic records (Internal). The `c`
-- index indicates the kind of record (for each record instance, the
-- user should define an index). The `r` index represents the mapping
-- from labels to values.  Labels are of kind `k'`. Values are still
-- polykinded (`k''`) since rich information can be statically
-- represented here (for instance, when a record of records, or a
-- record of Vectors is represented).  `k'` must implement the 'CMP'
-- family, although it is not visible here for simplicity. Records are
-- built putting fields ordered according to the `CMP` result of its
-- labels. __This is not intended to be used to build records__

data Rec (c :: k) (r :: [(k', k'')]) :: Type where
  EmptyRec :: Rec c '[] -- ^ empty record
  ConsRec :: TagField c l v -> Rec c r -> Rec c ('( l, v) ': r) -- ^ `ConsRec`
-- takes a field (`TagField`) and a 

-- | doc: comentar diseño, y falta de LabelSet
data TagField (cat :: k) (l :: k') (v :: k'') where
  TagField :: Label c -> Label l -> WrapField c v -> TagField c l v

-- | operator
-- (l :: Label l) .=. (v :: v) = TagField Label l v

type family  WrapField (c :: k')  (v :: k)

type family UnWrap (t :: Type) :: [(k,k')]
type instance UnWrap (Rec c (r :: [(k, k')])) = (r :: [(k, k')])

-- emptyRecord = EmptyRec

untagField :: TagField c l v -> WrapField c v
untagField (TagField lc lv v) = v

-- | comparisson of Labels, this family is polykinded, each record-like
-- structure must implement this family for labels
type family Cmp (a :: k) (b :: k) :: Ordering

-- | Instance for Symbols
type instance Cmp (a :: Symbol) (b :: Symbol) = CmpSymbol a b


-- | Function to show the name of records (Record, Mapping, etc):
type family ShowRec c :: Symbol

-- | Function to show the field of the record ("field named", "children", "tag:", etc)
type family ShowField c :: Symbol


-- * Operations

-- ** Lookup

-- | Datatype for lookup (wrapper)
data OpLookup (c :: Type)
              (l :: k)
              (r :: [(k, k')]) :: Type where
  OpLookup :: Label l -> Rec c r -> OpLookup c l r

-- | Datatype for lookup (internal)
data OpLookup' (b  :: Ordering)
               (c  :: Type)
               (l  :: k)
               (r  :: [(k, k')]) :: Type where
  OpLookup' :: Proxy b -> Label l -> Rec c r -> OpLookup' b c l r

-- | wrapper instance
instance
  Require (OpLookup' (Cmp l l') c l ('( l', v) ': r)) ctx
  =>
  Require (OpLookup c l ('( l', v) ': r)) ctx where
  type ReqR (OpLookup c l ('( l', v) ': r)) =
    ReqR (OpLookup' (Cmp l l') c l ('( l', v) ': r))
  req ctx (OpLookup l r) =
    req ctx (OpLookup' (Proxy @(Cmp l l')) l r)

-- | error instance (looking up an empty record)
instance
  Require (OpError (Text "field not Found on " :<>: Text (ShowRec c)
                     :$$: Text "looking up the " :<>: Text (ShowField c)
                           :<>: Text " " :<>: ShowT l
                          )) ctx
  =>
  Require (OpLookup c l ( '[] :: [(k,k')])) ctx where
  type ReqR (OpLookup c l ('[] :: [(k,k')])  ) = ()
  req = undefined

-- | label found!
instance
  Require (OpLookup' 'EQ c l ( '(l, v) ': r)) ctx where
  type ReqR (OpLookup' 'EQ c l ( '(l, v) ': r)) =
    WrapField c v
  req Proxy (OpLookup' Proxy Label (ConsRec f _)) =
    untagField f

-- | label not {yet} found
instance (Require (OpLookup c l r) ctx)
  =>
  Require (OpLookup' 'GT c l ( '(l', v) ': r)) ctx where
  type ReqR (OpLookup' 'GT c l ( '(l', v) ': r)) =
    ReqR (OpLookup c l r)
  req ctx (OpLookup' Proxy l (ConsRec _ r)) =
    req ctx (OpLookup l r)

-- | ERROR, we are beyond the supposed position for the label |l|,
-- so we can assert there is no field labelled |l|
-- (ot the record is ill-formed)
instance Require (OpError (Text "field not Found on " :<>: Text (ShowRec c)
                     :$$: Text "looking up the " :<>: Text (ShowField c)
                           :<>: Text " " :<>: ShowT l
                          )) ctx
  =>
  Require (OpLookup' 'LT c l ( '(l', v) ': r)) ctx where
  type ReqR (OpLookup' 'LT  c l ( '(l', v) ': r)) = ()
  req ctx (OpLookup' Proxy l (ConsRec _ r)) = ()

-- | Pretty lookup
(#) :: RequireR (OpLookup c l r) '[] v =>
  Rec c r -> Label l -> v
r # l = req (Proxy @ '[]) (OpLookup l r)


-- ** update

-- | update operator (wrapper)
data OpUpdate (c  :: Type)
              (l  :: k)
              (v  :: k')
              (r  :: [(k, k')]) :: Type where
  OpUpdate :: Label l -> WrapField c v -> Rec c r
           -> OpUpdate c l v r

-- | update operator (internal)
data OpUpdate' (b  :: Ordering)
               (c  :: Type)
               (l  :: k)
               (v  :: k')
               (r  :: [(k, k')]) :: Type where
  OpUpdate' :: Proxy b -> Label l -> WrapField c v ->  Rec c r
           -> OpUpdate' b c l v r

-- | wrapper instance
instance (Require (OpUpdate' (Cmp l l') c l v ( '(l', v') ': r) ) ctx )
  =>
  Require (OpUpdate c l v ( '(l', v') ': r) ) ctx where
  type ReqR (OpUpdate c l v ( '(l', v') ': r) ) =
    ReqR (OpUpdate' (Cmp l l') c l v ( '(l', v') ': r) )
  req ctx (OpUpdate l f r) =
    (req @(OpUpdate' (Cmp l l') _ _ v _ ))
      ctx (OpUpdate' (Proxy @(Cmp l l')) l f r)

-- | error instance
instance (Require (OpError (Text "field not Found on " :<>: Text (ShowRec c)
                    :$$: Text "updating the " :<>: Text (ShowField c)
                     :<>: ShowT l)) ctx)
  =>
  Require (OpUpdate c l v '[]) ctx where
  type ReqR (OpUpdate c l v ('[] )  ) = Rec c '[]
  req = undefined

-- | label found
instance 
  Require (OpUpdate' 'EQ c l v ( '(l, v') ': r)) ctx where
  type ReqR (OpUpdate' 'EQ c l v ( '(l, v') ': r)) =
    Rec c ( '(l, v) ': r)
  req ctx (OpUpdate' proxy label field (ConsRec tgf r)) =
    ConsRec (TagField Label label field) r

instance
  ( Require (OpUpdate c l v r) ctx
  , ( '(l', v') : r0)  ~ a -- only to unify kinds
  , ReqR (OpUpdate c l v r) ~ Rec c r0
  )
   =>
  Require (OpUpdate' 'GT c l v ( '(l',v') ': r)) ctx where
  type ReqR (OpUpdate' 'GT c l v ( '(l',v') ': r)) =
    Rec c ( '(l',v') ': (UnWrap (ReqR (OpUpdate c l v r))))
  req ctx (OpUpdate' _ l f (ConsRec field (r :: Rec c r))) =
    ConsRec field $ (req @(OpUpdate _ _ v r)) ctx (OpUpdate l f r)

-- | ERROR, we are beyond the supposed position for the label |l|,
-- so we can assert there is no field labelled with |l| to update
-- (or the record is ill-formed)
instance (Require (OpError (Text "field not Found on " :<>: Text (ShowRec c)
                    :$$: Text "updating the " :<>: Text (ShowField c)
                     :<>: ShowT l)) ctx)
  =>
  Require (OpUpdate' 'LT c l v ( '(l',v') ': r)) ctx where
  type ReqR (OpUpdate' 'LT c l v ( '(l',v') ': r)) =
    ()
  req = undefined


update (l :: Label l) (v :: v) (r :: Rec c r) =
  req Proxy (OpUpdate @l @c @v @r l v r)


-- ** Extension

-- | extension operator (wrapper)
data OpExtend (c :: Type)
              (l  :: k)
              (v  :: k')
              (r  :: [(k, k')]) :: Type where
  OpExtend :: Label l -> WrapField c v -> Rec c r
           -> OpExtend c l v r

-- | Extension operator (inner)
data OpExtend' (b   :: Ordering)
               (c   :: Type)
               (l   :: k)
               (v   :: k')
               (r   :: [(k, k')]) :: Type where
  OpExtend' :: Proxy b -> Label l -> WrapField c v -> Rec c r
           -> OpExtend' b c l v r

-- | extending an empty record
instance
  Require (OpExtend c l v '[]) ctx where
  type ReqR (OpExtend c l v '[]) =
    Rec c '[ '(l , v)]
  req ctx (OpExtend l v EmptyRec) =
    ConsRec (TagField (Label @c) l v) EmptyRec

-- | wrapper instance

instance
  Require (OpExtend' (Cmp l l') c l v ('(l', v') : r)) ctx
  =>
  Require (OpExtend c l v ( '(l', v') ': r)) ctx where
  type ReqR (OpExtend c l v ( '(l', v') ': r)) =
    ReqR (OpExtend' (Cmp l l') c l v ( '(l', v') ': r))
  req ctx (OpExtend l v (r :: Rec c ( '(l', v') ': r)) ) =
    req ctx (OpExtend' @(Cmp l l') @l @c @v Proxy l v r)

-- | keep looking
instance
  (Require (OpExtend c l v r) ctx
  , ( '(l', v') ': r0 ) ~ a
  , ReqR (OpExtend c l v r) ~ Rec c r0
  )
  =>
  Require (OpExtend' 'GT c l v ( '(l', v') ': r)) ctx where
  type ReqR (OpExtend' 'GT c l v ( '(l', v') ': r)) =
    Rec c ( '(l', v') ': UnWrap (ReqR (OpExtend c l v r)))
  req ctx (OpExtend' Proxy l v (ConsRec lv r)) =
    ConsRec lv $ req ctx (OpExtend @_ @_ @v l v r)

instance
  Require (OpExtend' 'LT c l v ( '(l', v') ': r)) ctx where
  type ReqR (OpExtend' 'LT c l v ( '(l', v') ': r)) =
    Rec c ( '(l, v) ': ( '(l', v') ': r))
  req ctx (OpExtend' Proxy l v r) =
    ConsRec (TagField Label l v) r

instance
  (Require (OpError (Text "cannot extend " :<>: Text (ShowRec c)
                     -- :<>: Text " because the label (" :<>: ShowT l
                     -- :<>: Text ") already exists"
                    :$$: Text "colision in " :<>: Text (ShowField c)
                     :<>: Text " ":<>: ShowT l)) ctx)
  =>
  Require (OpExtend' 'EQ c l v ( '(l, v') ': r)) ctx where
  type ReqR (OpExtend' 'EQ c l v ( '(l, v') ': r)) = ()
  req ctx = undefined


infixr 2 .*.
-- | operator
(TagField c l v) .*. r = req Proxy (OpExtend l v r)



-- | non emptyness test

-- data OpNonEmpty (c :: Type) (r :: [(k, k')]) where
--   OpNonEmpty :: Rec c r -> OpNonEmpty c r


-- instance Require (OpNonEmpty c ( '(l, v) ': r)) ctx where
--   ReqR 

-- -- instance (Require (OpError (Text "Empty " :<>: Text (ShowRec c)
-- --                           :$$: Text " Required to be nonempty "
-- --                           )) ctx)
-- --   => Require (OpNonEmpty c '[]) ctx where {}
