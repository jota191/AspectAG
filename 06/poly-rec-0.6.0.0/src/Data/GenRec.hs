{-|
Module      : Data.GenRecord
Description : polykinded extensible record library
Copyright   : (c) Juan García Garland,
                  Marcos Viera, 2019-2020
License     : GPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX

Extensible records/row polymorphism are features not implemented in
Haskell. Some other functional languages do it, like Purescript. GHC
extensions allowing type level-programming allow us to encode them in
Haskell.

Let us define records as a (partial) mapping from names (fields, wich
are static) to values.

There are many implementations out there. This is yet another one,
inspired in the HList library. It arose when programming the AspectAG
library.  Before, we depended on HList. Then we choose to implement a
record library from scratch for two reasons:

 * HList is experimental, it does not maintain a stable interface.
 * We prefer a solution that fits better in our use case.

AspectAG is a library to encode type safe attribute grammars.
Statically checked extensible records are used everywhere, knowing at
compile time the structure of the grammar, and checking if it is
well-formed.

Some example structures in AspectAG library are:

* Records: that's it, plane extensible records: Mappings from names to
  values.

* Attributions: mappings from attribute names to values. This is the
  same idea that the one for records, but we wanted to have different
  types for each structure, and for each label. This means that our
  labels must be polyinded.

* Children Records: That is a map from children to attibutions. It is
  a record of records. 

One common way to implement a record is by using a GADT. For instance indexed by
the list of pairs (label, value). We want labels polykinded, and values are
usually of kind Type, what makes sense since Type is the kind of
inhabited types, and records store values.  However, in cases such as
our children records, where we store attributions that are also
represented by an indexed GADT, we would like to be able to reflect
some of this structural information at the indexes of the record. This
can be achieved if we are polymorphic in the kind of the types
corresponding to the record fields.
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

module Data.GenRec
  (
    Rec(ConsRec, EmptyRec),
    TagField(TagField),
    WrapField,
    UnWrap,
    untagField,
    (.=.),
    (#),
    (.*.),

    OrdType,
    Cmp,
    ShowRec,
    ShowField,
    OpLookup(OpLookup),
    lookup,
    OpExtend(OpExtend),
    -- extend, TODO
    OpUpdate(OpUpdate),
    update,
    emptyGenRec,
    module Data.GenRec.Label
  ) where

import Data.Kind
import Data.Proxy
import Data.GenRec.Label
import Data.Type.Require
import Data.Type.Bool

import Prelude hiding (lookup)

import GHC.TypeLits


type family a == b where
  a == b = Equal a b


-- | Record data structure for generic records (Internal). The `c`
-- index indicates the kind of record (for each record instance, the
-- user should define an index). The `r` index represents the mapping
-- from labels to values.  Labels are of kind `k'`. Values are still
-- polykinded (`k''`) since rich information can be statically
-- represented here (for instance, when a record of records, or a
-- record of Vectors is represented).  `k'` must implement the `Cmp`
-- family, although it is not visible here for simplicity. Records are
-- built putting fields ordered according to the `Cmp` result of its
-- labels. __This constructors are not intended to be used to build__
-- __records__, (`ConsRec` is the problematic one). Use the smart
-- constructors `emptyRecord` and `.*.` instead. We export the
-- constructors to pattern match on them. Although there are solutions
-- to hide Constructors while supporting pattern matching, we kept
-- it simple

data Rec (c :: k) (r :: [(k', k'')]) :: Type where
  EmptyRec :: Rec c '[] -- ^ empty record
  ConsRec :: TagField c l v -> Rec c r -> Rec c ('( l, v) ': r) -- ^
-- `ConsRec` takes a tagged field (`TagField`) and a record, to build
-- a new record. Recall that fields should be ordered.

-- | The empty Record. Note that it is polymorphic on the kind of record `c`.
emptyGenRec = EmptyRec

-- | 'TagField'
data TagField (c :: k) (l :: k') (v :: k'') where
  TagField :: Label c -> Label l -> WrapField c v -> TagField c l v -- ^
-- `TagField` tags a value `v` with record and label information. `v`
-- is polykinded, for instance we could be tagging some kind of
-- record, because then we would build a matrix. In that case 'k''
-- could be something as `[(kindforlabels, Type)]`. But `TagField`
-- contains inhabited values, it tags values of a type of kind `Type`.
-- In this example perhaps some value of
-- type `Rec Something [(kindforlabels, Type)]`.
-- That is the role of the `WrapField` family. Given `c`, the kind of
-- record, and `v`, ir computes the wrapper.


-- | TagField operator, note that 'c' will be ambiguous if not annotated.
infix 4 .=.
(l :: Label l) .=. (v :: v) = TagField Label l v


-- | Given a type of record and its index, it computes the type of
-- record inhabitants
type family  WrapField (c :: k')  (v :: k) :: Type


-- | The inverse of `WrapField`
type family UnWrap (t :: Type) :: [(k,k')]
type instance UnWrap (Rec c (r :: [(k, k')])) = (r :: [(k, k')])

-- | This is the destructor of `TagField`. Note the use of `WrapField` here.
untagField :: TagField c l v -> WrapField c v
untagField (TagField lc lv v) = v

-- | comparisson of Labels, this family is polykinded, each record-like
-- structure must implement this family for its labels
--type family Cmp (a :: k) (b :: k) :: Ordering

-- | Instance for Symbols
--type instance Cmp (a :: Symbol) (b :: Symbol) = CmpSymbol a b

class OrdType k where
  type Cmp (a :: k) (b :: k) :: Ordering

instance OrdType Symbol where
  type Cmp a b = CmpSymbol a b

-- | Function to show the name of records (Record, Mapping, etc):
type family ShowRec c :: Symbol

-- | Function to show the field of the record ("field named", "children", "tag:", etc)
type family ShowField c :: Symbol


-- * Operations

-- ** Lookup

-- | Datatype for lookup (wrapper)
data OpLookup (c :: Type)
              (l  :: k)
              (r  :: [(k, k')]) :: Type where
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
                           :<>: Text " " :<>: ShowTE l
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
                           :<>: Text " " :<>: ShowTE l
                          )) ctx
  =>
  Require (OpLookup' 'LT c l ( '(l', v) ': r)) ctx where
  type ReqR (OpLookup' 'LT  c l ( '(l', v) ': r)) = ()
  req ctx (OpLookup' Proxy l (ConsRec _ r)) = ()

-- | Pretty lookup
(#) :: forall c l r ctx v. RequireR (OpLookupCall c l r) ctx v =>
  Rec c r -> Label l -> v
r # l = req (Proxy @ctx) (OpLookupCall l r)


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
                     :<>: ShowTE l)) ctx)
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
                     :<>: ShowTE l)) ctx)
  =>
  Require (OpUpdate' 'LT c l v ( '(l',v') ': r)) ctx where
  type ReqR (OpUpdate' 'LT c l v ( '(l',v') ': r)) =
    ()
  req = undefined

-- | The update function. Given a `Label` and value, and a `Record`
-- containing this label, it updates the value. It could change its
-- type. It raises a custom type error if there is no field
-- labelled with l.
update (l :: Label l) (v :: v) (r :: Rec c r) =
  req Proxy (OpUpdate @l @c @v @r l v r)

-- | The lookup function. Given a `Label` and a `Record`, it returns
-- the field at that position. It raises a custom type
-- error if there is no field labelled with l.
lookup (l :: Label l) (r :: Rec c r) =
  req Proxy (OpLookup @c @l @r l r)

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
                     :<>: Text " ":<>: ShowTE l)) ctx)
  =>
  Require (OpExtend' 'EQ c l v ( '(l, v') ': r)) ctx where
  type ReqR (OpExtend' 'EQ c l v ( '(l, v') ': r)) = ()
  req ctx = undefined


-- | '.*.' the pretty cons, hiding require
infixr 2 .*.
(TagField c l v :: TagField c l v) .*. (r :: Rec c r) =
  req emptyCtx (OpExtend @l @c @v @r l v r)



type family LabelSetF (r :: [(k, k')]) :: Bool where
  LabelSetF '[] = True
  LabelSetF '[ '(l, v)] = True
  LabelSetF ( '(l, v) ': '(l',v') ': r) =
    Cmp l l' == LT && LabelSetF ( '(l',v') ': r)


data OpLookupCall
  (c :: Type)
  (l  :: k)
  (r  :: [(k, k')]) :: Type where
  OpLookupCall :: Label l -> Rec c r -> OpLookupCall c l r


instance
  Require (OpLookup c l r) ( ShowType r ': ctx)
  =>
  Require (OpLookupCall c l r) ctx where
  type ReqR (OpLookupCall c l r) =
    ReqR (OpLookup c l r)
  req ctx (OpLookupCall l r) =
   req (Proxy @ (ShowType r ': ctx)) (OpLookup l r)
