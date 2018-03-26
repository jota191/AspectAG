{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, EmptyDataDecls #-}

{-
   The HList library

   (C) 2004-2006, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

   A model of labels as needed for extensible records. As before,
   all the information about labels is recorded in their type, so
   the labels of records may be purely phantom. In general,
   Labels are exclusively type-level entities and have no run-time
   representation.

   Record labels are triplets of type-level naturals, namespace,
   and description. The namespace part helps avoid confusions between
   labels from different Haskell modules. The description is
   an arbitrary nullary type constructor.
   For the sake of printing, the description is required to be the
   instance of Show. One must make sure that the show functions does
   not examine the value, as descr is purely phantom. Here's an
   example of the good Label description:
        data MyLabelDescr; instance Show MyLabelDescr where show _ = "descr"
   which obviously can be automated with Template Haskell.

   This model even allows the labels in a record to belong to different
   namespaces. To this end, the model employs the predicate for type
   equality.
-}

module Data.HList.Label3 where

import Data.HList.FakePrelude
import Data.HList.Record (ShowLabel(..))


-- Labels are type-level naturals
data HNat x => Label x ns desc  -- labels are exclusively type-level entities


-- Public constructors for labels

-- Construct the first label
firstLabel :: ns -> desc -> Label HZero ns desc
firstLabel = undefined


-- Construct the next label
nextLabel :: Label x ns desc -> desc' -> Label (HSucc x) ns desc'
nextLabel = undefined


-- Equality on labels (descriptions are ignored)

instance ( HEq x x' b
         , TypeEq ns ns' b'
         , HAnd b b' b''
         )
      =>   HEq (Label x ns desc) (Label x' ns' desc') b''


-- Show label

instance (HNat x, Show desc) => ShowLabel (Label x ns desc) where
  showLabel = show . getd
      where getd :: Label x ns desc -> desc -- for the sake of Hugs
            getd = undefined

instance (HNat x, Show desc) => Show (Label x ns desc)
 where
  show = show . getd
      where getd :: Label x ns desc -> desc -- for the sake of Hugs
            getd = undefined

