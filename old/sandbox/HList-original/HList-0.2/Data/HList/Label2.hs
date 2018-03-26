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
   For the sake of printing, the namespace part and the description
   are required to be the instance of Show. One must make sure that
   the show functions does not examine the value, as descr is purely phantom.
   Here's an example of the good Label description:
        data MyLabelDescr; instance Show MyLabelDescr where show _ = "descr"
   which obviously can be automated with Template Haskell.

   This model requires all labels in a record to inhabit the same namespace.
-}

module Data.HList.Label2 where

import Data.HList.FakePrelude
import Data.HList.Record (ShowLabel(..))


-- Labels are type-level naturals

data HNat x => Label x ns desc  -- labels are exclusively type-level entities


-- Construct the first label

firstLabel :: ns -> desc -> Label HZero ns desc
firstLabel = undefined


-- Construct the next label
nextLabel :: Label x ns desc -> desc' -> Label (HSucc x) ns desc'
nextLabel = undefined


-- Equality on labels (descriptions are ignored)

instance HEq x x' b
      => HEq (Label x ns desc1) (Label x' ns desc2) b


-- Show label

instance (HNat x, Show desc) => ShowLabel (Label x ns desc) where
  showLabel = show . getd
      where getd :: Label x ns desc -> desc
            getd = undefined

instance (HNat x, HNat2Integral x,Show ns) => Show (Label x ns desc) where
  show l = unwords ["L",show ((hNat2Integral x)::Integer), show ns]
      where geti :: Label x ns desc -> (x,ns) -- for the sake of Hugs
            geti = undefined
            (x,ns) = geti l
