{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}

{-
   The HList library

   (C) 2004-2006, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

   A model of label as needed for extensible records.

   Record labels are simply type-level naturals.
   This models is as simple and as portable as it could be.
-}

module Data.HList.Label1 where

import Data.HList.FakePrelude
import Data.HList.Record (ShowLabel(..))


-- Labels are type-level naturals

newtype Label x = Label x deriving Show


-- Public constructors for labels

label :: HNat n => n -> Label n
label =  Label


-- Construct the first label
firstLabel :: Label HZero
firstLabel = label hZero


-- Construct the next label
nextLabel ::( HNat t) => Label t -> Label (HSucc t)
nextLabel (Label n) = label (hSucc n)


-- Equality on labels

instance HEq n n' b
      => HEq (Label n) (Label n') b


-- Show label

instance Show n => ShowLabel (Label n)
 where
  showLabel (Label n) = show n
