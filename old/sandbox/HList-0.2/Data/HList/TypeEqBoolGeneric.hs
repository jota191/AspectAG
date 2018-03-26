{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
{-
   The HList library

   (C) 2004, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

   Generic implementations of type equality and disequality
-}

module Data.HList.TypeEqBoolGeneric where

import Data.HList.FakePrelude

instance            TypeEqTrue  x x
instance Fail () => TypeEqFalse x x
instance            TypeEqFalse x y
