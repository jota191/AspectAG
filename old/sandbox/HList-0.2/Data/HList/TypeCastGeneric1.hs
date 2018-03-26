{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

{-
   The HList library

   (C) 2004, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

   A generic implementation of type cast. For this implementation to
   work, we need to import it at a higher level in the module hierarchy
   than all clients of the class. Otherwise, type simplification will
   inline TypeCast x y, which implies compile-time unification of x and y.

   This technique works fine for ghc, and within limits for hugs.
-}

module Data.HList.TypeCastGeneric1 where

import Data.HList.FakePrelude

instance TypeCast x x
 where
  typeCast = id
