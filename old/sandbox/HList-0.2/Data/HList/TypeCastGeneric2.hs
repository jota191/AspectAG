{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}
{-
   The HList library

   (C) 2004, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

   A generic implementation of a type-safe cast. The specific coding
   here is only shown for completeness' sake and it is explained in the
   TR version of the paper. The shown coding does not rely on separate
   compilation (while TypeCastGeneric1.hs does), but on some other tricks.
-}

module Data.HList.TypeCastGeneric2 where

-- We make everything self-contained to show that separate compilation
-- is not needed.

import Data.HList.FakePrelude () -- hiding (TypeCast,typeCast)


{-----------------------------------------------------------------------------}

-- The actual encoding

class TypeCast   a b   | a -> b, b->a   where typeCast   :: a -> b
class TypeCast'  t a b | t a -> b, t b -> a where typeCast'  :: t->a->b
class TypeCast'' t a b | t a -> b, t b -> a where typeCast'' :: t->a->b
instance TypeCast'  () a b => TypeCast a b where typeCast x = typeCast' () x
instance TypeCast'' t a b => TypeCast' t a b where typeCast' = typeCast''
instance TypeCast'' () a a where typeCast'' _ x  = x


{-----------------------------------------------------------------------------}
