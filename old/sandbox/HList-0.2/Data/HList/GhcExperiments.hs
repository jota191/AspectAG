{-# LANGUAGE KindSignatures,MultiParamTypeClasses,FunctionalDependencies,FlexibleInstances, FlexibleContexts, UndecidableInstances #-}

{-
   (C) 2004, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

   This module gathers experiments that do not work with Hugs.
-}

module Data.HList.GhcExperiments where

import Data.HList.FakePrelude
import Data.HList.HListPrelude

class HDeleteMany e l l' | e l -> l'
 where
  hDeleteMany :: Proxy e -> l -> l'

instance HDeleteMany e HNil HNil
 where
  hDeleteMany _ HNil = HNil

instance (HList l, HDeleteMany e l l')
      => HDeleteMany e (HCons e l) l'
 where
  hDeleteMany p (HCons _ l) = hDeleteMany p l

{-

-- Hopelessly overlapping

instance (HList l, HDeleteMany e l l')
      => HDeleteMany e (HCons e' l) (HCons e' l')
 where
  hDeleteMany p (HCons e' l)
   =
     HCons e' (hDeleteMany p l)

-}

instance ( HList l
         , HDeleteMany e l l'
         , TypeCast (HCons e' l') l''
         )
      =>   HDeleteMany e (HCons e' l) l''
 where
  hDeleteMany p (HCons e' l)
   =
     typeCast (HCons e' (hDeleteMany p l))


-----------------------------------------------------------------------------

-- Test for type constructors

-- signature: * -> *
class IsTC1 x (f :: * -> *) b | x f -> b
instance TypeCast HTrue b => IsTC1 (f a) f b
instance TypeCast HFalse b => IsTC1 f x b

-- signature: * -> * -> *
class IsTC2 x (f :: * -> * -> *) b | x f -> b
instance TypeCast HTrue b => IsTC2 (f a b) f b
instance TypeCast HFalse b => IsTC2 f x b

-- Sample
funType :: IsTC2 t (->) b => t -> b
funType = undefined
