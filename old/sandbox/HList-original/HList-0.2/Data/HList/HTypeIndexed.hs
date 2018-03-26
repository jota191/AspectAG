{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances,
  UndecidableInstances, FlexibleContexts #-}

{-
   The HList library

   (C) 2004, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

   Type-indexed operations on typeful heterogeneous lists.
-}

module Data.HList.HTypeIndexed where

import Data.HList.FakePrelude
import Data.HList.HListPrelude
import Data.HList.HArray
import Data.HList.HOccurs


{-----------------------------------------------------------------------------}

class HDeleteMany e l l' | e l -> l'
 where
  hDeleteMany :: Proxy e -> l -> l'

instance HDeleteMany e HNil HNil
 where
  hDeleteMany _ HNil = HNil

instance ( HList l
         , TypeEq e e' b
         , HDeleteManyCase b e e' l l'
         )
      =>   HDeleteMany e (HCons e' l) l'
 where
  hDeleteMany p (HCons e' l) = l'
   where
    b  = proxyEq p (toProxy e')
    l' = hDeleteManyCase b p e' l

class HDeleteManyCase b e e' l l' | b e e' l -> l'
 where
  hDeleteManyCase :: b -> Proxy e -> e' -> l -> l'

instance HDeleteMany e l l'
      => HDeleteManyCase HTrue e e l l'
 where
  hDeleteManyCase _ p _ l = hDeleteMany p l


instance HDeleteMany e l l'
      => HDeleteManyCase HFalse e e' l (HCons e' l')
 where
  hDeleteManyCase _ p e' l = HCons e' (hDeleteMany p l)


{-----------------------------------------------------------------------------}

-- Map a type to a natural

class HNat n => HType2HNat e l n | e l -> n
instance (TypeEq e' e b, HType2HNatCase b e l n)
      =>  HType2HNat e (HCons e' l) n

-- Helper class

class (HBool b, HNat n) => HType2HNatCase b e l n | b e l -> n
instance HOccursNot e l => HType2HNatCase HTrue e l HZero
instance HType2HNat e l n => HType2HNatCase HFalse e l (HSucc n)

hType2HNat :: HType2HNat e l n => Proxy e -> l -> n
hType2HNat _ _ = undefined



-- Map types to naturals

class HTypes2HNats ps l ns | ps l -> ns
 where
  hTypes2HNats :: ps -> l -> ns

instance HTypes2HNats HNil l HNil
 where
  hTypes2HNats _ _ = HNil

instance ( HType2HNat   e l n
         , HTypes2HNats ps l ns
         )
      =>   HTypes2HNats (HCons (Proxy e) ps) l (HCons n ns)
 where
  hTypes2HNats (HCons p ps) l = HCons (hType2HNat p l) (hTypes2HNats ps l)


{-----------------------------------------------------------------------------}

-- Define type-indexed delete in terms of the natural-based primitive
hDeleteAtProxy :: (HDeleteAtHNat n l l', HType2HNat e l n) => Proxy e -> l -> l'
hDeleteAtProxy p l = hDeleteAtHNat (hType2HNat p l) l


{-----------------------------------------------------------------------------}

-- Define type-indexed update in terms of the natural-based update
hUpdateAtType :: (HUpdateAtHNat n e l l', HType2HNat e l n) => e -> l -> l'
hUpdateAtType e l = hUpdateAtHNat (hType2HNat (toProxy e) l) e l


{-----------------------------------------------------------------------------}

-- Projection based on proxies
hProjectByProxies :: (HProjectByHNats ns l l', HTypes2HNats ps l ns) => ps -> l -> l'
hProjectByProxies ps l = hProjectByHNats (hTypes2HNats ps l) l


{-----------------------------------------------------------------------------}

-- Splitting based on proxies
hSplitByProxies :: (HMap (HAddTag HTrue) l l', HSplitByHNats' ns l' l'1 l'',
                   HTypes2HNats ps l ns) =>
                  ps -> l -> (l'1, l'')
hSplitByProxies ps l = hSplitByHNats (hTypes2HNats ps l) l


{-----------------------------------------------------------------------------}
