{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances,
  FlexibleContexts, UndecidableInstances #-}
{-
   The HList library

   (C) 2004, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

   Array-like access to HLists.
 -}

module Data.HList.HArray where

import Data.HList.FakePrelude
import Data.HList.HListPrelude


{-----------------------------------------------------------------------------}

-- A lookup operation

class HNat n => HLookupByHNat n l e | n l -> e
 where
  hLookupByHNat :: n -> l -> e

instance HLookupByHNat HZero (HCons e l) e
 where
  hLookupByHNat _ (HCons e _) = e

instance (HLookupByHNat n l e', HNat n)
      => HLookupByHNat (HSucc n) (HCons e l) e'
 where
  hLookupByHNat n (HCons _ l) = hLookupByHNat (hPred n) l


{-----------------------------------------------------------------------------}

-- A delete operation

class HNat n => HDeleteAtHNat n l l' | n l -> l'
 where
  hDeleteAtHNat :: n -> l -> l'

instance HDeleteAtHNat HZero (HCons e l) l
 where
  hDeleteAtHNat _ (HCons _ l) = l

instance (HDeleteAtHNat n l l', HNat n)
      => HDeleteAtHNat (HSucc n) (HCons e l) (HCons e l')
 where
  hDeleteAtHNat n (HCons e l) = HCons e (hDeleteAtHNat (hPred n) l)


{-----------------------------------------------------------------------------}

-- An update operation

class HNat n => HUpdateAtHNat n e l l' | n e l -> l', l' n -> e
 where
  hUpdateAtHNat :: n -> e -> l -> l'

instance HUpdateAtHNat HZero e' (HCons e l) (HCons e' l)
 where
  hUpdateAtHNat _ e' (HCons _ l) = HCons e' l

instance (HUpdateAtHNat n e' l l', HNat n)
      => HUpdateAtHNat (HSucc n) e' (HCons e l) (HCons e l')
 where
  hUpdateAtHNat n e' (HCons e l)
   = HCons e (hUpdateAtHNat (hPred n) e' l)


{-----------------------------------------------------------------------------}

-- Splitting an array according to indices
-- Signature is inferred:
-- hSplitByHNats :: (HSplitByHNats' ns l' l'1 l'', HMap (HAddTag HTrue) l l') =>
--                ns -> l -> (l'1, l'')
hSplitByHNats ns l = hSplitByHNats' ns (hFlag l)

class HNats ns => HSplitByHNats' ns l l' l'' | ns l -> l' l''
 where
  hSplitByHNats' :: ns -> l -> (l',l'')

instance HSplit l l' l''
      => HSplitByHNats' HNil l HNil l'
 where
  hSplitByHNats' HNil l = (HNil,l')
   where
    (l',_) = hSplit l

instance ( HLookupByHNat n l (e,b)
         , HUpdateAtHNat n (e,HFalse) l l'''
         , HSplitByHNats' ns l''' l' l''
         )
      =>   HSplitByHNats' (HCons n ns) l (HCons e l') l''
 where
  hSplitByHNats' (HCons n ns) l = (HCons e l',l'')
   where
    (e,_)    = hLookupByHNat  n l
    l'''     = hUpdateAtHNat  n (e,hFalse) l
    (l',l'') = hSplitByHNats' ns l'''


{-----------------------------------------------------------------------------}

-- Another projection operation

class HNats ns => HProjectByHNats ns l l' | ns l -> l'
 where
  hProjectByHNats :: ns -> l -> l'

instance HProjectByHNats HNil HNil HNil
 where
  hProjectByHNats _ _ = HNil

instance HProjectByHNats HNil (HCons e l) HNil
 where
  hProjectByHNats _ _ = HNil

instance ( HLookupByHNat n (HCons e l) e'
         , HProjectByHNats ns (HCons e l) l'
         )
         => HProjectByHNats (HCons n ns) (HCons e l) (HCons e' l')
 where
  hProjectByHNats (HCons n ns) l = HCons e' l'
   where e' = hLookupByHNat n l
         l' = hProjectByHNats ns l


{-----------------------------------------------------------------------------}

-- The complement of projection

class HProjectAwayByHNats ns l l' | ns l -> l'
 where
  hProjectAwayByHNats :: ns -> l -> l'

instance ( HLength l len
         , HBetween len nats
         , HDiff nats ns ns'
         , HProjectByHNats ns' l l'
         )
           => HProjectAwayByHNats ns l l'
 where
  hProjectAwayByHNats ns l = l'
   where
    len  = hLength l
    nats = hBetween len
    ns'  = hDiff nats ns
    l'   = hProjectByHNats ns' l


{-----------------------------------------------------------------------------}

-- Generate naturals from 1 to x - 1

class HBetween x y | x -> y
 where
  hBetween :: x -> y

instance HBetween (HSucc HZero) (HCons HZero HNil)
 where
  hBetween _ = HCons hZero HNil

instance ( HNat x
         , HBetween (HSucc x) y
         , HAppend y (HCons (HSucc x) HNil) z
         , HList y
         )
           => HBetween (HSucc (HSucc x)) z
 where
  hBetween x = hBetween (hPred x) `hAppend` HCons (hPred x) HNil


-- Set-difference on naturals

class HDiff x y z | x y -> z
 where
  hDiff :: x -> y -> z

instance HDiff HNil x HNil
 where
  hDiff _ _ = HNil

instance ( HOrdMember e y b
         , HDiff x y z
         , HCond b z (HCons e z) z'
         )
           => HDiff (HCons e x) y z'
 where
  hDiff (HCons e x) y = z'
   where z' = hCond b z (HCons e z)
         b  = hOrdMember e y
         z  = hDiff x y


-- Membership test for types with HOrd instances
-- This special type equality/comparison is entirely pure!

class HOrdMember e l b | e l -> b
 where
  hOrdMember :: e -> l -> b

instance HOrdMember e HNil HFalse
 where
  hOrdMember _ _ = hFalse

instance ( HEq e e' b1
         , HOrdMember e l b2
         , HOr b1 b2 b
         )
           => HOrdMember e (HCons e' l) b
 where
  hOrdMember e (HCons e' l) = hOr b1 b2
   where
    b1 = hEq e e'
    b2 = hOrdMember e l


{-----------------------------------------------------------------------------}

-- Length operation

class (HList l, HNat n) => HLength l n | l -> n
instance HLength HNil HZero
instance (HLength l n, HNat n, HList l)
      => HLength (HCons a l) (HSucc n)

hLength   :: HLength l n => l -> n
hLength _ =  undefined


{-----------------------------------------------------------------------------}

-- Bounded lists

class HMaxLength l s
instance (HLength l s', HLt s' (HSucc s) HTrue) => HMaxLength l s

class HMinLength l s
instance (HLength l s', HLt s (HSucc s') HTrue) => HMinLength l s

class HSingleton l
instance HLength l (HSucc HZero) => HSingleton l

hSingle :: (HSingleton l, HHead l e) => l -> e
hSingle = hHead


{-----------------------------------------------------------------------------}
