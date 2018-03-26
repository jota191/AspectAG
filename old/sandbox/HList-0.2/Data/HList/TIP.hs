{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances,
    FlexibleContexts #-}

module Data.HList.TIP where

{-
   The HList library

   (C) 2004, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

   Type-indexed products.
-}

import Data.HList.FakePrelude
import Data.HList.HListPrelude
import Data.HList.HArray
import Data.HList.HOccurs
import Data.HList.HTypeIndexed


{-----------------------------------------------------------------------------}

-- The newtype for type-indexed products

newtype TIP l = TIP l
        deriving (Read,Show)

mkTIP :: HTypeIndexed l => l -> TIP l
mkTIP = TIP

unTIP :: TIP l -> l
unTIP (TIP l) = l

emptyTIP :: TIP HNil
emptyTIP = mkTIP HNil



{-----------------------------------------------------------------------------}

-- Type-indexed type sequences

class HList l => HTypeIndexed l
instance HTypeIndexed HNil
instance (HOccursNot e l,HTypeIndexed l) => HTypeIndexed (HCons e l)


{-----------------------------------------------------------------------------}

--
-- One occurrence and nothing is left
--
-- This variation provides an extra feature for singleton lists.
-- That is, the result type is unified with the element in the list.
-- Hence the explicit provision of a result type can be omitted.
--

instance TypeCast e' e => HOccurs e (TIP (HCons e' HNil))
 where
  hOccurs (TIP (HCons e' _)) = typeCast e'

instance HOccurs e (HCons x (HCons y l))
      => HOccurs e (TIP (HCons x (HCons y l)))
 where
  hOccurs (TIP l) = hOccurs l


{-----------------------------------------------------------------------------}

-- HOccursNot lifted to TIPs

instance HOccursNot e l => HOccursNot e (TIP l)


{-----------------------------------------------------------------------------}

-- Type-indexed extension
-- signature is inferred
-- hExtend' :: (HTypeIndexed t, HOccursNot e t) => e -> TIP t -> TIP (HCons e t)
hExtend' e (TIP l) = mkTIP (HCons e l)

{-

Valid type I

hExtend' :: (HTypeIndexed l, HOccursNot e l)
         => e -> TIP l -> TIP (HCons e l)

Valid type II

*TIP> :t hExtend'
hExtend' :: forall l e.
            (HTypeIndexed (HCons e l)) =>
            e -> TIP l -> TIP (HCons e l)

-}


{-----------------------------------------------------------------------------}

-- Lift extension through HExtend

instance ( HOccursNot e l
         , HTypeIndexed l
         )
      => HExtend e (TIP l) (TIP (HCons e l))
 where
  hExtend = hExtend'


{-----------------------------------------------------------------------------}

-- Lifting previous operations


instance ( HAppend l l' l''
         , HTypeIndexed l''
         )
           => HAppend (TIP l) (TIP l') (TIP l'')
 where
  hAppend (TIP l) (TIP l') = mkTIP (hAppend l l')


instance HOccursMany e l
      => HOccursMany e (TIP l)
 where
  hOccursMany = hOccursMany . unTIP


instance HOccursMany1 e l
      => HOccursMany1 e (TIP l)
 where
  hOccursMany1 = hOccursMany1 . unTIP


instance HOccursFst e l
      => HOccursFst e (TIP l)
 where
  hOccursFst = hOccursFst . unTIP


instance HOccursOpt e l
      => HOccursOpt e (TIP l)
 where
  hOccursOpt = hOccursOpt . unTIP


{-----------------------------------------------------------------------------}

-- Shielding type-indexed operations
-- The absence of signatures is deliberate! They all must be inferred.

onTIP f (TIP l) = mkTIP (f l)

tipyDelete  p t  = onTIP (hDeleteAtProxy p) t
tipyUpdate  e t  = onTIP (hUpdateAtType e) t
tipyProject ps t = onTIP (hProjectByProxies ps) t


-- Split produces two TIPs
tipySplit ps (TIP l) = (mkTIP l',mkTIP l'')
 where
  (l',l'') = hSplitByProxies ps l


{-----------------------------------------------------------------------------}

-- Subtyping for TIPs

instance SubType (TIP l) (TIP HNil)
instance (HOccurs e l, SubType (TIP l) (TIP l'))
      =>  SubType (TIP l) (TIP (HCons e l'))


{-----------------------------------------------------------------------------}

-- Sample code

{-

Assume

myTipyCow = TIP myAnimal

animalKey :: (HOccurs Key l, SubType l (TIP Animal)) => l -> Key
animalKey = hOccurs

Session log

*TIP> :t myTipyCow
myTipyCow :: TIP Animal

*TIP> hOccurs myTipyCow :: Breed
Cow

*TIP> hExtend BSE myTipyCow
TIP (HCons BSE
    (HCons (Key 42)
    (HCons (Name "Angus")
    (HCons Cow
    (HCons (Price 75.5)
     HNil)))))

*TIP> BSE .*. myTipyCow
--- same as before ---

*TIP> Sheep .*. myTipyCow
Type error ...

*TIP> Sheep .*. tipyDelete myTipyCow (HProxy::HProxy Breed)
TIP (HCons Sheep (HCons (Key 42) (HCons (Name "Angus") (HCons (Price 75.5) HNil))))

*TIP> tipyUpdate myTipyCow Sheep
TIP (HCons (Key 42) (HCons (Name "Angus") (HCons Sheep (HCons (Price 75.5) HNil))))

-}

{-----------------------------------------------------------------------------}

-- This example from the TIR paper challenges singleton lists.
-- Thanks to the HW 2004 reviewer who pointed out the value of this example.
-- We note that the explicit type below is richer than the inferred type.
-- This richer type is needed for making this operation more polymorphic.
-- That is, a) would not work without the explicit type, while it would:
--  a)  ((+) (1::Int)) $ snd $ tuple oneTrue
--  b)  ((+) (1::Int)) $ fst $ tuple oneTrue

tuple :: ( HOccurs e1 (TIP l)
         , HType2HNat e1 l n
         , HDeleteAtHNat n l l'
         , HOccurs e2 (TIP l')
         , HOccurs e2 (TIP l)
         , HType2HNat e2 l n'
         , HDeleteAtHNat n' l l''
         , HOccurs e1 (TIP l'')
         ) =>
              TIP l -> (e1, e2)

tuple (TIP l) = let
                 x  = hOccurs (TIP l)
                 l' = hDeleteAtProxy (toProxy x) l
                 y  = hOccurs (TIP l')
                in (x,y)


-- A specific tuple
oneTrue :: TIP (HCons Int (HCons Bool HNil))
oneTrue = hExtend (1::Int) (hExtend True emptyTIP)


{-----------------------------------------------------------------------------}
