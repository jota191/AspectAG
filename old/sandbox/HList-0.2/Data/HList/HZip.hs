{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}

module Data.HList.HZip where

import Data.HList.HListPrelude

{-
   The HList library

   (C) 2004, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

   Zipping and unzipping for (conceptually) lists of pairs.
 -}

{-----------------------------------------------------------------------------}

-- Test for zippability

class HZippable x y
instance HZippable HNil HNil
instance HZippable l l' => HZippable (HCons e l) (HCons e' l')


{-----------------------------------------------------------------------------}

-- Zip and unzip

class HZip x y l | x y -> l, l -> x y
 where
  hZip   :: x -> y -> l
  hUnzip :: l -> (x,y)

{-

-- Zipping version I
-- Somehow too polymorphic.
-- Version II specialises for HNil and HCons.

instance HZippable x y => HZip x y (x,y)
 where
  hZip x y = (x,y)
  hUnzip = id

-}

{-

-- Zipping version II
-- Built-in show and alias-based type construction inconvenient.
-- Version III goes for a true list of pairs.

instance HZip HNil HNil (HNil,HNil)
 where
  hZip x y = (x,y)
  hUnzip = id

instance HZip xt yt zt
      => HZip (HCons xh xt) (HCons yh yt) (HCons xh xt,HCons yh yt)
 where
  hZip x y = (x,y)
  hUnzip = id

-}


-- {-

--- Zipping version III
--- Works best for us.

instance HZip HNil HNil HNil
 where
  hZip HNil HNil = HNil
  hUnzip HNil = (HNil,HNil)

instance HZip tx ty l
      => HZip (HCons hx tx) (HCons hy ty) (HCons (hx,hy) l)
 where
  hZip (HCons hx tx) (HCons hy ty) = HCons (hx,hy) (hZip tx ty)
  hUnzip (HCons (hx,hy) l) = (HCons hx tx, HCons hy ty)
   where
    (tx,ty) = hUnzip l

-- -}
