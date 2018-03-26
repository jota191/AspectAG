{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances,
  UndecidableInstances, FlexibleContexts #-}

{-
   The HList library

   (C) 2004, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

   Variants, i.e., labelled sums.

   One approach to their implementation would be to consider both
   the favoured label and the corresponding value as dynamics upon
   variant construction. Since we are too lazy to programme some
   Typeable instances for non-ghc systems (NB: in GHC, Typeable
   is derivable), we rather model variants as (opaque) records
   with maybies for the values. Only one value will actually hold
   non-Nothing, as guaranteed by the constructor.

   See VariantP.hs for a different approach to open sums.
-}

module Data.HList.Variant where

import Data.HList.FakePrelude
import Data.HList.HListPrelude
import Data.HList.HArray
import Data.HList.Record


{-----------------------------------------------------------------------------}

-- Variant types on the basis of label-maybe pairs.

newtype Variant mr = Variant mr


{-----------------------------------------------------------------------------}

-- Turn proxy sequence into sequence of Nothings

class HMaybied r r' | r -> r'
 where
  hMaybied :: r -> r'

instance HMaybied HNil HNil
 where
  hMaybied _ = HNil

instance HMaybied r r'
      => HMaybied (HCons (LVPair l (Proxy v)) r) (HCons (LVPair l (Maybe v)) r')
 where
  hMaybied (HCons _ r) = HCons (LVPair Nothing) (hMaybied r)


{-----------------------------------------------------------------------------}

-- Public constructor

mkVariant :: ( RecordLabels v ls
             , HFind x ls n
             , HMaybied v v'
             , HUpdateAtHNat n (LVPair x (Maybe y)) v' v'
             )
          => x -> y -> (Record v) -> Variant v'

mkVariant x y (Record v) = Variant v'
 where
  n       = hFind x (recordLabels' v)
  ms      = hMaybied v
  v'      = hUpdateAtHNat n (newLVPair x (Just y)) ms


{-----------------------------------------------------------------------------}

-- Public destructor

unVariant :: ( RecordLabels v ls
             , HFind x ls n
             , HLookupByHNat n v (LVPair x (Maybe y))
             )
          => x -> Variant v -> Maybe y

unVariant x (Variant v) = y
 where
  n       = hFind x (recordLabels' v)
  LVPair y     = hLookupByHNat n v


{-----------------------------------------------------------------------------}

-- Variants are opaque

instance Show (Variant v)
 where
  show _ = "<Cannot show Variant content!>"


{-----------------------------------------------------------------------------}
