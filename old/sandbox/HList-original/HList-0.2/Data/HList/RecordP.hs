{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts,
  UndecidableInstances, FlexibleInstances #-}
{-# OPTIONS -fglasgow-exts #-}

{-
   The HList library

   (C) 2004-2006, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

   Extensible records: labels are phantom, so at run-time, the record
   is just a heterogenous list of field values.
   This sort of record is generalizable to `tables' (which are, at
   run-time, a list or a map containing the heterogenous lists
   of field values).

   The are different models of labels that go with this module;
   see the files Label?.hs.
-}

module Data.HList.RecordP where

import Data.HList.FakePrelude
import Data.HList.HListPrelude
import Data.HList.Record
import Data.HList.HArray

{-----------------------------------------------------------------------------}

-- Record types as Phantom labels with values

newtype RecordP ls vs = RecordP vs


-- Build a record. I wonder if the 'ls' argument of mkRecordP can be
-- removed. So far, we had no need for it...

mkRecordP :: (HSameLength ls vs, HLabelSet ls) => ls -> vs -> RecordP ls vs
mkRecordP _ vs = RecordP vs

-- The contraint that two HLists have the same length
class HSameLength l1 l2
instance HSameLength HNil HNil
instance HSameLength l1 l2 => HSameLength (HCons e1 l1) (HCons e2 l2)

-- Build an empty record
emptyRecordP :: RecordP HNil HNil
emptyRecordP = mkRecordP HNil HNil

-- Converting between RecordP and Record (label/value pairs)

-- The following class declares a bijection between Record and recordP
class HRLabelSet r => RecordR2P r ls vs | r -> ls vs, ls vs -> r where
    record_r2p :: Record r -> RecordP ls vs
    record_p2r :: RecordP ls vs -> Record r

instance RecordR2P HNil HNil HNil where
    record_r2p _ = emptyRecordP
    record_p2r _ = emptyRecord

instance (RecordR2P r ls vs, HRLabelSet (HCons (LVPair l v) r),
          HLabelSet (HCons l ls), HSameLength ls vs)
    => RecordR2P (HCons (LVPair l v) r) (HCons l ls) (HCons v vs) where
    record_r2p (Record (HCons f r)) = hExtend f (record_r2p (Record r))
    record_p2r (RecordP (HCons v r)) = hExtend (LVPair v) (record_p2r (RecordP r))

labels_of_recordp :: RecordP ls vs -> ls
labels_of_recordp = undefined


{-----------------------------------------------------------------------------}

-- A Show instance to appeal to normal records
-- to save the coding time (rather than run-time), we just
-- convert RecordP to regular Record, which we know how to show

instance (RecordR2P r ls vs, ShowComponents r, HRLabelSet r) =>
    Show (RecordP ls vs) where show rp = show $ record_p2r rp


{-----------------------------------------------------------------------------}

-- Extension for records

instance (HLabelSet (HCons l ls), HSameLength ls vs)
    => HExtend (LVPair l v) (RecordP ls vs) (RecordP (HCons l ls) (HCons v vs))
 where
  hExtend (LVPair v) (RecordP vs) = mkRecordP undefined (HCons v vs)


{-----------------------------------------------------------------------------}

-- Record concatenation

instance ( HLabelSet ls''
         , HAppend ls ls' ls''
         , HAppend vs vs' vs''
         , HSameLength ls'' vs''
         )
    => HAppend (RecordP ls vs) (RecordP ls' vs') (RecordP ls'' vs'')
 where
  hAppend (RecordP vs) (RecordP vs') = mkRecordP undefined (hAppend vs vs')

{-----------------------------------------------------------------------------}

-- Lookup operation

-- Because hLookupByLabel is so frequent and important, we
-- implement it separately. The algorithm is familiar assq,
-- only the comparison operation is done at compile-time

instance (HEq l l' b, HasFieldP' b l (RecordP (HCons l' ls) vs) v)
    => HasField l (RecordP (HCons l' ls) vs) v where
    hLookupByLabel = hLookupByLabelP' (undefined::b)

class HasFieldP' b l r v | b l r -> v where
    hLookupByLabelP' :: b -> l -> r -> v

instance HasFieldP' HTrue l (RecordP (HCons l ls) (HCons v vs)) v where
    hLookupByLabelP' _ _ (RecordP (HCons v _)) = v

instance HasField l (RecordP ls vs) v
    => HasFieldP' HFalse l (RecordP (HCons l' ls) (HCons v' vs)) v where
    hLookupByLabelP' _ l (RecordP (HCons _ vs)) =
        hLookupByLabel l ((RecordP vs)::RecordP ls vs)


{-----------------------------------------------------------------------------}

-- Delete operation
hDeleteAtLabelP :: HProjectByLabelP l ls vs lso v vso =>
                   l -> RecordP ls vs -> RecordP lso vso
hDeleteAtLabelP l r = snd $ h2ProjectByLabelP l r


{-----------------------------------------------------------------------------}

-- Update operation
hUpdateAtLabelP :: (HUpdateAtHNat n e1 t1 l', HFind e t n) => e -> e1 -> RecordP t t1 -> RecordP ls l'
hUpdateAtLabelP l v rp@(RecordP vs) = RecordP (hUpdateAtHNat n v vs)
 where
  n       = hFind l (labels_of_recordp rp)

{-----------------------------------------------------------------------------}
-- Projection for records
-- It is also an important operation: the basis of many
-- deconstructors -- so we try to implement it efficiently.

-- Project by a single label
class HProjectByLabelP l ls vs lso v vso | l ls vs -> lso v vso where
    h2ProjectByLabelP :: l -> RecordP ls vs -> (v,RecordP lso vso)

instance (HEq l l' b, HProjectByLabelP' b l (HCons l' ls) vs lso v vso)
    => HProjectByLabelP l (HCons l' ls) vs lso v vso where
    h2ProjectByLabelP = h2ProjectByLabelP' (undefined::b)

class HProjectByLabelP' b l ls vs lso v vso | b l ls vs -> lso v vso where
    h2ProjectByLabelP' :: b -> l -> RecordP ls vs -> (v,RecordP lso vso)

instance HProjectByLabelP' HTrue l (HCons l ls) (HCons v vs) ls v vs where
    h2ProjectByLabelP' _ _ (RecordP (HCons v vs)) = (v,RecordP vs)

instance (HProjectByLabelP l ls vs lso' v vso')
    => HProjectByLabelP' HFalse l (HCons l' ls) (HCons v' vs)
       (HCons l' lso') v (HCons v' vso') where
    h2ProjectByLabelP' _ l (RecordP (HCons v' vs)) =
        let (v,RecordP vso) = h2ProjectByLabelP l ((RecordP vs)::RecordP ls vs)
        in (v, RecordP (HCons v' vso))


-- Invariant: r = rin `disjoint-union` rout
--            labels(rin) = ls
-- classes H2ProjectByLabels and H2ProjectByLabels' are declared in
-- Record.hs

instance H2ProjectByLabels (HCons l ls)
                           (RecordP HNil HNil) (RecordP HNil HNil)
                           (RecordP HNil HNil)
    where
    h2projectByLabels _ _ = (emptyRecordP,emptyRecordP)

instance (HMember l' ls b,
          H2ProjectByLabels' b ls (RecordP (HCons l' ls') vs') rin rout)
    => H2ProjectByLabels ls (RecordP (HCons l' ls') vs') rin rout where
    h2projectByLabels = h2projectByLabels' (undefined::b)

instance H2ProjectByLabels ls (RecordP ls' vs') (RecordP lin vin) rout =>
    H2ProjectByLabels' HTrue ls (RecordP (HCons l' ls') (HCons v' vs'))
                             (RecordP (HCons l' lin) (HCons v' vin)) rout where
    h2projectByLabels' _ ls (RecordP (HCons v' vs')) =
        (RecordP (HCons v' vin), rout)
        where (RecordP vin,rout) =
                  h2projectByLabels ls ((RecordP vs')::RecordP ls' vs')

instance H2ProjectByLabels ls (RecordP ls' vs') rin (RecordP lo vo) =>
    H2ProjectByLabels' HFalse ls (RecordP (HCons l' ls') (HCons v' vs'))
                              rin (RecordP (HCons l' lo) (HCons v' vo)) where
    h2projectByLabels' _ ls (RecordP (HCons v' vs')) =
        (rin, RecordP (HCons v' vo))
        where (rin,RecordP vo) =
                  h2projectByLabels ls ((RecordP vs')::RecordP ls' vs')


{-----------------------------------------------------------------------------}

-- Subtyping for records

-- Hmm, a bit too conservative. It works for all our examples,
-- where the record extension is by simple extension. In the future,
-- we should account for possible field permutation.

instance H2ProjectByLabels ls' (RecordP ls vs) (RecordP ls' vs') rout
    =>  SubType (RecordP ls vs) (RecordP ls' vs')
