{-# OPTIONS -XMultiParamTypeClasses -XFunctionalDependencies
            -XFlexibleContexts -XFlexibleInstances
            -XUndecidableInstances
            -XExistentialQuantification
            -XEmptyDataDecls -XRank2Types
            -XTypeSynonymInstances -XTypeFamilies -XPolyKinds #-}

import HList
import FakePrelude hiding (Apply,apply)
import HArray
import HListPrelude
import Record hiding (hUpdateAtLabel)
import GhcSyntax


{-
class Apply2 f a r | f a -> r where

  apply2 :: f -> a -> r
  apply2 = undefined
-}

class Apply2 f a where
  type ApplyRes f a
  apply2 :: f -> a -> ApplyRes f a
  apply2 = undefined

data Fam c p = Fam c p

type Rule sc ip ic sp ic' sp'
  = Fam sc ip -> Fam ic sp -> Fam ic' sp'

data FnSyn att = FnSyn att


instance HExtend (LVPair att val) sp sp'
   => ApplyRule ic sp sp' (FnSyn att) (Fam sc ip -> val) where
  type ApplyRuleRes ic sp sp' (FnSyn att) (Fam sc ip -> val) = Rule sc ip ic sp ic sp'
  applyRule = undefined



class ApplyRule ic sp sp' f a where
  type ApplyRuleRes ic sp sp' f a
  applyRule :: ic -> sp -> sp' -> f -> a -> ApplyRuleRes ic sp sp' f a
  applyRule = undefined



instance ( HAllTaggedLV sp
         , HExtendR Record (Tagged att val) sp ~ sp'
         , HLabelSet (Label att : LabelsOf sp))
           =>
  Apply (FnSyn att) (Fam sc ip -> val)
        (Rule sc ip ic sp ic sp') where
  apply (FnSyn _) f =  syndef (Label :: Label att) . f
