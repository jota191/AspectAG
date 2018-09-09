{-# LANGUAGE 
             FlexibleInstances,
             FlexibleContexts,
             DataKinds,
             TypeOperators
#-}

module Aspects where

import HList
import Attribution
import Record
import Attribute
import Data.Kind
import Data.Tagged
import TPrelude
import AspectAG
import TagUtils
import ChildAtts
import Test

asp_smin = (p_Leaf =. leaf_smin)`ConsR` ((p_Node =. node_smin)`ConsR` EmptyR)

asp_smin :: (LabelSet ('(Att_smin, val) : sp1),
      LabelSet ('(Att_smin, Attribution v) : sp2), Ord val,
      HasFieldAtt Att_smin r1 val, HasFieldAtt Att_smin r2 val,
      HasChild (Ch_i, Int) r v, HasChild (Ch_l, Tree) r3 r1,
      HasChild (Ch_r, Tree) r3 r2) =>
     Record
       '[ '(P_Leaf,
           Fam r p1
           -> Fam ic1 sp2 -> Fam ic1 ('(Att_smin, Attribution v) : sp2)),
         '(P_Node,
           Fam r3 p2 -> Fam ic2 sp1 -> Fam ic2 ('(Att_smin, val) : sp1))]
