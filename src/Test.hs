{-# LANGUAGE TypeInType,
             GADTs,
             KindSignatures,
             TypeOperators,
             TypeFamilies,
             MultiParamTypeClasses,
             FlexibleInstances,
             FlexibleContexts,
             StandaloneDeriving,
             UndecidableInstances,
             FunctionalDependencies,
             ConstraintKinds,
             ScopedTypeVariables,
             AllowAmbiguousTypes,
             UnicodeSyntax#-}

module Test where

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

data Root = Root Tree
          deriving Show
data Tree = Leaf Int
          | Node Tree Tree
          deriving Show

--emptyRule ∷ Rule '[] '[] '[] '[] '[] '[]
--emptyRule = \r -> id

-- Labels (attribute names) for the example
data Att_smin; smin = Label :: Label Att_smin
data Att_ival; ival = Label :: Label Att_ival
data Att_sres; sres = Label :: Label Att_sres

-- Labels for childs
data Ch_tree -- root
data Ch_r    -- node
data Ch_l    -- node
data Ch_i    -- leaf

----non terminals
nt_Root = undefined :: Root
nt_Tree = undefined :: Tree
-- TODO change to labels? (change defs)

ch_tree = Label :: Label (Ch_tree, Tree)
ch_r    = Label :: Label (Ch_r, Tree)
ch_l    = Label :: Label (Ch_l, Tree)
ch_i    = Label :: Label (Ch_i, Int)

data P_Root; p_Root = Label :: Label (P_Root)
data P_Node; p_Node = Label :: Label (P_Node)
data P_Leaf; p_Leaf = Label :: Label (P_Leaf)  

type SP = '[ '(Att_smin,Int), '(Att_sres, Tree)]
type IL = '[ '(Att_ival, Int)]
type IR = '[ '(Att_ival, Int)]

type IC = '[ '((Ch_l,Tree),IL), '((Ch_r, Tree),IR)]

type Output_Node_Fam = Fam IC SP

leaf_smin
  :: (LabelSet ('(Att_smin, Attribution v) : sp),
      HasChild (Ch_i, Int) r v) =>
     Fam r p -> Fam ic sp -> Fam ic ('(Att_smin, Attribution v) : sp)

node_smin
  :: (LabelSet ('(Att_smin, val) : sp), Ord val,
      HasFieldAtt Att_smin r1 val, HasFieldAtt Att_smin r2 val,
      HasChild (Ch_l, Tree) r3 r1, HasChild (Ch_r, Tree) r3 r2) =>
     Fam r3 p -> Fam ic sp -> Fam ic ('(Att_smin, val) : sp)
     
leaf_smin (Fam chi par)
  = syndef smin (hLookupByChild ch_i chi)
node_smin (Fam chi par)
  = syndef smin ((lookupByLabelAtt smin (hLookupByChild ch_l chi))
                  `min`
                 (lookupByLabelAtt smin (hLookupByChild ch_r chi)))

root_ival (Fam chi par)
  = inhdef ival (HCons nt_Tree HNil)
    ( (ch_tree =. (lookupByLabelAtt smin (hLookupByChild ch_tree chi))) `ConsR` EmptyR)

node_ival (Fam chi par)
  = inhdef ival (HCons nt_Tree HNil)
     ((ch_l =. (lookupByLabelAtt ival par))  `ConsR`
     ((ch_r =. (lookupByLabelAtt ival par)) `ConsR` EmptyR))

root_sres (Fam chi par)
  = syndef sres (lookupByLabelAtt sres (hLookupByChild ch_tree chi))

leaf_sres (Fam chi par)
  = syndef sres (Leaf (lookupByLabelAtt ival par))

node_sres (Fam chi par)
  = syndef sres (Node (lookupByLabelAtt sres (hLookupByChild ch_l chi))
                      (lookupByLabelAtt sres (hLookupByChild ch_r chi)))


--asp_smin = (p_Leaf =. leaf_smin) `ConsR` 
--           ((p_Node =. node_smin) `ConsR` EmptyR)
