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

fam = undefined :: Fam IC '[]
testFam = Fam (ConsCh (TaggedChAttr (ch_i) (ConsAtt (smin .=. 3) EmptyAtt))
               EmptyCh)
          (EmptyAtt)

     
leaf_smin (Fam chi par)
  = syndef smin (lookupByLabelAtt (Label :: Label Val) (hLookupByChild ch_i chi))

node_smin (Fam chi par)
  = syndef smin ((lookupByLabelAtt smin (hLookupByChild ch_l chi))
                  `min`
                 (lookupByLabelAtt smin (hLookupByChild ch_r chi)))

root_ival (Fam chi par)
  = inhdef ival (HCons nt_Tree HNil)
    ( (ch_tree =. (lookupByLabelAtt smin (hLookupByChild ch_tree chi)))
      `ConsR` EmptyR)

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


root_smin (Fam chi par)
  = syndef smin (lookupByLabelAtt smin (hLookupByChild ch_tree chi))



asp_smin =       (p_Leaf =. leaf_smin) `ConsR` ((p_Node =. node_smin) `ConsR` ((p_Root =. root_smin) `ConsR` EmptyR))

asp_ival = (p_Root =. root_ival) `ConsR` ((p_Node =. node_ival) `ConsR` EmptyR)
asp_sres = (p_Root =. root_sres) `ConsR` ((p_Node =. node_sres)
                                 `ConsR` ((p_Leaf =. leaf_sres)`ConsR` EmptyR))




sem_Root asp (Root t)
  = knit (hLookupByLabelRec p_Root asp) (  ch_tree =. sem_Tree asp t 
                                        *. EmptyR )
  
sem_Tree asp (Node left right)
  = knit (hLookupByLabelRec p_Node asp) (  ch_l =. sem_Tree asp left 
                                        *. ch_r =. sem_Tree asp right 
                                        *. EmptyR )

sem_Tree asp (Leaf i)
  = knit (hLookupByLabelRec p_Leaf asp) (  ch_i =. (sem_Lit i) 
                                        *. EmptyR )


sem_Lit :: Int -> Attribution '[] -> Attribution ( '(Val, Int) ': '[])
sem_Lit e EmptyAtt = ((Label) .=. e) `ConsAtt` EmptyAtt 


--repmin tree = lookupByLabelAtt smin $ sem_Root asp_smin (Root tree) EmptyAtt

tree = Leaf 4



examplet =    (Node (Node (Node (Leaf (-45)) (Leaf 4))
                          (Node (Leaf 2) (Leaf 7))
                    )

                    (Node (Node (Leaf 9) (Leaf (-23)))
                          (Leaf 6)
                    )
              )

--minimo = sem_Tree (asp_smin) examplet EmptyAtt


asp_smin
  :: (Ord val1, HasChild (Ch_i, Int) r4 r5,
      HasChild (Ch_r, Tree) r3 r6, HasChild (Ch_l, Tree) r3 r7,
      HasChild (Ch_tree, Tree) r8 r9, HasFieldAtt Val r5 val2,
      HasFieldAtt Att_smin r6 val1, HasFieldAtt Att_smin r7 val1,
      HasFieldAtt Att_smin r9 val3, LabelSet ('(Att_smin, val2) : sp1),
      LabelSet ('(Att_smin, val1) : sp2),
      LabelSet ('(Att_smin, val3) : sp3)) =>
     Record
       '[ '(P_Leaf,
           Fam r4 p1 -> Fam ic1 sp1 -> Fam ic1 ('(Att_smin, val2) : sp1)),
         '(P_Node,
           Fam r3 p2 -> Fam ic2 sp2 -> Fam ic2 ('(Att_smin, val1) : sp2)),
         '(P_Root,
           Fam r8 p3 -> Fam ic3 sp3 -> Fam ic3 ('(Att_smin, val3) : sp3))]


-- asp_smin
--   :: (HasChild (Ch_i, Int) r4 r5, HasChild (Ch_r, Tree) r3 r6,
--       HasChild (Ch_l, Tree) r3 r7, HasFieldAtt Val r5 val1,
--       HasFieldAtt Att_smin r6 val2, HasFieldAtt Att_smin r7 val2,
--       Ord val2, LabelSet ('(Att_smin, val1) : sp1),
--       LabelSet ('(Att_smin, val2) : sp2)) =>
--      Record
--        '[ '(P_Leaf,
--            Fam r4 p1 -> Fam ic1 sp1 -> Fam ic1 ('(Att_smin, val1) : sp1)),
--          '(P_Node,
--            Fam r3 p2 -> Fam ic2 sp2 -> Fam ic2 ('(Att_smin, val2) : sp2))]

asp_ival
  :: (HasChild (Ch_tree, Tree) r2 r1,
      SingleDef
        (HasLabelChildAttsRes (Ch_tree, Tree) ic'4)
        'True
        Att_ival
        (Tagged (Ch_tree, Tree) v1)
        ic'4
        ic'5,
      SingleDef
        (HasLabelChildAttsRes (Ch_l, Tree) ic'6)
        'True
        Att_ival
        (Tagged (Ch_l, Tree) v2)
        ic'6
        ic'3,
      SingleDef
        (HasLabelChildAttsRes (Ch_r, Tree) ic'7)
        'True
        Att_ival
        (Tagged (Ch_r, Tree) v2)
        ic'7
        ic'6,
      HasLabelChildAtts (Ch_tree, Tree) ic'4,
      HasLabelChildAtts (Ch_l, Tree) ic'6,
      HasLabelChildAtts (Ch_r, Tree) ic'7, HasFieldAtt Att_smin r1 v1,
      HasFieldAtt Att_ival r v2) =>
     Record
       '[ '(P_Root, Fam r2 p -> Fam ic'4 sp1 -> Fam ic'5 sp1),
         '(P_Node, Fam c r -> Fam ic'7 sp2 -> Fam ic'3 sp2)]
asp_sres
  :: (HasChild (Ch_tree, Tree) r4 r5, HasChild (Ch_r, Tree) r3 r6,
      HasChild (Ch_l, Tree) r3 r7, HasFieldAtt Att_sres r5 val,
      HasFieldAtt Att_sres r6 Tree, HasFieldAtt Att_sres r7 Tree,
      HasFieldAtt Att_ival r Int, LabelSet ('(Att_sres, Tree) : sp2),
      LabelSet ('(Att_sres, Tree) : sp3),
      LabelSet ('(Att_sres, val) : sp1)) =>
     Record
       '[ '(P_Root,
           Fam r4 p1 -> Fam ic1 sp1 -> Fam ic1 ('(Att_sres, val) : sp1)),
         '(P_Node,
           Fam r3 p2 -> Fam ic2 sp2 -> Fam ic2 ('(Att_sres, Tree) : sp2)),
         '(P_Leaf,
           Fam c r -> Fam ic3 sp3 -> Fam ic3 ('(Att_sres, Tree) : sp3))]
