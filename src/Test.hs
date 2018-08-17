
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
             UnicodeSyntax,
             NoMonomorphismRestriction
#-}

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
data Val



leaf_smin (Fam chi par)
  = syndef smin (lookupByLabelAtt ch_i (hLookupByChild ch_i chi))
-- = syndef smin (hLookupByChild ch_i chi)

node_smin (Fam chi par)
  = syndef smin ((lookupByLabelAtt smin (hLookupByChild ch_l chi))
                  `min`
                 (lookupByLabelAtt smin (hLookupByChild ch_r chi)))




root_smin (Fam chi par)
  = syndef smin (lookupByLabelAtt smin (hLookupByChild ch_tree chi))


root_ival (Fam chi par)
  = inhdef ival (HCons nt_Tree (HCons nt_Root HNil))
    ( (ch_tree =. (lookupByLabelAtt smin (hLookupByChild ch_tree chi)))
      `ConsR` EmptyR)

node_ival (Fam chi par)
  = inhdef ival (HCons nt_Tree (HCons nt_Root HNil))
     ((ch_l =. (lookupByLabelAtt ival par))  `ConsR`
     ((ch_r =. (lookupByLabelAtt ival par)) `ConsR` EmptyR))

leaf_ival (Fam chi par) = inhdef ival (HCons nt_Tree (HCons nt_Root HNil))
                       ((ch_i =. (lookupByLabelAtt ival par)) `ConsR` EmptyR)

root_sres (Fam chi par)
  = syndef sres (lookupByLabelAtt sres (hLookupByChild ch_tree chi))

leaf_sres (Fam chi par)
  = syndef sres (Leaf (lookupByLabelAtt ival par))

node_sres (Fam chi par)
  = syndef sres (Node (lookupByLabelAtt sres (hLookupByChild ch_l chi))
                      (lookupByLabelAtt sres (hLookupByChild ch_r chi)))


asp_smin = (p_Leaf =. leaf_smin)
  `ConsR` ((p_Node =. node_smin)
  `ConsR` ((p_Root =. root_smin)
  `ConsR` EmptyR))

asp_ival = (p_Root =. root_ival)
  `ConsR` ((p_Node =. node_ival)
  `ConsR` ((p_Leaf =. leaf_ival)
  `ConsR` EmptyR))
  
asp_sres = (p_Root =. root_sres)
  `ConsR` ((p_Node =. node_sres)
  `ConsR` ((p_Leaf =. leaf_sres)
  `ConsR` EmptyR))

----catamorphism
sem_Tree  asp (Node l r) = knit (hLookupByLabelRec p_Node asp )
                                ((ch_l =. sem_Tree asp l)`ConsR`
                                ((ch_r =. sem_Tree asp r) `ConsR` EmptyR))

sem_Tree  asp (Leaf i) = knit (hLookupByLabelRec p_Leaf asp)
                         ((ch_i =. sem_Lit i) `ConsR` EmptyR )

sem_Root  asp (Root t) = knit (hLookupByLabelRec p_Root asp)
                              ((ch_tree =. sem_Tree asp t) 
                              `ConsR` EmptyR )

sem_Lit :: Int -> Attribution '[ '((Ch_i, Int), a)] -> Attribution '[ '((Ch_i, Int), Int)]
sem_Lit i _ = (ch_i .=. i) `ConsAtt` EmptyAtt



--minimo = lookupByLabelAtt smin (sem_Tree (asp_smin) examplet EmptyR)

{-

data IntList = Nil
             | Cons Int IntList
             deriving Show
data V a = V a

-- non terminals
nt_Cons = Label :: Label IntList

----productions
data P_Cons;   p_Cons   = Label :: Label P_Cons
data P_Nil;    p_Nil    = Label :: Label P_Nil


--children labels
data Ch_c;      ch_c     = Label :: Label (Ch_c,IntList)
data Ch_v;      ch_v     = Label :: Label (Ch_v,Int)

-- cata
sem_List asp (Cons v c) = knit (hLookupByLabelRec  p_Cons asp)
                               ((ch_c =. sem_List asp c) 
                               `ConsR` ((ch_v =. sem_Lit v)
                               `ConsR` EmptyR ))

sem_List  asp (Nil) = knit (hLookupByLabelRec p_Nil asp)
                           ((ch_v  =. sem_Lit (0::Int)) 
                            `ConsR` EmptyR )


--sem_Lit :: Int -> Attribution '[] -> Int --Attribution ( '(Val, Int) ': '[])
--sem_Lit e EmptyAtt = e -- ((Label) .=. e) `ConsAtt` EmptyAtt 
sem_Lit :: Int -> Attribution '[] -> Attribution '[ '(Att_ssum, Int)]
sem_Lit v _ = (ConsAtt (ssum .=. v) EmptyAtt)

data Att_ssum;   ssum = Label :: Label Att_ssum

nil_ssum (Fam chi par)
  = syndef ssum(lookupByLabelAtt(Label::Label Val) (hLookupByChild ch_v chi))

cons_ssum (Fam chi par)
  = syndef ssum $ (lookupByLabelAtt ssum (hLookupByChild ch_c chi))
                   +
                  (lookupByLabelAtt(Label::Label Val) (hLookupByChild ch_v chi))


asp_ssum
  :: (LabelSet ('(Att_ssum, val1) : sp1),
      LabelSet ('(Att_ssum, val2) : sp2), Num val2,
      HasFieldAtt Att_ssum r4 val2, HasFieldAtt Val r5 val1,
      HasFieldAtt Val r6 val2, HasChild (Ch_c, IntList) r3 r4,
      HasChild (Ch_v, Int) r7 r5, HasChild (Ch_v, Int) r3 r6) =>
     Record
       '[ '(P_Nil,
           Fam r7 p1 -> Fam ic1 sp1 -> Fam ic1 ('(Att_ssum, val1) : sp1)),
         '(P_Cons,
           Fam r3 p2 -> Fam ic2 sp2 -> Fam ic2 ('(Att_ssum, val2) : sp2))]

asp_ssum = (p_Nil  =. nil_ssum) `ConsR` ((p_Cons =. cons_ssum) `ConsR` EmptyR)

--asp_ssum =    (p_Nil  .=. nil_ssum) .*. (p_Cons .=. cons_ssum) .*. emptyRecord

--suma= lookupByLabelAtt ssum (sem_List (asp_ssum) examplel EmptyAtt)
examplel = (Cons 5 (Cons 4 Nil))

-- sumalista = (sem_List (asp_ssum) examplel emptyRecord) # ssum

-}




examplet =    (Node (Node (Node (Leaf 3) (Leaf 4))
                          (Node (Leaf 2) (Leaf 7))
                    )

                    (Node (Node (Leaf 9) (Leaf (-23)))
                          (Leaf 6)
                    )
              )
