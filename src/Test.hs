
{-# LANGUAGE TypeInType,
             TypeFamilies,
             FlexibleContexts,
             ScopedTypeVariables,
             NoMonomorphismRestriction,
             AllowAmbiguousTypes
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
data Att_ssum; ssum = Label :: Label Att_ssum

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



leaf_smin (Fam chi par)
  = syndef smin (lookupByLabelAtt ch_i (hLookupByChild ch_i chi))
-- = syndef smin (hLookupByChild ch_i chi)

node_smin (Fam chi par)
  = syndef smin ((lookupByLabelAtt smin (hLookupByChild ch_l chi))
                  `min`
                 (lookupByLabelAtt smin (hLookupByChild ch_r chi)))
root_smin (Fam chi par)
  = syndef smin (lookupByLabelAtt smin (hLookupByChild ch_tree chi))


node_ssum (Fam chi par)
  = syndef ssum ((lookupByLabelAtt ssum (hLookupByChild ch_l chi))
                  +
                 (lookupByLabelAtt ssum (hLookupByChild ch_r chi)))
leaf_ssum (Fam chi par)
  = syndef ssum (lookupByLabelAtt ch_i (hLookupByChild ch_i chi))


asp_ssum =  (p_Leaf =. leaf_ssum)
   `ConsR` ((p_Node =. node_ssum)
   `ConsR` EmptyR)


asp_ival = (p_Root =. root_ival)
   `ConsR` ((p_Node =. node_ival)
   `ConsR` EmptyR)
asp_sres = (p_Root =. root_sres)
   `ConsR` ((p_Node =. node_sres)
   `ConsR` ((p_Leaf =. leaf_sres)
   `ConsR` EmptyR))
asp_smin =  (p_Leaf =. leaf_smin)
   `ConsR` ((p_Node =. node_smin)
   `ConsR` EmptyR)


asp_repmin = asp_smin .+. asp_sres .+. asp_ival


----catamorphism
sem_Tree  asp (Node l r) = knit (hLookupByLabelRec p_Node asp )
                                ((ch_l =. sem_Tree asp l)`ConsR`
                                ((ch_r =. sem_Tree asp r) `ConsR` EmptyR))
-- sem_Tree asp (Leaf i) 
--    =  \_ -> ((smin .=. i) `ConsAtt` EmptyAtt)


sem_Tree  asp (Leaf i) = knit (hLookupByLabelRec p_Leaf asp)
                         ((ch_i =. sem_Lit i) `ConsR` EmptyR )


sem_Root  asp (Root t) = knit (hLookupByLabelRec p_Root asp)
                              ((ch_tree =. sem_Tree asp t) 
                              `ConsR` EmptyR )

sem_Lit :: Int -> Attribution p
        -> Attribution '[ '((Ch_i, Int), Int)]
sem_Lit i _ = (ch_i .=. i) `ConsAtt` EmptyAtt



minimo t = lookupByLabelAtt smin (sem_Tree (asp_smin) t EmptyAtt)

-- repmin t
--   = lookupByLabelAtt sres ((sem_Root (asp_repmin) (Root t) EmptyAtt) :: Attribution '[ '(Att_sres, Tree)])


examplet =    (Node (Node (Node (Leaf 3) (Leaf 4))
                          (Node (Leaf 2) (Leaf 7))
                    )

                    (Node (Node (Leaf (5)) (Leaf (27)))
                          (Leaf 6)
                    )
              )


exampleT 0 = examplet
exampleT n = Node (exampleT (n-1)) (exampleT (n-1))

  
