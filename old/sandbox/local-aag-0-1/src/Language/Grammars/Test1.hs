{-# OPTIONS -fcontext-stack=100 #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Test1 where

import AspectAG
import GhcSyntax
import HList
import FakePrelude
import HListPrelude
import Record
import HArray



--data types-------------------------------------------------------------------
data Root = Root Tree
          deriving Show

data Tree = Node Tree Tree
          | Leaf Int
          deriving Show


--data types' dependent definitions

----non terminals
nt_Root = proxy::Proxy Root
nt_Tree = proxy::Proxy Tree

----productions
data P_Root;   p_Root    = proxy::Proxy P_Root
data P_Node;   p_Node    = proxy::Proxy P_Node
data P_Leaf;   p_Leaf    = proxy::Proxy P_Leaf

----children labels
data Ch_tree;   ch_tree  = proxy::Proxy (Ch_tree, Tree)
data Ch_l;      ch_l     = proxy::Proxy (Ch_l,    Tree)
data Ch_r;      ch_r     = proxy::Proxy (Ch_r,    Tree)
data Ch_i;      ch_i     = proxy::Proxy (Ch_i,    Int)

----catamorphism
sem_Tree  asp (Node l r) = knit (asp # p_Node) (   ch_l .=. sem_Tree asp l 
                                               .*. ch_r .=. sem_Tree asp r
                                               .*. emptyRecord )
sem_Tree  asp (Leaf i) = knit (asp # p_Leaf)(ch_i .=. sem_Lit i 
                                                  .*. emptyRecord )
sem_Root  asp (Root t) = knit (asp # p_Root)(ch_tree .=. sem_Tree asp t 
                                                     .*. emptyRecord )


--repmin-----------------------------------------------------------------------

data Att_smin;   smin    = proxy::Proxy Att_smin
data Att_ival;   ival    = proxy::Proxy Att_ival
data Att_sres;   sres    = proxy::Proxy Att_sres




leaf_smin (Fam chi par)
  = syndef smin (chi # ch_i)

node_smin (Fam chi par)
  = syndef smin (((chi #ch_l) # smin)
                  `min`
                 ((chi #ch_r) # smin))

root_ival (Fam chi par)
  = inhdef ival (nt_Tree .*. HNil)
    ((ch_tree .=. ((chi # ch_tree) # smin)) .*. emptyRecord)

node_ival (Fam chi par)
  = inhdef ival (nt_Tree .*. HNil)
     ((ch_l .=. (par # ival))  .*.
     ((ch_r .=. (par # ival))  .*. emptyRecord))

root_sres (Fam chi par)
  = syndef sres ((chi # ch_tree) # sres)

leaf_sres (Fam chi par)
  = syndef sres (Leaf (par # ival))


node_sres (Fam chi par)
  = syndef sres (Node ((chi # ch_l)# sres)
                      ((chi # ch_r)# sres))



asp_smin =    (p_Leaf .=. leaf_smin)
          .*. (p_Node .=. node_smin)
          .*. emptyRecord



asp_ival =     (p_Root .=. root_ival)
           .*. (p_Node .=. node_ival)
           .*. emptyRecord


asp_sres =     (p_Root .=. root_sres)
           .*. (p_Node .=. node_sres)
           .*. (p_Leaf .=. leaf_sres)
           .*. emptyRecord



asp_repmin =  asp_smin .+. asp_sres .+. asp_ival 

repmin tree = sem_Root (asp_repmin) (Root tree) () # sres


               

----example--------------------------------------------------------------------


examplet =    (Node (Node (Node (Leaf 3) (Leaf 4))
                          (Node (Leaf 2) (Leaf 7))
                    )

                    (Node (Node (Leaf 9) (Leaf (-23)))
                          (Leaf 6)
                    )
              )

minimo = (sem_Tree (asp_smin) examplet emptyRecord) # smin

rep = repmin examplet


data IntList = Nil
             | Cons Val IntList
             deriving Show

data Val = Val Int deriving Show

-- non terminals
nt_Cons = proxy :: Proxy IntList


----productions
data P_Cons;   p_Cons   = proxy::Proxy P_Cons
data P_Nil;    p_Nil    = proxy::Proxy P_Nil
data P_Val;    p_Val   = proxy::Proxy P_Val

--children labels
data Ch_c;      ch_c     = proxy::Proxy (Ch_c,IntList)
data Ch_v;      ch_v     = proxy::Proxy (Ch_v,Val)
data Ch_raw;    ch_raw   = proxy::Proxy (Ch_raw,Int)


-- cata
sem_List  asp (Cons v c) = knit (asp # p_Cons) (   ch_c .=. sem_List asp c 
                                               .*. ch_v .=. sem_Val asp v
                                               .*. emptyRecord )
sem_List  asp (Nil) = knit (asp # p_Nil) (  ch_v  .=. sem_Lit (0::Int) 
                                        .*. emptyRecord )

sem_Val asp (Val v) = knit (asp # p_Val) ( ch_raw  .=. sem_Lit v 
                                        .*. emptyRecord )

-- | Semantic function of a terminal
sem_Lit :: a -> Record HNil -> a
sem_Lit e (Record HNil) = e


data Att_ssum;   ssum    = proxy::Proxy Att_ssum

nil_ssum (Fam chi par)
  = syndef ssum ((chi # ch_v)#ssum)

cons_ssum (Fam chi par)
  = syndef ssum $ ((chi # ch_c)# ssum) + ((chi # ch_v)#ssum)

val_ssum (Fam chi par)
  = syndef ssum $ ((chi # ch_v)# ssum)


--asp_ssum
--   = (p_Val .=. val_ssum) .*. (p_Nil  .=. nil_ssum) .*. (p_Cons .=. cons_ssum) .*. emptyRecord

--suma = (sem_List (asp_ssum) examplel emptyRecord) # ssum


examplel = (Cons (Val 5) (Cons (Val 4) Nil))

--sumalista = (sem_List (asp_ssum) examplel emptyRecord) # ssum


instance HEq (Proxy (Ch_c, IntList)) (Proxy (Ch_v, Int)) HFalse
instance HEq (Proxy P_Cons) (Proxy P_Nil) HFalse
instance HEq (Proxy (Ch_v, Int)) (Proxy (Ch_c, IntList)) HFalse
instance HEq (Proxy P_Nil) (Proxy P_Cons) HFalse
instance HEq (Proxy P_Val) (Proxy P_Nil) HFalse
instance HEq (Proxy (Ch_c, IntList)) (Proxy (Ch_v, Val)) HFalse
instance HEq (Proxy P_Cons) (Proxy P_Val) HFalse
instance HEq (Proxy P_Nil) (Proxy P_Val) HFalse
instance HEq (Proxy (Ch_v, Val)) (Proxy (Ch_c, IntList)) HFalse


instance HEq (Proxy x)(Proxy x) HTrue
instance HEq (Proxy P_Leaf) (Proxy P_Node) HFalse
instance HEq (Proxy P_Root) (Proxy P_Node) HFalse
instance HEq (Proxy P_Root) (Proxy P_Leaf) HFalse
instance HEq (Proxy (Ch_l, Tree)) (Proxy (Ch_r, Tree)) HFalse
instance HEq (Proxy P_Node) (Proxy P_Leaf) HFalse
instance HEq (Proxy (Ch_r, Tree)) (Proxy (Ch_l, Tree)) HFalse
instance HEq (Proxy P_Node) (Proxy P_Root) HFalse
instance HEq (Proxy P_Leaf) (Proxy P_Root) HFalse
instance HEq (Proxy Att_smin) (Proxy Att_sres) HFalse
instance HEq (Proxy Att_sres) (Proxy Att_smin) HFalse
