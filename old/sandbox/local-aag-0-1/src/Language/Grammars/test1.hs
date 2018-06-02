{-# OPTIONS -fcontext-stack=100 #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Test where

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
    ((ch_tree .=. ((chi # ch_tree) # smin)) .*. HNil)

node_ival (Fam chi par)
  = inhdef ival (nt_Tree .*. HNil)
     ((ch_l .=. (par # ival))  .*.
     ((ch_r .=. (par # ival))  .*. HNil))

root_sres (Fam chi par)
  = syndef sres ((chi # ch_tree) # sres)

leaf_sres (Fam chi par)
  = syndef sres (Leaf (par # ival))


node_sres (Fam chi par)
  = syndef sres (Node ((chi # ch_l)# sres)
                      ((chi # ch_r)# sres))



asp_smin =     (p_Leaf .=. leaf_smin)
          .*. (p_Node .=. node_smin)
          .*. emptyRecord



asp_ival =     (p_Root .=. root_ival)
           .*. (p_Node .=. node_ival)
           .*. emptyRecord


asp_sres =     (p_Root .=. root_sres)
           .*. (p_Node .=. node_sres)
           .*. (p_Leaf .=. leaf_sres)
           .*. emptyRecord



--asp_repmin () =  asp_smin .+. asp_sres .+. asp_ival -- (\c -> c # smin)

--repmin tree = sem_Root (asp_repmin ()) (Root tree) () # sres


               
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

instance HEq (Proxy (Ch_r, Tree)) (Proxy (Ch_r, Tree)) HTrue
instance HEq (Proxy (Ch_i, Int)) (Proxy (Ch_i, Int)) HTrue
instance HEq (Proxy (Ch_l, Tree)) (Proxy (Ch_l, Tree)) HTrue
instance HEq (Proxy P_Node) (Proxy P_Node) HTrue
instance HEq (Proxy P_Leaf) (Proxy P_Leaf) HTrue
instance HEq (Proxy Att_smin) (Proxy Att_smin) HTrue
instance HEq (Proxy Att_sres) (Proxy Att_sres) HTrue
instance HEq (Proxy P_Root) (Proxy P_Root) HTrue
instance HEq (Proxy (Ch_tree, Tree)) (Proxy (Ch_tree, Tree)) HTrue
                          
---- si no pongo el tipo no compila, sin embargo el interprete deduce
----  el tipo TODO
asp_smin
  :: (HasField (Proxy Att_smin) r3 val2,
      HasField (Proxy Att_smin) r2 val2,
      HasField (Proxy (Ch_i, Int)) r val1,
      HasField (Proxy (Ch_r, Tree)) r1 r3,
      HasField (Proxy (Ch_l, Tree)) r1 r2, Ord val2,
      HExtend (Att (Proxy Att_smin) val1) sp1 sp'1,
      HExtend (Att (Proxy Att_smin) val2) sp2 sp'2) =>
     Record
       (HCons
          (LVPair (Proxy P_Leaf) (Fam r p1 -> Fam ic1 sp1 -> Fam ic1 sp'1))
          (HCons
             (LVPair (Proxy P_Node) (Fam r1 p2 -> Fam ic2 sp2 -> Fam ic2 sp'2))
             HNil))

asp_ival
  :: (Defs
        (Proxy Att_ival)
        (HCons (Proxy Tree) HNil)
        (HCons (LVPair (Proxy (Ch_tree, Tree)) v1) HNil)
        ic1
        ic'1,
      Defs
        (Proxy Att_ival)
        (HCons (Proxy Tree) HNil)
        (HCons
           (LVPair (Proxy (Ch_l, Tree)) v2)
           (HCons (LVPair (Proxy (Ch_r, Tree)) v2) HNil))
        ic2
        ic'2,
      HasField (Proxy Att_smin) r2 v1, HasField (Proxy Att_ival) r v2,
      HasField (Proxy (Ch_tree, Tree)) r1 r2) =>
     Record
       (HCons
          (LVPair (Proxy P_Root) (Fam r1 p -> Fam ic1 sp1 -> Fam ic'1 sp1))
          (HCons
             (LVPair (Proxy P_Node) (Fam c r -> Fam ic2 sp2 -> Fam ic'2 sp2))
             HNil))
asp_sres
  :: (HEq (Proxy P_Node) (Proxy P_Leaf) leq,
      HRLabelSet'
        (Proxy P_Node)
        (Fam r4 p1 -> Fam ic1 sp1 -> Fam ic1 sp'1)
        (Proxy P_Leaf)
        (Fam c r -> Fam ic2 sp2 -> Fam ic2 sp'2)
        leq
        HNil,
      HasField (Proxy Att_sres) r5 Tree,
      HasField (Proxy Att_sres) r3 Tree,
      HasField (Proxy Att_sres) r7 val, HasField (Proxy Att_ival) r Int,
      HasField (Proxy (Ch_l, Tree)) r4 r5,
      HasField (Proxy (Ch_r, Tree)) r4 r3,
      HasField (Proxy (Ch_tree, Tree)) r6 r7,
      HExtend (Att (Proxy Att_sres) Tree) sp1 sp'1,
      HExtend (Att (Proxy Att_sres) Tree) sp2 sp'2,
      HExtend (Att (Proxy Att_sres) val) sp3 sp'3) =>
     Record
       (HCons
          (LVPair (Proxy P_Root) (Fam r6 p2 -> Fam ic3 sp3 -> Fam ic3 sp'3))
          (HCons
             (LVPair (Proxy P_Node) (Fam r4 p1 -> Fam ic1 sp1 -> Fam ic1 sp'1))
             (HCons
                (LVPair (Proxy P_Leaf) (Fam c r -> Fam ic2 sp2 -> Fam ic2 sp'2))
                HNil)))  
{-
asp_smin () = synAspect smin ( nt_Tree .*. hNil ) (min::Int->Int->Int)  (0::Int) ( p_Node .*. hNil )
                        (   p_Leaf .=. (\(Fam chi _) -> chi # ch_i)
                        .*. emptyRecord )

asp_ival f  = inhAspect ival ( nt_Tree .*. hNil ) ( p_Node .*. hNil )
                        (   p_Root .=. (\(Fam _ _ chi _) -> (   ch_tree .=. f (chi # ch_tree) 
                                                            .*. emptyRecord ) )
                        .*. emptyRecord )

asp_sres () = synAspect sres ( nt_Root .*. nt_Tree .*. hNil ) Node (Leaf 0) ( p_Node .*. hNil )
                        (   p_Root .=. (\(Fam _ _ chi _) -> (chi # ch_tree) # sres)
                        .*. p_Leaf .=. (\(Fam _ _ _ par) -> Leaf (par # ival))
                        .*. emptyRecord )


asp_repmin () =  asp_smin () .+. asp_sres () .+. asp_ival (\c -> c # smin)

repmin tree = sem_Root (asp_repmin ()) (Root tree) () # sres


--average----------------------------------------------------------------------

data Att_ssum;   ssum    = proxy::Proxy Att_ssum
data Att_scnt;   scnt    = proxy::Proxy Att_scnt

asp_ssum att f  = 
              synAspect att ( nt_Tree .*. hNil ) ((+)::Int->Int->Int)  (0::Int) ( p_Node .*. hNil )
                        (   p_Leaf .=. (\(Fam _ _ chi _) -> f chi )
                        .*. emptyRecord )

asp_avg () = asp_ssum scnt (const 1) .+. asp_ssum ssum (\c -> c # ch_i) .+. asp_sres () .+. asp_ival (\c -> div (c # ssum) (c # scnt))

avg tree  = sem_Root (asp_avg ()) (Root tree) () # sres

-}
----example--------------------------------------------------------------------


examplet =    (Node (Node (Node (Leaf 3) (Leaf 4))
                          (Node (Leaf 2) (Leaf 7))
                    )

                    (Node (Node (Leaf 9) (Leaf (-23)))
                          (Leaf 6)
                    )
              )

--minimo = (sem_Tree (asp_smin) examplet emptyRecord) # smin


{-
res_repmin = repmin examplet

res_avg = avg examplet

-}
