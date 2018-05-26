{-# OPTIONS -fcontext-stack=100 #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}

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
    ((ch_tree .=. (chi # ch_tree) # smin) .*. HNil)

node_ival (Fam chi par)
  = inhdef ival (nt_Tree .*. HNil)
     ((ch_l .=. (par # ival))  .*.
     ((ch_r .=. (par # ival))  .*. HNil))
{-
root_sres (Fam chi par)
  = syndef sres (lookupByLabelAtt sres (hLookupByChild ch_tree chi))

leaf_sres (Fam chi par)
  = syndef sres (Leaf (lookupByLabelAtt ival par))

node_sres (Fam chi par)
  = syndef sres (Node (lookupByLabelAtt sres (hLookupByChild ch_l chi))
                      (lookupByLabelAtt sres (hLookupByChild ch_r chi)))
-}
{-
asp_smin () = synAspect smin ( nt_Tree .*. hNil ) (min::Int->Int->Int)  (0::Int) ( p_Node .*. hNil )
                        (   p_Leaf .=. (\(Fam _ _ chi _) -> chi # ch_i)
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


----example--------------------------------------------------------------------


examplet =    (Node (Node (Node (Leaf 1) (Leaf 4))
                          (Node (Leaf 2) (Leaf 1))
                    )

                    (Node (Node (Leaf 9) (Leaf 8))
                          (Leaf 6)
                    )
              )

res_repmin = repmin examplet

res_avg = avg examplet

-}
