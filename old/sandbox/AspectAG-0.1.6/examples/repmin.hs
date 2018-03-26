{-# OPTIONS -XEmptyDataDecls #-}
{-# LANGUAGE TemplateHaskell #-}

module Repmin where

import Data.AspectAG
import Data.AspectAG.Derive

import Data.HList.Label4
import Data.HList.TypeEqGeneric1
import Data.HList.TypeCastGeneric1



--data types-------------------------------------------------------------------

data Root = Root { tree :: Tree}
          deriving Show

data Tree = Node {l::Tree, r::Tree}
          | Leaf {i::Int}
          deriving Show


$(deriveAG ''Root)

 
--repmin-----------------------------------------------------------------------


$(attLabels ["smin","ival","sres"])

asp_smin () = synAspect smin ( nt_Tree .*. hNil ) (min::Int->Int->Int)  (0::Int) ( p_Node .*. hNil )
                        (   p_Leaf .=. (\(Fam chi _) -> chi # ch_i)
                        .*. emptyRecord )

asp_ival () = inhAspect ival ( nt_Tree .*. hNil ) ( p_Node .*. hNil )
                        (   p_Root .=. (\(Fam chi _) -> (   ch_tree .=. ((chi # ch_tree) # smin)
                                                        .*. emptyRecord ) )
                        .*. emptyRecord )

asp_sres () = synAspect sres ( nt_Root .*. nt_Tree .*. hNil ) Node (Leaf 0) ( p_Node .*. hNil )
                        (   p_Root .=. (\(Fam chi _) -> (chi # ch_tree) # sres)
                        .*. p_Leaf .=. (\(Fam _ par) -> Leaf (par # ival))
                        .*. emptyRecord )


asp_repmin () =   asp_sres () .+. asp_ival () .+. asp_smin ()

repmin tree = sem_Root (asp_repmin ()) (Root tree) () # sres




----example--------------------------------------------------------------------


examplet =    (Node (Node (Node (Leaf 1) (Leaf 4))
                          (Node (Leaf 2) (Leaf 1))
                    )

                    (Node (Node (Leaf 9) (Leaf 8))
                          (Leaf 6)
                    )
              )

slidest = Node  {  l = Node  {  l = Node  {  l = Leaf { i = 5}
                                          ,  r = Leaf { i = 4}
                                          }
                             ,  r = Node  {  l = Leaf { i = 2}
                                          ,  r = Leaf { i = 3}
                                          }
                             }
                ,  r = Node  {  l = Leaf  {  i = 9 }
                             ,  r = Node  {  l = Leaf { i = 7}
                                          ,  r = Leaf { i = 6}
                                          }
                             }
                } 

res_repmin = repmin examplet


