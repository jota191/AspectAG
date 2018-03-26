{-# OPTIONS -XEmptyDataDecls #-}
{-# LANGUAGE TemplateHaskell #-}

module Test where

import Data.AspectAG
import Data.AspectAG.Derive


import Data.HList.Label4
import Data.HList.TypeEqGeneric1
import Data.HList.TypeCastGeneric1



--data types-------------------------------------------------------------------

data Root = Root { tree :: Tree}
          deriving Show

data Tree = Node {l::Tree, r::Tree}
          | Bin  {lb::Tree, ib::Int, rb::Tree}
          | Leaf {i::Int}
          deriving Show


$(deriveAG ''Root)

 

--repmin-----------------------------------------------------------------------


$(attLabels ["smin","ival","sres"])


asp_smin () = synAspect smin ( nt_Tree .*. hNil ) (min::Int->Int->Int)  (0::Int)  ( p_Node .*. p_Bin .*.  hNil )
                        (   p_Leaf .=. (\(Fam chi _) -> chi # ch_i)
                        .*. emptyRecord )

asp_ival f  = inhAspect ival ( nt_Tree .*. hNil ) ( p_Node .*. p_Bin .*. hNil )
                        (   p_Root .=. (\(Fam chi _) -> (   ch_tree .=. f (chi # ch_tree) 
                                                        .*. emptyRecord ) )
                        .*. emptyRecord )

asp_sres () = synAspect sres ( nt_Root .*. nt_Tree .*. hNil ) Node (Leaf 0) ( p_Node .*. hNil )
                        (   p_Root .=. (\(Fam chi _) -> (chi # ch_tree) # sres)
                        .*. p_Leaf .=. (\(Fam _ par) -> Leaf (par # ival))
                        .*. p_Bin  .=. (\(Fam chi _) -> Bin ((chi # ch_lb) # sres) (chi # ch_ib) ((chi # ch_rb) # sres))
                        .*. emptyRecord )


asp_repmin () =  asp_smin () .+. asp_sres () .+. asp_ival (\c -> c # smin)

repmin tree = sem_Root (asp_repmin ()) (Root tree) () # sres



--average----------------------------------------------------------------------

$(attLabels ["ssum","scnt"])

asp_ssum ()  = 
              synAspect ssum ( nt_Tree .*. hNil ) ((+)::Int->Int->Int)  (0::Int) ( p_Node .*. p_Bin .*. hNil )
                        (   p_Leaf .=. (\(Fam chi _) -> chi  # ch_i)
                        .*. emptyRecord )

asp_scnt ()  = 
              synAspect scnt ( nt_Tree .*. hNil ) ((+)::Int->Int->Int)  (0::Int) ( p_Node .*. p_Bin .*. hNil )
                        (   p_Leaf .=. (\(Fam chi _) -> 1)
                        .*. emptyRecord )

asp_avg () = asp_scnt () .+. asp_ssum () .+. asp_sres () .+. asp_ival (\c -> div (c # ssum) (c # scnt))

avg tree  = sem_Root (asp_avg ()) (Root tree) () # sres


----example--------------------------------------------------------------------

examplet =    (Node (Bin  (Node (Leaf 1) (Leaf 4))
                          100
                          (Node (Leaf 2) (Leaf 1))
                    )

                    (Node (Bin  (Leaf 9) 300 (Leaf 8))
                          (Leaf 6)
                    )
              )

res_repmin = repmin examplet

res_avg = avg examplet

