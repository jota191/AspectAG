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
          | Leaf {i::Int}
          deriving Show


$(deriveAG ''Root)


--repmin-----------------------------------------------------------------------

$(attLabels ["smin","ival","sres"])


asp_smin () = synAspect smin ( nt_Tree .*. hNil ) (min::Int->Int->Int)  (0::Int) ( p_Node .*. hNil )
                        (   p_Leaf .=. (\(Fam chi _) -> chi # ch_i)
                        .*. emptyRecord )

asp_ival a  = inhAspect ival ( nt_Tree .*. hNil ) ( p_Node .*. hNil )
                        (   p_Root .=. (\(Fam chi _) -> (   ch_tree .=. (chi # ch_tree) # a
                                                        .*. emptyRecord ) )
                        .*. emptyRecord )

asp_sres a  = synAspect sres ( nt_Root .*. nt_Tree .*. hNil ) Node (Leaf 0) ( p_Node .*. hNil )
                        (   p_Root .=. (\(Fam chi _) -> (chi # ch_tree) # sres)
                        .*. p_Leaf .=. (\(Fam _ par) -> Leaf (par # a))
                        .*. emptyRecord )


asp_repmin a =  asp_smin () .+. asp_sres a .+. asp_ival smin

repmin tree = sem_Root (asp_repmin ival) (Root tree) () # sres


--chained attribute------------------------------------------------------------

$(attLabel "ccnt")


asp_ccnt () = chnAspect ccnt (nt_Root .*. nt_Tree .*. hNil ) ( p_Node .*. hNil )
                        (   p_Root .=. (\(Fam _ _) -> (   ch_tree .=. (0::Int)
                                                      .*. emptyRecord ) ) 
                        .*. emptyRecord )
                        (   p_Leaf .=. (\(Fam chi par) -> 
                                            if chi # ch_i == (par # ival) 
                                                 then (par # ccnt) +1 
                                                 else  par # ccnt
                                       )
                        .*. emptyRecord )



asp_cnt () = asp_ccnt () .+. asp_repmin ccnt

cnt tree  = sem_Root (asp_cnt ()) (Root tree) () # sres


----example--------------------------------------------------------------------


examplet =    (Node (Node (Node (Leaf 1) (Leaf 4))
                          (Node (Leaf 2) (Leaf 1))
                    )

                    (Node (Node (Leaf 9) (Leaf 8))
                          (Leaf 6)
                    )
              )

res_repmin = repmin examplet

res_cnt = cnt examplet

