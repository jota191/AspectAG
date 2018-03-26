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
                        (   p_Leaf .=. (def $ liftM id (at ch_i))
                        .*. emptyRecord )

asp_ival () = inhAspect ival ( nt_Tree .*. hNil ) ( p_Node .*. hNil )
                        (   p_Root .=. (def $ do  tree <- at ch_tree 
                                                  return (   ch_tree .=. tree # smin
                                                         .*. emptyRecord ) )
                        .*. emptyRecord )

asp_sres () = synAspect sres ( nt_Root .*. nt_Tree .*. hNil ) Node (Leaf 0) ( p_Node .*. hNil )
                        (   p_Root .=. (def $ do  tree <- at ch_tree
                                                  return $ tree # sres)
                        .*. p_Leaf .=. (def $ do  lhs  <- at lhs 
                                                  return $ Leaf (lhs # ival))
                        .*. emptyRecord )


asp_repmin () =  asp_smin () .+. asp_sres () .+. asp_ival ()

repmin tree = sem_Root (asp_repmin ()) (Root tree) () # sres




----example--------------------------------------------------------------------


examplet =    (Node (Node (Node (Leaf 1) (Leaf 4))
                          (Node (Leaf 2) (Leaf 1))
                    )

                    (Node (Node (Leaf 9) (Leaf 8))
                          (Leaf 6)
                    )
              )

res_repmin = repmin examplet


