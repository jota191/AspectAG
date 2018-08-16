{-# LANGUAGE FlexibleContexts, NoMonomorphismRestriction #-}


import Test1 (p_Root,root_sres, p_Node, node_sres, p_Leaf, leaf_sres)
import Record
import GhcSyntax
import HList


asp_sres = (p_Root .=. root_sres) .*. (p_Node .=. node_sres) .*. (p_Leaf .=.leaf_sres) .*. emptyRecord
