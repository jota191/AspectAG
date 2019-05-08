{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE 
             TypeFamilies,
             FlexibleContexts,
             ScopedTypeVariables,
             NoMonomorphismRestriction,
             ImplicitParams,
             ExtendedDefaultRules,
             UnicodeSyntax,
             DataKinds,
             TypeApplications,
             PartialTypeSignatures
#-}


module Repmin where

import System.Exit (exitFailure)
import Language.Grammars.AspectAG2
--import Language.Grammars.AspectAG.Derive
import Control.Monad
import Data.Proxy
import GHC.TypeLits

data Root = Root Tree
          deriving Show
data Tree = Leaf Int
          | Node Tree Tree
          deriving (Show, Eq)


smin = Label @ ('Att "smin" Int)
savg = Label @ ('Att "savg" Int)
sres = Label @ ('Att "sres" Tree)
ival = Label @ ('Att "ival" Int)

type P_Node = 'Prd "p_Node" ('NT "Tree")
p_Node = Label @ P_Node

type P_Leaf = 'Prd "p_Leaf" ('NT "Tree") -- ?
p_Leaf = Label @ P_Leaf

type P_Root = 'Prd "p_Root" ('NT "Root")
p_Root = Label @ P_Root

type Nt_Tree = 'NT "Tree"

ch_l    = Label @ ('Chi "ch_l"    P_Node ('Left Nt_Tree))
ch_r    = Label @ ('Chi "ch_r"    P_Node ('Left Nt_Tree))
ch_tree = Label @ ('Chi "ch_tree" P_Root ('Left Nt_Tree))
ch_i    = Label @ ('Chi "ch_i"    P_Leaf ('Right ('T Bool)))

node_smin =
  syndefM smin p_Node $ min <$> at ch_l smin <*> at ch_r savg-- smin

leaf_smin
  = syndefM smin p_Leaf $ at ch_i lit

node_sres
  = syndefM sres p_Node $ Node <$> at ch_l sres <*> at ch_r sres

leaf_sres = syndefM sres p_Leaf $ Leaf <$> at lhs ival

root_sres = syndefM sres p_Root $ at ch_tree sres


root_ival = inhdefM ival p_Root ch_tree $ at ch_tree smin


node_ival_l = inhdefM ival p_Node ch_l $ at lhs ival

node_ival_r = inhdefM ival p_Node ch_r $ at lhs ival


sem_Tree asp (Node l r) = knit ((asp .#. p_Node))$
                             (ch_l .=. sem_Tree asp l)
                        .*. ((ch_r .=. sem_Tree asp r)
                        .*.  EmptyRec)
sem_Tree asp (Leaf i)   = knit (asp .#. p_Leaf)$
                          ch_i .=. sem_Lit i .*. EmptyRec
sem_Root asp (Root r)   = knit (asp .#. p_Root)$
                          ch_tree .=. sem_Tree asp r .*. EmptyRec


asp_Node = node_smin `ext` node_smin `ext` node_ival_l `ext` node_ival_r


asp_smin =   p_Leaf .=. leaf_smin
        .*.  p_Node .=. node_smin
        .*. emptyRecord

minimo t = sem_Tree asp_smin t emptyAtt #. smin

asp_repmin
   =  p_Root .=. (root_sres `ext` root_ival)
  .*. p_Leaf .=. (leaf_sres `ext` leaf_smin)
  .*. p_Node .=. node_sres `ext` node_smin `ext` node_ival_l `ext` node_ival_r
  .*. emptyRecord

examplet =    (Node (Node (Node (Leaf 3) (Leaf 4))
                      (Node (Leaf 2) (Leaf 7))
                    )
                (Node (Node (Leaf (5)) (Leaf (27)))
                  (Leaf 6)
                )
              )

exampleT 0 = examplet
exampleT n = Node (exampleT (n-1)) (exampleT (n-1))

repmin t = sem_Root asp_repmin (Root t) emptyAtt #. sres
