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
import Control.Monad
import Control.Applicative
import Data.Proxy
import GHC.TypeLits

data Root = Root Tree
          deriving Show
data Tree = Leaf Int
          | Node Tree Tree
          deriving (Show, Eq)

examplet =    (Node (Node (Node (Leaf 3) (Leaf 4))
                      (Node (Leaf 2) (Leaf 7))
                    )
                (Node (Node (Leaf (5)) (Leaf (27)))
                  (Leaf 6)
                )
              )


type Nt_Tree = 'NT "Tree"


type P_Node = 'Prd "p_Node" Nt_Tree
p_Node = Label @ P_Node

type P_Leaf = 'Prd "p_Leaf" Nt_Tree
p_Leaf = Label @ P_Leaf

type P_Root = 'Prd "p_Root" Nt_Tree
p_Root = Label @ P_Root


ch_l    = Label @ ('Chi "ch_l"    P_Node ('Left Nt_Tree))
ch_r    = Label @ ('Chi "ch_r"    P_Node ('Left Nt_Tree))
ch_tree = Label @ ('Chi "ch_tree" P_Root ('Left Nt_Tree))
ch_i    = Label @ ('Chi "ch_i"    P_Leaf ('Right ('T Int)))


sem_Tree asp (Node l r) = knitAspect p_Node asp
                           $  ch_l .=. sem_Tree asp l
                          .*. ch_r .=. sem_Tree asp r
                          .*.  EmptyRec
sem_Tree asp (Leaf i)   = knitAspect p_Leaf asp$
                          ch_i .=. sem_Lit i .*. EmptyRec
sem_Root asp (Root r)   = knitAspect p_Root asp$
                          ch_tree .=. sem_Tree asp r .*. EmptyRec


smin = Label @ ('Att "smin" Int)
sres = Label @ ('Att "sres" Tree)
ival = Label @ ('Att "ival" Int)

-- | rules for smin
--node_smin
--  = syndefM smin p_Node $ min <$> at ch_l smin <*> at ch_r smin

node_smin
  = use smin p_Node (KCons (Proxy @ Nt_Tree) KNil) min 0
leaf_smin
  = syndefM smin p_Leaf $ at ch_i lit

-- | rules for sres
node_sres
  = traceRule (Proxy @ ('Text "node_sres"))
  $ syndefM sres p_Node $ Node <$> at ch_l sres <*> at ch_r sres
leaf_sres
  = syndefM sres p_Leaf $ Leaf <$> at lhs ival
root_sres
  = syndefM sres p_Root $ at ch_tree sres


-- | rules for ival
root_ival
  = inhdefM ival p_Root ch_tree $ at ch_tree smin
node_ival_l
  = inhdefM ival p_Node ch_l $ at lhs ival
node_ival_r
  = inhdefM ival p_Node ch_r $ at lhs ival



-- | Aspects


asp_smin = traceAspect (Proxy @ ('Text "smin"))
    $   node_smin
   .+:  leaf_smin
   .+:  emptyAspect

asp_sres = traceAspect (Proxy @ ('Text "sres"))
    $   node_sres
   .+:  leaf_sres
   .+:  root_sres
   .+:  emptyAspect

asp_ival = traceAspect (Proxy @ ('Text "ival"))
    $   node_ival_l
   .+:  node_ival_r
   .+:  root_ival
   .+:  emptyAspect

node_smin'
  = synmodM smin p_Node $ max <$> at ch_l smin <*> at ch_r smin

asp_repmin = traceAspect (Proxy @ ('Text "repmin"))
    $   asp_smin
  .:+:  asp_sres
  .:+:  asp_ival

repmin t
  = sem_Root asp_repmin (Root t) emptyAtt #. sres

minimo t
  = sem_Tree asp_smin t emptyAtt #. smin



ssiz = Label @ ('Att "ssiz" Int)

asp_ssiz =   syndefM ssiz p_Leaf (pure 1)
        .+: (syndefM ssiz p_Node (at ch_l ssiz <**> pure (+) <*> at ch_r ssiz))
        .+: emptyAspect

repavg t = sem_Root asp_repavg (Root t) emptyAtt #. sres
  where asp_repavg  = ival' .+: asp_ssiz .:+: asp_ssum .:+: asp_repmin
        ival'       = inhmodM ival p_Root ch_tree
            $ div <$> at ch_tree ssum <*> at ch_tree ssiz

ssum = Label @ ('Att "ssum" Int)
asp_ssum
  =  syndefM ssum p_Node (at ch_l ssum <**> pure (+) <*> at ch_r ssum)
 .+: syndefM ssum p_Leaf (at ch_i lit)
 .+: emptyAspect

