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

smin = Label @ ('Att "smin" Int)
sres = Label @ ('Att "sres" Tree)
ival = Label @ ('Att "ival" Int)

type P_Node = 'Prd "p_Node" ('NT "Tree")
p_Node = Label @ P_Node

type P_Leaf = 'Prd "p_Leaf" ('NT "Tree")
p_Leaf = Label @ P_Leaf

type P_Root = 'Prd "p_Root" ('NT "Root")
p_Root = Label @ P_Root

type Nt_Tree = 'NT "Tree"

ch_l    = Label @ ('Chi "ch_l"    P_Node ('Left Nt_Tree))
ch_r    = Label @ ('Chi "ch_r"    P_Node ('Left Nt_Tree))
ch_tree = Label @ ('Chi "ch_tree" P_Root ('Left Nt_Tree))
ch_i    = Label @ ('Chi "ch_i"    P_Leaf ('Right ('T Int)))

sem_Tree' asp (Node l r) = knit' ((asp .#. p_Node))$
                             (ch_l .=. sem_Tree' asp l)
                        .*. ((ch_r .=. sem_Tree' asp r)
                        .*.  EmptyRec)
sem_Tree' asp (Leaf i)   = knit' (asp .#. p_Leaf)$
                          ch_i .=. sem_Lit i .*. EmptyRec
sem_Root' asp (Root r)   = knit' (asp .#. p_Root)$
                           ch_tree .=. sem_Tree' asp r .*. EmptyRec


sem_Tree asp (Node l r) = knitAspect (Proxy @ '[Text "sem"]) p_Node asp
                           $  ch_l .=. sem_Tree asp l
                          .*. ch_r .=. sem_Tree asp r
                          .*.  EmptyRec
sem_Tree asp (Leaf i)   = knitAspect (Proxy @ '[Text "sem"]) p_Leaf asp$
                          ch_i .=. sem_Lit i .*. EmptyRec
sem_Root asp (Root r)   = knitAspect (Proxy @ '[Text "sem"]) p_Root asp$
                          ch_tree .=. sem_Tree asp r .*. EmptyRec

sem_Tree_Node asp fsemL fsemR
  = knitAspect (Proxy @ '[Text "sem_Tree_Node"]) p_Node asp$
      (ch_l .=. fsemL)
  .*. ((ch_r .=. fsemR)
  .*.  EmptyRec)

sem_Tree_Leaf asp semL
  = knitAspect (Proxy @ '[Text "sem_Tree_Leaf"]) p_Leaf asp$
    ch_i .=. semL .*. EmptyRec

-- | rules for smin
node_smin
  = syndefM smin p_Node $ min <$> at ch_l smin <*> at ch_r smin
leaf_smin
  = syndefM smin p_Leaf $ at ch_i lit
  
-- | rules for sres
node_sres
  = syndefM sres p_Node $ Node <$> at ch_l sres <*> at ch_r sres
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

  
asp_smin = updCAspect smin  
  $   node_smin
  .+: leaf_smin
  .+: emptyAspect
asp_sres = updCAspect sres
  $   node_sres
  .+: leaf_sres
  .+: root_sres
  .+: emptyAspect

asp_ival = updCAspect ival
  $   node_ival_l
  .+: node_ival_r
  .+: root_ival
  .+: emptyAspect

asp_repmin
   =  asp_smin
 .:+: asp_sres 
 .:+: asp_ival

repmin t
  = sem_Root asp_repmin (Root t) emptyAtt #. sres

minimo t
  = sem_Tree asp_smin t emptyAtt #. smin
{-
ssiz = Label @ ('Att "ssiz" Int)

asp_ssiz =   syndefM ssiz p_Leaf (pure 1)
        .+: (syndefM ssiz p_Node
             (at ch_l ssiz <**> pure (+) <*> at ch_r ssiz))
        .+: emptyAspect

size t = sem_Tree asp_ssiz t emptyAtt #. ssiz

ssum = Label @ ('Att "ssum" Int)
asp_ssum
  =  syndefM ssum p_Node (at ch_l ssum <**> pure (+) <*> at ch_r ssum)
 .+: syndefM ssum p_Leaf (at ch_i lit)
 .+: emptyAspect


-- defines ival in another way
root_avg = inhdefM ival p_Root ch_tree
 $ do zi <- at ch_tree ssiz
      su <- at ch_tree ssum
      pure $ su `div` zi

repavg t = sem_Root repavg (Root t) emptyAtt #. sres
  where repavg =  node_ival_l
              .+: node_ival_r
              .+: root_avg
              .+: asp_ssiz .:+: asp_sres .:+: asp_ssum

spoly :: Proxy a -> Label ('Att "spoly" a)
spoly _ = Label

getProxy :: a -> Proxy a
getProxy _ = Proxy
-}
