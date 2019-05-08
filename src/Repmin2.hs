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
sres = Label @ ('Att "sres" Tree)
ival = Label @ ('Att "ival" Int)

type P_Node = 'Prd "p_Node" ('NT "Tree")
p_Node = Label @ P_Node

type P_Leaf = 'Prd "p_Leaf" ('NT "Tree") -- ?
p_Leaf = Label @ P_Leaf

type P_Root = 'Prd "p_Root" ('NT "Root")
p_Root = Label @ P_Root

ch_l    = Label @ ('Chi "ch_l"    P_Node ('NT "Tree"))
ch_r    = Label @ ('Chi "ch_r"    P_Node ('NT "Tree"))
ch_tree = Label @ ('Chi "ch_tree" P_Root ('NT "Root"))
ch_i    = Label @ ('Chi "ch_i"    P_Node ('T Int))

node_smin =
  syndef smin p_Node
  $(\_ fam ->
      ((chi fam .# ch_l #. smin) `min` (chi fam .# ch_r #. smin))
   )

leaf_smin
  = syndef smin p_Leaf
  $(\_ fam ->
      (chi fam .# ch_i #. lit @ Int)
   )

node_sres
  = syndef sres p_Node
  $(\_ fam ->
      ((chi fam .# ch_l #. sres) `Node` (chi fam .# ch_r #. sres))
   )

leaf_sres = syndef sres p_Leaf $
  \_ fam -> Leaf (par fam #. ival)

root_sres = syndef sres p_Root $
 \_ fam -> chi fam .# ch_tree #. sres


root_ival   = inhdef ival p_Root ch_tree (\_ fam -> chi fam .# ch_tree #. smin)
node_ival_l = inhdef ival p_Node ch_l (\_ fam -> par fam #. ival)
node_ival_r = inhdef ival p_Node ch_r (\_ fam -> par fam #. ival)


asp_Node = root_sres `ext2` node_smin --`ext` node_ival_l `ext` node_ival_r

sem_Tree asp (Node l r) = knit ((asp .#. p_Node))$
                             (ch_l .=. sem_Tree asp l)
                        .*. ((ch_r .=. sem_Tree asp r)
                        .*.  EmptyRec)
sem_Tree asp (Leaf i)   = knit (asp .#. p_Leaf)$
                         ch_i .=. sem_Lit i .*. EmptyRec
sem_Root asp (Root r)   = knit (asp .#. p_Root)$
                          ch_tree .=. sem_Tree asp r .*. EmptyRec



-- asp_smin =  p_Leaf .=. leaf_smin
--         .*. p_Node .=. node_smin
--         .*. emptyRecord


-- minimo t = sem_Tree asp_smin t emptyAtt #. smin

-- node_sres = syndef sres p_Node
--   $(\_ fam -> ((chi fam .# ch_l #. sres) `Node` (chi fam .# ch_r #. sres)))


-- leaf_sres = syndef sres p_Leaf $
--   \_ fam -> Leaf (par fam #. ival)

-- node_ival_l = inhdef ival p_Node ch_l (\_ fam -> par fam #. ival)
-- node_ival_r = inhdef ival p_Node ch_r (\_ fam -> par fam #. ival)

-- root_ival   = inhdef ival p_Root ch_tree (\_ fam -> chi fam .# ch_tree #. smin)


-- root_sres = syndef sres p_Root $
--  \_ fam -> chi fam .# ch_tree #. sres

-- asp_sresNT
--   =  p_Root .=. root_sres
--  .*. p_Node .=. node_sres
--  .*. emptyRecord

-- asp_repmin
--    =  p_Root .=. (root_sres `ext2` root_ival)
--   .*. p_Leaf .=. (leaf_sres `ext2` leaf_smin)
--   .*. p_Node .=. node_sres `ext2` node_smin `ext2` node_ival_l `ext2` node_ival_r
--   .*. emptyRecord

examplet =    (Node (Node (Node (Leaf 3) (Leaf 4))
                      (Node (Leaf 2) (Leaf 7))
                    )
                (Node (Node (Leaf (5)) (Leaf (27)))
                  (Leaf 6)
                )
              )



-- exampleT 0 = examplet
-- exampleT n = Node (exampleT (n-1)) (exampleT (n-1))

-- repmin t = sem_Root asp_repmin (Root t) emptyAtt #. sres

-- -- -- minimo t = sem_Tree asp_smin t emptyAtt #. smin
