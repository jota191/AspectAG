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
             TypeApplications
#-}


module Repmin where

import System.Exit (exitFailure)
import Language.Grammars.AspectAG
import Language.Grammars.AspectAG.Derive
import Control.Monad
import Data.Proxy
import GHC.TypeLits

data Root = Root Tree
          deriving Show
data Tree = Leaf Int
          | Node Tree Tree
          deriving (Show, Eq)

data Att_smin; smin = Label :: Label Att_smin
data Att_ival; ival = Label :: Label Att_ival
data Att_sres; sres = Label :: Label Att_sres
data Att_ssum; ssum = Label :: Label Att_ssum

-- Labels for childs
data Ch_tree -- root
data Ch_r    -- node
data Ch_l    -- node
data Ch_i    -- leaf

ch_tree = Label :: Label '(Ch_tree, Tree)
ch_r    = Label :: Label '(Ch_r, Tree)
ch_l    = Label :: Label '(Ch_l, Tree)
ch_i    = Label :: Label '(Ch_i, Int)


----non terminals
nt_Root = undefined :: Label Root
nt_Tree = undefined :: Label Tree

data P_Root; p_Root = Label :: Label (P_Root)
data P_Node; p_Node = Label :: Label (P_Node)
data P_Leaf; p_Leaf = Label :: Label (P_Leaf)  

sem_Tree asp (Node l r) = knit (asp .#. p_Node)$
                           ch_l .=. sem_Tree asp l
                       .*. ch_r .=. sem_Tree asp r
                       .*. emptyRecord

sem_Tree asp (Leaf i)   = knit (asp .#. p_Leaf)$
                          ch_i .=. sem_Lit i .*. emptyRecord

sem_Root  asp (Root t) = knit (asp .#. p_Root)$
                         ch_tree .=. sem_Tree asp t .*. emptyRecord




root_ival (Fam chi par) =
  inhdef ival (nt_Tree .: ε) (  ch_tree .=.(chi .# ch_tree #. smin)
                            .*. emptyRecord)
  
node_ival (Fam chi par) =
  inhdef ival (nt_Tree .: ε) (  ch_l .=. (par #. ival)
                            .*. ch_r .=. (par #. ival)
                            .*. emptyRecord)

root_sres (Fam chi par)
  = syndef' sres (chi .# ch_tree #. sres)

node_sres (Fam chi par)
  = syndef' sres (Node ((lookupCtx (Proxy @ '[Text "syndef sres"])chi ch_l) #. sres)
                      ((lookupCtx (Proxy @ '[Text "syndef sres"])chi ch_r) #. sres))

--node_sres = use sres (nt_Tree .: ε) Node (error "unreacheable")

leaf_sres (Fam chi par)
  = syndef' sres $ Leaf (par #. ival)

--f = lookupCtx' @Reco (Proxy @ '[] ) (asp_smin) p_Leaf

--node_smin (Fam chi par)
--  = syndef smin $ (chi .# ch_l #. smin) `min` (chi .# ch_r #. smin)


smin1 (Fam chi par) = syndef' smin (8 :: Int)
smin2 (Fam chi par) = syndef' sres (1 :: Int)

err inp  = snd (((smin1 `ext` smin2) inp (Fam EmptyRec EmptyRec)),
               ((smin1 `ext` smin2) inp))

err'= (req (Proxy @ '[Text "1"])
       (OpExtend @_ @Reco sres (1 :: Int)
       (req (Proxy @ '[Text "0"])
       (OpExtend @_ @Reco smin (0 :: Int) EmptyRec))))
       


node_smin (Fam chi par)
  = syndef' smin $ ((lookupCtx (Proxy @ '[Text "syndef smin"])chi ch_l) #. smin)
  `min` ((lookupCtx (Proxy @ '[Text "syndef smin"])chi ch_r) #. smin)

--node_smin = use smin (nt_Tree .: ε) min 0

leaf_smin (Fam chi par)
  = syndef smin $ chi .# ch_i #. (lit @ Int)

asp_ival =  p_Root .=. root_ival
        .*. p_Node .=. node_ival
        .*. emptyRecord
asp_sres =  p_Root .=. root_sres
        .*. p_Node .=. node_sres
        .*. p_Leaf .=. leaf_sres
        .*. emptyRecord
asp_smin =  p_Leaf .=. leaf_smin
        .*. p_Node .=. node_smin
        .*. emptyRecord



asp_repmin = asp_smin  .+. asp_sres .+. asp_ival

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

--minimo t = sem_Tree asp_smin t emptyAtt #. smin
