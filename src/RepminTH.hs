{-# LANGUAGE 
             TemplateHaskell,
             TypeFamilies,
             FlexibleContexts,
             ScopedTypeVariables,
             NoMonomorphismRestriction,
             DataKinds,
             TypeApplications,
             PolyKinds
#-}


module RepminTH where

import System.Exit (exitFailure)
import Language.Grammars.AspectAG
import Language.Grammars.AspectAG.Derive
import Control.Monad
import Data.Kind

data Root = Root {tree :: Tree}
          deriving Show
data Tree = Leaf { i  :: Int}
          | Node {l,r :: Tree}
          deriving (Show, Eq)



$(attLabels ["smin","ival","sres"])
$(deriveAG '' Root)

root_ival (Fam chi par) =
  inhdef ival (nt_Tree .: ε) (  ch_tree .=.(chi .# ch_tree #. smin)
                            .*. emptyRecord)
  
-- node_ival (Fam chi par) =
--   inhdef ival (nt_Tree .:ε) (   ch_l .=. (par #. ival)
--                             .*. ch_r .=. (par #. ival)
--                             .*. emptyRecord)
node_ival = copy ival (nt_Tree .: ε)

root_sres (Fam chi par)
  = syndef sres (chi .# ch_tree #. sres)

-- node_sres (Fam chi par)
--   = syndef sres (Node (chi .# ch_l #. sres)(chi .# ch_r #. sres))
node_sres = use sres (nt_Tree .:ε) Node (Leaf 0)

leaf_sres (Fam chi par)
  = syndef sres $ Leaf (par #. ival)


--node_smin (Fam chi par)
--  = syndef smin $ (chi .# ch_l #. smin) `min` (chi .# ch_r #. smin)
node_smin = use smin (nt_Tree .:ε) min 0

leaf_smin (Fam chi par)
  = syndef smin $ chi .# ch_i #. lit @ Int

asp_ival =  p_Root .=. root_ival
        .*. p_Node .=. node_ival
        .*. emptyRecord
asp_sres =  p_Root .=. root_sres
        .*. p_Node .=. node_sres
        .*. p_Leaf .=. leaf_sres
        .*. emptyRecord
asp_smin =   p_Leaf .=. leaf_smin
        .*.  p_Node .=. node_smin
        .*. emptyRecord



asp_repmin = asp_smin .+. asp_sres .+. asp_ival

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
minimo t = sem_Tree asp_smin t emptyAtt #. smin



