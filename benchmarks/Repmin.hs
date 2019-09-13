{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}


module Main where

import Language.Grammars.AspectAG
import Language.Grammars.AspectAG.TH
import System.Environment

$(addNont "Root")
$(addNont "Tree")

$(addProd "Leaf" ''Nt_Tree [("val", Ter ''Int)])
$(addProd "Node" ''Nt_Tree [("l", NonTer ''Nt_Tree),("r", NonTer ''Nt_Tree)])
$(addProd "Root" ''Nt_Root [("tree",NonTer ''Nt_Tree)])

$(closeNTs [''Nt_Root,''Nt_Tree])
$(mkSemFunc ''Nt_Tree)
$(mkSemFunc ''Nt_Root)



$(attLabels [("sres", ''Tree), ("smin", ''Int), ("ival", ''Int)])

asp_smin
 =   syn smin p_Node (min @ Int <$> at ch_l smin <*> at ch_r smin)
 .+: syn smin p_Leaf (ter ch_val)
 .+: emptyAspect

asp_sres
 =    syn sres p_Node (Node <$> at ch_l sres <*> at ch_r sres)
 .+:  syn sres p_Leaf (Leaf <$> at lhs ival)
 .+:  syn sres p_Root (at ch_tree sres)
 .+:  emptyAspect

asp_ival
 =    inh ival p_Root ch_tree (at ch_tree smin)
 .+:  inh ival p_Node ch_l (at lhs ival)
 .+:  inh ival p_Node ch_r (at lhs ival)
 .+:  emptyAspect

asp_repmin
  = asp_smin .:+: asp_sres .:+: asp_ival


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

main
  = getArgs >>= \args ->
    let n = (read :: String -> Int) (args!!0) in
    print $ length $ show $ repmin $ exampleT n
