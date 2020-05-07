{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

module ManyFeatures where

import Language.Grammars.AspectAG
import Language.Grammars.AspectAG.TH

import Data.Kind

$(addNont "Tree")
$(addProd "Leaf" ''Nt_Tree [("leaf", Ter ''Int)])

$(addProd "Node" ''Nt_Tree  [("nl",   NonTer ''Nt_Tree),
                            ("inner", Ter ''Int),
                            ("nr",  NonTer ''Nt_Tree)])

$(addProd "Fork" ''Nt_Tree  [("fl",   NonTer ''Nt_Tree),
                             ("fr",  NonTer ''Nt_Tree)])

$(closeNT ''Nt_Tree)
$(mkSemFuncs [''Nt_Tree])


-- replaces all occurences of an integer (old) by a new one (new).

$(attLabels [("old", ''Int), ("new", ''Int), ("res", ''Tree)])

asp_old =
  old `copyatChi` ch_nl .+:
  old `copyatChi` ch_nr .+:
  old `copyatChi` ch_fl .+:
  old `copyatChi` ch_fr .+:
  emptyAspect
asp_new =
  new `copyatChi` ch_nl .+:
  new `copyatChi` ch_nr .+:
  new `copyatChi` ch_fl .+:
  new `copyatChi` ch_fr .+:
  emptyAspect

asp_res =
  syn res p_Leaf (do val <- ter ch_leaf
                     old <- at lhs old
                     new <- at lhs new
                     if old /= val
                     then return (Leaf val)
                     else return (Leaf new)
                  ) .+:
  syn res p_Fork (Fork <$> at ch_fl res <*> at ch_fr res) .+:
  syn res p_Node (do val <- ter ch_inner
                     old <- at lhs old
                     new <- at lhs new
                     l   <- at ch_nl res
                     r   <- at ch_nr res
                     if old /= val
                     then return (Node l val r)
                     else return (Node l new r)
                 ) .+:
  emptyAspect

replace o n t =
  sem_Tree (asp_old .:+: asp_new .:+: asp_res) t (old .=. o .*. new .=. n .*. emptyAtt) #.res

examplet =
  Fork (Node (Leaf 5) 3 (Leaf 4))
       (Fork (Node (Leaf 2) 4 (Leaf 5))
             (Leaf 3))


$(attLabels [("size", ''Int)])
