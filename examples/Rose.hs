{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
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
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeInType #-}

module Rose where

import Language.Grammars.AspectAG
import Language.Grammars.AspectAG.TH
import Data.Type.Require

import Data.Kind
import Data.Proxy

--- data Rose = Node Int ListRose
--- data ListRose = Nil | Cons Rose ListRose

$(addNont "Rose")
$(addNont "List")
$(addProd "Node" ''Nt_Rose [("v", Ter ''Int),
                            ("ls", NonTer ''Nt_List)])
$(addProd "Nil"  ''Nt_List [])
$(addProd "Cons" ''Nt_List [("hd", NonTer ''Nt_Rose),
                            ("tl", NonTer ''Nt_List)])
$(closeNTs   [''Nt_List, ''Nt_Rose])
$(mkSemFuncs [''Nt_List, ''Nt_Rose])

exampleT =
  Node 5 (Cons (Node 3 Nil)
          (Cons (Node 3 (Cons (Node 3 Nil) Nil))
            Nil))

-- size of Tree
$(attLabels [("size", ''Int)])

-- TODO: solve this bug
-- asp_size =
--   use size p_Node (nt_List .:. eL) ((+) . (+1)) 1 .+:
--   syn size p_Nil (pure 0) .+:
--   use size p_Cons (nt_Rose .:. nt_List .:. eL) (+) 1 .+:
--   emptyAspect

asp_size =
  syn size p_Node ((1+) <$> at ch_ls size) .+:
  syn size p_Nil (pure 0) .+:
  syn size p_Cons ((+) <$> at ch_hd size <*> at ch_tl size) .+:
  emptyAspectC (p_Node .:. p_Cons .:. p_Nil .:. eL) Proxy

siz t = sem_Rose asp_size t emptyAtt #. size


-- a constant attribute, to be defined only in one nonterminal
$(attLabels [("cst", ''String)])

asp_const =
  syn cst p_Node (at ch_ls cst -- pure "cst"
                 ) .+:
  emptyAspectC (p_Node .:. p_Cons .:. p_Nil .:. eL) Proxy
  -- same:
  -- emptyRuleatPrd p_Node .+:
  -- emptyRuleatPrd p_Cons .+:
  -- emptyRuleatPrd p_Nil  .+:
  -- emptyAspect

con t = sem_Rose asp_const t emptyAtt #. cst

type family ProdsOfNt1 (nt :: NT) :: [Prod]
type instance ProdsOfNt1 Nt_Rose = '[P_Node]

type family ProdsOfNtRec (nt :: NT) :: [Prod]
type instance ProdsOfNtRec Nt_Rose = '[P_Node, P_Nil, P_Cons]

-- -- | generada con TH
-- type family NtsOfProd (prd :: Prod) :: [NT]

-- emptyAspectC
