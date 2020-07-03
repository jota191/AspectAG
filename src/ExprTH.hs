{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE IncoherentInstances       #-}
{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE UnicodeSyntax             #-}

module Expr where
import Language.Grammars.AspectAG
import Language.Grammars.AspectAG.TH
import Language.Grammars.AspectAG.RecordInstances

import Data.Type.Require hiding (emptyCtx)

import Data.GenRec hiding (Label)
import Data.GenRec.Label

import Data.Kind
import Data.Proxy
import GHC.TypeLits

import Data.Maybe
import Data.Type.Equality
import Control.Monad.Reader

import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.Ord
import Data.Singletons.Prelude.Eq
import Data.Singletons.Prelude.Either
import Data.Singletons.CustomStar
import Data.Singletons.Decide
import Data.Singletons.Prelude.List

$(addNont "Expr")
$(addNont "Value")

$(addProd "Add" ''Nt_Expr [("l", NonTer ''Nt_Expr),
                           ("r", NonTer ''Nt_Expr)])
$(addProd "Val" ''Nt_Expr [("v", NonTer ''Nt_Value)])
$(addProd "Int"  ''Nt_Value [("i", Ter ''Int)])
$(addProd "Var" ''Nt_Value [("s", Ter ''String)])

$(closeNTs [''Nt_Expr, ''Nt_Value])

-- $(mkSemFuncs [''Nt_Expr, ''Nt_Value])

data AspExp expr value =
  AspExp { expr  :: expr,
           value :: value
         }

sem_Expr asp (Val v)
  = ((knitAspect p_Val) $ expr asp)
    (((.*.) (((.=.) ch_v) ((sem_Value asp) v))) emptyGenRec)
sem_Expr asp (Add l r)
  = ((knitAspect p_Add) $ expr asp)
    (((.*.) (((.=.) ch_l) ((sem_Expr asp) l)))
      (((.*.) (((.=.) ch_r) ((sem_Expr asp) r))) emptyGenRec))
sem_Value asp (Var s)
  = ((knitAspect p_Var) $ value asp)
    (((.*.) (((.=.) ch_s) (sem_Lit s))) emptyGenRec)
sem_Value asp (Int i)
  = ((knitAspect p_Int) $ value asp)
    (((.*.) (((.=.) ch_i) (sem_Lit i))) emptyGenRec)


type Env = [(String, Int)]

$(attLabel "eval" ''Int)
$(attLabel "env" ''Env)

asp_expr_eval =
  syn eval p_Add ((+) @Int <$> at ch_l eval <*> at ch_r eval) .+:
  syn eval p_Val (at ch_v eval) .+: emptyAspect 

asp_value_eval =
  syn eval p_Var (
  do env <- at lhs env
     x   <- ter ch_s
     case lookup x env of
       Just v -> return v
  ) .+:
  syn eval p_Int (ter ch_i) .+: emptyAspect

asp_expr_env' =
  inh env p_Add ch_l (at lhs env) .+:
  inh env p_Add ch_r (at lhs env) .+:
  inh env p_Val ch_v (at lhs env) .+:
  emptyAspect

asp_expr_env'' =
  copyAtChi env ch_r .+:
  copyAtChi env ch_l .+:
  copyAtChi env ch_v .+:
  emptyAspect

asp_expr_env = copyAtChis env chiList Proxy
  where chiList = ch_r `SCons` ch_l `SCons` ch_v `SCons` SNil

aspHash =
  AspExp
  (asp_expr_eval .:+: asp_expr_env)
  (asp_value_eval)

evalExpr e = sem_Expr aspHash e (env =. [("x",(4 :: Int)), ("y",99)]
                                *. emptyAtt) #. eval

exampleExpr =
  Add (Val (Var "x"))(Add (Val (Int 4))(Val (Int 5)))

