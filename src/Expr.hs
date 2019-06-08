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
             PartialTypeSignatures,
             AllowAmbiguousTypes
#-}


module Expr where

import System.Exit (exitFailure)
import Language.Grammars.AspectAG
import Control.Monad
import Control.Applicative
import Data.Proxy
import GHC.TypeLits
import Data.Map
import Data.Maybe
import Debug.Trace

type Nt_Expr = 'NT "Expr"
expr = Label @ Nt_Expr

type P_Add = 'Prd "p_Add" Nt_Expr
add = Label @ P_Add

type P_Val = 'Prd "p_Val" Nt_Expr
val = Label @ P_Val

type P_Var = 'Prd "p_Var" Nt_Expr
var = Label @ P_Var

nt_Expr = Label @ Nt_Expr

leftAdd   = Label @ ('Chi "leftAdd"   P_Add ('Left Nt_Expr))
rightAdd  = Label @ ('Chi "rightAdd"  P_Add ('Left Nt_Expr))
ival      = Label @ ('Chi "ival"      P_Val ('Right ('T Int)))
vname     = Label @ ('Chi "vname"     P_Var ('Right ('T String)))

eval = Label @ ('Att "eval" Int)
env  = Label @ ('Att "env"  (Map String Int))

add_eval  =  syndefM eval add  $ (+) <$> at leftAdd eval <*> at rightAdd eval
--add_eval = syndef eval add (\Proxy (Fam sc ip)-> (+) (sc .# leftAdd #. eval) (sc .# rightAdd #. eval))

--add_eval = use eval add (nt_Expr .:. eL) (+) 0
--add_eval  =  syndefM eval add  $ ter ival

val_eval  =  syndefM eval val  $ ter ival
var_eval  =  syndefM eval var  $ slookup <$> ter vname <*> at lhs env

slookup nm = fromJust . Data.Map.lookup nm

aspEval   =  traceAspect (Proxy @ ('Text "eval"))
          $  add_eval .+: val_eval .+: var_eval .+: emptyAspect


add_param_env ch = inhdefM env add ch  $ at lhs env
add_leftAdd_env  = --inhdefM env add leftAdd  $ at lhs env
  add_param_env leftAdd
add_rightAdd_env = inhdefM env add rightAdd $ at lhs env
-- val_ival_env = inhdefM env val ival $ at lhs env

aspEnv  =  traceAspect (Proxy @ ('Text "env"))
        $  add_leftAdd_env .+: add_rightAdd_env .+: emptyAspect 


asp = aspEval .:+: aspEnv


data Expr = Val Int
          | Var String
          | Add Expr Expr
       deriving Show



sem_Expr asp (Add l r) = knitAspect add asp
                           $  leftAdd  .=. sem_Expr asp l
                          .*. rightAdd .=. sem_Expr asp r
                          .*.  EmptyRec
sem_Expr asp (Val i)   = knitAspect val asp$
                          ival  .=. sem_Lit i .*. EmptyRec
sem_Expr asp (Var v)   = knitAspect var asp$
                          vname .=. sem_Lit v .*. EmptyRec

evalExpr e m = sem_Expr asp e (env =. m .*. emptyAtt) #. eval


exampleExpr =  Add (Val (-9)) (Add (Var "x") (Val 2))
exampleEval =  evalExpr exampleExpr (insert "x" 5 Data.Map.empty)

