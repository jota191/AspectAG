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


leftAdd   = Label @ ('Chi "leftAdd"   P_Add ('Left Nt_Expr))
rightAdd  = Label @ ('Chi "rightAdd"  P_Add ('Left Nt_Expr))
ival      = Label @ ('Chi "ival"      P_Val ('Right ('T Int)))
vname     = Label @ ('Chi "vname"     P_Var ('Right ('T String)))

eval = Label @ ('Att "eval" Int)
env  = Label @ ('Att "env"  (Map String Int))


add_eval  =  syndefM eval add  $ (+) <$> at leftAdd eval <*> at rightAdd eval
val_eval  =  syndefM eval val  $ ter ival
var_eval  =  syndefM eval var  $ slookup <$> ter vname <*> at lhs env

aspEval   =  traceAspect (Proxy @ ('Text "eval"))
          $  add_eval .+: val_eval .+: var_eval .+: emptyAspect

slookup nm = fromJust . Data.Map.lookup nm

add_leftAdd_env  = inhdefM env add leftAdd  $ at lhs env
add_rightAdd_env = inhdefM env add rightAdd $ at lhs env

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



type P_Let = 'Prd "p_Let" Nt_Expr
elet = Label @ P_Let


exprLet   = Label @ ('Chi "exprLet"   P_Let ('Left Nt_Expr))
bodyLet   = Label @ ('Chi "bodyLet"   P_Let ('Left Nt_Expr))
vlet      = Label @ ('Chi "vlet"      P_Let ('Right ('T String)))


aspEval2  = traceAspect (Proxy @ ('Text "eval2"))
          $ syndefM eval elet (at bodyLet eval) .+: aspEval


aspEnv2   =   traceAspect (Proxy @ ('Text "env2"))
          $   inhdefM env elet exprLet (at lhs env)
         .+:  inhdefM env elet bodyLet (insert  <$> ter vlet
                                                <*> at exprLet eval
                                                <*> at lhs env)
         .+:  aspEnv


asp2 = aspEval2 .:+: aspEnv2

data Expr' = Val' Int
           | Var' String
           | Add' Expr' Expr'
           | Let String Expr' Expr'
       deriving Show



sem_Expr' asp (Add' l r) = knitAspect add asp
                           $  leftAdd  .=. sem_Expr' asp l
                          .*. rightAdd .=. sem_Expr' asp r
                          .*.  EmptyRec
sem_Expr' asp (Val' i)   = knitAspect val asp
                          $ ival  .=. sem_Lit i .*. EmptyRec
sem_Expr' asp (Var' v)   = knitAspect var asp
                          $ vname .=. sem_Lit v .*. EmptyRec

sem_Expr' asp (Let v e b) = knitAspect elet asp
                           $   vlet     .=. sem_Lit v
                          .*.  exprLet  .=. sem_Expr' asp e
                          .*.  bodyLet  .=. sem_Expr' asp b
                          .*.  EmptyRec

evalExpr' e m = sem_Expr' asp2 e (env =. m .*. emptyAtt) #. eval 

exampleExpr' =  Add' (Val' (-9))
                     (Add' (Var' "x") (Let "x" (Val' 2)
                                               (Var' "x")))
exampleEval' =  evalExpr' exampleExpr'
                          (insert "x" 5 Data.Map.empty)



val_eval'  =  synmodM eval val  $ abs <$> ter ival


evalExpr'' e m = sem_Expr' (val_eval' .+: asp2) e
                           (env =. m *. emptyAtt) #. eval 
exampleEval'' =  evalExpr'' exampleExpr'
                            (insert "x" 5 Data.Map.empty)

