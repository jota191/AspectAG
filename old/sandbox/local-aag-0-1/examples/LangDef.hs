{-# OPTIONS -fcontext-stack=100 #-}
{-# LANGUAGE TemplateHaskell, EmptyDataDecls, NoMonomorphismRestriction #-}

module LangDef where

import Language.Grammars.AspectAG
import Language.Grammars.AspectAG.Derive

import Data.HList.Label4
import Data.HList.TypeEqGeneric1
import Data.HList.TypeCastGeneric1

import Data.Maybe

import UU.Pretty

import Control.Monad 


data AGItf = AGItf { expr :: T_Expr}
          deriving Show

data T_Expr  =  Cst {cv  :: Int}
             |  Var {vnm :: String}
             |  Mul {me1 :: T_Expr, me2 :: T_Expr}
             |  Add {ae1 :: T_Expr, ae2 :: T_Expr}
             |  Let {lnm :: String, val :: T_Expr, body :: T_Expr}
          deriving Show



syn = syndefM
inh = inhdefM


$(deriveAG ''AGItf)

exprNT = nt_T_Expr .*. hNil
allNT  = nt_AGItf .*. exprNT
 

$(attLabels ["spp"])

sppAGItf  = syn spp $ liftM (# spp) (at ch_expr)
sppCst    = syn spp $ liftM pp      (at ch_cv)
sppVar    = syn spp $ liftM pp      (at ch_vnm)
sppMul    = syn spp $ do  e1 <- at ch_me1 
                          e2 <- at ch_me2
                          return $ e1 # spp >|< " * " >|< e2 # spp 
sppAdd    = syn spp $ do  e1 <- at ch_ae1 
                          e2 <- at ch_ae2
                          return $ e1 # spp >|< " + " >|< e2 # spp 

sppLet    = syn spp $ do  lnm  <- at ch_lnm
                          val  <- at ch_val
                          body <- at ch_body
                          return $ "let " >|< pp lnm >|< " = " >|< val # spp >|< " in " >|< body # spp    


$(attLabels ["ienv","sval"])


ienvRule  = copy ienv exprNT  
ienvAGItf = inh ienv exprNT $ do return  (ch_expr .=. ([] :: [(String,Int)]) .*.  emptyRecord)
ienvCst   = ienvRule
ienvVar   = ienvRule
ienvMul   = ienvRule
ienvAdd   = ienvRule
ienvLet   = inh ienv exprNT $ do lnm <- at ch_lnm
                                 val <- at ch_val
                                 lhs <- at lhs
                                 return  $  ch_val   .=.  lhs # ienv .*.
                                            ch_body  .=.  (lnm, val # sval) : lhs # ienv .*.  
                                            emptyRecord


svalRule  f = use sval allNT f  (0::Int)  
svalAGItf = svalRule ((*)::Int->Int->Int)
svalCst   = syn sval $ liftM id (at ch_cv)
svalVar   = syn sval $ do  vnm <- at ch_vnm 
                           lhs <- at lhs
                           return $ fromJust (lookup vnm (lhs # ienv)) 
svalMul   = svalRule ((*)::Int->Int->Int)
svalAdd   = svalRule ((+)::Int->Int->Int)
svalLet   = syn sval $ liftM (# sval) (at ch_body)


aspAGItf = sppAGItf `ext` ienvAGItf `ext` svalAGItf
aspCst   = sppCst   `ext` ienvCst   `ext` svalCst  
aspVar   = sppVar   `ext` ienvVar   `ext` svalVar  
aspMul   = sppMul   `ext` ienvMul   `ext` svalMul  
aspAdd   = sppAdd   `ext` ienvAdd   `ext` svalAdd  
aspLet   = sppLet   `ext` ienvLet   `ext` svalLet


semAGItf  = semP_AGItf aspAGItf 
semCst    = semP_Cst aspCst 
semVar    = semP_Var aspVar 
semMul    = semP_Mul aspMul
semAdd    = semP_Add aspAdd
semLet    = semP_Let aspLet 


ex1Expr = semLet  (sem_Lit "x")  (semCst $ sem_Lit  2) 
                  (semAdd (semVar $ sem_Lit "x") (semCst $ sem_Lit  3)) 

eval ex = do
        let res = ex (ienv .=. [] .*. emptyRecord)
        print $ res  # spp
        print $ res  # sval

ex1 = eval ex1Expr



