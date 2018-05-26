{-# OPTIONS -fcontext-stack=100 #-}
{-# LANGUAGE TemplateHaskell, EmptyDataDecls, NoMonomorphismRestriction #-}

module LangExt where

import Language.Grammars.AspectAG
import Language.Grammars.AspectAG.Derive

import Data.HList.Label4
import Data.HList.TypeEqGeneric1
import Data.HList.TypeCastGeneric1

import Data.Maybe

import UU.Pretty

import Control.Monad 

import LangDef


-- modifications of the semantics
synM = synmodM
inhM = inhmodM


 
--Square
-- $(chLabel "se" ''T_Expr)
$(addProd "Sq" [ ("se",''T_Expr) ])

sppSq = synM spp $ do me1 <- at ch_se 
                      return $ "square" >#< (me1 # spp)   

se2m r = (ch_me1 .=. (r # ch_se) .*. ch_me2 .=. (r # ch_se) .*. emptyRecord)
m2se r = (ch_se .=. (r # ch_me1) .*. emptyRecord)


-- aspSq = sppSq `ext` (adapt aspMul se2m se2m m2se)
aspSq = sppSq `ext` (mapChildren aspMul (ch_me1 .=. ch_se .*. ch_me2 .=. ch_se .*. emptyRecord))

-- semSq = \s -> knit aspSq (s .*. emptyRecord)  
semSq = semP_Sq aspSq



ex2Expr = semLet  (sem_Lit "x")  (semCst $ sem_Lit  2) 
                  (semSq (semVar $ sem_Lit "x")) 

ex2 = eval ex2Expr


--Pyth
-- $(chLabels ["pe1","pe2"] ''T_Expr)
$(addProd "Pyth" [ ("pe1",''T_Expr), ("pe2",''T_Expr) ])

sppSq' = synM spp $ do liftM (# spp) (at ch_se) 
aspSq' = sppSq' `ext` aspSq 

sppPyth  = synM spp  $ do  pe1 <- at ch_pe1
                           pe2 <- at ch_pe2 
                           return $ "pyth" >#< (pe1 # spp) >#< (pe2 # spp)   
{-
aspAdd' =  graft  (graft  aspAdd
                          (ch_ae2 .=. ch_ae2 .*. emptyRecord)
                          ch_ae1 
                          aspSq' 
                          (ch_se .=. ch_pe1 .*. emptyRecord))
                  (ch_pe1 .=. ch_pe1 .*. emptyRecord)
                  ch_ae2
                  aspSq' 
                  (ch_se .=. ch_pe2 .*. emptyRecord)
-}

aspAdd' =  agMacro  (aspAdd   ,   ch_ae1 ==> (aspSq', ch_se --> ch_pe1)   
                             <.>  ch_ae2 ==> (aspSq', ch_se --> ch_pe2))

aspPyth    = sppPyth `ext` aspAdd'
-- semPyth = \p1 p2 -> knit  aspPyth (p1 .*. p2 .*. emptyRecord)  
semPyth = semP_Pyth aspPyth

ex3Expr = semLet  (sem_Lit "x")  (semCst $ sem_Lit  2) 
                  (semPyth (semVar $ sem_Lit "x") (semCst $ sem_Lit  3) ) 

ex3 = eval ex3Expr


--AddSq
$(addProd "AddSq" [ ("as1",''T_Expr), ("as2",''T_Expr) ])


sppAddSq  = synM spp  $ do  as1 <- at ch_as1
                            as2 <- at ch_as2 
                            return $ "addsq" >#< (as1 # spp) >#< (as2 # spp)   



{-
aspAddSq = sppAddSq `ext`
           (graft  (graft  aspMul
                           (ch_me2 .=. ch_me2 .*. emptyRecord)
                           ch_me1 
                           aspAdd 
                           (ch_ae1 .=. ch_as1 .*. ch_ae2 .=. ch_as2 .*. emptyRecord))
                   (ch_as1 .=. ch_as1 .*. ch_as2 .=. ch_as2 .*. emptyRecord)
                   ch_me2
                   aspAdd 
                   (ch_ae1 .=. ch_as1 .*. ch_ae2 .=. ch_as2 .*. emptyRecord))
-}

aspAddSq = sppAddSq `ext`
            agMacro  (aspMul   ,   ch_me1 ==> (aspAdd, ch_ae1 --> ch_as1 <.> ch_ae2 --> ch_as2)
                              <.>  ch_me2 ==> (aspAdd, ch_ae1 --> ch_as1 <.> ch_ae2 --> ch_as2))


semAddSq = semP_AddSq aspAddSq

ex4Expr = (semAddSq (semCst $ sem_Lit 2) (semCst $ sem_Lit  3) ) 

ex4 = eval ex4Expr


--Double
-- $(chLabel "de" ''T_Expr)
$(addProd "Db" [ ("de",''T_Expr) ])

aspTwo = fixCst aspCst ch_cv 2
{-
aspMul' =  graft  aspMul
                  (ch_me2 .=. ch_de .*. emptyRecord) 
                  ch_me1
                  aspTwo
                  emptyRecord 
-}

aspMul' =  agMacro  (aspMul   ,   ch_me1 ==> (aspTwo, flip const)
                             <.>  ch_me2 --> ch_de)
                  

sppDb = synM spp $ do de <- at ch_de 
                      return $ "double" >#< (de # spp)   

aspDb = sppDb `ext` aspMul'
                
--semDb = \d -> knit aspDb (d .*. emptyRecord)
semDb = semP_Db aspDb
           

ex5Expr = (semAdd (semCst $ sem_Lit 2) (semDb (semCst $ sem_Lit  3)) ) 

ex5 = eval ex5Expr



--AddMul
-- $(chLabels ["am1","am2","am3"] ''T_Expr)
$(addProd "AddMul" [ ("am1",''T_Expr), ("am2",''T_Expr), ("am3",''T_Expr) ])


sppAddMul = synM spp $ do  am1 <- at ch_am1 
                           am2 <- at ch_am2 
                           am3 <- at ch_am3 
                           return $ "addmul" >#< (am1 # spp) >#< (am2 # spp) >#< (am3 # spp)  
{-
aspAddMul = ext sppAddMul $  graft  aspAdd
                                    (ch_ae1 .=. ch_am1 .*. emptyRecord)
                                    ch_ae2 
                                    aspMul
                                    (ch_me1 .=. ch_am2 .*. ch_me2 .=. ch_am3 .*. emptyRecord)
-}
aspAddMul = sppAddMul `ext`
            agMacro  (aspAdd   ,  ch_ae1 --> ch_am1
                              <.> ch_ae2 ==> (aspMul, ch_me1 --> ch_am2 <.> ch_me2 --> ch_am3))

 
-- semAddMul = \p1 p2 p3 -> knit aspAddMul (p1 .*. p2 .*. p3 .*. emptyRecord)
semAddMul = semP_AddMul aspAddMul                          

ex6Expr = (semAddMul (semCst $ sem_Lit 2) (semCst $ sem_Lit  3) (semCst $ sem_Lit  4)) 

ex6 = eval ex6Expr


--LetX
$(addProd "LetX" [ {-("valx",''T_Expr),-} ("bodyx",''T_Expr) ])


sppLetX = synM spp $ do -- valx  <- at ch_valx
                        bodyx <- at ch_bodyx
                        return $ "x =" >#< {-(valx # spp)-} "10" >#< "=>" >#< (bodyx # spp)  

{-
aspLet' = fixCst aspLet ch_lnm "x"

aspLetX = sppLetX `ext` (mapChildren aspLet' (ch_val .=. ch_valx .*. ch_body .=. ch_bodyx .*. emptyRecord))
-}                

aspLetX = sppLetX `ext` 
           agMacro (aspLet ,  ch_lnm ~~> "x" <.>
                              ch_val ~~> (sval .=. 10 .*. spp .=. "10" .*. emptyRecord) <.> -- --> ch_valx <.> 
                              ch_body --> ch_bodyx) 

semLetX = semP_LetX aspLetX
           

ex7Expr = (semLetX {-(semCst $ sem_Lit 10)-} (semDb (semVar $ sem_Lit  "x")) ) 

ex7 = eval ex7Expr


--AddMulMul
$(addProd "AddMulSq" [ ("ams1",''T_Expr), ("ams2",''T_Expr), ("ams3",''T_Expr) ])


sppAddMulSq = 
            synM spp $ do  ams1 <- at ch_ams1 
                           ams2 <- at ch_ams2 
                           ams3 <- at ch_ams3 
                           return $ "addmulsq" >#< (ams1 # spp) >#< (ams2 # spp) >#< (ams3 # spp)  

aspAddMulSq = sppAddMulSq `ext`
                   agMacro  (aspAdd   ,  ch_ae1 --> ch_ams1
                                     <.> ch_ae2 ==> (aspMul, ch_me1 --> ch_ams2 <.>
                                                             ch_me2 ==> (aspMul, ch_me1 --> ch_ams3 <.> ch_me2 --> ch_ams3)))


semAddMulSq = semP_AddMulSq aspAddMulSq                          

ex8Expr = semAddMulSq (semCst $ sem_Lit 2) (semCst $ sem_Lit  3) (semCst $ sem_Lit  4)

ex8 = eval ex8Expr


main = ex1 >> ex2 >> ex3 >> ex4 >> ex5 >> ex6 >> ex7 >> ex8


