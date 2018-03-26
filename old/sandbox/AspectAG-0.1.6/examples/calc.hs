{-# OPTIONS -XEmptyDataDecls #-}
{-# LANGUAGE TemplateHaskell #-}

module Calc where

import Data.AspectAG
import Data.AspectAG.Derive

import Data.HList.Label4
import Data.HList.TypeEqGeneric1
import Data.HList.TypeCastGeneric1

import UU.Pretty hiding (par)

--data types-------------------------------------------------------------------

data AGItf = AGItf { expr :: Expr}
          deriving Show

data Expr = IConst {int::Int}
          | Add    {e1::Expr, e2::Expr}
          | Let    {lnm::String, val::Expr, body::Expr}
          | Var    {vnm::String}
          deriving Show


$(deriveAG ''AGItf)


allNT = nt_AGItf .*. nt_Expr .*. hNil
 
-------------------------------------------------------------------------------


$(attLabel "spp")

asp_spp () = synAspect spp allNT ((>|<)::PP_Doc->PP_Doc->PP_Doc)  (empty::PP_Doc) ( p_AGItf .*. hNil )
                       (   p_IConst .=. (\(Fam chi _) -> pp (chi # ch_int))
                       .*. p_Add    .=. (\(Fam chi _) -> ((chi # ch_e1) # spp) >|< "+" >|< ((chi # ch_e2) # spp))    
                       .*. p_Var    .=. (\(Fam chi _) -> pp (chi # ch_vnm))
                       .*. p_Let    .=. (\(Fam chi _) -> "[" >|< (chi # ch_lnm) >|< "=" >|<
                                                         ((chi # ch_val) # spp) >|< ":" >|< ((chi # ch_body) # spp) >|< "]")    
                       .*. emptyRecord )


$(attLabels ["ienv","sval"])

asp_ienv () = inhAspect ienv ( nt_Expr .*. hNil ) ( p_Add .*. p_Let .*. hNil )
                       (   p_Let    .=. (\(Fam chi par) -> (    ch_body .=. ((chi # ch_lnm), ((chi # ch_val) # sval)) : (par # ienv)  
                                                           .*.  emptyRecord))
                       .*. p_AGItf  .=. (\(Fam chi _)   -> (    ch_expr .=. ([] :: [(String,Int)])
                                                           .*.  emptyRecord))
                       .*. emptyRecord )

asp_sval () = synAspect sval allNT ((+)::Int->Int->Int)  (0::Int) ( p_AGItf .*. p_Add .*. hNil )
                       (   p_IConst .=. (\(Fam chi _)   -> chi # ch_int)
                       .*. p_Var    .=. (\(Fam chi par) -> maybe 0 id (lookup (chi # ch_vnm) (par # ienv)))
                       .*. p_Let    .=. (\(Fam chi _)   -> (chi # ch_body) # sval)    
                       .*. emptyRecord )


$(attLabel "ccount")


asp_ccount () =   chnAspect ccount allNT ( p_AGItf .*. p_IConst .*. p_Add .*. p_Let .*. p_Var .*. hNil )
                       emptyRecord
                       (   p_Add    .=. (\(Fam chi _) -> ((chi # ch_e2) # ccount) + 1 )    
                       .*. emptyRecord )


----example--------------------------------------------------------------------


ex = Let "x" (Add (Add (IConst 2) (IConst 3)) (IConst 1)) (Add (Var "x") (Var "x"))

 
expp  = sem_AGItf (asp_spp ()) (AGItf ex) () # spp
exval = sem_AGItf (asp_sval () .+. asp_ienv ()) (AGItf ex) () # sval
excnt = sem_AGItf (asp_ccount ()) (AGItf ex)  (ccount .=. 0 .*. emptyRecord) # ccount

