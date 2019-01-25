{-# LANGUAGE 
             TypeFamilies,
             FlexibleContexts,
             ScopedTypeVariables,
             NoMonomorphismRestriction,
             AllowAmbiguousTypes,
             ImplicitParams,
             ExtendedDefaultRules,
             UnicodeSyntax,
             DataKinds
#-}

module Main where
import Language.Grammars.AspectAG
import System.Exit (exitFailure)
import qualified Data.Map as M
import Data.Maybe

data Exp
  = Lit Int
  | Add Exp Exp
  | Inc Exp
  | Var Name
  | Let Name Exp Exp
  deriving Show

type Name = String

data Att_sval; sval = Label :: Label Att_sval
data Att_ienv; ienv = Label :: Label Att_ienv

data Ch_Lit;      ch_lit      = Label :: Label (Ch_Lit, Int)
data Ch_Add_l;    ch_add_l    = Label :: Label (Ch_Add_l, Exp)
data Ch_Add_r;    ch_add_r    = Label :: Label (Ch_Add_r, Exp)
data Ch_Inc;      ch_inc      = Label :: Label (Ch_Inc, Exp)
data Ch_Var;      ch_var      = Label :: Label (Ch_Var, String)
data Ch_Let_Name; ch_let_name = Label :: Label (Ch_Let_Name, Name)
data Ch_Let_Val;  ch_let_val  = Label :: Label (Ch_Let_Val, Exp)
data Ch_Let_Exp;  ch_let_exp  = Label :: Label (Ch_Let_Exp, Exp)

data P_Lit; p_Lit = Label :: Label P_Lit
data P_Add; p_Add = Label :: Label P_Add
data P_Inc; p_Inc = Label :: Label P_Inc
data P_Var; p_Var = Label :: Label P_Var 
data P_Let; p_Let = Label :: Label P_Let

nt_Exp = undefined :: Label Exp



lit_sval (Fam c p)
  = syndef sval $ c # ch_lit # val
add_sval (Fam c p)
  = syndef sval $ (c # ch_add_l # sval) + (c # ch_add_r # sval)
inc_sval (Fam c p)
  = syndef sval $ c # ch_inc # sval +1
var_sval (Fam c p)
  = syndef sval $ let name = c # ch_var # nam
                      env  = p # ienv
                  in fromJust . M.lookup name $ env

let_sval (Fam c p)
  = syndef sval $ c # ch_let_exp # sval

add_ienv (Fam c p)
  = inhdef ienv (nt_Exp .: ε)
        (  ch_add_l .=. p # ienv
       .*. ch_add_r .=. p # ienv
       .*. emptyRecord)
inc_ienv (Fam c p)
  = inhdef ienv (nt_Exp .: ε)
        (  ch_inc .=. p # ienv
       .*. emptyRecord)
let_ienv (Fam c p)
  = inhdef ienv (nt_Exp .: ε)
        (  ch_let_val .=. (p # ienv)
       .*. ch_let_exp .=. (let key = c # ch_let_name # nam
                               val = c # ch_let_val # sval
                               env = p # ienv
                           in M.insert key val env)
       .*. emptyRecord)

sem_Exp asp (Add l r)
  = knit (asp .#. p_Add) $  ch_add_l .=. sem_Exp asp l
                        .*. ch_add_r .=. sem_Exp asp r
                        .*. emptyRecord
sem_Exp asp (Inc e)
  = knit (asp .#. p_Inc) $ ch_inc .=. sem_Exp asp e
                        .*. emptyRecord
sem_Exp asp (Lit i)
  = knit (asp .#. p_Lit)$ ch_lit .=. sem_Lit i .*. emptyRecord
sem_Exp asp (Var n)
  = knit (asp .#. p_Var) $ ch_var .=. sem_Name n
                        .*. emptyRecord
sem_Exp asp (Let name val exp)
  = knit (asp .#. p_Let) $  ch_let_name .=. sem_Name name
                        .*. ch_let_val  .=. sem_Exp asp val
                        .*. ch_let_exp  .=. sem_Exp asp exp
                        .*. emptyRecord

sem_Lit :: Int -> Attribution '[]
        -> Attribution '[ '((Lit, Int), Int)]
sem_Lit i _ = (val =. i) *. emptyAtt
data Lit; val = Label :: Label (Lit,Int)


sem_Name :: Name -> Attribution '[]
        -> Attribution '[ '((Nam, Name), Name)]
sem_Name n _ = (nam =. n) *. emptyAtt
data Nam; nam = Label :: Label (Nam,Name)

testexp = Lit 4 `Add` Inc (Lit 5)

asp_sval
  =  p_Lit .=. lit_sval
 .*. p_Add .=. add_sval
 .*. p_Inc .=. inc_sval
 .*. p_Var .=. var_sval
 .*. p_Let .=. let_sval
 .*. emptyRecord

asp_ienv
  =  p_Add .=. add_ienv
 .*. p_Inc .=. inc_ienv
 .*. p_Let .=. let_ienv
 .*. emptyRecord



eval e = sem_Exp (asp_ienv .+. asp_sval) e (ienv =. M.empty *. emptyAtt) # sval


main = --exitFailure
  return ()
  -- pendiente ejecutar efectivamente tests automáticos
