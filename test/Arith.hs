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

data Exp
  = Lit Int
  | Add Exp Exp
  | Inc Exp
  | Var Name
  deriving Show

type Name = String

data Att_sval; sval = Label :: Label Att_sval


data Ch_Lit;     ch_lit   = Label :: Label (Ch_Lit, Int)
data Ch_Add_l;   ch_add_l = Label :: Label (Ch_Add_l, Int)
data Ch_Add_r;   ch_add_r = Label :: Label (Ch_Add_r, Int)
data Ch_Inc;     ch_inc   = Label :: Label (Ch_Inc, Int)
data Ch_Var;     ch_var   = Label :: Label (Ch_Var, Int)

data P_Lit; p_Lit = Label :: Label P_Lit
data P_Add; p_Add = Label :: Label P_Add
data P_Inc; p_Inc = Label :: Label P_Inc
data P_Var; p_Var = Label :: Label P_Var 

nt_Exp = undefined :: Exp


lit_sval (Fam c p)
  = syndef sval $ c # ch_lit # val

add_sval (Fam c p)
  = syndef sval $ (c # ch_add_l # sval) + (c # ch_add_r # sval)

inc_sval (Fam c p)
  = syndef sval $ c # ch_inc # sval +1

var_sval (Fam c p)
  = syndef sval 0 -- por ahora, las variables valen todas cero


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
  = knit (asp .#. p_Var) $ ch_var .=. sem_Lit 0
                        .*. emptyRecord

sem_Lit :: Int -> Attribution '[]
        -> Attribution '[ '((Val, Int), Int)]
sem_Lit i _ = (val =. i) *. emptyAtt
data Val; val = Label :: Label (Val,Int)


testexp = Lit 4 `Add` Inc (Lit 5)

asp_sval =  p_Lit .=. lit_sval
        .*. p_Add .=. add_sval
        .*. p_Inc .=. inc_sval
        .*. p_Var .=. var_sval
        .*. emptyRecord


eval e = sem_Exp asp_sval e emptyAtt # sval


main = --exitFailure
  return ()
  -- pendiente ejecutar efectivamente tests automáticos
