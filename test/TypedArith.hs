{-# LANGUAGE FlexibleContexts,
  DataKinds, GADTs, TypeFamilies, NoMonomorphismRestriction #-}
module TypedArith where

import Language.Grammars.AspectAG
import Data.Maybe
import Control.Monad.Except

type Name = String

-- | The AST for a simple expression language
data Expr
  = B Bool
  | N Int
  | Add  Expr Expr
  | Cond Expr Expr Expr
  | IsZ  Expr
  | Var Name
  | Let Name Expr Expr
  deriving (Eq, Show)


-- | Labels for productions
data P_B    ; p_B    = Label :: Label P_B
data P_N    ; p_N    = Label :: Label P_N
data P_Add  ; p_Add  = Label :: Label P_Add
data P_Cond ; p_Cond = Label :: Label P_Cond
data P_IsZ  ; p_IsZ  = Label :: Label P_IsZ
data P_Var  ; p_Var  = Label :: Label P_Var
data P_Let  ; p_Let  = Label :: Label P_Let

-- | Labels for children
data Ch_B;      ch_B      = Label :: Label (Ch_B,      Bool)
data Ch_N;      ch_N      = Label :: Label (Ch_N,      Int)
data Ch_Add_L;  ch_Add_L  = Label :: Label (Ch_Add_L,  Expr)
data Ch_Add_R;  ch_Add_R  = Label :: Label (Ch_Add_R,  Expr)
data Ch_Cond_C; ch_Cond_C = Label :: Label (Ch_Cond_C, Expr)
data Ch_Cond_T; ch_Cond_T = Label :: Label (Ch_Cond_T, Expr)
data Ch_Cond_E; ch_Cond_E = Label :: Label (Ch_Cond_E, Expr)
data Ch_IsZ;    ch_IsZ    = Label :: Label (Ch_IsZ,    Expr)
data Ch_Var;    ch_Var    = Label :: Label (Ch_Var,    Name)
data Ch_Let_N;  ch_Let_N  = Label :: Label (Ch_Let_N,  Name)
data Ch_Let_E;  ch_Let_E  = Label :: Label (Ch_Let_E,  Expr)
data Ch_Let_B;  ch_Let_B  = Label :: Label (Ch_Let_B,  Expr)

-- | Labels for terminals
data BVal; bval = Label :: Label (BVal, Bool)
data NVal; nval = Label :: Label (NVal, Int)
data VVal; vval = Label :: Label (VVal, Name)



-- | semantic functions
sem_Nat :: Int -> Attribution p -> Attribution '[ '((NVal, Int), Int) ]
sem_Nat  n _ = (nval =. n) *. emptyAtt
sem_Bool :: Bool -> Attribution p -> Attribution '[ '((BVal, Bool), Bool) ]
sem_Bool b _ = (bval =. b) *. emptyAtt
sem_Var :: Name -> Attribution p -> Attribution '[ '((VVal, Name), Name) ]
sem_Var nam _ = (vval =. nam) *. emptyAtt

sem_Expr asp (N n)
  = knit (asp .#. p_N) $ (ch_N .=. sem_Nat n) .*. emptyRecord
                  ---- TODO: no esta haciendo nada, testear
sem_Expr asp (B b)
  = knit (asp .#. p_B) $ (ch_B .=. sem_Bool b) .*. emptyRecord

sem_Expr asp (Add l r)
  = knit (asp .#. p_Add) $  ch_Add_L .=. sem_Expr asp l
                        .*. ch_Add_R .=. sem_Expr asp r
                        .*. emptyRecord
sem_Expr asp (Cond c t e)
  = knit (asp .#. p_Cond) $  ch_Cond_C .=. sem_Expr asp c
                         .*. ch_Cond_T .=. sem_Expr asp t
                         .*. ch_Cond_E .=. sem_Expr asp e
                         .*. emptyRecord
sem_Expr asp (IsZ e)
  = knit (asp .#. p_IsZ) $  ch_IsZ .=. sem_Expr asp e
                        .*. emptyRecord
--sem_Expr asp (Var nam)
-- = knit (asp .#. p_Var) $  ch_Var .=. sem_Var nam
--                       .*. emptyRecord


-- | An attribute type is used to compute the type of an expression
data Att_stype; stype = Label :: Label Att_stype

data Types
  = Boolean
  | Natural
  deriving (Eq, Show)

b_stype (Fam c p)
  = syndef stype $ Right Boolean

n_stype (Fam c p)
  = syndef stype $ Right Natural

add_stype (Fam c p)
  = syndef stype $ do leftT  <- c # ch_Add_L # stype
                      rightT <- c # ch_Add_R # stype
                      if leftT == rightT && rightT == Natural
                      then return Natural
                      else throwError addError  

cond_stype (Fam c p)
  = syndef stype $ do condT <- c # ch_Cond_C # stype
                      if condT /= Boolean
                      then throwError condError
                      else do 
                        thenT <- c # ch_Cond_T # stype
                        elseT <- c # ch_Cond_E # stype
                        if thenT == elseT
                        then return thenT
                        else throwError ifError 

isZ_stype (Fam c p)
  = syndef stype $ do chT <- c # ch_IsZ # stype
                      if chT == Natural
                      then return Boolean
                      else throwError isZError

addError  = "Error: trying to add a non Natural"
condError = "Error: conditions must be of type bool"
ifError   = "Error: then and else expressions must have the same Type"
isZError  = "Error: Zero testing must be applied to Naturals"




-- | Aspect for typing
asp_stype
  =   p_N    .=. n_stype
  .*. p_B    .=. b_stype
  .*. p_Add  .=. add_stype
  .*. p_Cond .=. cond_stype
  .*. p_IsZ  .=. isZ_stype
  .*. emptyRecord


typeCheck e = sem_Expr asp_stype e emptyAtt # stype


-- | An attribute for the evaluation of an expression, the returned
-- value is an integer, regardless what type the expression has.
-- This models in some sense a low level representation of values,
-- then piecen together type information and evaluation the
-- proper interpretation is computed
data Att_sval; sval = Label :: Label Att_sval

b_sval (Fam c p)
  = syndef sval $ b2Int $ c # ch_B # bval
  where b2Int b = if b then 1 else 0
n_sval (Fam c p)
  = syndef sval $ c # ch_N # nval
add_sval (Fam c p)
  = syndef sval $ c # ch_Add_L # sval + c # ch_Add_R # sval  
cond_sval (Fam c p)
  = syndef sval $ if c # ch_Cond_C # sval /= 0 -- 0 -> F, _ -> T
                  then c # ch_Cond_T # sval
                  else c # ch_Cond_E # sval
isZ_sval (Fam c p)
  = syndef sval $ if c # ch_IsZ # sval == 0 then 1 else 0 

asp_sval
  =   p_N    .=. n_sval
  .*. p_B    .=. b_sval
  .*. p_Add  .=. add_sval
  .*. p_Cond .=. cond_sval
  .*. p_IsZ  .=. isZ_sval
  .*. emptyRecord 

eval e = sem_Expr asp_sval e emptyAtt # sval


-- | expressions for testing
ok1 = N 12 `Add` N 23 `Add` N 23
ok2 = Cond (IsZ (N 0)) ok1 (N 0)
ok3 = Cond (IsZ (N 0)) (N 0) ok1
ok4 = Cond (B False) (IsZ (Add ok1 ok1)) (B False)

no1 = Cond ok1 ok2 ok2
no2 = Cond (B False) ok4 ok1




{-
 b_sval (Fam c p)
   = syndef stype $ _

With this hole the message showed is:

Relevant bindings include
        p :: Attribution p (bound at TypedArith.hs:55:15)
        c :: ChAttsRec c (bound at TypedArith.hs:55:13)
        b_sval :: Fam c p -> Fam ic sp -> Fam ic ('(Att_stype, val) : sp)

which is not really useful to construct a proof since
there is no information abou c and p

It would be really useful for AspectAG to have access to have access to the
type class constraints of typed holes, to be able to effectively do type
driven programming of attribute grammars.

https://stackoverflow.com/questions/23028124/is-there-a-way-to-make-ghc-provide-the-type-class-constraints-of-typed-holes

-}



{-


sem_Nat :: Int -> Attribution p -> Attribution '[ '((NVal, Int), Int) ]
sem_Nat n _ = nval
sem_Expr asp (B n)
  = knit (asp .#. p_B) $ ch_N .=. sem_Nat n .*. emptyRecord


TypedArith.hs:92:15: error:
    • Couldn't match expected type ‘Attribution '['((NVal, Int), Int)]’
                  with actual type ‘Label (NVal, Bool)’
    • In the expression: nval
      In an equation for ‘sem_Nat’: sem_Nat n _ = nval
   |
92 | sem_Nat n _ = nval
   |               ^^^^

TypedArith.hs:94:43: error:
    • Couldn't match expected type ‘Int’ with actual type ‘Bool’
    • In the first argument of ‘sem_Nat’, namely ‘n’
      In the second argument of ‘(.=.)’, namely ‘sem_Nat n’
      In the first argument of ‘(.*.)’, namely ‘ch_N .=. sem_Nat n’
   |
94 |   = knit (asp .#. p_B) $ ch_N .=. sem_Nat n .*. emptyRecord
   |                                           ^
Failed, no modules loaded.

-}
