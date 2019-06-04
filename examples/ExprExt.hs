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

module ExprExt where

import Language.Grammars.AspectAG
import Control.Monad
import Control.Applicative
import Data.Proxy
import GHC.TypeLits
import Data.Map
import Data.Maybe
import Expr


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


type P_Abs = 'Prd "p_Abs" Nt_Expr
eabs = Label @ P_Abs
type P_App = 'Prd "p_App" Nt_Expr
eapp = Label @ P_App

tAbs   = Label @ ('Chi "tAbs"   P_Abs ('Left Nt_Expr))
xAbs   = Label @ ('Chi "xAbs"   P_Abs ('Right ('T String)))

tApp   = Label @ ('Chi "tApp"   P_App ('Left Nt_Expr))
uApp   = Label @ ('Chi "uApp"   P_App ('Left Nt_Expr))



appStack = Label @ ('Att "appStack" [Int])

app_eval      = syndefM eval eapp $ at tApp eval
app_env_t     = inhdefM env eapp tApp $ at lhs env
app_env_u     = inhdefM env eapp uApp $ at lhs env
app_appStk_t  = inhdefM appStack eapp tApp
  $ do u      <- at uApp eval
       oldStk <- at lhs appStack
       return (u:oldStk)
app_appStk_u = inhdefM appStack eapp uApp $ pure []

abs_eval = syndefM eval eabs $ at tAbs eval
abs_env = inhdefM env eabs tAbs
  $ do x      <- ter xAbs
       envi   <- at lhs env
       st  <- at lhs appStack
       case st of
        -- [] -> return envi
         (s:_) -> return (insert x s envi)
abs_appStk_t = inhdefM appStack eabs tAbs
  $ tail <$> at lhs appStack

add_appStk_l  = inhdefM appStack add leftAdd  $ pure []
add_appStk_r  = inhdefM appStack add rightAdd $ pure []

let_appStk_r = inhdefM appStack elet bodyLet $ pure []
let_appStk_l = inhdefM appStack elet exprLet $ pure []

(.:+.) = flip (.+:)

aspLam = asp2 .:+. app_env_t .:+. app_env_u .:+. abs_env .:+. app_eval .:+. abs_eval
  .:+. abs_appStk_t .:+. app_appStk_t .:+. app_appStk_u
  .:+. let_appStk_l .:+. let_appStk_r .:+. add_appStk_r .:+. add_appStk_l

evalExpr'' e = sem_Expr'' aspLam e ( (appStack =. []) .*. (env =. (Data.Map.empty :: Map String Int )) .*. emptyAtt) #. eval


data Expr'' = Val'' Int
            | Var'' String
            | Add'' Expr'' Expr''
            | Let'' String Expr'' Expr''
            | App Expr'' Expr''
            | Abs String Expr''

sem_Expr'' asp (Add'' l r) = knitAspect add asp
                           $  leftAdd  .=. sem_Expr'' asp l
                          .*. rightAdd .=. sem_Expr'' asp r
                          .*.  EmptyRec
sem_Expr'' asp (Val'' i)   = knitAspect val asp
                         $ ival  .=. sem_Lit i .*. EmptyRec
sem_Expr'' asp (Var'' v)   = knitAspect var asp
                         $ vname .=. sem_Lit v .*. EmptyRec

sem_Expr'' asp (Let'' v e b) = knitAspect elet asp
                          $   vlet     .=. sem_Lit v
                         .*.  exprLet  .=. sem_Expr'' asp e
                         .*.  bodyLet  .=. sem_Expr'' asp b
                         .*.  EmptyRec
sem_Expr'' asp (Abs x t) = knitAspect eabs asp
                          $   xAbs   .=. sem_Lit x
                         .*.  tAbs   .=. sem_Expr'' asp t
                         .*.  EmptyRec
sem_Expr'' asp (App t u) = knitAspect eapp asp
                          $   uApp   .=. sem_Expr'' asp u
                         .*.  tApp   .=. sem_Expr'' asp t
                         .*.  EmptyRec


--evalExpr'' e = sem_Expr'' asp_All e (emptyAtt) #. eval


fun = Abs "x" (Var'' "x" `Add''` Val'' 4)

ex1 = fun `App` Val'' 89

f $$ x = App f x

instance Num Expr'' where
  fromInteger = Val'' . fromIntegral

lam = Abs
leti = Let''
v = Var''


f = (lam ("x") ((v "x") `Add''` (5 :: Expr'')))
g = (lam ("y") ((v "y") `Add''` (4::Expr'')))

