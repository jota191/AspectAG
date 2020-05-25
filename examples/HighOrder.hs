{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeInType #-}

module HighOrder where

import Language.Grammars.AspectAG
import Language.Grammars.AspectAG.TH
import Data.Type.Require
import GHC.TypeLits


import Data.Kind
import Data.Proxy
import Data.Set as S
import Data.Map as M

type Name = String

$(addNont "Term")
$(addProd "Var" ''Nt_Term [("v", Ter ''Name)])
$(addProd "App" ''Nt_Term [("l", NonTer ''Nt_Term),
                           ("r", NonTer ''Nt_Term)])
$(addProd "Abs" ''Nt_Term [("x", Ter ''Name),
                           ("e", NonTer ''Nt_Term)])

$(closeNT ''Nt_Term)
$(mkSemFuncs [''Nt_Term])


type VarSet = Set Name
type Env = M.Map Name Term 
-- whnf

$(attLabels [("eval", ''Term),
             ("fv", ''VarSet),
             ("isAbs", ''Bool ),
             ("env", ''Env),
             ("sid", ''Term),
             ("spp", ''String)
            ])

asp_id =
      syn sid p_Abs (Abs <$> ter ch_x <*> at ch_e sid)
  .+: syn sid p_App (App <$> at ch_l sid <*> at ch_r sid)
  .+: syn sid p_Var (Var <$> ter ch_v)
  .+: emptyAspect

asp_isAbs =
      syn isAbs p_Abs (pure True)
  .+: syn isAbs p_App (pure False)
  .+: syn isAbs p_Var (pure False)
  .+: emptyAspect

asp_fv =
  syn fv p_Var (S.singleton <$> ter ch_v) .+:
  syn fv p_App (S.union <$> at ch_l fv <*> at ch_r fv) .+:
  syn fv p_Abs (S.delete <$> ter ch_x <*> at ch_e fv) .+:
  emptyAspect

asp_env =
      env `copyAtChi` ch_l
  .+: env `copyAtChi` ch_r
  .+: env `copyAtChi` ch_e
  .+: emptyAspect

asp_eval =
  (syn eval p_Var
    $ do envir <- at lhs env
         vname <- ter ch_v
         do case M.lookup vname envir of
              Nothing -> return (Var vname)
              Just t  -> return t
  )
  .+:
  (syn eval p_Abs
    $ Abs <$> ter ch_x <*> at ch_e eval
  )
  .+:
  (syn eval p_App
    $ do lam  <- at ch_l eval
         arg  <- at ch_r eval
         envi <- at lhs env
         case lam of
           Abs v body -> return (evalTerm body (M.insert v arg M.empty))
           _ -> return $ App lam arg
  )
  .+: emptyAspect

asp_pp =
  (syn spp p_Abs
    $ do var <- ter ch_x
         bo  <- at ch_e spp
         return $ 'λ':var ++ ". " ++ bo
  ).+:
  (syn spp p_App
    $ do l <- at ch_l spp
         r <- at ch_r spp
         return $ l ++ " " ++ r
  ).+:
  (syn spp p_Var (ter ch_v)
  ).+: emptyAspect

evalTerm t e = sem_Term (asp_eval .:+: asp_env .:+: asp_id
                        ) t (env .=. e .*. emptyAtt) #. eval

pp t = sem_Term asp_pp t emptyAtt #. spp

ev t = evalTerm t M.empty

tid = Abs "x" (Var "x")
tt  = Abs "t" $ Abs "f" $ Var "t"
ff  = Abs "t" $ Abs "f" $ Var "f"

chnat n =
  Abs "s" $ Abs "z" $ chaux n
  where chaux 0 = Var "z"
        chaux n = App (Var "s") $ chaux (n - 1)

suc = Abs "n" $ Abs "f" $ Abs "x" $
  App (Var "f")(App (App (Var "n")(Var "f"))(Var "x"))

-- add = Abs "m" $ Abs "n" $ Abs "f" $ Abs "x" $
--   App (App (Var "n")(Var "f"))
--   (App (App (Var "m")(Var "f")) (Var "x")) 
add = lam "m" $ lam "n" $ app3 (Var "m") suc (Var "n")

lam x v = Abs x v
app3 m n k = App (App m n) k


mult = lam "m" $ lam "n" $ app3 (Var "m") (App add (Var "n")) (chnat 0)

pow = lam "b" $ lam "e" $ App (Var "b") (Var "e")

data family C (l :: [Type]) :: Type

data instance C '[] = N
data instance C (x ': xs) = C x | B (C xs)
