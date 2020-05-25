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

module Lambda where

import Language.Grammars.AspectAG
import Language.Grammars.AspectAG.TH
import Data.Type.Require

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
$(addProd "S" ''Nt_Term [])
$(addProd "K" ''Nt_Term [])
$(addProd "I" ''Nt_Term [])


$(closeNT ''Nt_Term)
$(mkSemFuncs [''Nt_Term])


type VarSet = Set Name
type Env = M.Map Name Term 
-- whnf


-- kinds of syn constructs
data SynC = V | Ab | Ap

$(attLabels [("seval", ''Term),
             ("sfv", ''VarSet),
             ("ssynC", ''SynC ),
             ("ienv", ''Env),
             ("sid", ''Term),
             ("spp", ''String)
            ])

asp_sid =
      syn sid p_Abs (Abs <$> ter ch_x <*> at ch_e sid)
  .+: syn sid p_App (App <$> at ch_l sid <*> at ch_r sid)
  .+: syn sid p_Var (Var <$> ter ch_v)
  .+: syn sid p_S (pure S)
  .+: syn sid p_K (pure K)
  .+: syn sid p_I (pure I)
  .+: emptyAspect

asp_ssynC =
      syn ssynC p_Abs (pure Ab)
  .+: syn ssynC p_App (pure Ap)
  .+: syn ssynC p_Var (pure V)
  .+: syn ssynC p_S (pure V)
  .+: syn ssynC p_K (pure V)
  .+: syn ssynC p_I (pure V)
  .+: emptyAspect

asp_fv =
  syn sfv p_Var (S.singleton <$> ter ch_v) .+:
  syn sfv p_App (S.union <$> at ch_l sfv <*> at ch_r sfv) .+:
  syn sfv p_Abs (S.delete <$> ter ch_x <*> at ch_e sfv) .+:
  syn sfv p_S (pure S.empty) .+:
  syn sfv p_K (pure S.empty) .+:
  syn sfv p_I (pure S.empty) .+:
  emptyAspect
  

asp_spp =
      syn spp p_Var (ter ch_v)
  .+: syn spp p_App (do l <- at ch_l spp
                        r <- at ch_r spp
                        lk <- at ch_l ssynC
                        rk <- at ch_r ssynC
                        case (lk, rk) of
                          (Ap, Ap) -> return $ l ++ " (" ++ r ++ ")"
                          (Ap, _)  -> return $ l ++ " " ++ r
                          (Ab, Ap) -> return $ "(" ++ l ++ ") (" ++ r ++ ")"
                          (Ab, Ab) -> return $ "(" ++ l ++ ") (" ++ r ++ ")"
                          (Ab, _)  -> return $ "(" ++ l ++ ") " ++ r
                          (V, Ap)  -> return $ l ++ " (" ++ r ++ ")"
                          (V, Ab)  -> return $ l ++ " (" ++ r ++ ")"
                          (V, _)   -> return $ l ++ " " ++ r
                    )
  .+: syn spp p_Abs (do x  <- ter ch_x
                        rk <- at ch_e ssynC
                        e  <- at ch_e spp
                        case rk of
                          Ab -> return ("\\" ++ x ++ " " ++ tail e)
                          _  -> return ( "\\" ++ x ++ " -> " ++ e)
                   )
  .+: syn spp p_S (return "S")
  .+: syn spp p_K (return "K")
  .+: syn spp p_I (return "I")
  .+: emptyAspect

ppExpr e =
  sem_Term asp_spp' e emptyAtt #. spp
  where asp_spp' = asp_spp .:+: asp_ssynC

display = putStrLn . ppExpr

--- examples-----------------
tid = Abs "x" (Var "x")
tt  = Abs "t" $ Abs "f" $ Var "t"
ff  = Abs "t" $ Abs "f" $ Var "f"

chnat n =
  Abs "f" $ Abs "x" $ chaux n
  where chaux 0 = Var "x"
        chaux n = App (Var "f") $ chaux (n - 1)

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

compile :: Term -> Term
compile (Abs x (App l r)) =
  let cl = compile (Abs x l)
      cr = compile (Abs x r)
  in App (App S cl) cr
compile (Abs x (Var y))
  | x == y    = I 
  | otherwise = App K (Var y)
compile (Abs x t@(Abs y u)) =
  let t' = compile t
  in compile (Abs x t')
compile (Abs x comb) = App K comb
-- compile (App l r) = App (compile l)(compile r)
compile a = a
-- (Var x) = App I (Var x)
-- compile S = S
-- compile K = K
-- compile I = I

