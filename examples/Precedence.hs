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

module Rose where

import Language.Grammars.AspectAG
import Language.Grammars.AspectAG.TH

import Data.Kind
import Data.Proxy

type Atom = String
data Op = Plus | Times | Exp deriving (Eq,Read,Show)

ppOp Plus = " + "
ppOp Times = " * "
ppOp Exp = " ^ "

prec :: Op -> Int
prec Plus  = 6
prec Times = 7
prec Exp = 8

$(addNont "Exp")
$(addProd "Lit" ''Nt_Exp [("lit", Ter ''Atom)])
$(addProd "Bop" ''Nt_Exp [("l", NonTer ''Nt_Exp),
                          ("bop", Ter ''Op),
                          ("r", NonTer ''Nt_Exp)])
$(closeNTs [''Nt_Exp])

$(attLabels [("pp" , ''String), ("pr", ''Int)])
$(mkSemFuncs [''Nt_Exp])

asp_pp =
  syn pp p_Lit (ter ch_lit)
  .+:
  syn pp p_Bop
  (
    do l <- at ch_l pp
       r <- at ch_r pp
       op <- ter ch_bop
       let localPrec  = prec op
       lPrec <- at ch_l pr
       rPrec <- at ch_r pr
       return $ wrapIf (localPrec > lPrec) l
         ++ ppOp op
         ++ wrapIf (localPrec > rPrec) r
  )
  .+: emptyAspect
  where wrapIf :: Bool -> String -> String
        wrapIf b s = if b
                     then "(" ++ s ++ ")"
                     else s

asp_pr =
  syn pr p_Lit (pure 11) -- bigger than any prec
 .+: syn pr p_Bop (prec <$> ter ch_bop)
 .+: emptyAspect

printExp e = sem_Exp (asp_pp .:+: asp_pr) e emptyAtt #. pp

e 1 = Bop (Lit "e1") Plus (Lit "e2")
e 2 = Bop (Lit "e1") Times (Lit "e2")
e 3 = Bop (e 1) Plus (e 2)
e 4 = Bop (e 2) Times (e 3)
e 5 = Bop (Bop (Bop (Lit "e")
                    Exp
                    (Lit "e"))
                Times
                (Lit "e"))
        Plus
        (Lit "e")
e 6 = Bop (Bop (Bop (Lit "e")
                    Plus
                    (Lit "e"))
                Times
                (Lit "e"))
        Plus
        (Lit "e")
