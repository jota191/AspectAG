{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE IncoherentInstances       #-}
{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE UnicodeSyntax             #-}
{-# LANGUAGE ImpredicativeTypes        #-}

module Language.Grammars.FirstClass where

import Data.Kind
import Language.Grammars.AspectAG
import Language.Grammars.AspectAG.RecordInstances
import Language.Grammars.AspectAG.HList

import Data.Type.Require

import GHC.Exts
import Unsafe.Coerce

import Data.Kind (Type, Constraint)
import GHC.TypeLits (Symbol, TypeError, ErrorMessage(..), AppendSymbol)
import Data.Proxy

type NTName     = Symbol
type ProdName   = Symbol
type ChildName  = Symbol


-- El tipo de una gramática:
data {-kind-} Grammar where
  Grammar :: [(NTName, [(ProdName, [(ChildName, Either NT T)])])] -> Grammar

-- ejemplo:
type ExpGrammar
  = 'Grammar '[ '("E", '[ '("Add", '[ '("l", NonTerminal ('NT "E"))
                                    , '("r", NonTerminal ('NT "E"))
                                      ]),
                          '("Val", '[ '("v", Terminal Int)])])]

-- value-level
exprGrammar = Proxy :: Proxy ExpGrammar


{- Variant es el constructor genérico para ASTs

Dada una gramática, un no terminal, y una produccion 
(nt pertenece a gram, prod a nt, eso se puede controlar con constraints)

Se computan los argumentos con la TF |Args|.

Cómo sabemos qué tipo tienen las posiciones recursivas? 
A priori no lo sabemos, para eso generamos variables polimórficas. 
Las variables polimórficas no pueden aparecer en el lado derecho 
de las cláusulas de una TF así que el truco es pasar un argumento 
polimórfico y darle al constraint solver la info que necesita para 
generarlas. Los argumentos (polys a b c d polys') cumplen esa función.
(todo esto es otro "design pattern", btw)
-}

data Variant (g :: Grammar) (e :: NTName) (p :: ProdName) where
  Variant :: forall g e p polys a b c d polys' .
    (polys ~ ( '(a,b) ': '(c,d) ': polys'))
   => HList (Args g e p polys) -> Variant g e p


-- Ok, entonces:
one
  = Variant @ExpGrammar @"E" @"Val" (3 .: ε)
oneplusone
  = Variant @ExpGrammar @"E" @"Add" (one .: one .: ε)
oneplusoneplusone
  = Variant @ExpGrammar @"E" @"Add" (oneplusone .: one .: ε)

--(ε es nil, (.:) es cons)

{- Tipos:
one :: Variant ExpGrammar "E" "Val"
oneplusone, oneplusoneplusone :: Variant ExpGrammar "E" "Add"

Está mal tipado, por ejemplo:

illtyped = Variant @ExpGrammar @"E" @"Add" (oneplusone .: ε)
illtyped = Variant @ExpGrammar @"X" @"Add" ε

(da el error en eps.. pero se puede mejorar esto usando 
Require en el constructor Variant...)
-}



class Sem (g :: Grammar) (e :: NTName) (p :: ProdName) asp ip sp
  where
  sem :: CAspect '[] asp -> Variant g e p
      -> Attribution ip -> Attribution sp

instance SemAux (GetProds g p) g e p asp ip sp (polys :: [(NTName, ProdName)])
   =>  Sem g e p asp ip sp where
   sem asp v
     = semAux (Proxy @(GetProds g p)) (Proxy @polys) asp v

class
  SemAux (prd :: (ProdName, [(ChildName, Either NT T)]))
         (g :: Grammar) (e :: NTName) (p :: ProdName) asp ip sp
         (polys :: [(NTName, ProdName)])
         where
  semAux :: Proxy prd -> Proxy polys -> CAspect '[] asp -> Variant g e p
      -> Attribution ip -> Attribution sp

instance
  (Require (OpLookup PrdReco (GetProd pnam g) asp) c
  ,   ReqR (OpLookup PrdReco (GetProd pnam g) (asp :: [(Prod, Type)]))
    ~ CRule '[] (GetProd pnam g)
      ('[] :: [(Child, [(Att, Type)])]) ip
      ('[] :: [(Child, [(Att, Type)])])
      ('[] :: [(Att, Type)])
      ('[] :: [(Child, [(Att, Type)])]) sp
  , c ~ '[ 'Text (AppendSymbol
                "knit:" (FromEM (ShowTE (GetProd pnam g))))]
  ) =>
  SemAux '(pnam, '[]) g e pnam asp ip sp polys where
  semAux p q (asp :: CAspect '[] asp) (Variant l)
   = (knitAspect (prd (Proxy @g) (Proxy @pnam))
      asp emptyGenRec) :: Attribution ip -> Attribution sp

instance
  (Args g e pnam ('(a, b) : '(c, d) : polys') ~ '[t],
  polys ~ ('(a, b) : '(c, d) : polys'))
  => 
  SemAux '(pnam, '[ '(chnam,'Right ('T t))]) g e pnam asp ip sp
  ('(a, b) : '(c, d) : polys') where
  semAux p (q :: Proxy ('(a, b) : '(c, d) : polys')) asp
   (Variant ((HCons c _)
    :: HList (Args g e pnam ('(a, b) : '(c, d) : polys'))))=
    knitAspect (prd (Proxy @g) (Proxy @pnam)) asp
     (Label @('Chi chnam ('Prd pnam ('NT e)) ('Right ('T t))) .=. sem asp c
     .*. emptyGenRec)

----- burocracia
-- hardcoded para esta gramática, luego lo escribimos mejor
type family Args (g :: Grammar)
                 (e :: NTName)
                 (p :: ProdName)
                 (polys :: [(NTName, ProdName)]) where
  Args ('Grammar '[ '(e, '(p, chi) ': vl )]) e p polys
    = CH2List ('Grammar '[ '(e, '(p, chi) ': vl )]) chi polys
  Args ('Grammar '[ '(e, t ': '(p, chi) ': vl )]) e p polys
    = CH2List ('Grammar '[ '(e, t ': '(p, chi) ': vl )]) chi polys
  Args _ _ _ _ = TypeError (Text "Error!")

type family CH2List (g :: Grammar)
                    (c :: [(ChildName, Either NT T)])
                    (polys :: [(NTName, ProdName)]) :: [Type] where
  CH2List g '[] p = '[]
  CH2List g ( '(_, 'Right ('T t)) ': ts) p
    = t ': CH2List g ts p
  CH2List g ( '(_, 'Left ('NT e)) ': ts) ('(nt, prd) ': p)
    = Variant g nt prd ': CH2List g ts p

-- no las uso, pero eventualmente

type family GetProds (g :: Grammar) (nam :: ProdName)
         :: (ProdName, [(ChildName, Either NT T)]) where
  GetProds ('Grammar '[ '(nt, '(nam, chi) ': prds )]) nam = '(nam, chi)
  GetProds ('Grammar '[ '(nt, '(nam', chi) ': prds )]) nam =
    GetProds ('Grammar '[ '(nt, prds )]) nam 
type family LookupProd (nam :: ProdName)
                       (t :: [(ProdName, [(ChildName, Either NT T)])]) where
   LookupProd nam '[] = 'Nothing
   LookupProd nam ( '(nam, _)  ': ls) = Just nam
   LookupProd nam ( '(_, _)  ': ls) = LookupProd nam ls

type family GetProd (nam :: ProdName) (g :: Grammar) where
  GetProd nam ('Grammar '[ '(nt, l)]) = 'Prd nam ('NT nt)

prd :: Proxy (g :: Grammar) -> Proxy (nam :: ProdName)
    -> Label (GetProd nam g)
prd Proxy Proxy = Label


-- Goal: from chi structure, generate fc

class FC (prd :: (ProdName, [(ChildName, Either NT T)])) l asp where
  type FCR prd :: [(Child, Type)]
  fc :: Proxy prd -> Record (FCR prd)

instance FC '(pname, '[]) l asp where
  type FCR '(pname, '[]) = '[]
  fc _ = emptyGenRec

-- instance FC '(pname, chis) l asp =>
--   FC '(pname, '(chi, 'Left ('NT nt)) ': chis) l asp where
--   type FCR '(pname, '(chi, 'Left ('NT nt)) ': chis)
--     = '(Chi chi ('Prd pname ('NT nt)) ('Left ('NT nt)), Type)
--       ': FCR '(pname, chis)
--   fc p = TagField Label Label undefined
--      `ConsRec` (fc (Proxy @'(pname, chis)) :: Record (FCR '(pname, chis)))

data SBool (b :: Bool) where
  STrue  :: SBool 'True
  SFalse :: SBool 'False


data DT (b :: Bool) where
  DT :: forall b (b' :: Bool) . SBool b' -> SBool b -> DT b 

class Equa (b :: Bool) (b' :: Bool) where
  equ :: DT b -> Bool

instance Equa 'True True where
  equ (DT STrue STrue) = True

type family And (b :: Bool) (b' :: Bool) where
  And True True  = True
  And _ _        = False


data DTE (b :: Bool) where
  DTE :: forall b' b. SBool b -> SBool b' -> SBool (And b b') -> DTE b

--e1 = DTE STrue -- :: (And b b' ~ 'True) => DTE b

class C (b' :: Bool) (a :: Type) where
  c :: DTE b -> a

instance C b' (SBool 'True) where
  c (DTE b b' r) =
   case b of STrue -> case b' of STrue -> r
           -- SFalse -> r, fails
   
