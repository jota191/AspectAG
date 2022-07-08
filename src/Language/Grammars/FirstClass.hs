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
import GHC.Exts
import Unsafe.Coerce

import Data.Kind (Type, Constraint)
import GHC.TypeLits (Symbol)
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
-}

class Sem (g :: Grammar) (e :: NTName) (p :: ProdName)
          (polys :: [(NTName, ProdName)])
  where
  sem :: CAspect '[] asp -> Variant g e p
      -> Attribution ip -> Attribution sp

instance SemAux (GetProds g p) g e p ('(a, b) : '(c, d) : polys)
  =>  Sem g e p ('(a, b) : '(c, d) : polys) where
  sem asp (Variant (l :: HList (Args g e p ('(a, b) : '(c, d) : polys))))
    = semAux asp (l :: HList (Args g e p (('(a, b) : '(c, d) : polys))))

class
  SemAux (prd :: (ProdName, [(ChildName, Either NT T)]))
         (g :: Grammar) (e :: NTName) (p :: ProdName)
         (polys :: [(NTName, ProdName)]) where
  semAux :: CAspect '[] asp -> HList (Args g e p polys)
      -> Attribution ip -> Attribution sp

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

