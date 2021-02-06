{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

module RecTest where

import Language.Grammars.AspectAG
import Language.Grammars.AspectAG.Require
import Language.Grammars.AspectAG.GenRecord
import Language.Grammars.AspectAG.TPrelude
import GHC.TypeLits
import Data.Proxy
import Data.Kind

-- import Language.Grammars.AspectAG.Label

l1  = Label @ "l1"
l2  = Label @ "l2"
l3  = Label @ "l3"
l4  = Label @ "l4"
l5  = Label @ "l5"
l6  = Label @ "l6"
l7  = Label @ "l7"
l8  = Label @ "l8"
l9  = Label @ "l9"
l10 = Label @ "l10"
l11 = Label @ "l11"
l12 = Label @ "l12"
l13 = Label @ "l13"
l14 = Label @ "l14"
l15 = Label @ "l15"
l16 = Label @ "l16"
l17 = Label @ "l17"
l18 = Label @ "l18"
l19 = Label @ "l19"
l20 = Label @ "l20"
l21 = Label @ "l21"
l22  = Label @ "l22"
l23  = Label @ "l23"
l24  = Label @ "l24"
l25  = Label @ "l25"
l26  = Label @ "l26"
l27  = Label @ "l27"
l28  = Label @ "l28"
l29  = Label @ "l29"
l30 = Label @ "l30"
l31 = Label @ "l31"
l32 = Label @ "l32"
l33 = Label @ "l33"
l34 = Label @ "l34"
l35 = Label @ "l35"
l36 = Label @ "l36"
l37 = Label @ "l37"
l38 = Label @ "l38"
l39 = Label @ "l39"
l40 = Label @ "l40"
l41 = Label @ "l41"
l42 = Label @ "l42"
l43 = Label @ "l43"
l44 = Label @ "l44"
l45 = Label @ "l45"
l46 = Label @ "l46"
l47 = Label @ "l47"
l48 = Label @ "l48"
l49 = Label @ "l49"

-- reco =
--   l1  .=. True .*.
--   l2  .=. True .*.
--   l3  .=. True .*.
--   l4  .=. True .*.
--   l5  .=. True .*.
--   l6  .=. True .*.
--   l7  .=. True .*.
--   l8  .=. True .*.
--   l9  .=. True .*.
--   l10 .=. True .*.
--   l11 .=. True .*.
--   l12 .=. True .*.
--   l13 .=. True .*.
--   l14 .=. True .*.
--   l15 .=. True .*.
--   l15 .=. True .*.
--   emptyRecord


--infixr 2 .**. 
--(TagField l1 l2 v :: TagField c l v) .**. r
--  = req (Proxy :: Proxy ( '[ 'Text ""] )) (OpExtend @l @c @v l2 v r)

infixr 2 .**.
(.**.) :: (Require (OpExtend' (And (NewLabel l r) (LabelSetF r)) c l v r)
                   '[ 'Text ""],
                 WrapField c v ~ v) =>
                Tagged l v -> Rec c r -> ReqR (OpExtend c l v r)
(Tagged v :: Tagged l v) .**. r
  = req (Proxy :: Proxy ( '[ 'Text ""] )) (OpExtend @_ @_ @v (Label @l) v r)


reco1 =
  l1  .=. True .**.
  l2  .=. True .**.
  l3  .=. True .**.
  l4  .=. True .**.
  l5  .=. True .**.
  l6  .=. True .**.
  l7  .=. True .**.
  l8  .=. True .**.
  l9  .=. True .**.
  l10 .=. True .**.
  l11 .=. True .**.
  l12 .=. True .**.
  l13 .=. True .**.
  l14 .=. True .**.
  l35  .=. True .**.
  l16  .=. True .**.
  l17  .=. True .**.
  l18 .=. True .**.
  l19  .=. True .**.
  l20  .=. True .**.
  l21  .=. True .**.
  l22  .=. True .**.
  l23  .=. True .**.
  l24 .=. True .**.
  l25  .=. True .**.
  l26  .=. True .**.
  l27  .=. True .**.
  l28 .=. True .**.
  l29  .=. True .**.
  l30  .=. True .**.
  l31  .=. True .**.
  l32  .=. True .**.
  l33  .=. True .**.
  l34  .=. True .**.
  l38  .=. True .**.
  l36  .=. True .**.
  l37  .=. True .**.
  l39  .=. True .**.
  l40  .=. True .**.
  l41  .=. True .**.
  (l15 .=. True .**.
   emptyRecord :: Rec Reco ('[ '("l15", Bool)] ))
