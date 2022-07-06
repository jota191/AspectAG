{-|
Module      : Language.Grammars.AspectAG
Description : Main module, First-class attribute grammars
Copyright   : (c) Juan García-Garland, Marcos Viera, 2019, 2020
License     : GPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX
-}

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
{-# LANGUAGE TemplateHaskell           #-}

module Language.Grammars.AspectAG.THGen where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Data.Proxy
import GHC.TypeLits

import Language.Grammars.AspectAG
import Language.Grammars.AspectAG.TH

-- mkMsgPos :: Label ('Att att v) -> Label ('Prd prd nt) -> Proxy pos
--   -> Proxy (Text att :<>: Text " definition in production "
--             :<>:Text prd :<>: Text pos)
-- mkMsgPos Label Label Proxy = Proxy

-- synLoc att prd def =
--   let loc = $(proxyLoc) in
--   traceRule (mkMsgPos att prd (seq loc loc)) $
--    syndefM att prd def
