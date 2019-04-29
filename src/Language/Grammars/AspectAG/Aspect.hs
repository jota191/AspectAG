
{-|
Module      : Language.Grammars.AspectAG.Aspect
Description : tagged rules
Copyright   : (c) Juan García Garland, 2019
License     : GPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX

Yet another specialized record.
-}
{-# LANGUAGE DataKinds,
             TypeOperators,
             PolyKinds,
             GADTs,
             TypeInType,
             RankNTypes,
             StandaloneDeriving,
             FlexibleInstances,
             FlexibleContexts,
             ConstraintKinds,
             MultiParamTypeClasses,
             FunctionalDependencies,
             UndecidableInstances,
             ScopedTypeVariables,
             TypeFamilies,
             PatternSynonyms
#-}

module Language.Grammars.AspectAG.Aspect where

import Data.Kind 
import Data.Type.Equality
import Data.Proxy
import Language.Grammars.AspectAG.TPrelude
import Language.Grammars.AspectAG.TagUtils
import Language.Grammars.AspectAG.GenRecord
import GHC.TypeLits



