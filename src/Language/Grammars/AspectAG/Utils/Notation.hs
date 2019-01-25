
{-|
Module      : Language.Grammars.AspectAG.Utils.Notation
Description : some syntactic sugar
Copyright   : (c) Juan García Garland, 2018 
License     : LGPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX

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
             UnicodeSyntax
#-}


module Language.Grammars.AspectAG.Utils.Notation where

import Language.Grammars.AspectAG.Utils.HList
import Language.Grammars.AspectAG.Utils.Attribution
import Language.Grammars.AspectAG.Utils.Record
import Language.Grammars.AspectAG.Utils.Attribute
import Data.Kind
import Data.Tagged hiding (unTagged)
import Language.Grammars.AspectAG.Utils.TPrelude
import Data.Proxy
import Language.Grammars.AspectAG.Utils.ChildAtts
import Language.Grammars.AspectAG.Utils.TagUtils
import GHC.TypeLits




-- | * Classes that are interfaces to extensible records.

-- | Note that all operators can be implemented on the same class,
--  but this is painful since some operators are agnostic
--  to most parameters. To avoid this I prefer
--  (at least in this iteration of development) this implementation


-- | a class for all record types, to unify syntax of getters/setters
class RecLookup
      (l :: k)                   --  The labels
      (r :: [ (k, k') ])         --  The record andd its kind
      (wl:: k -> Type)           --  the proxy for labels 
      (c :: [ (k, k') ] -> Type) --  The wrapper used to construct
                                 --   inhabited Types
      v                          --  The type of the values
      | l r wl c -> v
      where (#) :: c r -> wl l -> v
            
instance (LookupByLabelRec l r ~ v, HasFieldRec l r)
  => RecLookup l r Label Record v where
  (#) = (.#.)

instance (HasFieldAtt l r v)
  => RecLookup l r Label Attribution v where
  (#) = (#.)

instance (HasChild l r v)
  => RecLookup l r Label ChAttsRec (Attribution v) where
  (#) = (.#)

infixl #


  -- tests

data Lbl = L1 | L2

-- r1 = (Label :: Label L1) .=. True .*. emptyRecord
