{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell, CPP, DataKinds, KindSignatures, FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}

module Language.Grammars.AspectAG.TH where

import Language.Haskell.TH

import Data.List
import Data.Set (Set)
import Data.List (isPrefixOf, isSuffixOf, sort)
import qualified Data.Set as S
import Data.Proxy

import Language.Grammars.AspectAG
import Control.Monad

-- * Attribute labels

-- | makes a type level lit (Symbol) from a String
str2Sym s = litT$ strTyLit s


-- | TH function to define a typed attribute label given a name
-- and a quoted type
attLabel :: String -> Name -> DecsQ
attLabel s t
  = [d| $(varP (mkName s)) = Label :: Label ( 'Att $(str2Sym s)
                                            $(conT t)) |]

-- | for completness, to have a name as the next one
attMono = attLabel

-- | TH function to define a polymorphic attribute
attPoly :: String -> DecsQ
attPoly s
    = [d| $(varP (mkName s)) = Label :: forall a . Label ( 'Att $(str2Sym s) a) |]

-- | multiple monomorphic attributes at once
attLabels :: [(String,Name)] -> Q [Dec]
attLabels xs = liftM concat . sequence $ [attLabel att ty | (att,ty) <- xs ]

-- * Non terminals

-- | add a non terminal symbol
addNont :: String -> Q [Dec]
addNont s
  = liftM concat . sequence $ [addNTLabel s, addNTType s]

addNTLabel :: String -> Q [Dec]
addNTLabel s
  = [d| $(varP (mkName ("nt_" ++ s))) = Label :: Label ('NT $(str2Sym s)) |]

addNTType :: String -> Q [Dec]
addNTType s
  = return [TySynD (mkName ("Nt_"++ s)) [] (AppT (PromotedT 'NT) (LitT (StrTyLit s)))]

