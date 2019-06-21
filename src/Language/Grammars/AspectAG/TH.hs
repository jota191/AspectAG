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
{-# LANGUAGE TemplateHaskell           #-}

module Language.Grammars.AspectAG.TH where

import Language.Haskell.TH
import Data.Proxy
import Data.Either
import GHC.TypeLits
-- import Data.Kind

import Control.Monad

import Language.Grammars.AspectAG


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


-- * Productions
--data Symbol = N String | Te Name

type family Terminal s :: Either NT T where
  Terminal s = 'Right ('T s)

type family NonTerminal s where
  NonTerminal s = 'Left s


data SymTH = Ter Name | NonTer Name

addTest :: String -> SymTH -> Q [Dec]
addTest s sym
  = case sym of
      Ter n -> [d| $(varP (mkName s)) = Label :: Label $(conT n) |]

--addProd :: String -> 


addChi  :: String -- chi name
        -> Name   -- prd
        -> SymTH  -- symbol type
        -> Q [Dec]
addChi chi prd (Ter typ)
  = [d| $(varP (mkName ("ch_" ++chi)))
           = Label :: Label ( 'Chi $(str2Sym chi)
                                   $(conT prd)
                                    (Terminal $(conT typ)))|]
addChi chi prd (NonTer typ)
  = [d| $(varP (mkName ("ch_" ++chi)))
           = Label :: Label ( 'Chi $(str2Sym chi)
                                   $(conT prd)
                                    (NonTerminal $(conT typ)))|]

-- | only prod symbol
addPrd :: String  --name
       -> Name    --nonterm
       -> Q [Dec]
addPrd prd nt = liftM concat . sequence
              $ [addPrdType prd nt, addPrdLabel prd nt]

addPrdLabel prd nt
  = [d| $(varP (mkName ("p_" ++ prd)))
         = Label :: Label ('Prd $(str2Sym prd) $(conT nt))|]

addPrdType prd nt
  = return [TySynD (mkName ("P_"++ prd)) []
            (AppT (AppT (PromotedT 'Prd) (LitT (StrTyLit prd))) (ConT nt))]


-- | Productions

addProd :: String             -- name
        -> Name               -- nt
        -> [(String, SymTH)]  -- chiLst
        -> Q [Dec]
addProd prd nt xs
  = liftM concat . sequence $
  addPrd prd nt : [addChi chi (mkName ("P_" ++ prd)) sym | (chi, sym) <- xs]
