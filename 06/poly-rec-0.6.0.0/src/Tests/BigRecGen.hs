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
             InstanceSigs,
             AllowAmbiguousTypes,
             TypeApplications,
             PatternSynonyms,
             TemplateHaskell
#-}


module Tests.BigRecGen where
import Data.GenRec
import Data.GenRec.RecInstances.Record


import Language.Haskell.TH

r0 = emptyRecord

recN :: Int -> DecsQ


recAux 0 = [e| emptyRecord :: Record '[] |]
--recAux n = [e| $(varE $ mkName $ "r" ++ show (n-1))|]
recAux n = [e| Label @ $(litT $ strTyLit (show n)) .=. (3 ::Int) .*. $(recAux (n-1))|]

recN n =
  [d| $(varP (mkName ("r"  ++ show n))) = $(recAux n)|]
