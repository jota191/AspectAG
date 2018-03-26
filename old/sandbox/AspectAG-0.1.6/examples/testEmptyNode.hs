{-# LANGUAGE TemplateHaskell, EmptyDataDecls #-}

module Test where


import Data.AspectAG
import Data.AspectAG.Derive

import Data.HList.Label4
import Data.HList.TypeEqGeneric1
import Data.HList.TypeCastGeneric1

 
data EList = ECons {e :: Expression, es :: EList} | ENil


data Expression
    =   Application { eFn :: Expression, eArgs :: EList }
    |   Atom { eAtom :: String }
    |   Lambda { eFormalArgs :: [String], eBody :: Expression }
    |   Constant { eConst :: Int }

 
$(deriveAG ''Expression)

$(attLabel "cantArgs")

allNT = nt_Expression .*. nt_EList .*. hNil

-- counts the total number of 'eArgs' in an expression
asp_cantArgs () = synAspect cantArgs allNT 
                            ((+)::Int->Int->Int)  (0::Int) ( p_Application .*. p_Atom .*. p_Lambda .*. p_Constant .*. p_ENil .*. hNil ) -- use rule
                            (   p_ECons .=. (def $ do  e  <- at ch_e                     
                                                       es <- at ch_es
                                                       return $ (e # cantArgs) + 1 + (es # cantArgs) )  -- add 1 for each element of the list
                            .*. emptyRecord )


ex = Application (Lambda ["x","y"] (Atom "x")) (ECons (Constant 2) $ ECons (Constant 5) ENil)

main = sem_Expression (asp_cantArgs ()) ex emptyRecord # cantArgs    

