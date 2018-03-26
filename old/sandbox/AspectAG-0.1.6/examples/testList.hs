{-# LANGUAGE TemplateHaskell, EmptyDataDecls #-}

module Test where
import qualified Data.Set as S


import Data.AspectAG
import Data.AspectAG.Derive

import Data.HList.Label4
import Data.HList.TypeEqGeneric1
import Data.HList.TypeCastGeneric1

import Language.Haskell.TH
 
$(typeList "EList" "Expression")

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
                            ((+)::Int->Int->Int)  (0::Int) ( p_Application .*. p_Atom .*. p_Lambda .*. p_Constant .*. p_NilEList .*. hNil ) -- use rule
                            (   p_ConsEList .=. (def $ do  e  <- at ch_hdEList                     
                                                           es <- at ch_tlEList
                                                           return $ (e # cantArgs) + 1 + (es # cantArgs) )  -- add 1 for each element of the list
                            .*. emptyRecord )



ex = Application (Lambda ["x","y"] (Atom "x")) (ConsEList (Constant 2) $ ConsEList (Constant 5) NilEList)


main = sem_Expression (asp_cantArgs ()) ex emptyRecord # cantArgs    

