{-# OPTIONS -fcontext-stack=100 #-}
{-# LANGUAGE TemplateHaskell, EmptyDataDecls #-}

module Test where
import qualified Data.Set as S


import Language.Grammars.AspectAG
import Language.Grammars.AspectAG.Derive

import Data.HList.Label4
import Data.HList.TypeEqGeneric1
import Data.HList.TypeCastGeneric1

import Language.Haskell.TH
 
type EList = [Expression]
type MaybeInt = Maybe Int

data Expression
    =   Application { eFn :: Expression, eArgs :: EList }
    |   Atom { eAtom :: String }
    |   Lambda { eFormalArgs :: [String], eBody :: Expression }
    |   Constant { eConst :: MaybeInt } 


$(deriveAG ''Expression)

$(attLabel "cantArgs")

allNT = nt_Expression .*. nt_EList .*. hNil

-- counts the total number of 'eArgs' in an expression
asp_cantArgs () = synAspect cantArgs allNT 
                            ((+)::Int->Int->Int)  (0::Int) ( p_Application .*. p_Atom .*. p_Lambda .*. p_Constant .*. p_EList_Nil .*. 
                                                             p_MaybeInt_Just .*. p_MaybeInt_Nothing .*. hNil ) -- use rule
                            (   p_EList_Cons .=. (def $ do  e  <- at ch_hd_EList_Cons                     
                                                            es <- at ch_tl_EList_Cons
                                                            return $ (e # cantArgs) + 1 + (es # cantArgs) )  -- add 1 for each element of the list
                            .*. emptyRecord )



ex = Application (Lambda ["x","y"] (Atom "x")) [Constant Nothing, Application (Atom "y") [Constant $ Just 3] ]


main = sem_Expression (asp_cantArgs ()) ex emptyRecord # cantArgs    

