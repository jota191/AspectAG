{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE
             TypeFamilies,
             FlexibleContexts,
             ScopedTypeVariables,
             NoMonomorphismRestriction,
             ImplicitParams,
             ExtendedDefaultRules,
             UnicodeSyntax,
             DataKinds,
             TypeApplications,
             PartialTypeSignatures,
             AllowAmbiguousTypes,
             RankNTypes
#-}


module List where

import Prelude hiding (head, tail, sum, all)

import Language.Grammars.AspectAG
import Control.Monad
import Control.Applicative
import Data.Proxy
import GHC.TypeLits
import Data.Map
import Data.Maybe
import Debug.Trace

type Nt_List = 'NT "List"
list = Label @ Nt_List

type P_Cons = 'Prd "Cons" Nt_List
cons = Label @ P_Cons


type P_Nil = 'Prd "Nil" Nt_List
nil = Label @ P_Nil

head :: forall a . Label ('Chi "head" P_Cons ('Right ('T a)))
head   = Label

tail   = Label @ ('Chi "tail"   P_Cons ('Left Nt_List))
nilCh :: Label ('Chi "nilCh"  P_Nil  ('Right ('T ())))
nilCh = Label


  -- data List a = Cons a (List a) | Nil () deriving Show

sem_List (proxy :: Proxy a) asp (x:xs)
  = knitAspect cons asp
  $    head @ a .=. sem_Lit @ a x
 .*.   tail  .=. sem_List proxy asp xs
 .*.   EmptyRec
sem_List (_ :: Proxy a) asp []
  = knitAspect nil asp
  $ nilCh  .=. sem_Lit () .*. EmptyRec

cata :: forall b . Label ('Att "cata" b)
cata = Label

asp_cata (Proxy :: Proxy a) f e
  =   (syndefM (cata @ a) cons $ f <$> ter head <*> at tail (cata @ a))
  .+: (syndefM (cata @ a) nil $ pure e)
  .+: emptyAspect

sum :: [Integer] -> Integer
sum xs = sem_List (Proxy @ Integer) (asp_cata (Proxy @ Integer) (+) 0) xs emptyAtt #. (cata @ Integer)

all xs = sem_List (Proxy @ Bool) (asp_cata (Proxy @ Bool) (&&) True) xs emptyAtt #. (cata @ Bool)


catamorphism :: (a -> b -> b) -> b -> [a] -> b
catamorphism (f :: a -> b -> b) e xs
  = sem_List (Proxy @ a) (asp_cata (Proxy @ b) f e) xs emptyAtt #. (cata @ b)


tyApp :: (forall a. Label ('Att "cata" a)) -> Proxy a -> (Label ('Att "cata" a))
tyApp poly (Proxy :: Proxy a) = poly @ a
