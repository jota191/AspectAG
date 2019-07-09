> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE ScopedTypeVariables #-}

> {-# LANGUAGE TemplateHaskell #-}
> {-# LANGUAGE FlexibleContexts  #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE TypeFamilies #-}

> {-# LANGUAGE AllowAmbiguousTypes #-}
> {-# LANGUAGE NoMonomorphismRestriction #-}
> {-# LANGUAGE DataKinds #-}

> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE TypeApplications #-}


> module Hoas where

> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH

> import Data.Proxy
> import Language.Grammars.AspectAG.Require

This module tests AspectAG to encode semantics of a GADT,
representing a grammar using higher order abstract syntax.

From WYAH:

> data Expr a where
>  Lift :: a                       -> Expr a
>  Tup  :: Expr a -> Expr b        -> Expr (a, b)
>  Lam  :: (Expr a -> Expr b)      -> Expr (a -> b)
>  App  :: Expr (a -> b) -> Expr a -> Expr b
>  Fix  :: Expr (a -> a)           -> Expr a

> type Nt_Expr = 'NT "Expr"
> nt_Expr = Label @ Nt_Expr

> type P_Lift = 'Prd "Lift" Nt_Expr
> p_Lift = Label @ P_Lift

> ch_unLift :: forall a . Label ('Chi "unLift" P_Lift ('Right ('T a)))
> ch_unLift = Label

> type P_Tup = 'Prd "Tup" Nt_Expr
> p_Tup = Label @ P_Tup

> ch_fst :: forall a . Label ('Chi "fst" P_Tup ('Left Nt_Expr))
> ch_fst = Label

> ch_snd :: forall a . Label ('Chi "snd" P_Tup ('Left Nt_Expr))
> ch_snd = Label

-- > sem_Expr asp (Lift a :: Expr a)
-- >   =  knitAspect p_Lift asp
-- >   $  ch_unLift @ a .=. sem_Lit @ a a
-- >  .*. EmptyRec
-- > sem_Expr asp ((Tup a b) :: Expr (a, b))
-- >   =  knitAspect p_Tup asp
-- >   $  ch_fst @ a .=. sem_Expr asp a
-- >   $  ch_snd @ b .=. sem_Expr asp b
-- >  .*. EmptyRec

-- > sem_Expr asp (Proxy :: Proxy a)(Lift a :: Expr a)
-- >   =  knitAspect p_Lift asp
-- >   $  ch_unLift @ a .=. sem_Lit @ a a
-- >  .*. EmptyRec
-- > sem_Expr asp (Proxy :: Proxy (a,b)) ((Tup a b) :: Expr (a, b))
-- >   =  knitAspect p_Tup asp
-- >   $  ch_fst @ a .=. sem_Expr proxy asp a
-- >   $  ch_snd @ b .=. sem_Expr proxy asp b
-- >  .*. EmptyRec


-- > foo (Lift a) = show a
-- > foo (Tup a b) = foo a ++ foo b

> class Sem_Expr a where
>   sem_Expr :: CAspect '[] r -> Expr a -> Attribution ip -> Attribution sp

> instance
>   (Language.Grammars.AspectAG.Require.ReqR (OpLookup PrdReco P_Lift r) ~
>   CRule '[]
>               P_Lift
>               '[ '( 'Chi "unLift" P_Lift ('Right ('T a)), '[ '( 'Att "term" a, a)])]
>               ip
>              '[ '( 'Chi "unLift" P_Lift ('Right ('T a)), '[])]
>              '[]
>              '[ '( 'Chi "unLift" P_Lift ('Right ('T a)), '[])]
>               sp)
>   => Sem_Expr a where
>   sem_Expr asp (Lift a)
>     = knitAspect p_Lift asp
>     $  ch_unLift @ a .=. sem_Lit @ a a
>     .*. EmptyRec
