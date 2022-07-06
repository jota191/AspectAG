> {-# LANGUAGE TypeFamilies, FlexibleContexts, ScopedTypeVariables,
>              NoMonomorphismRestriction, ImplicitParams, ExtendedDefaultRules,
>              UnicodeSyntax, DataKinds, TypeApplications, PartialTypeSignatures,
>              AllowAmbiguousTypes, RankNTypes, ScopedTypeVariables,
>              TypeSynonymInstances, FlexibleInstances, TemplateHaskell,
>              MultiParamTypeClasses, TypeOperators
> #-}

> module Expr.Syn where

> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH
> import Data.Map as M
> import GHC.TypeLits

> import Data.Proxy


> type Nt_Expr = 'NT "Expr"
> nt_Expr = Label @ Nt_Expr



> type P_Val  = 'Prd "Val" Nt_Expr
> p_Val       = Label @ P_Val
> type P_Var  = 'Prd "Var" Nt_Expr
> p_Var       = Label @ P_Var
> type P_Add  = 'Prd "Add" Nt_Expr
> p_Add       = Label @ P_Add


> ch_Add_l    = Label  @ ('Chi "Add_l"    P_Add (NonTerminal  Nt_Expr))

> ch_Add_r    = Label  @ ('Chi "Add_r"    P_Add (NonTerminal  Nt_Expr))

> ch_Val_val  :: forall v. Label ('Chi "Val_val"  P_Val (Terminal v))
> ch_Val_val  = Label

> ch_Var_var  = Label  @ ('Chi "Var_var"  P_Var (Terminal     [Char]))


> data Expr v = Val v | Var String | Add (Expr v)(Expr v)

> sem_Expr asp (Val (v :: v))
>  =  knitAspect p_Val asp
>  $  ch_Val_val @v .=. sem_Lit v .*. emptyGenRec

 > sem_Expr asp (Var (v :: v))
 >  =  knitAspect p_Var asp
 >  $  ch_Var_var .=. sem_Lit v .*. emptyGenRec

> sem_Expr asp (Add l r)
>  =  knitAspect p_Add asp
>  $    ch_Add_l .=. sem_Expr asp l
>  .*.  ch_Add_r .=. sem_Expr asp r
>  .*.  emptyGenRec

> evalP :: forall v. Label ('Att "evalP" v); evalP = Label

> evalP_add = \(Proxy :: Proxy v) ->
>   syn (evalP) p_Add (add   <$> at ch_Add_l (evalP)
>                            <*> at ch_Add_r (evalP)) 

> evalP_val = \(Proxy :: Proxy v) ->
>   syn (evalP) p_Val
>    (ter (ch_Val_val))

 > evalP_var = \(Proxy :: Proxy v) ->
 >   syn (evalP @v) p_Var (pure (1 :: Integer))

> asp_evalP = \p -> evalP_add p -- .+:  evalP_var p
>          .+:  evalP_val p
>          .+: emptyAspect

> evaluator (e :: Expr v)
>   = sem_Expr (asp_evalP (Proxy @v)) e emptyAtt
>     #. evalP @v


> class Add v where add :: v -> v -> v
