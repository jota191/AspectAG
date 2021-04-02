
\section{Grammar specification}
\label{sec:grammarspecification}

The abstract syntax of our expression language is given by the
following grammar:

<  expr    ->  ival
<  expr    ->  vname
<  expr    ->  expr_l + expr_r

\noindent
where |ival| and |vname| are terminals corresponding to integer values
and variable names, respectively. Both are said to be \emph{children}
in their productions.  In the third production there are two children
|expr_l| and |expr_r|, both occurrences of the non-terminal
|expr|. They have different names (the indexes l and r) so that we can
refer to each one unambiguously.


\subsection{Grammar implementation in AspectAG}

We declare the syntax of the expression language in the {\tt Expr.Syn}
module. As in every Haskell module part of a bigger system we must
declare the module giving it a name, and a list of module imports. In
this case we include the \AspectAG library modules. We also declare a
set of extensions to use (although this could be done in the build
system, we use the module-wise approach).

All this information is given in the following lines of code:

> {-# LANGUAGE TypeFamilies, FlexibleContexts, ScopedTypeVariables,
>              NoMonomorphismRestriction, ImplicitParams, ExtendedDefaultRules,
>              UnicodeSyntax, DataKinds, TypeApplications, PartialTypeSignatures,
>              AllowAmbiguousTypes, RankNTypes, ScopedTypeVariables,
>              TypeSynonymInstances, FlexibleInstances, TemplateHaskell,
>              MultiParamTypeClasses, TypeOperators
> #-}

> module Expr.Syn where

> import Language.Grammars.AspectAG hiding (syndefM)
> import qualified Language.Grammars.AspectAG  as AAG
> import Language.Grammars.AspectAG.TH
> import Data.Map as M
> import GHC.TypeLits

> import Data.Proxy -- ocultar, should be exported by AspectAG


> syndefM att prd def =
>   (traceAspect (mkMsg att prd) $
>    (AAG.syndefM att prd def) .+: emptyAspect) .#.. prd

> mkMsg :: Label ('Att att v) -> Label ('Prd prd nt)
>   -> Proxy (Text att :<>: Text " definition in production ":<>:Text prd)
> mkMsg Label Label = Proxy

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
> ch_Val_val  = Label  @ ('Chi "Val_val"  P_Val (Terminal     Integer))
> ch_Var_var  = Label  @ ('Chi "Var_var"  P_Var (Terminal     [Char]))


> data Expr
>  = Add {l :: Expr, r :: Expr} |
>    Var {var :: String} |
>    Val {val :: Integer}
>     deriving (Show, Eq, Read)



> sem_Expr asp (Add l r)
>  = knitAspect p_Add asp  $    ch_Add_l .=. sem_Expr asp l
>                          .*.  ch_Add_r .=. sem_Expr asp r
>                          .*.  emptyGenRec
> sem_Expr asp (Var var)
>  = knitAspect p_Var asp   $   ch_Var_var .=. sem_Lit var
>                           .*.  emptyGenRec
> sem_Expr asp (Val val)
>  = knitAspect p_Val asp   $   ch_Val_val .=. sem_Lit val
>                           .*.  emptyGenRec


> sem_Expr_Add' asp sl sr =
>  knitAspect p_Add asp $
>  ch_Add_l   .=. sl  .*.
>  ch_Add_r  .=. sr  .*. emptyGenRec

> sem_Expr_Val' asp val =
>   knitAspect p_Val asp $
>   ch_Val_val  .=. sem_Lit @Integer val .*. emptyGenRec

> sem_Expr_Var' asp var =
>   knitAspect p_Var asp $
>   ch_Var_var  .=. sem_Lit @String var .*. emptyGenRec

> sem_Expr_Add asp sl sr =
>  knit Proxy asp $
>  ch_Add_l  .=. sl  .*.
>  ch_Add_r  .=. sr  .*. emptyGenRec

> sem_Expr_Val asp val =
>   knit Proxy asp $
>   ch_Val_val  .=. sem_Lit @Integer val .*. emptyGenRec

> sem_Expr_Var asp var =
>   knit Proxy asp $
>   ch_Var_var  .=. sem_Lit @String var .*. emptyGenRec


> eval  = Label @ ('Att "eval"  Integer)
> env   = Label @ ('Att "env"   Env)


> type Env = M.Map String Integer

> add_eval  =
>   syndefM env p_Add
>     $    (+) @Integer
>     <$>  at ch_Add_l eval
>     <*>  at ch_Add_r eval


> val_eval  =
>   syndefM eval p_Val (ter ch_Val_val)


> var_eval  =
>   syndefM eval p_Var ( -- undefined
>   do -- M.lookup <$> ter ch_Var_var <*> at lhs env
>      env  <- at lhs env
>      x    <- ter ch_Var_var
>      case M.lookup x env of
>        Just e -> return e
>   )



> asp_eval_num =
>     traceAspect (Proxy @ ('Text "definition of eval for numbers")) $
>     val_eval {- .+: var_eval -} .+: emptyAspect

> asp_eval_nonum =
>     traceAspect (Proxy @ ('Text "definition of eval for non numbers")) $
>     add_eval .+: var_eval
>     .+: emptyAspect


> asp_eval = traceAspect (Proxy @ ('Text "combination for eval")) $
>     asp_eval_num .:+: asp_eval_nonum

 > asp_eval = traceAspect (Proxy @ ('Text "combination of rules for eval")) $
 >     val_eval' .+: add_eval .+: val_eval .+: var_eval .+: emptyAspect


> add_env_l =
>   inhdefM env p_Add ch_Add_l (at lhs env)

> add_env_r =
>   inhdefM env p_Add ch_Add_r (at lhs env)

> asp_env = traceAspect (Proxy @('Text "env")) $
>         add_env_l  .+: add_env_r  .+: emptyAspect


> asp_sem = asp_eval .:+: asp_env

> evaluator :: Expr -> Env -> Integer
> evaluator exp envi =
>  sem_Expr asp_sem exp (env =. envi *. emptyAtt) #. eval
