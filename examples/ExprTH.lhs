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


> module Expr where

> import Language.Grammars.AspectAG
> import Language.Grammars.AspectAG.TH
> import Data.Maybe

> $(addNont "Expr")

> $(addProd "Val" ''Nt_Expr
>   [  ("val", Ter ''Int)])

> $(addProd "Add" ''Nt_Expr
>   [  ("leftAdd",   NonTer ''Nt_Expr),
>      ("rightAdd",  NonTer ''Nt_Expr)])

> $(addProd "Var" ''Nt_Expr
>   [  ("var", Ter ''String)])
> $(closeNTs [''Nt_Expr])
> $(mkSemFunc ''Nt_Expr)

> type Env = [(String, Int)]

> $(attLabels [("eval", ''Int), ("env", ''Env)])

> eval_add = syn eval p_Add (do l <- at ch_leftAdd eval
>                               r <- at ch_rightAdd eval
>                               return (l + r))
> eval_val = syn eval p_Val (ter ch_val)
> eval_var = syn eval p_Var (do e <- at lhs env
>                               x <- ter ch_var
>                               return (fromJust $ lookup x e))

> asp_eval = eval_add .+: eval_val .+: eval_var .+: emptyAspect

> env_add_l = inh env p_Add ch_leftAdd (at lhs env)
> env_add_r = inh env p_Add ch_rightAdd (at lhs env)

> asp_all = env_add_l .+: env_add_r .+: asp_eval

> evalExpr exp envi = sem_Expr asp_all exp  (env =. envi *. emptyAtt) #. eval
