\subsection{Rules}

Rules are actually functions from an input family to an output family

\todo{\lipsum}


> data  {- kind -}  Att    = Att Symbol Type
> data  {- kind -}  Prod   = Prd Symbol NT
> data  {- kind -}  Child  = Chi Symbol Prod (Either NT T)
> data  {- kind -}  NT     = NT Symbol
> data  {- kind -}  T      = T Type


\todo{\lipsum}

> data Fam  (prd  ::  Prod)
>           (c    ::  [(Child, [(Att, Type)])])
>           (p    ::  [(Att, Type)])  :: Type
>  where
>   Fam  ::  ChAttsRec prd c -> Attribution p
>        ->  Fam prd c p

> type Rule
>   (prd  :: Prod)
>   (sc   :: [(Child, [(Att, Type)])])
>   (ip   :: [(Att,       Type)])
>   (ic   :: [(Child, [(Att, Type)])])
>   (sp   :: [(Att,       Type)])
>   (ic'  :: [(Child, [(Att, Type)])])
>   (sp'  :: [(Att,       Type)])
>   =   Fam prd sc ip
>   ->  Fam prd ic sp -> Fam prd ic' sp'

\todo{\lipsum}

> newtype CRule (ctx :: [ErrorMessage]) prd sc ip ic sp ic' sp'
>  = CRule { mkRule :: (Proxy ctx -> Rule prd sc ip ic sp ic' sp')}

\subsection{Defining Attributes}

The function |syndef| takes an attribute name |att| and a production
|prd|

> syndef
>   :: (   RequireEq t t' ctx'
>      ,   RequireR (OpExtend AttReco ('Att att t) t sp) ctx (Attribution sp')
>      ,   ctx'  ~     ((Text "syndef("
>                :<>:  ShowT ('Att att t) :<>: Text ", "
>                :<>:  ShowT prd :<>: Text ")") ': ctx))
>      =>  Label ('Att att t)
>      ->  Label prd
>      ->  (Proxy ctx' -> Fam prd sc ip -> t')
>      ->  CRule ctx prd sc ip ic sp ic sp'
> syndef att prd f
>   =  CRule $ \ctx inp (Fam ic sp)
>      ->  Fam ic $ req ctx (OpExtend att (f Proxy inp) sp)

In practice it is useful to use a monadic version of |syndef|

> syndefM att prd = syndef att prd . def

where

> def :: Reader (Proxy ctx, Fam prd chi par) a
>     -> (Proxy ctx -> (Fam prd chi par) -> a)
> def = curry . runReader









> newtype CAspect (ctx :: [ErrorMessage]) (asp :: [(Prod, Type)] )
>   = CAspect { mkAspect :: Proxy ctx -> Aspect asp}
