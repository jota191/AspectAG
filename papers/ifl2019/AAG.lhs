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

> chi :: Fam prd c p -> ChAttsRec prd c
> chi (Fam c p) = c

> par :: Fam prd c p -> Attribution p
> par (Fam c p) = p


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


> type family IC (rule :: Type) where
>   IC (Rule prd sc ip ic sp ic' sp') = ic
>   IC (CRule ctx prd sc ip ic sp ic' sp') = ic
> type family SP (rule :: Type) where
>   SP (Rule prd sc ip ic sp ic' sp') = sp
>   SP (CRule ctx prd sc ip ic sp ic' sp') = sp



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



> inhdef
>   :: ( RequireEq t t' ctx'
>      , RequireR  (OpExtend AttReco ('Att att t) t r) ctx (Attribution v2)
>      , RequireR (OpUpdate (ChiReco ('Prd prd nt))
>                 ('Chi chi ('Prd prd nt) ntch) v2 ic) ctx
>                 (ChAttsRec ('Prd prd nt) ic')
>      , RequireR (OpLookup (ChiReco ('Prd prd nt))
>                 ('Chi chi ('Prd prd nt) ntch) ic) ctx
>                 (Attribution r)
>      , ntch ~ 'Left n
>      , ctx' ~ ((Text "inhdef("
>                 :<>: ShowT ('Att att t)  :<>: Text ", "
>                 :<>: ShowT ('Prd prd nt) :<>: Text ", "
>                 :<>: ShowT ('Chi chi ('Prd prd nt) ntch) :<>: Text ")")
>                 ': ctx))
>      =>
>      Label ('Att att t)
>      -> Label ('Prd prd nt)
>      -> Label ('Chi chi ('Prd prd nt) ntch)
>      -> (Proxy ctx' -> Fam ('Prd prd nt) sc ip -> t')
>      -> CRule ctx ('Prd prd nt) sc ip ic sp ic' sp
> inhdef  att prd chi f
>   = CRule $ \ctx inp (Fam ic sp)
>        -> let ic'   = req ctx (OpUpdate chi catts' ic)
>               catts = req ctx (OpLookup chi ic)
>               catts'= req ctx (OpExtend  att (f Proxy inp) catts)
>           in  Fam ic' sp

> inhdefM att prd chi = inhdef att prd chi . def



\subsection{Combining rules}

> ext' ::  CRule ctx prd sc ip ic sp ic' sp'
>      ->  CRule ctx prd sc ip a b ic sp
>      ->  CRule ctx prd sc ip a b ic' sp'
> (CRule f) `ext'` (CRule g)
>  = CRule $ \ctx input -> f ctx input . g ctx input

> ext ::  RequireEq prd prd' (Text "ext":ctx)
>      => CRule ctx prd sc ip ic sp ic' sp'
>      -> CRule ctx prd' sc ip a b ic sp
>      -> CRule ctx prd sc ip a b ic' sp'
> ext = ext'

> infixr 6 .+.
> (.+.) = ext



\subsection{Aspects}

> newtype CAspect (ctx :: [ErrorMessage]) (asp :: [(Prod, Type)] )
>   = CAspect { mkAspect :: Proxy ctx -> Aspect asp}


> emptyAspect :: CAspect ctx '[]
> emptyAspect  = CAspect $ const EmptyRec

> comAspect ::
>  ( Require (OpComAsp al ar) ctx
>  , ReqR (OpComAsp al ar) ~ Aspect asp)
>  =>  CAspect ctx al -> CAspect ctx ar -> CAspect ctx asp
> comAspect al ar
>   = CAspect $ \ctx -> req ctx (OpComAsp (mkAspect al ctx) (mkAspect ar ctx))


> traceAspect (_ :: Proxy (e::ErrorMessage))
>   = mapCAspect $ \(_ :: Proxy ctx) -> Proxy @ ((Text "aspect ":<>: e) : ctx)

> traceRule (_ :: Proxy (e::ErrorMessage))
>   = mapCRule $ \(_ :: Proxy ctx) -> Proxy @ ((Text "rule ":<>: e) : ctx)


> mapCRule :: (Proxy ctx -> Proxy ctx')
>           -> CRule ctx' prd sc ip ic sp ic' sp'
>           -> CRule ctx  prd sc ip ic sp ic' sp'
> mapCRule fctx (CRule frule) = CRule $ frule . fctx

> mapCAspect fctx (CAspect fasp) = CAspect $ 
>        mapCtxRec fctx . fasp . fctx

> class MapCtxAsp (r :: [(Prod,Type)]) (ctx :: [ErrorMessage])
>                                      (ctx' :: [ErrorMessage])  where
>   type ResMapCtx r ctx ctx' :: [(Prod,Type)]
>   mapCtxRec :: (Proxy ctx -> Proxy ctx')
>             -> Aspect r -> Aspect (ResMapCtx r ctx ctx')

> instance ( MapCtxAsp r ctx ctx' 
>          , ResMapCtx r ctx ctx' ~ r'
>          , LabelSetF ('(l, CRule ctx prd sc ip ic sp ic' sp') : r')
>          ~ True) =>
>   MapCtxAsp ( '(l, CRule ctx' prd sc ip ic sp ic' sp') ': r) ctx ctx' where
>   type ResMapCtx ( '(l, CRule ctx' prd sc ip ic sp ic' sp') ': r) ctx ctx'
>      =  '(l, CRule ctx prd sc ip ic sp ic' sp') ':  ResMapCtx r ctx ctx'
>   mapCtxRec fctx (ConsRec (TagField c l r) rs) = (ConsRec (TagField c l
>                                                             (mapCRule fctx r))
>                                                           (mapCtxRec fctx rs))

> instance MapCtxAsp ('[] :: [(Prod,Type)]) ctx ctx' where
>   type ResMapCtx ('[] :: [(Prod,Type)]) ctx ctx'
>      =  '[]
>   mapCtxRec _ EmptyRec = EmptyRec

> extAspect
>   :: RequireR (OpComRA ctx prd sc ip ic sp ic' sp' a) ctx (Aspect asp)
>   => CRule ctx prd sc ip ic sp ic' sp'
>      -> CAspect ctx a -> CAspect ctx asp
> extAspect rule (CAspect fasp)
>   = CAspect $ \ctx -> req ctx (OpComRA rule (fasp ctx))

> (.+:) = extAspect
> infixr 3 .+:

> (.:+:) = comAspect
> infixr 4 .:+:

> data OpComAsp  (al :: [(Prod, Type)])
>                (ar :: [(Prod, Type)]) where
>   OpComAsp :: Aspect al -> Aspect ar -> OpComAsp al ar

> instance Require (OpComAsp al '[]) ctx where
>   type ReqR (OpComAsp al '[]) = Aspect al
>   req ctx (OpComAsp al _) = al

> instance
>   ( RequireR (OpComAsp al ar) ctx  (Aspect ar')
>   , Require  (OpComRA ctx prd sc ip ic sp ic' sp' ar') ctx
>   )
>   => Require (OpComAsp al
>        ( '(prd, CRule ctx prd sc ip ic sp ic' sp') ': ar)) ctx where
>   type ReqR (OpComAsp al
>        ( '(prd, CRule ctx prd sc ip ic sp ic' sp') ': ar))
>     = ReqR (OpComRA ctx prd sc ip ic sp ic' sp'
>             (UnWrap (ReqR (OpComAsp al ar))))
>   req ctx (OpComAsp al (ConsRec prdrule ar))
>    = req ctx (OpComRA (untagField prdrule)
>                       (req ctx (OpComAsp al ar)))


> data OpComRA  (ctx  :: [ErrorMessage])
>               (prd  :: Prod)
>               (sc   :: [(Child, [(Att, Type)])])
>               (ip   :: [(Att, Type)])
>               (ic   :: [(Child, [(Att, Type)])])
>               (sp   :: [(Att, Type)])
>               (ic'  :: [(Child, [(Att, Type)])])
>               (sp'  :: [(Att, Type)])
>               (a     :: [(Prod, Type)])  where
>   OpComRA :: CRule ctx prd sc ip ic sp ic' sp'
>           -> Aspect a -> OpComRA ctx prd sc ip ic sp ic' sp' a

> data OpComRA' (b :: Bool)
>               (ctx  :: [ErrorMessage])
>               (prd  :: Prod)
>               (sc   :: [(Child, [(Att, Type)])])
>               (ip   :: [(Att, Type)])
>               (ic   :: [(Child, [(Att, Type)])])
>               (sp   :: [(Att, Type)])
>               (ic'  :: [(Child, [(Att, Type)])])
>               (sp'  :: [(Att, Type)])
>               (a     :: [(Prod, Type)])  where
>   OpComRA' :: Proxy b -> CRule ctx prd sc ip ic sp ic' sp'
>           -> Aspect a -> OpComRA' b ctx  prd sc ip ic sp ic' sp' a


> instance
>  (Require (OpComRA' (HasLabel prd a) ctx prd sc ip ic sp ic' sp' a) ctx)
>   => Require (OpComRA ctx prd sc ip ic sp ic' sp' a) ctx where
>   type ReqR (OpComRA ctx prd sc ip ic sp ic' sp' a)
>      = ReqR (OpComRA' (HasLabel prd a) ctx prd sc ip ic sp ic' sp' a)
>   req ctx (OpComRA rule a)
>      = req ctx (OpComRA' (Proxy @ (HasLabel prd a)) rule a)

> instance
>   (Require (OpExtend PrdReco prd (CRule ctx prd sc ip ic sp ic' sp') a)) ctx
>   => Require (OpComRA' 'False ctx prd sc ip ic sp ic' sp' a) ctx where
>   type ReqR (OpComRA' 'False ctx prd sc ip ic sp ic' sp' a)
>     = ReqR (OpExtend PrdReco prd (CRule ctx prd sc ip ic sp ic' sp') a)
>   req ctx (OpComRA' _ (rule :: CRule ctx prd sc ip ic sp ic' sp') asp)
>     = req ctx (OpExtend (Label @ prd) rule asp)

> instance
>  ( Require (OpUpdate PrdReco prd (CRule ctx prd sc ip ic sp ic'' sp'') a) ctx
>  , RequireR (OpLookup PrdReco prd a) ctx (CRule ctx prd sc ip ic sp ic' sp') 
>  , (IC (ReqR (OpLookup PrdReco prd a))) ~ ic
>  , (SP (ReqR (OpLookup PrdReco prd a))) ~ sp
>  ) => 
>   Require (OpComRA' 'True ctx prd sc ip ic' sp' ic'' sp'' a) ctx where
>   type ReqR (OpComRA' 'True ctx prd sc ip ic' sp' ic'' sp'' a)
>     = ReqR (OpUpdate PrdReco prd
>            (CRule ctx prd sc ip
>              (IC (ReqR (OpLookup PrdReco prd a)))
>              (SP (ReqR (OpLookup PrdReco prd a)))
>             ic'' sp'') a)
>   req ctx (OpComRA' _ rule asp)
>     = let prd     = Label @ prd
>           oldRule = req ctx (OpLookup prd asp)
>           newRule = rule `ext` oldRule
>       in  req ctx (OpUpdate prd newRule asp)



\subsection{Terminals}

> class SemLit a where
>   sem_Lit :: a -> Attribution ('[] :: [(Att,Type)])
>                -> Attribution '[ '( 'Att "term" a , a)]
>   lit     :: Label ('Att "term" a)
> instance SemLit a where
>   sem_Lit a _ = (Label =. a) *. emptyAtt
>   lit         = Label @ ('Att "term" a)
