\subsection{Families and Rules}

On \AspectAG internals we use the concept of \emph{families} as input and output
for attribute computations. A family for a given production contains an
attribution for the parent, and a collection of attributions for children, one
for each. 
A family is implemented as a product, of |Attribution| and |ChAttsRec|, and it is
indexed by a production:

> data Fam  (prd  ::  Prod)
>           (c    ::  [(Child, [(Att, Type)])])
>           (p    ::  [(Att, Type)])  :: Type
>  where
>   Fam  ::  ChAttsRec prd c -> Attribution p
>        ->  Fam prd c p

Esto es prescindible: 

> chi :: Fam prd c p -> ChAttsRec prd c
> chi (Fam c p) = c

> par :: Fam prd c p -> Attribution p
> par (Fam c p) = p

Attribute computations, or rules are actually functions from an \emph{input
  family} (attributes inherited from the parent and synthesized of the children)
to an \emph{output family} (attributes synthesized for the parent, inherited to
children). We implement them with an extra arity to make them composable, this
trick was introduced in [REF]. Given an imput family we build a function that
updates the output family constructed thus far:

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


esto es prescindible:

> type family IC (rule :: Type) where
>   IC (Rule prd sc ip ic sp ic' sp') = ic
>   IC (CRule ctx prd sc ip ic sp ic' sp') = ic
> type family SP (rule :: Type) where
>   SP (Rule prd sc ip ic sp ic' sp') = sp
>   SP (CRule ctx prd sc ip ic sp ic' sp') = sp

To pass context information printable on type errors we can tag a rule:

> newtype CRule (ctx :: [ErrorMessage]) prd sc ip ic sp ic' sp'
>  = CRule { mkRule :: (Proxy ctx -> Rule prd sc ip ic sp ic' sp')}


\subsection{Defining Attributes}

The function |syndef| takes an attribute name |att| and a production
|prd|, an update function |f|:

> syndef  ::  (   RequireEq t t' ctx'
>             ,   RequireR  ( OpExtend AttReco ('Att att t) t sp)
>                             ctx (Attribution sp')
>             ,   ctx'  ~     ((Text "syndef("
>                             :<>:  ShowT ('Att att t) :<>: Text ", "
>                             :<>:  ShowT prd :<>: Text ")") ': ctx) )
>         =>  Label ('Att att t) ->  Label prd
>         ->  (Proxy ctx' -> Fam prd sc ip -> t')
>         ->  CRule ctx prd sc ip ic sp ic sp'
> syndef att prd f
>   =  CRule $ \ctx inp (Fam ic sp)
>      ->  Fam ic $ req ctx (OpExtend att (f Proxy inp) sp)

In practice it is useful to use a monadic version of |syndef|

> syndefM att prd = syndef att prd . def

where

> def :: Reader (Proxy ctx, Fam prd chi par) a
>     -> (Proxy ctx -> (Fam prd chi par) -> a)
> def = curry . runReader

To define an inherited attribute we can use the function |inhdef|:

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


Again, a monadic version fits better when calling it:

> inhdefM att prd chi = inhdef att prd chi . def


\subsection{Combining Rules.}

Functions like |syndef| or |inhdef| build a rule from scratch defining how to
compute one single new attribute from a given family using functions of the
host language.
Rules can be more than that, building a full family. To build a big rule
we compose smaller rules. Composing them is easy once since we encoded them
using the extra arity trick:

> ext' ::  CRule ctx prd sc ip ic sp ic' sp'
>      ->  CRule ctx prd sc ip a b ic sp
>      ->  CRule ctx prd sc ip a b ic' sp'
> (CRule f) `ext'` (CRule g)
>  = CRule $ \ctx input -> f ctx input . g ctx input

Note that to compose rules they must be tagged from the same productions
|prd|. If we use |ext'| and try to combine two rules from different
productions, we get a huge type error where the type mismatch is
obfuscated on hundreds of lines of error code, where every record such as
|ic| or |sp| are printed, and every clas constraint such as |Require|s is
printed (each one printing again some record and so on). We need a clear
and small type error and this can be done by using the following definition:

> ext ::  RequireEq prd prd' (Text "ext":ctx)
>      => CRule ctx prd sc ip ic sp ic' sp'
>      -> CRule ctx prd' sc ip a b ic sp
>      -> CRule ctx prd sc ip a b ic' sp'
> ext = ext'
> infixr 6 .+.
> (.+.) = ext

Here we use |RequireEq| wich is actually a sugar for a couple of constraints:

> type RequireEq (t1 :: k )(t2 :: k) (ctx:: [ErrorMessage])
>     = (Require (OpEq t1 t2) ctx, t1 ~ t2)

The first is a requirement, using the following operator:

> data OpEq t1 t2

which is trivially implemented when |t1==t2|

> instance Require (OpEq t t) ctx where
>   type ReqR (OpEq t t) = ()
>   req = undefined

and builds an understandable error message for label mistmatch otherwise:

> instance Require (OpError (Text "" :<>: ShowT t1 :<>: Text " /= "
>                             :<>: ShowT t2)) ctx
>   => Require (OpEq t1 t2) ctx where
>   type ReqR (OpEq t1 t2) = ()
>   req = undefined

\todo{no me convence esto}



\subsection{Aspects}

Aspects are collections of rules, indexed by productions. They are an instance
of |GenRecord|, defined as:

> data PrdReco
> type instance  WrapField PrdReco (rule :: Type)
>   = rule
> type Aspect (asp :: [(Prod, Type)]) =  Rec PrdReco asp
> type instance ShowRec PrdReco       =  "Aspect"
> type instance ShowField PrdReco     =  "production named "

\todo{ hay cierta inconsistencia aca, estamos metiendo las reglas bajo
el wrapper type. Creo que manejarlas explícitamente sería muy doloroso,
e incluso creo que podemos tener algun problema para instanciar los kinds
del argumento extra, La solución puede pasar por decir simplemente
que lo hacemos así para simplificar (es la realidad), pero hay que ser menos
enfático antes cada vez que se habla de poner toda la informacion posible en
los kinds
}

Again, to move contexts we introduce the concept of a tagged aspect:

> newtype CAspect (ctx :: [ErrorMessage]) (asp :: [(Prod, Type)] )
>   = CAspect { mkAspect :: Proxy ctx -> Aspect asp}




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


\subsection{Combining Aspects}

> comAspect ::
>  ( Require (OpComAsp al ar) ctx
>  , ReqR (OpComAsp al ar) ~ Aspect asp)
>  =>  CAspect ctx al -> CAspect ctx ar -> CAspect ctx asp
> comAspect al ar
>   = CAspect $ \ctx
>     -> req ctx (OpComAsp (mkAspect al ctx) (mkAspect ar ctx))

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
>                -> Attribution [( 'Att "term" a , a)]
>   lit     :: Label ('Att "term" a)
> instance SemLit a where
>   sem_Lit a _ = (Label =. a) *. emptyAtt
>   lit         = Label @ ('Att "term" a)



\subsection{Monadic interface}

> data Lhs
> lhs :: Label Lhs
> lhs = Label
>
> class At pos att m  where
>  type ResAt pos att m
>  at :: Label pos -> Label att -> m (ResAt pos att m)


> instance ( RequireR (OpLookup (ChiReco prd) ('Chi ch prd nt) chi) ctx
>                     (Attribution r)
>          , RequireR (OpLookup AttReco ('Att att t) r) ctx t'
>          , RequireEq prd prd' ctx
>          , RequireEq t t' ctx 
>          )
>       => At ('Chi ch prd nt) ('Att att t)
>             (Reader (Proxy ctx, Fam prd' chi par))  where
>  type ResAt ('Chi ch prd nt) ('Att att t) (Reader (Proxy ctx, Fam prd' chi par))
>          = t 
>  at (ch :: Label ('Chi ch prd nt)) (att :: Label ('Att att t))
>   = liftM (\(ctx, Fam chi _)  -> let atts = req ctx (OpLookup ch chi)
>                                  in  req ctx (OpLookup att atts))
>           ask

> instance
>          ( RequireR (OpLookup AttReco ('Att att t) par) ctx t'
>          , RequireEq t t' ctx
>          )
>  => At Lhs ('Att att t) (Reader (Proxy ctx, Fam prd chi par))  where
>  type ResAt Lhs ('Att att t) (Reader (Proxy ctx, Fam prd chi par))
>     = t
>  at lhs att
>   = liftM (\(ctx, Fam _ par) -> req ctx (OpLookup att par)) ask


\subsection{Putting it all together: How the computation is done}

> class Kn (fcr :: [(Child, Type)]) (prd :: Prod) where
>   type ICh fcr :: [(Child, [(Att, Type)])]
>   type SCh fcr :: [(Child, [(Att, Type)])]
>   kn :: Record fcr -> ChAttsRec prd (ICh fcr) -> ChAttsRec prd (SCh fcr)

> instance Kn '[] prod where
>   type ICh '[] = '[]
>   type SCh '[] = '[] 
>   kn _ _ = emptyCh

> instance ( lch ~ 'Chi l prd nt
>          , Kn fc prd
>          , LabelSet ('(lch, sch) : SCh fc)
>          , LabelSet ('(lch, ich) : ICh fc)
>          ) => 
>   Kn ( '(lch , Attribution ich -> Attribution sch) ': fc) prd where
>   type ICh ( '(lch , Attribution ich -> Attribution sch) ': fc)
>     = '(lch , ich) ': ICh fc
>   type SCh ( '(lch , Attribution ich -> Attribution sch) ': fc)
>     = '(lch , sch) ': SCh fc
>   kn ((ConsRec (TagField _ lch fch) (fcr :: Record fc)))
>    = \((ConsCh pich icr) :: ChAttsRec prd ( '(lch, ich) ': ICh fc))
>    -> let scr = kn fcr icr
>           ich = unTaggedChAttr pich
>       in ConsCh (TaggedChAttr lch
>                (fch ich)) scr



> emptyCtx = Proxy @ '[]


> class Empties (fc :: [(Child,Type)]) (prd :: Prod) where
>   type EmptiesR fc :: [(Child, [(Att, Type)])] 
>   empties :: Record fc -> ChAttsRec prd (EmptiesR fc)

> instance Empties '[] prd where
>   type EmptiesR '[] = '[]
>   empties _ = emptyCh

> instance ( Empties fcr prd
>          , chi ~ 'Chi ch prd nt
>          , LabelSet ( '(chi, '[]) ': EmptiesR fcr))
>  => Empties ( '(chi, Attribution e -> Attribution a) ': fcr) prd where
>   type EmptiesR ( '(chi, Attribution e -> Attribution a) ': fcr)
>     = '(chi, '[]) ': EmptiesR fcr
>   empties (ConsRec pch fcr)
>     = let lch = labelTChAtt pch
>       in  (lch .= emptyAtt) .* (empties fcr)

> knit (ctx  :: Proxy ctx)
>      (rule :: CRule ctx prd (SCh fc) ip (EmptiesR fc) '[] (ICh fc) sp)
>      (fc   :: Record fc)
>      (ip   :: Attribution ip)
>   = let (Fam ic sp) = mkRule rule ctx
>                        (Fam sc ip) (Fam ec emptyAtt)
>         sc          = kn fc ic
>         ec          = empties fc
>     in  sp


> knitAspect (prd :: Label prd) asp fc ip
>   = let ctx  = Proxy @ '[]
>         ctx' = Proxy @ '[Text "knit" :<>: ShowT prd]
>     in  knit ctx (req ctx' (OpLookup prd ((mkAspect asp) ctx))) fc ip
