\subsection{Families and Rules}
\label{sec:rules}

On \AspectAG internals we use the concept of \emph{families} as input and output
for attribute computations. A family for a given production contains an
attribution for the parent, and a collection of attributions for children, one
for each. 
A family is implemented as a product of |Attribution| and |ChAttsRec|, and it is
indexed with the production which it belongs:

> data Fam  (prd  ::  Prod)
>           (c    ::  [(Child, [(Att, Type)])])
>           (p    ::  [(Att, Type)])  :: Type where
>   Fam  ::  ChAttsRec prd c -> Attribution p
>        ->  Fam prd c p


Attribute computations, or rules are actually functions from an \emph{input
  family} (attributes inherited from the parent and synthesized of the children)
to an \emph{output family} (attributes synthesized for the parent, inherited to
children). We implement them with an extra arity to make them composable, this
trick was introduced in [REF]. Given an imput family we build a function that
updates the output family constructed thus far

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

To pass context information printable on type errors we use tagged rules:

> newtype CRule (ctx :: [ErrorMessage]) prd sc ip ic sp ic' sp'
>  = CRule { mkRule :: (Proxy ctx -> Rule prd sc ip ic sp ic' sp')}


\subsection{Defining Attributes}
\label{sec:defs}

The function |syndef| introduces a new synthesized attribute.

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

It takes an attribute name |att|, a production |prd|, and a function |f| that
computes the value of the attribute in terms of the input family. |f| takes
an extra |proxy| argument to carry context information. It appends information
about the current definition to the existing context of the attribution being
extended.
In practice it is useful to use a monadic version of |syndef|

> syndefM att prd = syndef att prd . def

where

> def :: Reader (Proxy ctx, Fam prd chi par) a
>     -> (Proxy ctx -> (Fam prd chi par) -> a)
> def = curry . runReader

We define a monadic function |at| to sugarize definitions:

> class At pos att m  where
>  type ResAt pos att m
>  at :: Label pos -> Label att -> m (ResAt pos att m)

> instance
>  (  RequireR  (OpLookup  (ChiReco prd) ('Chi ch prd nt) chi)
>               ctx (Attribution r)
>  ,  RequireR  (OpLookup AttReco ('Att att t) r) ctx t'
>  ,  RequireEq prd prd' ctx
>  ,  RequireEq t t' ctx
>  )
>  => At ('Chi ch prd nt) ('Att att t)
>        (Reader (Proxy ctx, Fam prd' chi par))  where
>  type ResAt ('Chi ch prd nt) ('Att att t)
>             (Reader (Proxy ctx, Fam prd' chi par))
>    = t
>  at  (ch :: Label ('Chi ch prd nt))
>      (att :: Label ('Att att t))
>   =  liftM  (\(ctx, Fam chi _)  ->
>                let atts = req ctx (OpLookup ch chi)
>                in  req ctx (OpLookup att atts))
>             ask

For instance in the example of section[REF], |add_eval| can be rewritten as:

> add_eval = syndef eval add
>  (\Proxy (Fam sc ip)->
>   (+) (sc .#. leftAdd .#. eval) (sc .#. rightAdd .#. eval))

where |(.#.)| is the lookup operator. If the programmer prefers, he or she can
use this desugarized functions.



To define an inherited attribute we can use the function |inhdef|. This time
we present this definition omiting the constraints.

%if False
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
%endif

> inhdef :: ( ... )
>      => Label ('Att att t)
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

Inherited attribute definitions are also related to a child. Again, the monadic
alternative |inhdefM| is provided. Functions to define synthesized and inherited
attributes are neccesary to compose nontrivial attribute grammar. More
constructs are useful in practice. In section[REF] |synmod| was used and proved
to be useful to change semantics. Its inherited counterpart |inhmod| is also
provided. On top of this we implement some common patterns that generate rules
from higher level specifications.
\todo{}





\subsection{Combining Rules.}

Functions as |syndef| or |inhdef| build rules from scratch defining how to
compute one single new attribute from a given family using functions of the host
language. A full rule is usually more complex, since it builds a full output
family, where many attributes are computed in many ways. To build a big rule we
compose smaller rules. Composing them is easy once since we encoded them using
the extra arity trick:

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


> instance RequireEqRes t1 t2 ctx
>   => Require (OpEq t1 t2) ctx where
>   type ReqR (OpEq t1 t2) = ()
>   req = undefined

> type family RequireEqRes  (t1 :: k) (t2 :: k)
>                           (ctx :: [ErrorMessage]) ::  Constraint where
>   RequireEqRes t1 t2 ctx
>   = If            (t1 `Equal` t2)
>         {-then-}  (() :: Constraint)
>         {-else-}  (Require (OpError (Text "" :<>: ShowT t1
>                             :<>: Text " /= " :<>: ShowT t2)) ctx)



and builds an understandable error message for label mistmatch otherwise.



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

As done in section \ref{sec:rules} with rules, to keep track on contexts
contexts we introduce the concept of a tagged aspect:

> newtype CAspect (ctx :: [ErrorMessage]) (asp :: [(Prod, Type)] )
>   = CAspect { mkAspect :: Proxy ctx -> Aspect asp}

In section \ref{sec:defs} we see that context is extended when an attribute is
defined usinf |syndef| or |inhdef|. In the running example in section
\ref{sec:defs} the function |traceAspect| was introduced. |traceAspect| is as a
tool for the user to place marks visible in the trace when a type error occurs.
We implement |traceAspect| using a sort of |map| function, traversing the record.


> traceAspect (_ :: Proxy (e::ErrorMessage))
>  = mapCAspect  $   \(_ :: Proxy ctx)
>                ->  Proxy @ ((Text "aspect ":<>: e) : ctx)



> mapCAspect fctx (CAspect fasp)
>   = CAspect $ mapCtxRec fctx . fasp . fctx

where |mapCtxRec| is a dependent function:

> class MapCtxAsp (r :: [(Prod,Type)]) (ctx :: [ErrorMessage])
>                                      (ctx' :: [ErrorMessage])  where
>   type ResMapCtx r ctx ctx' :: [(Prod,Type)]
>   mapCtxRec  :: (Proxy ctx -> Proxy ctx')
>              -> Aspect r -> Aspect (ResMapCtx r ctx ctx')

whose implementation does not offer new insight.

> (.+:) = extAspect
> infixr 3 .+:

\begin{table}[t] 
   \label{tab:ops}
   \small % text size of table content
   \centering % center the table
   \begin{tabular}{lcccc} % alignment of each column data
   \toprule[\heavyrulewidth] \textbf{{\tt ASCII} op.} & \textbf{Unicode op.} &
   \textbf{Left arg.} & \textbf{Right arg.} & \textbf{Associativity}\\ \midrule
   {\tt (.+:)} & |(.+:)| & Rule & Aspect & right \\ \hline
   {\tt (.:+.)} & |(.:+.)| & Aspect & Rule & left \\ \hline
      {\tt (.:+:)} & |(.:+:)| & Aspect & Aspect & right \\ \hline
   {\tt (.+.)} & |(.+.)| & Rule & Rule & --\\
   \bottomrule[\heavyrulewidth]
   \end{tabular}
   \caption{Operators to combine semantics}
\end{table}

\todo{donde poner esto, capaz no es necesario}

> mapCRule :: (Proxy ctx -> Proxy ctx')
>           -> CRule ctx' prd sc ip ic sp ic' sp'
>           -> CRule ctx  prd sc ip ic sp ic' sp'
> mapCRule fctx (CRule frule) = CRule $ frule . fctx

> traceRule (_ :: Proxy (e::ErrorMessage))
>   = mapCRule  $   \(_ :: Proxy ctx)
>               ->  Proxy @ ((Text "rule ":<>: e) : ctx)

\subsection{Combining Aspects}

An aspect represents the semantic of one production. To make semantics
extensible it is enough to implement an algorithm to merge two aspects, and a
way to make an aspect from one single rule. Since our most basic primitives
|syndef| and |inhdef| build a single rule adding a rule one by one is a common
operation. As we show in \ref{tab:ops} we provide a set of operators to combine
semantics.


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
