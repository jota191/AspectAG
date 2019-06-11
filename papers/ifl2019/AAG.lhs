\subsection{Families and Rules}
\label{sec:rules}

In \AspectAG\ internals we use the concept of \emph{families} as input and output
for attribute computations. A family for a given production contains an
attribution for the parent, and a collection of attributions, one for each
children. A family is implemented as a product of |Attribution|
and |ChAttsRec|, and it is indexed with the production which it belongs:

> data Fam  (prd  ::  Prod)
>           (c    ::  [(Child, [(Att, Type)])])
>           (p    ::  [(Att, Type)])  :: Type where
>   Fam  ::  ChAttsRec prd c -> Attribution p
>        ->  Fam prd c p


Attribute computations, or rules are actually functions from an \emph{input
  family} (attributes inherited from the parent and synthesized of the children)
to an \emph{output family} (attributes synthesized for the parent, inherited to
children). We implement them with an extra arity to make them composable, a
known trick\cite{Moor99first-classattribute}. 

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

Given an input family we build a function that updates the output family
constructed thus far. Note that rules are indexed by a production.

To carry context information printable on type errors, most of the time we
actually manipulate tagged rules:

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

After we can define the monadic function |at| used to sugarize definitions:

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

For instance in the example of section \ref{sec:example}, |add_eval| can be rewritten as:

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

An aspect models a piece of semantics of a gramamr. To make semantics extensible
it is enough to implement an algorithm to merge two aspects, and a way to make
an aspect from one single rule. Since our most basic primitives |syndef| and
|inhdef| build a single rule adding a rule one by one is a common operation. As
we show in \ref{tab:ops} we provide a set of operators to combine rules and
aspects. We keep implementing in our |Require| framework.

\subsubsection{Adding a Rule}

We define an operation |OpComRA| (combine a rule, and an aspect). There are two
possibilities. If the rule is indexed by a production not appearing on the
aspect, the combination is simply an append. Otherwise we must lookup the
current rule an update it, combining the inserted rule.


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


where |HasLabel| is a type level function:

> type family HasLabel (l :: k) (r :: [(k, k')]) :: Bool where
>   HasLabel l '[] = False
>   HasLabel l ( '(l', v) ': r) = Or (l == l') (HasLabel l r)


Then, |Require| instances for |OpComRa'| are implemented. The case where
the first parameter is |'False| is easy, an append. The |'True| case is
much more verbose, but anyway inmediate.

Finally we define the proper |extAspect| function, that adds a rule to a record,
now carrying a context.

> extAspect
>   :: RequireR (OpComRA ctx prd sc ip ic sp ic' sp' a) ctx (Aspect asp)
>   => CRule ctx prd sc ip ic sp ic' sp'
>      -> CAspect ctx a -> CAspect ctx asp
> extAspect rule (CAspect fasp)
>   = CAspect $ \ctx -> req ctx (OpComRA rule (fasp ctx))

And we implement an operator

> (.+:) = extAspect
> infixr 3 .+:

\subsubsection{Combining two aspects}

To combine two aspects
we define the operation |OpComAsp|, which takes two aspects as parameters:

> data OpComAsp  (al :: [(Prod, Type)])
>                (ar :: [(Prod, Type)]) where
>   OpComAsp :: Aspect al -> Aspect ar -> OpComAsp al ar

We chose arbitrarly to do the recursion on the second argument. The empty aspect
is a neutral element:

> instance Require (OpComAsp al '[]) ctx where
>   type ReqR (OpComAsp al '[]) = Aspect al
>   req ctx (OpComAsp al _) = al

The recursive case is more interesting:

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

We take the tail of the recursive argument |al|, and call the recursive function
with |al| and |ar|. We need to combine this big aspect with the head rule. For that,
we use the previously defined operation |OpComRA|.

> (.:+:) = comAspect
> infixr 4 .:+:

\subsection{Semantic functions}




In section
\ref{sec:example} we show how |sem_Expr| is defined. It takes an aspect, an
abstract syntax tree (i.e. an |Expr|) and builds a function from the synthesized
attributes to the inherited attributes. More in general, for the domain
associated with each non-terminal we take the function mapping its inherited to
its synthesized attributes. The function |knitAspect| is a wrapper to add
context

> knitAspect (prd :: Label prd) asp fc ip
>   = let ctx  = Proxy @ '[]
>         ctx' = Proxy @ '[Text "knit" :<>: ShowT prd]
>     in  knit ctx (req ctx' (OpLookup prd ((mkAspect asp) ctx))) fc ip

and the real hard work is done by the funtion |knit|, wich takes the combined
rules for a node and the semantic functions of the children, and builds a
function from the inherited attributes of the parent to its synthesized
attributes.

> knit (ctx   :: Proxy ctx)
>      (rule  :: CRule ctx prd (SCh fc) ip (EmptiesR fc) '[] (ICh fc) sp)
>      (fc    :: SemFunRec fc)
>      (ip    :: Attribution ip)
>   =  let  (Fam ic sp)  = mkRule rule ctx
>                          (Fam sc ip) (Fam ec emptyAtt)
>           sc           = kn fc ic
>           ec           = empties fc
>      in   sp

where the function |kn| is a dependent |zipWith ($)|.


> class Kn (fcr   :: [(Child,  Type)]) (prd :: Prod) where
>   type ICh fcr  :: [(Child,  [(Att, Type)])]
>   type SCh fcr  :: [(Child,  [(Att, Type)])]
>   kn  :: SemFunRec fcr -> ChAttsRec prd (ICh fcr)
>       -> ChAttsRec prd (SCh fcr)

and |empties| builds an empty attribution for each child.

> class Empties (fc :: [(Child,Type)]) (prd :: Prod) where
>   type EmptiesR fc :: [(Child, [(Att, Type)])] 
>   empties :: Record fc -> ChAttsRec prd (EmptiesR fc)

While they are nice examples of type level programming, we left the
implementation out of this paper, this technique is well documented in the
literature \cite{Viera:2009:AGF:1596550.1596586, Moor99first-classattribute,
DBLP:conf/gcse/MoorPW99}.


\subsection{Terminals}

A production specifies how a nonterminal symbol can be rewritten. It can rewrite
to a mix of terminal and nonterminal symbols. From the datatype perspective, a
constructor can contain recursive and nonrecursive positions. Usually, in
attribute grammar systems a terminal has only one attribute: itself. In
\AspectAG all children are put in a record, each position containing an
attribution. In old versions of \AspectAG terminals where directly put as a
children instead of an attribution. This was possible since at type level this
records were essentialy untyped. We decided to lift the shape of the structure
to kinds, adding up static guarantees, but losing this flexibility.

There are at least two approaches to treat terminals:

\begin{itemize}
\item
  |ChAttsRec| could contain a promoted sum type, each child is either a terminal
  or nonterminal with an attribution |'(Att, Type)|.
\item
  For each terminal there is a child, with a trivial attribution containing only
  an attribute for the terminal.
\end{itemize}

The second option was chosen since it is easier and clearer to have a uniform
structure.

To introduce an attribute the user defines an unique name. As we say, there is a
trivial attribute for each terminal. To chose a name is not a problem since it
is isolated behind a children. Accordingly, semantic functions of the children
can be coded in a polymorphic way.

> class SemLit a where
>   sem_Lit :: a -> Attribution ('[] :: [(Att,Type)])
>                -> Attribution [( 'Att "term" a , a)]
>   lit     :: Label ('Att "term" a)
> instance SemLit a where
>   sem_Lit a _ = (Label .=. a) *. emptyAtt
>   lit         = Label @ ('Att "term" a)

All of them are labelled with the |lit| label, and the semantic function simply
wraps a value in an attribution.

