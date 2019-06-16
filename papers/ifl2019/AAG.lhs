In this section we show how we put records and requirements to
work in the implementation of \AspectAG.

\subsection{Families and Rules}
\label{sec:rules}

We use the concept of \emph{families} as input and output
for attribute computations. A family for a given production contains an
attribution for the parent, and a collection of attributions, one for each
of the children. A family is implemented as a product of |Attribution|
and |ChAttsRec|, and it is indexed with the production to which it belongs:

> data Fam  (prd  ::  Prod)
>           (c    ::  [(Child, [(Att, Type)])])
>           (p    ::  [(Att, Type)])  :: Type where
>   Fam  ::  ChAttsRec prd c -> Attribution p ->  Fam prd c p


Attribute computations, or rules, are actually functions from an \emph{input
  family} (attributes inherited from the parent and synthesized of the children)
to an \emph{output family} (attributes synthesized for the parent, inherited to
children). We implement them with an extra arity to make them composable, a
well-known trick\cite{Moor99first-classattribute}. 

> type Rule  (prd  :: Prod)
>            (sc   :: [(Child, [(Att, Type)])])
>            (ip   :: [(Att,       Type)])
>            (ic   :: [(Child, [(Att, Type)])])
>            (sp   :: [(Att,       Type)])
>            (ic'  :: [(Child, [(Att, Type)])])
>            (sp'  :: [(Att,       Type)])
>   =   Fam prd sc ip ->  Fam prd ic sp -> Fam prd ic' sp'

Given an input family we build a function that updates the output family
constructed thus far. Note that the rules are indexed by a production.

To carry context information printable on type errors, most of the time we
actually manipulate \emph{tagged} rules:

> newtype CRule (ctx :: [ErrorMessage]) prd sc ip ic sp ic' sp'
>  = CRule {mkRule :: Proxy ctx -> Rule prd sc ip ic sp ic' sp'}


\subsection{Defining Attributes}
\label{sec:defs}

The function |syndef| introduces a new synthesized attribute;
i.e. a rule that extends the attribution for the parent in the
output family, provided that some requirements are fullfiled.

> syndef  ::  (   ctx' ~ (  (  Text "syndef(" :<>:  ShowT ('Att att t) :<>:
>                              Text ", " :<>:  ShowT prd :<>: Text ")")
>                           ': ctx)
>             ,   RequireEq t t' ctx'
>             ,   RequireR   (OpExtend AttReco ('Att att t) t sp) ctx
>                            (Attribution sp') )
>         =>  Label ('Att att t) ->  Label prd
>         ->  (Proxy ctx' -> Fam prd sc ip -> t')
>         ->  CRule ctx prd sc ip ic sp ic sp'
> syndef att prd f
>   =  CRule $ \ctx inp (Fam ic sp)
>      ->  Fam ic $ req ctx (OpExtend att (f Proxy inp) sp)

It takes an attribute name |att|, a production |prd|, and a function |f| that
computes the value of the attribute in terms of the input family.
The function |f| takes an extra |proxy| argument to carry context
information. In this case, we extend the current context |ctx|
to a new one (|ctx'|) including information about the |syndef| definition
where it was called.
We require the type |t'| of the value returned by |f|
to be equal to the type |t| of the attribute,
using a |RequireEq| requirement.
Notice that we could have implemented this restriction by using the same
type variable |t| for |t| and |t'|. But in this case we
would not have a customized error message.
The last requirement (|OpExtend|) states that we have to be able to extend
the attribution indexed by |sp| with the attribute |att| and the result is
an attribution with index sp'. This requirement imposes the constraint that
assures that this insertion does not duplicate the attribute |att|.
Since this requirement is not internal to the computation defined in |syndef|,
que use the current context |ctx| instead of |ctx'|.

Using |syndef| we can define rules like |add_eval| of Section~\ref{sec:example}:

> add_eval = syndef eval add $ \Proxy (Fam sc ip)->
>   (+) (sc .#. leftAdd .#. eval) (sc .#. rightAdd .#. eval)
%
where |(.#.)| is the lookup operator. 
In practice it is useful to use a monadic version of |syndef|,
which is the one we used in Section~\ref{sec:example}:

> syndefM att prd = syndef att prd . def
%
where

> def :: Reader (Proxy ctx, Fam prd chi par) a
>     -> (Proxy ctx -> (Fam prd chi par) -> a)
> def = curry . runReader

We defined the monadic function |at| used to sugarize definitions:
> class At pos att m  where
>  type ResAt pos att m
>  at :: Label pos -> Label att -> m (ResAt pos att m)
%
with instances for looking up attributes into the attribution of the parent (|lhs|)
or the attribution of a given child. The following is the instance for
the case of children:
> instance
>   ( RequireR  (OpLookup   (ChiReco prd) ('Chi ch prd nt) chi)
>                           ctx (Attribution r)
>   , RequireR  (OpLookup   AttReco ('Att att t) r) ctx t'
>   , RequireEq  prd prd' ctx
>   , RequireEq  t t' ctx
>   , RequireEq  ('Chi ch prd nt) ('Chi ch prd ('Left ('NT n)))  ctx)
>  => At  ('Chi ch prd nt) ('Att att t)
>         (Reader (Proxy ctx, Fam prd' chi par))  where
>  type ResAt  ('Chi ch prd nt) ('Att att t)
>              (Reader (Proxy ctx, Fam prd' chi par))
>   = t
>  at ch att
>   = liftM  (\(ctx,  Fam chi _)
>                     ->  let  atts = req ctx (OpLookup ch chi)
>                         in   req ctx (OpLookup att atts))
>            ask
In this case there are two lookups involved, because we have to find the
child in the record of children and then the attribute in its attribution.
We also require some equalities, including the fact that the child
has to be a non-terminal |('Left ('NT n))|.

The function |inhdef| defines an inherited attribute.
For simplicity reasons we omit the constraints.

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

> inhdef :: ( ... )  => Label ('Att att t)
>                    -> Label prd
>                    -> Label ('Chi chi prd ntch)
>                    -> (Proxy ctx' -> Fam prd sc ip -> t')
>                    -> CRule ctx prd sc ip ic sp ic' sp
> inhdef  att prd chi f
>   = CRule $ \ctx inp (Fam ic sp)
>        ->  let  catts   = req ctx (OpLookup chi ic)
>                 catts'  = req ctx (OpExtend  att (f Proxy inp) catts)
>                 ic'     = req ctx (OpUpdate chi catts' ic)
>            in   Fam ic' sp

An inherited attribute |att| is defined in a production |prd| for
a given child |chi|. In this case we have to lookup the attribution of the child into
the inherited attributes of the children |ic|, then extend it and update |ic|.

Again, the monadic
alternative |inhdefM| is provided. Functions to define synthesized and inherited
attributes are neccesary to compose nontrivial attribute grammars. More
constructs are useful in practice. In Section~\ref{sec:example} |synmod| (that modifies an attribute instead of adding it)
was used and proved to be useful to change semantics. Its inherited counterpart |inhmod|
is also provided. On top of this we can implement some common patterns that generate
rules from higher level specifications.

\subsection{Combining Rules.}

Functions as |syndef| or |inhdef| build rules from scratch defining how to
compute one single new attribute from a given family using functions of the host
language. A full rule is usually more complex, since it builds a full output
family, where usually many attributes are computed in many ways. To build such
rules we compose smaller rules. Composing them is easy, given the extra arity trick:

> ext  ::  RequireEq prd prd' (Text "ext":ctx)
>      =>  CRule ctx prd sc ip ic sp ic' sp'
>      ->  CRule ctx prd' sc ip a b ic sp
>      ->  CRule ctx prd sc ip a b ic' sp'
> (CRule f) `ext` (CRule g)
>  = CRule $ \ctx input -> f ctx input . g ctx input

Note that we require the rules to be tagged from the same production.
If instead of using |RequireEq| we unify |prd| and |prd'| to the same type variable,
and try to combine two rules from different productions,
we get a huge type error where the type mismatch is
obfuscated on hundreds of lines of error code, printing every record, such as
|ic| or |sp|, and every class constraint, such as |Require|. 



\subsection{Aspects}

Aspects are collections of rules, indexed by productions. They are an instance
of |GenRecord|, defined as:

> data PrdReco
> type instance  WrapField PrdReco (rule :: Type) = rule
> type Aspect (asp :: [(Prod, Type)])  =  Rec PrdReco asp
> type instance ShowRec PrdReco        =  "Aspect"
> type instance ShowField PrdReco      =  "production named "


As done in Section~\ref{sec:rules} with rules, to keep track on contexts
we introduce the concept of a tagged aspect:

> newtype CAspect (ctx :: [ErrorMessage]) (asp :: [(Prod, Type)] )
>   = CAspect { mkAspect :: Proxy ctx -> Aspect asp}

In Section~\ref{sec:defs} we saw how that context is extended when an attribute is
defined using |syndef| or |inhdef|. In the running example in Section~\ref{sec:example}
the function |traceAspect| was introduced as a
tool for the user to place marks visible in the trace when a type error occurs.
We implement |traceAspect| using a sort of |map| function, traversing the record.


> traceAspect (_ :: Proxy (e::ErrorMessage))
>  = mapCAspect  $   \(_ :: Proxy ctx)
>                ->  Proxy @ ((Text "aspect ":<>: e) : ctx)
> mapCAspect fctx (CAspect fasp)
>   = CAspect $ mapCtxRec fctx . fasp . fctx
%
where |mapCtxRec| is a dependent function:

> class MapCtxAsp  (r     :: [(Prod,Type)])
>                  (ctx   :: [ErrorMessage])
>                  (ctx'  :: [ErrorMessage])  where
>   type ResMapCtx r ctx ctx' :: [(Prod,Type)]
>   mapCtxRec  :: (Proxy ctx -> Proxy ctx')
>              -> Aspect r -> Aspect (ResMapCtx r ctx ctx')
%
whose implementation does not offer new insights.

\begin{table}[t] 
   \small % text size of table content
   \centering % center the table
   \begin{tabular}{lccccc} % alignment of each column data
   \toprule[\heavyrulewidth] \textbf{op.} & \textbf{Unicode op.} &
   \textbf{larg} & \textbf{rarg} & \textbf{Assoc.}& \textbf{impl.}\\ \midrule
   {\tt (.+:)} & |(.+:)| & Rule & Aspect & right& |extAspect| \\ \hline
   {\tt (.:+.)} & |(.:+.)| & Aspect & Rule & left& |flip extAspect|\\ \hline
      {\tt (.:+:)} & |(.:+:)| & Aspect & Aspect & right& |comAspect|\\ \hline
   {\tt (.+.)} & |(.+.)| & Rule & Rule & right & |ext|\\
   \bottomrule[\heavyrulewidth]
   \end{tabular}
   \caption{Operators to combine semantics}
   \label{tab:ops}
\end{table}


\subsection{Combining Aspects}

An aspect models a piece of semantics of a grammar. To make semantics extensible
it is enough to implement an algorithm to merge two aspects, and a way to make
an aspect from one single rule. Since our most basic primitives |syndef| and
|inhdef| build a single rule, adding rules one by one to an aspect is a common operation. As
we show in Table~\ref{tab:ops} we provide a set of operators to combine rules and
aspects. We already introduced |ext|, which combines two rules of the same
production.

%Within the |Require| framework, we implement operations to append rules to an
%aspect, and to combine Aspects.

\subsubsection{Adding a Rule}

We define an operation |OpComRA| to combine a rule with an aspect. 

> data OpComRA  (ctx  :: [ErrorMessage])
>               (prd  :: Prod)
>               (sc   :: [(Child, [(Att, Type)])])
>               (ip   :: [(Att, Type)])
>               (ic   :: [(Child, [(Att, Type)])])
>               (sp   :: [(Att, Type)])
>               (ic'  :: [(Child, [(Att, Type)])])
>               (sp'  :: [(Att, Type)])
>               (a    :: [(Prod, Type)])  where
>   OpComRA :: CRule ctx prd sc ip ic sp ic' sp'
>           -> Aspect a -> OpComRA ctx prd sc ip ic sp ic' sp' a
%
This operation has two cases. If the rule is indexed by a production not appearing on the
aspect, the combination is simply an append. Otherwise we must lookup the
current rule an update it, combining the inserted rule.
We implement these cases in a lower level operation |OpComRA'|, where the truth value of
the production membership is explicit, in a similar way as we have done
for the lookup operation in Section~\ref{sec:lookup}.
In this case the predicate is the type-level function |HasLabel|:

> type family HasLabel (l :: k) (r :: [(k, k')]) :: Bool where
>   HasLabel l '[]               = False
>   HasLabel l ( '(l', v) ': r)  = Or (l == l') (HasLabel l r)
%
The |Require| instance for |OpComRA'| in the case where the
first parameter is |'False| implements an append. The |'True| case is a little bit
more verbose, but anyway inmediate: we lookup the rule at the original aspect,
extend the rule with the one as argument, and update the aspect with the
resulting rule.

With this operation, we define the proper |extAspect| function, that adds a
tagged rule to a tagged Aspect.

%> extAspect  :: RequireR  (OpComRA ctx prd sc ip ic sp ic' sp' a) ctx
%>                         (Aspect asp)
%>            =>  CRule ctx prd sc ip ic sp ic' sp'
%>            ->  CAspect ctx a -> CAspect ctx asp
> extAspect rule (CAspect fasp)
>   = CAspect $ \ctx -> req ctx (OpComRA rule (fasp ctx))


\subsubsection{Combining two aspects}

To combine two aspects
we define the operation |OpComAsp|, which takes two aspects as parameters:

> data OpComAsp  (al :: [(Prod, Type)]) (ar :: [(Prod, Type)]) where
>   OpComAsp :: Aspect al -> Aspect ar -> OpComAsp al ar

We chose arbitrarly to do the recursion on the second argument. The empty aspect
is a neutral element:

> instance Require (OpComAsp al '[]) ctx where
>   type ReqR (OpComAsp al '[]) = Aspect al
>   req ctx (OpComAsp al _) = al

In the recursive case, we take the tail |ar| of the recursive argument,
and call the recursive function with |al| and |ar|.
The resulting aspect is combined with the head rule
using the operation |OpComRA|.

> instance
>    ( RequireR  (OpComAsp al ar) ctx  (Aspect ar')
>    , Require   (OpComRA ctx prd sc ip ic sp ic' sp' ar') ctx)
>   => Require (OpComAsp al
>      ( '(prd, CRule ctx prd sc ip ic sp ic' sp') ': ar)) ctx where
>   type ReqR  (OpComAsp al
>              ( '(prd, CRule ctx prd sc ip ic sp ic' sp') ': ar))
>     = ReqR  (OpComRA ctx prd sc ip ic sp ic' sp'
>             (UnWrap (ReqR (OpComAsp al ar))))
>   req ctx (OpComAsp al (ConsRec prdrule ar))
>    = req ctx (OpComRA  (untagField prdrule)
>                        (req ctx (OpComAsp al ar)))

Thus, the function that combines two tagged aspects is:
> comAspect al ar
>   = CAspect $ \ctx -> req ctx (OpComAsp  (mkAspect al ctx)
>                                          (mkAspect ar ctx))

\subsection{Semantic functions}
In Section~\ref{sec:example} we show how |sem_Expr| is defined. It takes an aspect, an
abstract syntax tree (i.e. an |Expr|) and builds a function from the synthesized
attributes to the inherited attributes. More in general, for the domain
associated with each non-terminal we take the function mapping its inherited to
its synthesized attributes. The function |knitAspect| is a wrapper to add
context

> knitAspect (prd :: Label prd) asp fc ip
>   =  let  ctx   = Proxy @ '[]
>           ctx'  = Proxy @ '[Text "knit" :<>: ShowT prd]
>      in   knit ctx
>           (req ctx' (OpLookup prd ((mkAspect asp) ctx))) fc ip

and the real work is done by the circular funtion |knit|, wich takes the combined
rules for a node and the semantic functions of the children, and builds a
function from the inherited attributes of the parent to its synthesized
attributes.

> knit (ctx   :: Proxy ctx)
>      (rule  :: CRule ctx prd (SCh fc) ip (EmptiesR fc) '[] (ICh fc) sp)
>      (fc    :: SemFunRec fc)
>      (ip    :: Attribution ip)
>   =  let  (Fam ic sp)  = mkRule rule ctx  (Fam sc ip)
>                                           (Fam ec emptyAtt)
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

While they are nice examples of type-level programming, we left the
implementation out of this paper, since this technique is well documented in the
literature \cite{Viera:2009:AGF:1596550.1596586, Moor99first-classattribute,
DBLP:conf/gcse/MoorPW99}.


\subsection{Terminals}

A production specifies how a nonterminal symbol can be rewritten. It can rewrite
to a mix of terminal and nonterminal symbols. From the datatype perspective, a
constructor can contain recursive and nonrecursive positions. Usually, in
attribute grammar systems a terminal has only one attribute: itself. In
\AspectAG\ all children are put in a record, each position containing an
attribution. In previous versions of \AspectAG\ terminals where directly put as a
children instead of an attributions. This was possible since at type-level this
records were essentialy untyped. We decided to lift the shape of the structure
to kinds, adding up static guarantees, but losing this flexibility.
There are at least two approaches to treat terminals,
of which we choose the second for simplicity:

\begin{itemize}
\item
  |ChAttsRec| could be a record containing a promoted sum type, each child is
  either a terminal, or a nonterminal with an index attribution of kind |[(Att,
    Type)]|. At term level, constructors for inhabitants can be build using a
  GADT.

\item
  Model all children as a record of attributions, with a trivial
  attribution containing only one attribute for the terminal case.
\end{itemize}

As seen before, to introduce an attribute the user defines a unique name (a
label). As we say, there is a trivial attribute for each terminal. To chose a
name is not a problem since it is isolated behind a children. Accordingly,
semantic functions of the children can be coded in a polymorphic way.

> class SemLit a where
>   sem_Lit :: a -> Attribution ('[] :: [(Att,Type)])
>                -> Attribution [( 'Att "term" a , a)]
>   lit     :: Label ('Att "term" a)

> instance SemLit a where
>   sem_Lit a _ = (Label .=. a) *. emptyAtt
>   lit         = Label @ ('Att "term" a)

All of them are labelled with the attribute named |"Term"|, accesible using
the |lit| expression, and the semantic function simply wraps a value in an
attribution.

