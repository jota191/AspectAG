%if False

> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE
>              TypeFamilies,
>              FlexibleContexts,
>              ScopedTypeVariables,
>              NoMonomorphismRestriction,
>              ImplicitParams,
>              ExtendedDefaultRules,
>              UnicodeSyntax,
>              DataKinds,
>              TypeApplications,
>              PartialTypeSignatures,
>              AllowAmbiguousTypes
> #-}

> module ExprPaper where

> import System.Exit (exitFailure)
> import Language.Grammars.AspectAG
> import Control.Monad
> import Control.Applicative hiding (empty)
> import Data.Proxy
> import GHC.TypeLits
> import Data.Map
> import Data.Maybe
> import Debug.Trace
> import Prelude hiding (lookup)

%endif

\newcommand{\alb}[2]{\textcolor{blue}{\textbf{Alb: #1} #2}}

\section{Overview of the library}
\label{sec:example}

In this section we explain the main features of the library by means of an example.
We start with a simple expression language formed by integer values, variables and addition,
which we then extend syntactically and semantically in order to show the different operations supported by the library.

\subsubsection*{Grammar declaration} 
The abstract syntax of the expression language is given by the following grammar:

<  expr    ->  ival
<  expr    ->  vname
<  expr    ->  expr_l + expr_r

%To keep it simple, we cannot bind variables with this constructs for now. Let us
%assume that they actually denote some value clear from a given context. For
%example, a concrete expression $x + 5 + 2$, evaluates to $9$ given the context
%$\{x = 2\}$.

%We have introduced one non-terminal, called |expr|, with three productions.

\noindent
 where |ival| and |vname| are terminals corresponding to integer values and
 variable names (given by strings), respectively. Both are said to be
 \emph{children} in their productions. The third production has two children
 of type |expr|, which we name with an index to refer them unambiguously.

In our EDSL this grammar is declared as follows.
First, we declare the non-terminal for our language:

> type Nt_Expr = 'NT "Expr"
> expr = Label @ Nt_Expr

\noindent
Non-terminals are types. They are built by a promoted algebraic datatype
constructor |'NT| (we say, an algebraic datakind) applied to a name (|"Expr"|).
Names are types of kind |Symbol|, the kind of promoted string symbols in modern
Haskell. At term level we define an expression using the |Label| constructor.
|Label| is a proxy type, with an appropiate name according to our domain instead
of the usual |Proxy|. We use the \texttt{TypeApplications} extension of GHC to
associate the type information to the label. The ``@@'' symbol above is a visible
type application.

 Productions are also identified by a name, and are related to a non-terminal,
 once again using algebraic datakinds.

> type P_Add = 'Prd "Add" Nt_Expr
> add = Label @ P_Add
> type P_Val = 'Prd "Val" Nt_Expr
> val = Label @ P_Val
> type P_Var = 'Prd "Var" Nt_Expr
> var = Label @ P_Var


The last ingredient of the grammar declaration is given by the introduction of
the children that occur in the productions.

> leftAdd   = Label @ ('Chi "leftAdd"   P_Add  ('Left Nt_Expr))
> rightAdd  = Label @ ('Chi "rightAdd"  P_Add  ('Left Nt_Expr))
> ival      = Label @ ('Chi "ival"   P_Val  ('Right ('T Int)))
> vname     = Label @ ('Chi "vname"  P_Var  ('Right ('T String)))


\noindent
Each child has a name, is tied to a production and can be either a non-terminal
or a terminal, in the latter case we include the type of values it
denotes (e.g. |('T Int)|).

Summing up the information just provided, we can see that our grammar declaration indirectly contains all the ingredients that take part in the datatype representation of its ASTs:

%The abstract syntax tree for this grammar can be implemented in Haskell,
%for example, with the datatype:

> data Expr  =  Val  Int |  Var  String |  Add  Expr Expr
%
%if False
>       deriving Show
%endif
%
%where the previous example expression is represented with the value:

%|Add (Add (Var "x") (Val 5)) (Val 2)|.

plus a set of names used to name explicitly each component.
An important thing
to notice is that the grammar representation is independent of this datatype.


We provide Template Haskell~\cite{Sheard:2002:TMH:636517.636528} functions that
can be used to generate all the \emph{boilerplate} defined above, as
follows:

> $(addNont "Expr")
> $(addProd "Val" ''Nt_Expr  [  ("val", Ter ''Int)])
> $(addProd "Add" ''Nt_Expr  [  ("leftAdd",   NonTer ''Nt_Expr),
>                               ("rightAdd",  NonTer ''Nt_Expr)])

Notice that the use of Template Haskell is purely optional, \AspectAG\ can be
used as an EDSL with neither preprocessing nor postprocessing of the source code.

\begin{figure*}
\numberson
> eval  = Label @ ('Att "eval" Int)               {-"\label{line:eval} "-}
> env   = Label @ ('Att "env"  (Map String Int))  {-"\label{line:env} "-}
> {-" "-}
> add_eval  =  syndefM eval add $  (+) <$> at leftAdd eval <*> at rightAdd eval {-"\label{line:add_eval} "-} 
>
> val_eval  =  syndefM eval val $  ter ival                                     {-"\label{line:val_eval} "-}
>
> var_eval  =  syndefM eval var $  slookup <$> ter vname <*> at lhs env         {-"\label{line:var_eval} "-}
>    where slookup nm = fromJust . lookup nm
> {-" "-}
> aspEval   =  traceAspect (Proxy @ ('Text "eval")) $  add_eval .+: val_eval .+: var_eval .+: emptyAspect {-"\label{line:aspEval} "-}
> {-" "-} 
> add_leftAdd_env   = inhdefM env add leftAdd   $ at lhs env   {-"\label{line:add_leftAdd_env} "-}
> add_rightAdd_env  = inhdefM env add rightAdd  $ at lhs env   {-"\label{line:add_rightAdd_env} "-}
> {-" "-}
> aspEnv  =  traceAspect (Proxy @ ('Text "env")) $  add_leftAdd_env .+: add_rightAdd_env .+: emptyAspect  {-"\label{line:aspEnv} "-}
> {-" "-}
> asp = aspEval .:+: aspEnv {-"\label{line:asp} "-}
> {-" "-}
> evalExpr e m  =  sem_Expr asp e rootAtt #. eval {-"\label{line:evalExpr} "-}
>               where rootAtt = env =. m .*. emptyAtt
\numbersoff
\vspace{-0.1in}
\caption{Evaluation Semantics}\label{fig:eval}
\end{figure*}

\subsubsection*{Semantics definition}
With the aim to provide semantics, AGs decorate the productions of context-free
grammars with \emph{attribute} computations. In an expression language as the
one defined, the usual semantics are given by the evaluation semantics. This can
be defined by using two attributes: |eval|, to represent the result of the
evaluation, and |env|, to distribute the environment containing the values for
variables. In the rest of this subsection we explain how the evaluation
semantics can be implemented using our library.

The complete definition is shown
in Figure~\ref{fig:eval}. In lines \ref{line:eval} and \ref{line:env} we declare
the attributes, specifying their types.

The attribute |eval| denotes the value of an expression. Attributes like this,
where the information computed flows from the children to their parent
productions, are called \emph{synthesized attributes}.

On the |add| production (Line~\ref{line:add_eval}) we compute |eval| as the sum
of the denotation of subexpressions. On each subexpression there is a proper
attribute |eval| that contains its value. Attribute |eval| is defined using
function |syndefM|, which is the library operation to define synthesized
attributes. It takes an attribute (the one for which the semantics is being
defined), a production (where it is being defined), and the respective
computation rule for the attribute.

Using an applicative interface, we take the values of |eval| at children
|leftAdd| and |rightAdd|, and combine them with the operator |(+)|. By means of
the operation |at leftAdd eval| we pick up the attribute |eval| from the
collection of synthesized attributes of the child |leftAdd|. We refer to these
collections of attributes as \emph{attributions}.

At the |val| production the value of the terminal corresponds to the semantics
of the expression. In terms of our implementation (Line~\ref{line:val_eval}) the
attribute |eval| is defined as the value of the terminal |ival|. |ter| is simply
a reserved keyword in our EDSL.

Finally, on the |var| production (Line~\ref{line:var_eval}), the expression
denotes the value of the variable on the given environment. We lookup up the
variable, with name given by the terminal |vname|, in the environment provided
by the attribute |env|. The name |lhs| indicates that we receive the |env|
attribute from the parent. Attributes like |env|, that flow in a top-down way,
are called \emph{inherited attributes}. The use of |fromJust| is of course
unsafe. We assume that the environment has an entry for each variable used in
the expression evaluated. Error handling can be treated orthogonally with new
attributes.

We combine all these rules on an \emph{aspect} in Line~\ref{line:aspEval}. The
operator |(.+:)| is a combinator that adds a rule to an aspect
(it associates to the right).
An aspect is a collection of rules. Here we build an aspect with all
the rules for a given attribute, but the user can combine them in the way she
wants (for example, by production). Aspects can be orthogonal among them, or
not. 

Aspects keep all the information of which attributes are computed, and which
children are used, taken from the rules used to build them. All the structure of
the grammar is known at compile time, which is used to compute precise errors.

The function |traceAspect| and also -implicitly- each application of |syndefM|
tag definitions to show more information on type errors. This is useful to have
a hint where the error was actually introduced. For instance, note that that
|aspEval| clearly depends on an attribute |env| with no rules attached to it at
this point, so it is not -yet- useful at all. We cannot decide locally that the
definition is wrong since the rules for |env| could be defined later (as we will
do), or perhaps in another module! If we actually use |aspEval| calling it on a
semantic function there will be a type error but it will be raised on the
semantic function application. Showing the trace is helpful in those scenarios
as we will see in Section~\ref{sec:errors}. Users are encouraged to use tags,
but they are optional.

For the definition of the inherited attribute |env| we use the |inhdefM| combinator, which
takes an attribute name, a production (where the rule is being defined), and a
child to which the information is being distributed. In our example, |env| is
copied to both children on the |add| production, so we build one rule for each child
(lines \ref{line:add_leftAdd_env} and \ref{line:add_rightAdd_env}),
and combine them on an aspect in Line~\ref{line:aspEnv}.

We can combine aspects with the |(.:+:)| operator.
In Line~\ref{line:asp} we combine |aspEval| and |aspEnv|,
to get the aspect with all the attributes needed for the evaluation semantics.
Note that this time we decided not to add a new tag.

Finally, given an implementation of the abstract syntax tree, like the |Expr|
datatype, we can encode a generic
\emph{semantic function}:
%
> sem_Expr asp (Add l r)  = knitAspect add asp
>                 $    leftAdd   .=. sem_Expr asp l
>                 .*.  rightAdd  .=. sem_Expr asp r  .*.  EmptyRec
> sem_Expr asp (Val i)    = knitAspect val asp
>                 $    ival   .=. sem_Lit i          .*.  EmptyRec
> sem_Expr asp (Var v)    = knitAspect var asp
>                 $    vname  .=. sem_Lit v          .*.  EmptyRec
%
Again this definition could be derived automatically using Template Haskell with a
splice:

> $(mkSemFunc ''Nt_Expr)

The semantic function |sem_Expr| takes the aspect,
the AST of an expression, and
an initial attribution
(with the inherited attributes of the root) and computes
the synthesized attibutes.

In the particular case of the evaluation semantics of our example we can define
an evaluator as the one in Line~\ref{line:evalExpr}. using the aspect (|asp|),
the AST of an expression (|e|) and an initial attribution (|rootAtt|). It finally
returns the value of the expression by performing a lookup operation |(#.)| of
the attribute |eval| in the resulting attribution.

%For example, the following expression evaluates to |9|.
%< evalExpr  (Add (Add (Var "x") (Val 5)) (Val 2))
%<           (insert "x" 2 empty)
%

\subsection{Semantic Extension: Adding and Modifying attributes}

Our approach allows the users to define alternative semantics or extending
already defined ones in a simple way. For instance suppose that we want to
collect the integral literals occurring in an expression. We define an attribute
|lits|:

> lits  = Label @ ('Att "lits"  [Int])

and the rules to compute it. This time we combine them on the fly:

> aspLits  =    syndefM lits add  ((++)   <$>  at leftAdd lits
>                                         <*>  at rightAdd lits)
>          .+:  syndefM lits val  ((:[])  <$>  ter ival)
>          .+:  syndefM lits var  (pure [])
>          .+:  emptyAspect

The function

> litsExpr e = sem_Expr aspLits e emptyAtt #. lits

returns a list with the literals occurring in an expression from left to right.

It is also possible to modify a semantics in a modular way.
For instance, to get the literals in the reverse order
we extend the original aspect |aspLits| with a rule
that redefines the computation of |lits| for the production |add|
in this way.
> aspLitsRev  =    synmodM lits add ((++)  <$>  at rightAdd lits
>                                          <*>  at leftAdd lits)
>             .+:  aspLits 
%
Notice that in this case we used |synmodM| instead of |syndefM|. The |mod|
variants of the combinators |syndefM| and |inhdefM| modify an existing attribute
instead of defining a new one, overriding the previous semantic function
definition.

\subsection{Grammar extension: Adding Productions}


% To completely tackle the expression problem we must be able to extend our grammar.
Now let's expand the grammar with a new production to bind local definitions:

< expr     -> let vname = expr_d in expr_i

We implement it with these definition:
%This new production has three children:

> type P_Let = 'Prd "Let" Nt_Expr
> elet = Label @ P_Let
>
> exprLet   = Label @ ('Chi "exprLet"   P_Let  ('Left Nt_Expr))
> bodyLet   = Label @ ('Chi "bodyLet"   P_Let  ('Left Nt_Expr))
> vlet      = Label @ ('Chi "vlet"      P_Let  ('Right ('T String)))

We extend the aspects we had with the definition of
the attributes for the new production:

> aspEval2  =  traceAspect (Proxy @ ('Text "eval2"))
>           $  syndefM eval elet (at bodyLet eval) .+: aspEval
>
> aspEnv2  =    traceAspect (Proxy @ ('Text "env2"))
>          $    inhdefM env elet exprLet (at lhs env)
>          .+:  inhdefM env elet bodyLet (insert   <$>  ter vlet
>                                                  <*>  at exprLet eval
>                                                  <*>  at lhs env)
>          .+:  aspEnv
%
%
and again combine them: 

> asp2 = aspEval2 .:+: aspEnv2

Since we are not tied to any particular datatype implementation, we can now
define the semantic functions for another datatype
%(e.g. |Expr'|)
definition that includes the new production.

\subsection{Error Messages}
\label{sec:errors}
In a EDSL implemented using type-level programming type error messages are hard
to understand and they often leak implementation details. Our library is
designed to provide good, DSL-oriented error messages for the mistakes an AG
programmer may make. We identify four categories of static errors. In this section we list
them and show examples of each one.


\subsubsection{Type errors in attribute expressions}
\label{sec:err1}
When defining an attribute we can have type errors
in the expressions that define the computation.
For example if in Line~\ref{line:add_eval} of  Figure~\ref{fig:eval}
we use an attribute with a different
type than the one expected (|env| instead of |eval|):
%
< add_eval  =  syndefM eval add  $ (+)  <$>  at leftAdd eval
<                                       <*>  at rightAdd env
%
we obtain a |GHC| type error, pointing at this position in the code,
with the message:
%
\begin{Verbatim}[fontsize=\small]
Couldn't match type 'Map String Int' with 'Int'
\end{Verbatim}
%
Similar messages are obtained if the expression has other internal type errors,
like writing |pure (2 + False)|. This is acomplished ``for free'' since
\AspectAG\ is embedded in Haskell, and this kind of error was well reported in
old versions of the library.

\subsubsection{Defining a computation that returns a value of a
different type than the type of the attribute.}
\label{sec:err2}
For example, if in
Figure~\ref{fig:eval} instead of Line~\ref{line:var_eval} we have the following
declaration that uses |lookup| instead of |slookup|:
%
< var_eval  =  syndefM eval var
<           $  lookup <$> ter vname <*> at lhs env
%
we get the error:
\begin{Verbatim}[fontsize=\small]
Error: Int /= Maybe Int
trace: syndef( Attribute eval:Int
             , Non-Terminal Expr::Production Var)
\end{Verbatim}
%
expressing that we provided a |Maybe Int| where an |Int| was expected. There is
also some \verb"trace" information, showing the context where the error appears.
In this case it is not really necessary since the source of the error and the
place where the error is detected are the same. But we will see later in this
section some examples where this information will guide us to the possible
source of an error that is produced in a later stage. This kind of error looks
similar to the previous one from the user's perspective, but it is very
different to us. It requires implementation work. In previous versions of
\AspectAG\ this kind of error could not be detected, since attributes had no
information about their type. Probably the program would fail anyway, possibly
with an error like the one in \ref{sec:err1} somewhere else. Then the programmer
should track where the error was actually introduced.



\subsubsection{References to lacking fields}

This kind of errors are related to the well-formedness of the AG, like trying to
access to a child that does not belong to the production where we are defining
the attribute, trying to lookup attributes that are not there, etc.

For example, if we modify Line~\ref{line:add_eval} with the following code:
< add_eval  =  syndefM eval add  $ ter ival
%
where we use the child |ival| that does not belong to the production |add|.
In this case the error points to |ter ival|, and says:
%
\begin{Verbatim}[fontsize=\small]
Error: Non-Terminal Expr::Production Val
       /=
       Non-Terminal Expr::Production Add
trace: syndef( Attribute eval:Int
             , Non-Terminal Expr::Production Add)
\end{Verbatim}
%
expressing that the production of type |Val| (of the non-terminal |Expr|) is
not equal to the expected production of type |Add| (of the non-terminal |Expr|).

Another example similar to the previous one, is to treat a non-terminal as a terminal,
or the other way around.
Then, if we use |ter| to get a value out of the child |leftAdd|:
< add_eval  =  syndefM eval add  $ ter leftAdd
%
We obtain a message indicating that the child
(belonging to the production |Add| of the non-terminal |Expr|) is a non-terminal (|Expr|),
and not a terminal of type |Int| as it was expected:
%
\begin{Verbatim}[fontsize=\small]
Error: Non-Terminal Expr::Production Add
       ::Child leftAdd:Non-Terminal Expr
       /=
       Non-Terminal Expr::Production Add
       ::Child leftAdd:Terminal Int
trace: syndef( Attribute eval:Int
             , Non-Terminal Expr::Production Add)
\end{Verbatim}
%
Similarly, if we try to treat a terminal as a non-terminal,
changing for example Line~\ref{line:val_eval} by the following:
< val_eval  =  syndefM eval val  $ at ival eval
%
the error says that |ival| is a terminal of type |Int| and
not some non-terminal |n0|:
%
\begin{Verbatim}[fontsize=\small]
Error: Non-Terminal Expr::Production Val
       ::Child ival:Terminal Int
       /=
       Non-Terminal Expr::Production Val
       ::Child ival:Non-Terminal n0
trace: syndef( Attribute eval:Int
             , Non-Terminal Expr::Production Val)
\end{Verbatim}


Now suppose we have an attribute |foo|, of type |Int|,
but without any rules defining its computation,
and we use it in the definition of the rule |add_eval|:
%
< add_eval  =  syndefM eval add  $ (+)  <$>  at leftAdd eval
<                                       <*>  at rightAdd foo
%
At this point this is not an error, because this rule can
be combined into an aspect where this attribute is defined.
However, it becomes an error at Line~\ref{line:evalExpr},
if we finally try to evaluate the incomplete aspect |asp|.
%
\begin{Verbatim}[fontsize=\small]
Error: Field not Found on Attribution
       looking up Attribute foo:Int
trace: syndef( Attribute eval:Int
             , Non-Terminal Expr::Production Add)
       aspect eval
\end{Verbatim}
%
Notice that in this case the trace guides us to the place
where the unsatisfied rule is defined:
the synthesized attribute |eval| at the production |Add| (Line~\ref{line:add_eval}),
into the aspect |eval| (Line~\ref{line:aspEval}).

\subsubsection{Duplication of Fields}
An attribute should not have more than one rule to compute it in a given
production. Also, children are unique.

For instance this kind of error could be introduced if |add_eval| is defined
twice when defining |aspEval| at Line~\ref{line:aspEval}.
%
< aspEval   =    traceAspect (Proxy @ ('Text "eval"))
<           $    add_eval .+: add_eval 
<           .+:  val_eval .+: var_eval .+: emptyAspect
%
Due to some flexibility matters that will become more clear in the next section,
we do not detect this error at this point.

The error appears again at Line~\ref{line:evalExpr}, when we close the AG:
\begin{Verbatim}[fontsize=\small]
Error: Duplicated Labels on Attribution
       of Attribute eval:Int
trace: aspect eval
\end{Verbatim}


This is another case where the trace is helpful in the task of finding the
source of an error. The trace information says that the duplication was
generated when we defined the aspect |eval|; i.e. Line~\ref{line:aspEval}.
