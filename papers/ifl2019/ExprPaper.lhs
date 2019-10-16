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

Higher order functions such as |foldr| are powerful abstraction tools for the
functional programmer. Given a datatype we capture the structural recursion
scheme by giving a function for each constructor to combine contained data and
recursive calls. From the algebraic perspective the programmer must provide an
\emph{algebra} capturing semantics for the grammar -or datatype, note that there
is a correspondence between both formalisms- and the \emph{catamorphism} builds
the computation. In practice, however, when constructing real world compilers
many problems arise. Abstract syntax trees tend to have a lot of alternatives
(meaning huge algebras), some information must flow top down, and many -maybe
non-orthogonal- alternative semantics are actually employed (well formedness
properties, type checking, program transformation, evaluation, among others).
Also, it is common for syntax to evolve over time when new constructs are added
to the language, breaking every algebra on an implementation.

More generally, given a functional program it is easy to extended it by defining
new functions. However, extending data (e.g. if a datatype is extended with a
new case construct) is not easy. Each case expression where a value of this type
is matched has to be inspected and modified accordingly. On the other side,
object oriented programing is good to define new data: one could implement
algebraic datatypes with a composite design pattern, and simply add a new class.
However, to define a new function for a data type, we have to inspect all the
existing subclasses and add a new method. This problem was first noted by
Reynolds\cite{REYNOLDS75B} and later referred to as “the expression problem” by Wadler
\cite{ExpressionProblem}. Attribute grammars offer an aproach to solve this
issue.

Attribute grammars were originally introduced to describe semantics for context
free languages\cite{Knuth68semanticsof}. Given a grammar, we associate
attributes to each production. Attribute values are computed from semantic rules
given by the implementator in every node of the abstract syntax tree in terms of
the attribute values of the children and the parent. Usually attributes are
classified in at least two sets: synthesized attributes (where information flows
bottom up) and inherited attibutes (where it flows top down).

Attribute grammars prove that they are not only useful to implement programming
language semantics, but as a general purpose programming paradigm. Pitifully an
attribute grammar is an example of a structure that can be easily illformed. It
is a common mistake to try to use attributes that are not defined in some
production.

We propose a library of first class strongly typed attribute grammars. We check
well formedness at compile time, and show precise error messages when they
occur. In section \ref{sec:example} we present the EDSL using an example.
In section \ref{sec:records} we summary some techniques we used.
In section \ref{sec:aag} we present some implementation details.


\section{Overview of the library}
\label{sec:example}

As a running example consider a simple expression language given by the following grammar,
including integer values (|ival|), variables (|vname|) and addition:

<  expr    ->  ival
<  expr    ->  vname
<  expr    ->  expr_l + expr_r


To keep it simple, we cannot bind variables with this constructs for now. Let us
assume that they actually denote some value clear from a given context. For
example, a concrete expression $x + 5 + 2$, evaluates to $9$ given the context
$\{x = 2\}$.

We have introduced one non-terminal, called |expr|, with three productions.
|ival| and |vname| are names for terminals, with types |Integer| and |String|,
respectively. We say they are \emph{children} in their productions. The third
production rewrites a non-terminal into two non-terminals. Each child has a
different name, to be able to refer to it unambiguously.

In our embedded DSL this grammar is declared as follows. Declare one non-terminal:

> type Nt_Expr = 'NT "Expr"
> expr = Label @ Nt_Expr

with three productions:

> type P_Add = 'Prd "p_Add" Nt_Expr
> add = Label @ P_Add

> type P_Val = 'Prd "p_Val" Nt_Expr
> val = Label @ P_Val

> type P_Var = 'Prd "p_Var" Nt_Expr
> var = Label @ P_Var

Declare four different children:

> leftAdd
>   = Label @ ('Chi "leftAdd" P_Add  ('Left Nt_Expr))
> rightAdd
>   = Label @ ('Chi "rightAdd" P_Add  ('Left Nt_Expr))
> ival
>   = Label @ ('Chi "ival" P_Val ('Right ('T Int)))
> vname
>   = Label @ ('Chi "vname" P_Var ('Right ('T String)))

%This is simpler than it seems.
Non-terminals are defined by names (like |"Expr"|). Note that we are using a
promoted |String| here, the kind |Symbol| in modern Haskell. Productions are
also identified by a name, and are related to a non-terminal. Children are once
again names, tied to a production and |Either| a non-terminal or a terminal.
Everything is wrapped on constructors of simple algebraic datakinds\footnote{for
  the rest of the paper, we say datakind when we refer to promoted datatypes},
since we implement everything strongly typed both at term level, and at type
level. |Label| is actually a |Proxy| with an alternative name adecuated to our
domain. Everything is defined at type-level but we will use this proxies as
carriers of type information, a widely used idiom in type-level programming.


The abstract syntax tree for this grammar can be implemented in Haskell,
for example, with the datatype:

> data Expr  =  Val  { ival'                 :: Int  }
>            |  Var  { vname'                :: String   }
>            |  Add  { leftAdd', rightAdd'   :: Expr     }
%
%if False
>       deriving Show
%endif
%
where the previous example expression is represented with the value:

|Add (Add (Var "x") (Val 5)) (Val 2)|.

In our library we provide some Template
Haskell\cite{Sheard:2002:TMH:636517.636528} functions that can be used to
generate the grammar definition (non-terminals, productions and children) out of
a datatype representing the abstract syntax tree (e.g. |Expr|). However, our
grammar representation is independent of such datatypes, which is actually
useful to solve the expression problem, as we shall discuss later.

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
> evalExpr e m =  sem_Expr asp e (env =. m .*. emptyAtt) #. eval {-"\label{line:evalExpr} "-}
\numbersoff
\caption{Evaluation Semantics}\label{fig:eval}
\end{figure*}


Attribute grammars decorate the productions of context-free grammars with
\emph{attribute} computations, in order to provide semantics to such grammars.
In our example the semantics consist on the denotation of the expressions. To
define the semantics we can use two attributes: |eval| to represent the result
of the evaluation and |env| to distribute the context defining semantics for
variables. In the rest of this subsection we will show how such semantics can be
implemented using the library, as shown in Figure~\ref{fig:eval}. In lines
\ref{line:eval} and \ref{line:env} we declare the attributes, specifying their
types.

% Time to define semantics.
The attribute |eval| denotes the value of an
expression. Attributes like this, where the information we compute flows
from the children to their parent productions, are called \emph{synthesized
attributes}.

On the |add| production (Line~\ref{line:add_eval}) we compute |eval| as the sum
of the denotation of subexpressions. On each subexpression there is a proper
attribute |eval| that contains its value. The function |syndefM| defines
synthesized attributes. It takes an attribute (for wich the semantics are being
defined), a production (where it is being defined), and the proper definition.

Using the applicative interface\cite{applicative}, we take the values of |eval| at children
|leftAdd| and |rightAdd|, and combine them with the operator |(+)|.
With the notation |at leftAdd eval|, we take from the collection of synthesized attributes of
the child |leftAdd| the attribute |eval|.
We call these collections of attributes \emph{attributions}.


At |val| production, where the grammar rewrites to a terminal, the value of that
terminal corresponds to the semantics of the expression. In terms of our
implementation (Line~\ref{line:val_eval}) the attribute |eval| is defined at
|val| as the value of the terminal |ival|. |ter| is simply a reserved keyword in
our EDSL.

Finally on variables (Line~\ref{line:var_eval}), the expression denotes the
value of the variable on a given context. We lookup a variable, with the name of
the terminal |vname|, into the environment provided by the attribute |env|. The
name |lhs| indicates that we receive the attribute from the parent. Attributes
like |env|, that flow in a top-down way, are called \emph{inherited attributes}.


We combine all these rules on an \emph{aspect} in Line~\ref{line:aspEval}.
Before understanding what is going on with this |traceAspect| wrapper, lets say
that the operator |(.+:)| is simply a combinator that adds a rule to an aspect
(it associates to the right). In our EDSL domain an aspect is a collection of
rules. Here we build an aspect with all the rules for a given attribute, but the
user can combine them in the way she wants (for example, by production). Aspects
can be orthogonal to one another, or not. Here |aspEval| clearly depends on an
attribute |env| with no rules attached to it at this point, so it is not -yet-
useful at all. We cannot complain here yet since the rules for |env| could be
defined later (as we will do), or perhaps in another module! If we try to
actually use |aspEval| calling it on a semantic function, there will be a type
error, but it will be raised on the semantic function application. The function
|traceAspect|, and also -implicitly- each application of |syndefM| tag
definitions to show them on type errors. This is useful to have a hint where the
error was actually introduced. Users are encouraged to use tags, but they are
optional.

For the inherited attribute |env| we provide the |inhdefM| combinator, which
takes an attribute name, a production where the rule is being defined, and a
child for what the information is being distributed. In our example |env| is
copied to both children on the |add| production, so we build one rule for each
(lines \ref{line:add_leftAdd_env} and \ref{line:add_rightAdd_env}),
and combine them on an aspect in Line~\ref{line:aspEnv}.

We can combine aspects with the |(.:+:)| operator.
In Line~\ref{line:asp} we combine |aspEval| and |aspEnv|,
to get the aspect with all the attributes needed for the evaluation semantics.
Note that this time we decided not to add a new tag.

Finally, given an implementation of the abstract syntax tree, like |Expr|, we can
encode (or derive with Template Haskell) the \emph{semantic function}.

> sem_Expr asp (Add l r)  = knitAspect add asp
>                 $    leftAdd   .=. sem_Expr asp l
>                 .*.  rightAdd  .=. sem_Expr asp r
>                 .*.  EmptyRec
> sem_Expr asp (Val i)    = knitAspect val asp
>                 $    ival   .=. sem_Lit i
>                 .*.  EmptyRec
> sem_Expr asp (Var v)    = knitAspect var asp
>                 $    vname  .=. sem_Lit v
>                 .*.  EmptyRec
%
|sem_Expr| takes an aspect, an
AST and an initial attribution (with the inherited attributes of the root)
and computes semantics for this expression.
The result is an attribution with all the synthesized attributes of the root. We
can define an evaluator, like the one in Line~\ref{line:evalExpr},
that takes an environment |m| mapping variable names to |Int|s.
For example, the following expression evaluates to |9|.
< evalExpr  (Add (Add (Var "x") (Val 5)) (Val 2))
<           (insert "x" 2 empty)
%
\subsection{Semantic Extension: Adding and Modifying attributes}

Defining alternative semantics or extending the already defined ones is simple.
 For example, suppose that we want to collect the integral literals
occurring on an expression. Define an attribute |lits|:

> lits  = Label @ ('Att "lits"  [Int])

And the rules to compute it. This time we combine them on the fly:

> aspLits  =    syndefM lits add  ((++)   <$>  at leftAdd lits
>                                         <*>  at rightAdd lits)
>          .+:  syndefM lits val  ((:[])  <$>  ter ival)
>          .+:  syndefM lits var  (pure [])
>          .+:  emptyAspect

The function:

> litsExpr e = sem_Expr aspLits e emptyAtt #. lits

returns a list of all literals occurring in the expression, in order.

It is also possible to modify semantics in a modular way.
As an example, to get the literals in the reverse order
we can extend the original aspect |aspLits| with a rule
that redefines the computation of |lits| for the production |add|
in this way.
> aspLitsRev  =    synmodM lits add ((++)  <$>  at rightAdd lits
>                                          <*>  at leftAdd lits)
>             .+:  aspLits 
%
Notice that in this case we used |synmodM| instead of |syndefM|.
The |mod| variants of the combinators |syndefM| and |inhdefM|
modify an existing attribute instead of defining a new one.

\subsection{Grammar extension: Adding Productions}


To completely tackle the expression problem we must be able to extend our grammar.
Suppose that we add a new production to bind local definitions:

< expr     -> let vname = expr_d in expr_i

We implement them with this definition:

> type P_Let = 'Prd "p_Let" Nt_Expr
> elet = Label @ P_Let

This new production has three children

> exprLet   = Label @ ('Chi "exprLet"   P_Let
>                                       ('Left Nt_Expr))
> bodyLet   = Label @ ('Chi "bodyLet"   P_Let
>                                       ('Left Nt_Expr))
> vlet      = Label @ ('Chi "vlet"      P_Let
>                                       ('Right ('T String)))

We extend the aspects with the definitions of
the attributes for the new production.

> aspEval2  =  traceAspect (Proxy @ ('Text "eval2"))
>           $  syndefM eval elet (at bodyLet eval) .+: aspEval


> aspEnv2
>   =    traceAspect (Proxy @ ('Text "env2"))
>   $    inhdefM env elet exprLet (at lhs env)
>   .+:  inhdefM env elet bodyLet (insert   <$>  ter vlet
>                                           <*>  at exprLet eval
>                                           <*>  at lhs env)
>   .+:  aspEnv
%
%
And again combine them.

> asp2 = aspEval2 .:+: aspEnv2

Since we are not tied to any particular datatype implementation, we can now
define the semantic functions for another datatype (e.g. |Expr'|) which includes
the new production.

\subsection{Error Messages}

When dealing with type-level programming, type error messages are usually very
difficult to understand, often leaking implementation details. Our library was
designed to provide good, DSL-oriented error messages for the mistakes an AG
programmer may make. In this subsection we show some examples of such error
messages.


A possible error when defining an attribute, is to have type errors
in the expressions that define the computation.
For example if in Line~\ref{line:add_eval} we use an attribute of different
type than the expected (|env| instead of |eval|):
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
Similar messages are obtained if the expression has other internal type errors,
like writing |pure (2 + False)|.


Another possible error is to define a computation that returns
a value of a different type than the type of the attribute.
For example, if in Figure~\ref{fig:eval}, instead of Line~\ref{line:var_eval}
we have the following declaration that uses |lookup| instead of |slookup|:
%
< var_eval  =  syndefM eval var
<           $  lookup <$> ter vname <*> at lhs env
%
we get the error:
\begin{Verbatim}[fontsize=\small]
Error: Int /= Maybe Int
trace: syndef( Attribute eval:Int
             , Non-Terminal Expr::Production p_Var)
\end{Verbatim}
%
expressing that we provided a |Maybe Int| where an |Int| was expected.
There is also some \verb"trace" information, showing the context where
the error appears.
In this case it is not necessary, since the source of the error and the place where
the error is detected are the same. But we will see later in this section some
examples where this information will guide us to the possible source of an
error that is produced in a later stage.


A more AG-specific error is to try to access to a child
that does not belong to the production where we are defining the attribute.
If we modify Line~\ref{line:add_eval} with the following code:
< add_eval  =  syndefM eval add  $ ter ival
%
where we use the child |ival| that does not belong to the production |add|.
In this case the error points to |ter ival|, and says:
%
\begin{Verbatim}[fontsize=\small]
Error: Non-Terminal Expr::Production p_Val
       /=
       Non-Terminal Expr::Production p_Add
trace: syndef( Attribute eval:Int
             , Non-Terminal Expr::Production p_Add)
\end{Verbatim}
%
expressing that the production of type |p_Val| (of the non-terminal |Expr|) is
not equal to the expected production of type |p_Add| (of the non-terminal |Expr|).

Another mistake, similar to the previous one, is to treat a non-terminal as a terminal,
or the other way around.
Then, if we use |ter| to get a value out of the child |leftAdd|:
< add_eval  =  syndefM eval add  $ ter leftAdd
%
We obtain a message indicating that the child
(belonging to the production |p_Add| of the non-terminal |Expr|) is a non-terminal (|Expr|),
and not a terminal of type |Int| as it was expected:
%
\begin{Verbatim}[fontsize=\small]
Error: Non-Terminal Expr::Production p_Add
       ::Child leftAdd:Non-Terminal Expr
       /=
       Non-Terminal Expr::Production p_Add
       ::Child leftAdd:Terminal Int
trace: syndef( Attribute eval:Int
             , Non-Terminal Expr::Production p_Add)
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
Error: Non-Terminal Expr::Production p_Val
       ::Child ival:Terminal Int
       /=
       Non-Terminal Expr::Production p_Val
       ::Child ival:Non-Terminal n0
trace: syndef( Attribute eval:Int
             , Non-Terminal Expr::Production p_Val)
\end{Verbatim}


Now suppose we have an attribute |foo|, of type |Int|,
but without any rules defining its computation,
and we use it in the definition of the rule |add_eval|:
< add_eval  =  syndefM eval add  $ (+)  <$>  at leftAdd eval
<                                       <*>  at rightAdd foo
%
At this point this is not an error, because this rule can
be combined into an aspect where this attribute is defined.
However, it becomes an error at Line~\ref{line:evalExpr},
where we finally try to evaluate the incomplete aspect |asp|.
\begin{Verbatim}[fontsize=\small]
Error: Field not Found on Attribution
       looking up Attribute foo:Int
trace: syndef( Attribute eval:Int
             , Non-Terminal Expr::Production p_Add)
       aspect eval
\end{Verbatim}
Notice that in this case the trace guides us to the place
where the unsatisfied rule is defined:
the synthesized attribute |eval| at the production |p_Add| (Line~\ref{line:add_eval}),
into the aspect |eval| (Line~\ref{line:aspEval}).

Another case where the trace is helpful in the task of finding
the source of an error, is when we define a duplicated attribute. 
For example, if add |add_eval| twice when defining |aspEval| at  Line~\ref{line:aspEval}.
%
< aspEval   =    traceAspect (Proxy @ ('Text "eval"))
<           $    add_eval .+: add_eval 
<           .+:  val_eval .+: var_eval .+: emptyAspect
%
Due to some flexibility matters that will become more clear in the next section,
we can not detect this error at this point.
The error appears again at Line~\ref{line:evalExpr}, when we close the AG:
\begin{Verbatim}[fontsize=\small]
Error: Duplicated Labels on Attribution
       of Attribute eval:Int
trace: aspect eval
\end{Verbatim}
However, the trace information says that the duplication was generated when we
defined the aspect |eval|; i.e. Line~\ref{line:aspEval}. 
