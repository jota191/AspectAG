\section{Introduction}

%% Higher order functions such as |foldr| are powerful abstraction tools for the
%% functional programmer. Given a datatype we capture the structural recursion
%% scheme by giving a function for each constructor to combine contained data and
%% recursive calls. From the algebraic perspective the programmer must provide an
%% \emph{algebra} capturing semantics for the grammar -or datatype, note that there
%% is a correspondence between both formalisms- and the \emph{catamorphism} builds
%% the computation. In practice, however, when constructing real world compilers
%% many problems arise. Abstract syntax trees tend to have a lot of alternatives
%% (meaning huge algebras), some information must flow top down, and many -maybe
%% non-orthogonal- alternative semantics are actually employed (well formedness
%% properties, type checking, program transformation, evaluation, among others).
%% Also, it is common for syntax to evolve over time when new constructs are added
%% to the language, breaking every algebra on an implementation.

%% More generally, given a functional program it is easy to extended it by defining
%% new functions. However, extending data (e.g. if a datatype is extended with a
%% new case construct) is not easy. Each case expression where a value of this type
%% is matched has to be inspected and modified accordingly. On the other side,
%% object oriented programing is good to define new data: one could implement
%% algebraic datatypes with a composite design pattern, and simply add a new class.
%% However, to define a new function for a data type, we have to inspect all the
%% existing subclasses and add a new method. This problem was first noted by
%% Reynolds\cite{REYNOLDS75B} and later referred to as “the expression problem” by Wadler
%% \cite{ExpressionProblem}. Attribute grammars offer an aproach to solve this
%% issue.

Attribute Grammars (AGs, for short) were originally introduced to describe
semantics for context free languages\cite{Knuth68semanticsof}. Given a grammar,
attributes are associated to each production. Attribute values are computed
according to semantic rules given by the implementator in every node of the
abstract syntax tree in terms of the attribute values of the children and the
parent. Usually attributes are classified in at least two sets: synthesized
attributes (where information flows bottom up) and inherited attibutes (where it
flows top down). AGs prove that they are not only useful to implement
programming language semantics, but as a general purpose programming paradigm.

Domain Specific Languages (DSLs) are a useful abstraction tool to solve problems
using specialized domain terms. DSLs can be implemented as a standalone language
introducing a full compiler toolchain, or embedded as a library in a host
language (Embedded DSLs, EDSLs for short). The latter approach has some
advantages. All constructs of the host language and its libraries are avaiable
to users. Also, the amount of work required compared to the standalone approach
is minimal. In higher order functional programming languages such as Haskell,
the embedded approach is common and succesfull. However, one big drawback is
that since the EDSL is simply a library, when type errors occur they don't
refer to domain terms, and they leak implementation details. This breaks all the
abstraction mechanism that the technique introduces.

\AspectAG\ is an EDSL implementing first class attribute grammars firstly
introduced by Viera in 2009 \cite{Viera:2009:AGF:1596550.1596586}. It uses
extensible polymorphic records and predicates encoded using old fashioned type
level programming to ensure well formedness of AGs at compile time. Type errors
were of course a weakness, aggravated by the fact that an AG is a structure that
can be easily illformed. For instance, for the grammar implementator it is a
common mistake to try to use attributes that are not defined in some production.
Moreover, at that time type level programming was really ad-hoc, exploiting
extensions originally introduced for other uses. In particular, at type level,
programming was essentialy untyped.

With recent additions to GHC this issues can be tackled. We propose a reworked
version of \AspectAG. Modern type level programming techniques allowed us to do
that strongly typed at type level (we say, strongly kinded), and to manipulate
type errors to show precise messages when they occur.

The structure of the rest of the paper is as follows: In section
\ref{sec:example} we present the EDSL using an example, including some error
cases with their messages. In section \ref{sec:records} we make a summary of
some techniques we used. There we propose a methodology to manage type errors.
In section \ref{sec:aag} we present some implementation details. After, we
discuss some related work and conclussions.
