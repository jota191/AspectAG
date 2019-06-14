\section{Introduction}

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


