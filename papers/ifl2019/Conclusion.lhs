
In this paper we presented a library of first class strongly kinded attribute
grammars. Using type level programming we achieved to get precise domain
specific type errors, although we did not completely avoid implementation leaks.

%% We inherite all the advantages of an embedding. All Haskell ecosystem and
%% language features are avaiable to the user when implementing grammars.

%% Even though Template Haskell functions are provided to scrap some boilerplate,
%% the library can be used as a pure embedding within the host language, with no
%% preprocessing or postprocessing. This represents an advantage since a staged
%% compilation makes interactive development and debugging difficult.


Grammars do not need to be tied to a datatype. Reusing an AG in a new datatype
when a language is extended is nice, but the semantic function must be
implemented (or derived) twice. This is not a problem of our implementation, but
of Haskell's expresiveness. To explore how to integrate our library with
extensible datatypes is left as an open problem.

We think the library is useful and easy to use. Having the DSL embedded in
Haskell allows to develop furher abstractions, such as common patterns, or
macros, or to use the power of higher order to generate grammars. In addition to
the examples we have coded during the development, it is being tested with
success in the implementation of a real compiler of a non trivial functional
language.

To get clear error messages we had to deal with some tradeoffs. It requires
careful management of context information annotated in types, and explicit term
level proxy arguments to carry type information during type checking.
Nevertheless, this implementation details are transparent to the user. By
strongly typing we have lost some flexibilities. For example, rules are related
to a production, this was not designed this way in previous versions of
\AspectAG, which allowed us to reuse some rules out of the box. Anyway, this can
be shallowed since the host language provides type -and kind- polymorphism.

We developed a methodology to manage error message generation using |Requirements|.
We think this idea can be applied similarly in other EDSL implementations.
