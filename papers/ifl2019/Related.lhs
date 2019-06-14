Attribute grammars encoded in functional languages have a long history, starting
with Johnson \cite{652508}. 


Related to Haskell, the {\tt uuagc} (Uthrech University Attribute Grammar
Compiler) is probably the most well known example. 

First class implementations of Attibute grammars in Haskell were introduced by
Moor \cite{Moor99first-classattribute} with a lightweight approach missing from
type safety. Viera \emph{et al} \cite{Viera:2009:AGF:1596550.1596586} in the
original design og \AspectAG\ introduced a type safe approach. Other embedded
implementations existed \cite{DBLP:phd/ethos/Balestrieri15}. Error messages were
a weakness. Also, we push a towards the direction of type safety making types
strongly kinded. \cite{DBLP:conf/ifl/VieraBP18}

Other embedded implementations \cite{DBLP:conf/ifl/VieraBP18} solve the type
diagnostic problem at the cost of making it staged.

Managing type errors on EDSLs is an old problem to the community and an active
research area. The idea of transforming a typing problem into a constraint
problem is not recent \cite{10635_42131, improvingtypeerror}.

Compiler support added with the |TypeError| was essential, but further support
would be desirable, in particular to control class constraint solving and avoid
leaks an non readable messages. Research by Heeren
{DBLP:phd/basesearch/Heeren05} was implemented it for the Helium compiler.
Recently, Serrano Mena \emph{et al} \cite{DBLP:phd/basesearch/Serrano18,
  DBLP:conf/ifl/SerranoH17} developed a set of techniques for customizing type
error diagnosis gor GHC. Unfortunately this implementation was not merged in
main tree.






