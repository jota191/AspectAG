
> {-# LANGUAGE DataKinds,
>              TypeOperators,
>              PolyKinds,
>              GADTs,
>              TypeInType,
>              RankNTypes,
>              StandaloneDeriving,
>              FlexibleInstances,
>              FlexibleContexts,
>              ConstraintKinds,
>              MultiParamTypeClasses,
>              FunctionalDependencies,
>              UndecidableInstances#-}

> import Data.Kind 
> import Data.Type.Equality (type (==))


An attribution will be a map from attribute names to attribute values,
where names are labels purely phantom.
So we must code strongly type heterogeneous records.

TODO:

\begin{itemize}
  \item  explain why Attribution and not Record
  \item  explain why a fresh implementation instead of doing it over lists
\end{itemize}


