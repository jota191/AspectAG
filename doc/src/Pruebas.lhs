> {-# LANGUAGE DataKinds            #-}
> {-# LANGUAGE FlexibleContexts     #-}
> {-# LANGUAGE GADTs                #-}
> {-# LANGUAGE KindSignatures       #-}
> {-# LANGUAGE PatternSynonyms      #-}
> {-# LANGUAGE Rank2Types           #-}
> {-# LANGUAGE ScopedTypeVariables  #-}
> {-# LANGUAGE TypeFamilies         #-}
> {-# LANGUAGE TypeOperators        #-}
> {-# LANGUAGE FlexibleInstances     #-}
> {-# LANGUAGE UndecidableInstances  #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE PolyKinds #-}



> module Pruebas where
> import GHC.TypeLits


> data Vec :: Nat -> * -> * where
>   VZ :: Vec 0 a
>   VS :: a -> Vec n a -> Vec (n+1) a

> vHead :: Vec (n+1) a -> a
> vHead (VS a _) = a

> vTail :: Vec (n+1) a -> Vec n a
> vTail (VS _ as) = as :: Vec n a
