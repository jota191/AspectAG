> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE AllowAmbiguousTypes #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE UndecidableInstances #-}
 
> import Data.Kind
> import GHC.TypeLits
> import Data.Proxy

I'll build a datatype to represent records (we are not controlling
uniqueness of labels, not important)

> data Tagged (l :: Symbol) v = Tagged v

> infixr 3 `Cons`
> data REC (r :: [(Symbol, Type)]) :: Type where
>   Emp  :: REC '[]
>   Cons :: Tagged l v -> REC r -> REC ( '(l,v) ': r)

Now, consider a polymorphic function such as |head|.

> f1 = Tagged @"1" head
> f2 = Tagged @"2" head
> f3 = Tagged @"3" head

> r1 = f1 `Cons` f2 `Cons` f2 `Cons` Emp


> infixr 3 `Con`
> data SymbolList (l :: [Symbol]) :: Type where
>   Nil  :: SymbolList '[]
>   Con :: Proxy s -> SymbolList l -> SymbolList (s ': l)


> class SameLength' (es1 :: [k]) (es2 :: [m])

> instance (es2 ~ '[]) => SameLength' '[] es2
> instance (SameLength' xs ys, es2 ~ (y ': ys)) => SameLength' (x ': xs) es2

 > instance SameLength' '[] '[]
 > instance (SameLength' xs ys) => SameLength' (x ': xs) (y ': ys)



> class
>   SameLength' l t
>   =>
>   Generate (t :: [Type]) (l :: [Symbol]) where
>   type GenerateR t l :: [(Symbol, Type)]
>   generate :: SymbolList l -> Proxy t -> REC (GenerateR t l)

> instance
>   Generate '[] '[] where
>   type GenerateR '[] '[] = '[]
>   generate _ _ = Emp

> instance
>   Generate ts l
>   =>
>   Generate (t ': ts) (s ': l) where
>   type GenerateR (t ': ts) (s ': l) =
>     '(s, [t] -> t) ': GenerateR ts l
>   generate (Con (p :: Proxy s) (ps :: SymbolList l)) (t :: Proxy (t ': ts))=
>     ((Tagged head) :: Tagged s ([t] -> t)) `Cons` (generate @ts @l ps Proxy)


> l = Proxy @"1" `Con` Proxy @"2" `Con` Nil
> hds = generate l (Proxy @ '[Int, Char])

> hds' = generate l Proxy -- works!

hds' :: REC '[ '("1", [y1] -> y1), '("2", [y2] -> y2)]

This works because of the SameLength constraint defined exactly this way.
