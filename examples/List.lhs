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
>              AllowAmbiguousTypes,
>              RankNTypes,
>              ScopedTypeVariables
> #-}


> module List where

> import Prelude hiding (head, tail, sum, all, length,null, last)

> import Language.Grammars.AspectAG
> import Control.Monad
> import Control.Applicative
> import Data.Proxy
> import GHC.TypeLits
> import Debug.Trace

> type Nt_List = 'NT "List"
> list = Label @ Nt_List

> type P_Cons = 'Prd "Cons" Nt_List
> cons = Label @ P_Cons


> type P_Nil = 'Prd "Nil" Nt_List
> nil = Label @ P_Nil

> head :: forall a . Label ('Chi "head" P_Cons ('Right ('T a)))
> head   = Label

> tail   = Label @ ('Chi "tail"   P_Cons ('Left Nt_List))
> nilCh :: Label ('Chi "nilCh"  P_Nil  ('Right ('T ())))
> nilCh = Label


> sem_List (proxy :: Proxy a) asp (x:xs)
>   = knitAspect cons asp
>   $    head @ a .=. sem_Lit @ a x
>  .*.   tail  .=. sem_List proxy asp xs
>  .*.   EmptyRec
> sem_List (_ :: Proxy a) asp []
>   = knitAspect nil asp
>   $ nilCh  .=. sem_Lit () .*. EmptyRec

> scata :: forall b . Label ('Att "cata" b)
> scata = Label

> asp_cata (Proxy :: Proxy a) f e
>   =   (syndefM (scata @ a) cons $ f <$> ter head <*> at tail (scata @ a))
>   .+: (syndefM (scata @ a) nil $ pure e)
>   .+: emptyAspect

> sum :: [Integer] -> Integer
> sum xs
>   = sem_List (Proxy @ Integer)
>     (asp_cata (Proxy @ Integer) (+) 0) xs emptyAtt #. (scata @ Integer)

> all xs
>   = sem_List (Proxy @ Bool)
>     (asp_cata (Proxy @ Bool) (&&) True) xs emptyAtt #. (scata @ Bool)


> cata :: (a -> b -> b) -> b -> [a] -> b
> cata (f :: a -> b -> b) e xs
>   = sem_List (Proxy @ a) (asp_cata (Proxy @ b) f e) xs emptyAtt #. (scata @ b)


> slen = Label @ ('Att "slen" Integer)

> asp_slen
>   =   syndefM slen cons ((1+) <$> at tail slen)
>   .+: syndefM slen nil (pure 0) .+: emptyAspect

> length xs
>   = sem_List (proxyFrom xs) asp_slen xs emptyAtt #. slen

> sempty = Label @ ('Att "sempty" Bool)
> asp_sempty
>   = syndefM sempty cons (pure False) .+: syndefM sempty nil (pure True) .+: emptyAspect

> null xs = sem_List (proxyFrom xs) asp_sempty xs emptyAtt #. sempty

> sid :: forall a . Label ('Att "sid" [a]) ; sid = Label

> asp_sid
>   = \(Proxy :: Proxy a)
>     ->   syndefM (sid @ a) cons ((:) <$> ter head <*> at tail sid)
>      .+: syndefM (sid @ a) nil (pure []) .+: emptyAspect

> idList (xs :: [a])
>   = sem_List (proxyFrom xs) (asp_sid (proxyFrom xs)) xs emptyAtt #. (sid @ a) -- TODO

If we want to avoid annotations, polymorphic attributes must take a proxy, so in this
case we can apply |proxyFrom|


> slast :: forall a . Label ('Att "slast" a); slast = Label
> asp_slast (Proxy :: Proxy a)
>   = syndefM (slast @ a) cons (
>     do isLast <- at tail sempty
>        case isLast of
>          True  -> ter head
>          False -> at tail slast
>     )
>    .+: syndefM (slast @ a) nil (error "Exception: empty list")
>    .+: emptyAspect

> last (xs :: [a])
>   = sem_List (proxyFrom xs) (asp_slast (proxyFrom xs) .:+: asp_sempty)
>     xs emptyAtt #. slast @ a


Some conclusions:

Both polymorphic attributes and polymorphic ASTs are working (combined in the
case of cata). We need some explicit types, and special semantic function to
distribute type information.

Actually, the semantic function of a functor is taking the proxy from the
 contained type...

A possibly better alternative:

> semListPoly asp (x:xs :: [a])
>   = knitAspect cons asp
>   $    head @ a .=. sem_Lit @ a x
>  .*.   tail  .=. semListPoly asp xs
>  .*.   EmptyRec
> semListPoly asp []
>   = knitAspect nil asp
>   $ nilCh  .=. sem_Lit () .*. EmptyRec

> length' xs   = semListPoly asp_slen xs emptyAtt #. slen
> cata' f (e :: e) xs = semListPoly (asp_cata (getProxy e) f e) xs emptyAtt #. (scata @ e)

> sumcata' = cata (+) 0
> lencata  = cata (const (+1)) 0


avoid annotations, without touching attribute definitions:
< tyApp :: (forall b. Label ('Att name b)) -> Proxy a -> Label ('Att name a)
< att `tyApp` Proxy = att

> cata'' :: (a -> b -> b) -> b -> [a] -> b  -- needed
> cata'' f e xs
>   = semListPoly (asp_cata (getProxy e) f e) xs emptyAtt
>       #. (scata `tyAppAtt` (getProxy e))


-------------------------------------------------------------------------------
testing use
