
> {-|
> Module      : Language.Grammars.AspectAG
> Description : Main module, First-class attribute grammars
> Copyright   : (c) Juan García Garland, Marcos Viera, 2019 
> License     : GPL
> Maintainer  : jpgarcia@fing.edu.uy
> Stability   : experimental
> Portability : POSIX

> -}

> {-# LANGUAGE PolyKinds                 #-}
> {-# LANGUAGE KindSignatures            #-}
> {-# LANGUAGE DataKinds                 #-}
> {-# LANGUAGE ConstraintKinds           #-}
> {-# LANGUAGE RankNTypes                #-}
> {-# LANGUAGE TypeOperators             #-}
> {-# LANGUAGE FlexibleInstances         #-}
> {-# LANGUAGE FlexibleContexts          #-}
> {-# LANGUAGE GADTs                     #-}
> {-# LANGUAGE UndecidableInstances      #-}
> {-# LANGUAGE MultiParamTypeClasses     #-}
> {-# LANGUAGE TypeFamilies              #-}
> {-# LANGUAGE NoMonomorphismRestriction #-}
> {-# LANGUAGE ScopedTypeVariables       #-}
> {-# LANGUAGE TypeFamilies              #-}
> {-# LANGUAGE TypeApplications          #-}
> {-# LANGUAGE FunctionalDependencies    #-}
> {-# LANGUAGE TypeFamilyDependencies    #-}
> {-# LANGUAGE PartialTypeSignatures     #-}
> {-# LANGUAGE IncoherentInstances       #-}

> module Language.Grammars.AspectAG2 (
>               module Language.Grammars.AspectAG2,
>               module Language.Grammars.AspectAG.Attribute,
>               module Language.Grammars.AspectAG.Attribution,
>               module Language.Grammars.AspectAG.ChildAtts,
>               module Language.Grammars.AspectAG.Record,
>               module Language.Grammars.AspectAG.TagUtils,
>               module Language.Grammars.AspectAG.HList,
>           --  module Language.Grammars.AspectAG.Notation,
>               module Language.Grammars.AspectAG.GenRecord,
>               module Language.Grammars.AspectAG.TypeError,
>               module Language.Grammars.AspectAG.TPrelude
>             ) where


> import Language.Grammars.AspectAG.HList
> import Language.Grammars.AspectAG.Attribution
> import Language.Grammars.AspectAG.Record
> import Language.Grammars.AspectAG.Attribute
> import Data.Kind
> --import Data.Tagged hiding (unTagged)
> import Language.Grammars.AspectAG.TPrelude
> import Data.Proxy
> import Language.Grammars.AspectAG.ChildAtts
> import Language.Grammars.AspectAG.TagUtils
> --import Language.Grammars.AspectAG.Notation
> import Language.Grammars.AspectAG.GenRecord
> import GHC.TypeLits
> import Language.Grammars.AspectAG.TypeError
> import Data.Maybe
> import GHC.Types
> import Data.Type.Equality
> import Control.Monad.Reader

> class SemLit a where
>   sem_Lit :: a -> Attribution ('[] :: [(Att,Type)])
>                -> Attribution '[ '( 'Att "term" a , a)]
>   lit     :: Label ('Att "term" a)
> instance SemLit a where
>   sem_Lit a _ = (Label =. a) *. emptyAtt
>   lit         = Label @ ('Att "term" a)


< data NT    = NT Symbol | T Type -- terminal, TODO: change name?
< data Prod  = Prd Symbol NT
< data Child = Chi Symbol Prod NT



> data Fam (prd :: Prod)
>          (c :: [(Child, [(Att, Type)])])
>          (p :: [(Att, Type)]) :: Type
>  where
>   Fam :: ChAttsRec prd c -> Attribution p -> Fam prd c p

> chi :: Fam prd c p -> ChAttsRec prd c
> chi (Fam c p) = c

> par :: Fam prd c p -> Attribution p
> par (Fam c p) = p

-- > -- | Rules, aka definition of attribution computations
-- > --Rules are defined as a mapping from an input family to an output family,
-- > --the added arity is for make them composable

> type Rule
>   (prd  :: Prod)
>   (sc   :: [(Child, [(Att, Type)])])
>   (ip   :: [(Att,       Type)])
>   (ic   :: [(Child, [(Att, Type)])])
>   (sp   :: [(Att,       Type)])
>   (ic'  :: [(Child, [(Att, Type)])])
>   (sp'  :: [(Att,       Type)])
>   = Fam prd sc ip -> Fam prd ic sp -> Fam prd ic' sp'

> newtype CRule (ctx :: [ErrorMessage]) prd sc ip ic sp ic' sp'
>  = CRule { runCRule :: (Proxy ctx -> Rule prd sc ip ic sp ic' sp')}



> syndef
>   :: ( Require (OpEq t t') ctx'
>      , Require
>          (OpExtend' (LabelSetF ('( 'Att att t, t) : sp))
>                      AttReco ('Att att t) t sp) ctx
>      , ReqR (OpExtend' (LabelSetF ('( ('Att att t), t) : sp))
>           AttReco ('Att att t) t sp)
>          ~ Rec AttReco sp'
>      , ctx'
>          ~ ((Text "syndef::"
>              :<>: ShowType ('Att att t)
>              :<>: ShowType prd) ': ctx)
>       , t ~ t'
>      )
>      => Label ('Att att t)
>      -> Label prd
>      -> (Proxy ctx' -> Fam prd sc ip -> t')
>      -> CRule ctx prd sc ip ic sp ic sp'
> syndef (att :: Label ('Att att t))
>        (prd :: Label prd)
>         f 
>   = CRule $ \(ctx :: Proxy ctx) inp (Fam ic sp)
>    -> let nctx = Proxy @ ((Text "syndef::"
>                            :<>: ShowType ('Att att t)
>                            :<>: ShowType prd) ': ctx)
>       in  Fam ic $ req ctx (OpExtend @_ @AttReco @t att (f nctx inp) sp)

> syndefM att prd = syndef att prd . def

> inhdef
>   :: ( Require (OpEq t t') ctx'
>      , t ~ t'
>      , ntch ~ 'Left n ---- {- TODO -}
>      , Require (OpExtend' (LabelSetF ('( ('Att att t), t) : r))
>                AttReco ('Att att t) t r) ctx,
>       Require (OpUpdate (ChiReco ('Prd prd nt))
>                 ('Chi chi ('Prd prd nt) ntch) v2 ic) ctx,
>       Require (OpLookup (ChiReco ('Prd prd nt))
>                ('Chi chi ('Prd prd nt) ntch) ic) ctx,
>       ReqR (OpLookup (ChiReco ('Prd prd nt))
>             ('Chi chi ('Prd prd nt) ntch) ic)
>        ~ Rec AttReco r,
>       ReqR (OpUpdate (ChiReco ('Prd prd nt))
>             ('Chi chi ('Prd prd nt) ntch) v2 ic)
>        ~ Rec (ChiReco ('Prd prd nt)) ic',
>       ReqR (OpExtend' (LabelSetF ('( ('Att att t), t) : r))
>               AttReco ('Att att t) t r)
>       ~ Rec AttReco v2
>      , ctx' ~ ((Text "inhdef::"
>                 :<>: ShowType ('Att att t) :<>: ShowType ('Prd prd nt)
>                 :<>: ShowType ('Chi chi ('Prd prd nt) ntch)) ': ctx))
>      =>
>      Label ('Att att t)
>      -> Label ('Prd prd nt)
>      -> Label ('Chi chi ('Prd prd nt) ntch)
>      -> (Proxy ctx' -> Fam ('Prd prd nt) sc ip -> t')
>      -> CRule ctx ('Prd prd nt) sc ip ic sp ic' sp
> inhdef (att :: Label ('Att att t))
>        (prd :: Label ('Prd prd nt))
>        (chi :: Label ('Chi chi ('Prd prd nt) ntch))
>         f
>   = CRule $ \(ctx :: Proxy ctx)
>               inp
>              (Fam ic sp :: Fam ('Prd prd nt) ic sp)
>        -> let
>         ic'   = req (Proxy @ ctx)
>               (OpUpdate @('Chi chi ('Prd prd nt) ntch)
>                         @(ChiReco ('Prd prd nt)) chi catts' ic)
>         catts = req (Proxy @ ctx)
>               (OpLookup @('Chi chi ('Prd prd nt) ntch)
>                         @(ChiReco ('Prd prd nt)) @ic chi ic)
>         catts'= req (Proxy @ ctx)
>               (OpExtend @('Att att t)
>                         @AttReco @t att (f nctx inp) catts)
>         nctx  = Proxy @ ((Text "inhdef::"
>                          :<>: ShowType ('Att att t)
>                          :<>: ShowType ('Prd prd nt)
>                          :<>: ShowType ('Chi chi ('Prd prd nt) ntch))
>                          ': ctx)
>           in  Fam ic' sp

> inhdefM att prd chi = inhdef att prd chi . def

> ext' :: CRule ctx prd sc ip ic sp ic' sp'
>     -> CRule ctx prd sc ip a b ic sp
>     -> CRule ctx prd sc ip a b ic' sp'
> (CRule f) `ext'` (CRule g)
>  = CRule $ \ctx input -> f ctx input . g ctx input

> ext ::  RequireEq prd prd' (Text "ext":ctx) -- (Require (OpEq prd prd') (Text "ext":ctx), prd ~ prd')
>      => CRule ctx prd sc ip ic sp ic' sp'
>      -> CRule ctx prd' sc ip a b ic sp
>      -> CRule ctx prd sc ip a b ic' sp'
> ext = ext'


> type family RequireEq (t1 :: k )(t2 :: k) (ctx:: [ErrorMessage])
>    :: Constraint where
>   RequireEq t1 t2 ctx
>     = (Require (OpEq t1 t2) ctx, t1 ~ t2)


> data OpEq prd1 prd2


> instance Require (OpEq prd prd) ctx where
>   type ReqR (OpEq prd prd) = ()
>   req = undefined


> instance Require (OpError (Text "" :<>: ShowType prd1 :<>: Text " /= "
>                             :<>: ShowType prd2)) ctx
>   => Require (OpEq prd1 prd2) ctx where
>   type ReqR (OpEq prd1 prd2) = ()
>   req = undefined


> data Lhs
> lhs :: Label Lhs
> lhs = Label
>
> class At pos att m  where
>  type ResAt pos att m
>  at :: Label pos -> Label att -> m (ResAt pos att m)


> instance ( Require (OpLookup (ChiReco prd) ('Chi ch prd nt) chi) ctx
>          , ReqR (OpLookup (ChiReco prd) ('Chi ch prd nt) chi) ~ Rec AttReco r
>          , Require (OpLookup AttReco ('Att att t) r) ctx
>          , ReqR (OpLookup AttReco ('Att att t) r) ~ t'
>          , prd ~ prd'
>          , Require (OpEq prd prd') ctx
>          , t ~ t'
>          , Require (OpEq t t') ctx 
>          )
>       => At ('Chi ch prd nt) ('Att att t)
>             (Reader (Proxy ctx, Fam prd' chi par))  where
>  type ResAt ('Chi ch prd nt) ('Att att t) (Reader (Proxy ctx, Fam prd' chi par))
>          = t -- ReqR (OpLookup (ChiReco prd) ('Chi ch prd nt) chi)
>  at (ch :: Label ('Chi ch prd nt)) (att :: Label ('Att att t))
>   = liftM (\((ctx, Fam chi _) :: (Proxy ctx, Fam prd' chi par))
>      -> let atts = req (Proxy @ ctx) (OpLookup @('Chi ch prd' nt)
>                                       @(ChiReco prd') ch chi)
>         in  req (Proxy @ ctx) (OpLookup @('Att att t)
>                                     @AttReco att atts)) ask

> instance
>          ( Require (OpLookup AttReco ('Att att t) par) ctx
>          , ReqR (OpLookup AttReco ('Att att t) par) ~ t'
>          , t ~ t'
>          , Require (OpEq t t') ctx
>          )
>  => At Lhs ('Att att t) (Reader (Proxy ctx, Fam prd chi par))  where
>  type ResAt Lhs ('Att att t) (Reader (Proxy ctx, Fam prd chi par))
>     = t
>  at lhs att
>   = liftM (\((ctx, Fam _ par) :: (Proxy ctx, Fam prd chi par))
>            -> req (Proxy @ ctx) (OpLookup @('Att att t)
>                                     @AttReco att par)) ask

> def :: Reader (Proxy ctx, Fam prd chi par) a
>     -> (Proxy ctx -> (Fam prd chi par) -> a)
> def = curry . runReader


instance MonadReader (Fam l ho chi par) m
       => At (Proxy Lhs) m par where
  at _ = liftM (\(Fam _ _ _ par) -> par) ask

> class Kn (fcr :: [(Child, Type)]) (prd :: Prod) where
>   type ICh fcr :: [(Child, [(Att, Type)])]
>   type SCh fcr :: [(Child, [(Att, Type)])]
>   kn :: Record fcr -> ChAttsRec prd (ICh fcr) -> ChAttsRec prd (SCh fcr)

> instance Kn '[] prod where
>   type ICh '[] = '[]
>   type SCh '[] = '[] 
>   kn _ _ = emptyCh

> instance ( lch ~ 'Chi l prd nt
>          , Kn fc prd
>          , LabelSet ('(lch, sch) : SCh fc)
>          , LabelSet ('(lch, ich) : ICh fc)
>          ) => 
>   Kn ( '(lch , Attribution ich -> Attribution sch) ': fc) prd where
>   type ICh ( '(lch , Attribution ich -> Attribution sch) ': fc)
>     = '(lch , ich) ': ICh fc
>   type SCh ( '(lch , Attribution ich -> Attribution sch) ': fc)
>     = '(lch , sch) ': SCh fc
>   kn ((ConsRec (TagField _ lch fch) (fcr :: Record fc)))
>    = \((ConsCh pich icr) :: ChAttsRec prd ( '(lch, ich) ': ICh fc))
>    -> let scr = kn fcr icr
>           ich = unTaggedChAttr pich
>       in ConsCh (TaggedChAttr lch
>                (fch ich)) scr



> emptyCtx = Proxy @ '[]

> knit :: ( Kn fc prd
>         , Empties fc prd)
>  => CRule '[] prd (SCh fc) ip (EmptiesR fc) '[] (ICh fc) sp
>   -> Record fc -> Attribution ip -> Attribution sp
> knit (rule :: CRule '[] prd (SCh fc) ip
>               (EmptiesR fc) '[] (ICh fc) sp)
>               (fc :: Record fc) ip
>   = let (Fam ic sp) = runCRule rule emptyCtx
>                        (Fam sc ip) (Fam ec emptyAtt)
>         sc          = kn fc ic
>         ec          = empties fc
>     in  sp


> class Empties (fc :: [(Child,Type)]) (prd :: Prod) where
>   type EmptiesR fc :: [(Child, [(Att, Type)])] 
>   empties :: Record fc -> ChAttsRec prd (EmptiesR fc)

> instance Empties '[] prd where
>   type EmptiesR '[] = '[]
>   empties _ = emptyCh

> instance ( Empties fcr prd
>          , chi ~ 'Chi ch prd nt
>          , LabelSet ( '(chi, '[]) ': EmptiesR fcr))
>  => Empties ( '(chi, Attribution e -> Attribution a) ': fcr) prd where
>   type EmptiesR ( '(chi, Attribution e -> Attribution a) ': fcr)
>     = '(chi, '[]) ': EmptiesR fcr
>   empties (ConsRec pch fcr)
>     = let lch = labelTChAtt pch
>       in  (lch .= emptyAtt) .* (empties fcr)

