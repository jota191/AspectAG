
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


> class SemLit a where
>   sem_Lit :: a -> Attribution e -> Attribution '[ '(a, a)]
>   lit     :: Label a
> instance SemLit a where
>   sem_Lit a _ = (Label =. a) *. emptyAtt
>   lit         = Label 


< data NT    = NT Symbol | T Type -- terminal, TODO: change name?
< data Prod  = Prd Symbol NT
< data Child = Chi Symbol Prod NT

> data Att   = Att Symbol Type


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
>   :: ( Require
>          (OpExtend' (LabelSetF ('( 'Att att t, t) : sp))
>                      AttReco ('Att att t) t sp) ctx
>      , ReqR (OpExtend' (LabelSetF ('( ('Att att t), t) : sp))
>           AttReco ('Att att t) t sp)
>          ~ Rec AttReco sp'
>      , ctx'
>          ~ ((Text "syndef::"
>              :<>: ShowType ('Att att t)
>              :<>: ShowType prd) ': ctx))
>      => Label ('Att att t)
>      -> Label prd
>      -> (Proxy ctx' -> Fam prd sc ip -> t)
>      -> CRule ctx prd sc ip ic sp ic sp'
> syndef (att :: Label ('Att att t)) (prd :: Label prd) (f :: Proxy ctx' -> Fam prd sc ip -> t)
>   = CRule $ \(ctx :: Proxy ctx) inp (Fam ic sp)
>    -> let nctx = Proxy @ ((Text "syndef::"
>                            :<>: ShowType ('Att att t)
>                            :<>: ShowType prd) ': ctx)
>       in  Fam ic $ req ctx (OpExtend @_ @AttReco @t att (f nctx inp) sp)


> inhdef
>   :: (Require (OpExtend' (LabelSetF ('( ('Att att t), t) : r))
>                AttReco ('Att att t) t r) ctx,
>       Require (OpUpdate (ChiReco ('Prd prd nt))
>                 ('Chi chi ('Prd prd nt) nt) v2 ic) ctx,
>       Require (OpLookup (ChiReco ('Prd prd nt))
>                ('Chi chi ('Prd prd nt) nt) ic) ctx,
>       ReqR (OpLookup (ChiReco ('Prd prd nt))
>             ('Chi chi ('Prd prd nt) nt) ic)
>        ~ Rec AttReco r,
>       ReqR (OpUpdate (ChiReco ('Prd prd nt))
>             ('Chi chi ('Prd prd nt) nt) v2 ic)
>        ~ Rec (ChiReco ('Prd prd nt)) ic',
>       ReqR (OpExtend' (LabelSetF ('( ('Att att t), t) : r))
>               AttReco ('Att att t) t r)
>       ~ Rec AttReco v2
>      , ctx' ~ ((Text "inhdef::"
>                 :<>: ShowType ('Att att t) :<>: ShowType ('Prd prd nt)
>                 :<>: ShowType ('Chi chi ('Prd prd nt) nt)) ': ctx))
>      =>
>      Label ('Att att t)
>      -> Label ('Prd prd nt)
>      -> Label ('Chi chi ('Prd prd nt) nt)
>      -> (Proxy ctx' -> Fam ('Prd prd nt) sc ip -> t)
>      -> CRule ctx ('Prd prd nt) sc ip ic sp ic' sp
> inhdef (att :: Label ('Att att t))
>        (prd :: Label ('Prd prd nt))
>        (chi :: Label ('Chi chi ('Prd prd nt) nt))
>        (f :: Proxy ctx' -> Fam ('Prd prd nt) sc ip -> v)
>   = CRule $ \(ctx :: Proxy ctx)
>               inp
>              (Fam ic sp :: Fam ('Prd prd nt) ic sp)
>        -> let
>         ic'   = req (Proxy @ ctx)
>               (OpUpdate @('Chi chi ('Prd prd nt) nt)
>                         @(ChiReco ('Prd prd nt)) chi catts' ic)
>         catts = req (Proxy @ ctx)
>               (OpLookup @('Chi chi ('Prd prd nt) nt)
>                         @(ChiReco ('Prd prd nt)) @ic chi ic)
>         catts'= req (Proxy @ ctx)
>               (OpExtend @('Att att t)
>                         @AttReco @t att (f nctx inp) catts)
>         nctx  = Proxy @ ((Text "inhdef::"
>                          :<>: ShowType ('Att att t)
>                          :<>: ShowType ('Prd prd nt)
>                          :<>: ShowType ('Chi chi ('Prd prd nt) nt))
>                          ': ctx)
>           in  Fam ic' sp


> ext :: CRule ctx prd sc ip ic sp ic' sp'
>     -> CRule ctx prd sc ip a b ic sp
>     -> CRule ctx prd sc ip a b ic' sp'
> (CRule f) `ext` (CRule g)
>  = CRule $ \ctx input -> f ctx input . g ctx input


> class Kn3 (fcr :: [(Child, Type)]) (prd :: Prod) where
>   type ICh3 fcr :: [(Child, [(Att, Type)])]
>   type SCh3 fcr :: [(Child, [(Att, Type)])]
>   kn3 :: Record fcr -> ChAttsRec prd (ICh3 fcr) -> ChAttsRec prd (SCh3 fcr)

> instance Kn3 '[] prod where
>   type ICh3 '[] = '[]
>   type SCh3 '[] = '[] 
>   kn3 _ _ = emptyCh

> instance ( lch ~ 'Chi l prd nt
>          , Kn3 fc prd
>          , LabelSet ('(lch, sch) : SCh3 fc)
>          , LabelSet ('(lch, ich) : ICh3 fc)
>          ) => 
>   Kn3 ( '(lch , Attribution ich -> Attribution sch) ': fc) prd where
>   type ICh3 ( '(lch , Attribution ich -> Attribution sch) ': fc)
>     = '(lch , ich) ': ICh3 fc
>   type SCh3 ( '(lch , Attribution ich -> Attribution sch) ': fc)
>     = '(lch , sch) ': SCh3 fc
>   kn3 ((ConsRec (TagField _ lch fch) (fcr :: Record fc)))
>    = \((ConsCh pich icr) :: ChAttsRec prd ( '(lch, ich) ': ICh3 fc))
>    -> let scr = kn3 fcr icr
>           ich = unTaggedChAttr pich
>       in ConsCh (TaggedChAttr lch
>                (fch ich)) scr



> emptyCtx = Proxy @ '[]

> knit :: ( Kn3 fc prd
>         , Empties fc prd)
>  => CRule '[] prd (SCh3 fc) ip (EmptiesR fc) '[] (ICh3 fc) sp
>   -> Record fc -> Attribution ip -> Attribution sp
> knit (rule :: CRule '[] prd (SCh3 fc) ip
>               (EmptiesR fc) '[] (ICh3 fc) sp)
>               (fc :: Record fc) ip
>   = let (Fam ic sp) = runCRule rule emptyCtx
>                        (Fam sc ip) (Fam ec emptyAtt)
>         sc          = kn3 fc ic
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


-- > consCtx :: Proxy ctx -> Proxy a -> Proxy (a ': ctx)
-- > consCtx Proxy Proxy = Proxy

-- > emptyCtx = Proxy @'[]

-- > ext :: CRule ctx prd sc ip ic sp ic' sp'
-- >     -> CRule ctx prd sc ip a b ic sp
-- >     -> CRule ctx prd sc ip a b ic' sp'
-- > (CRule f) `ext` (CRule g)
-- >  = CRule $ \ ctx input -> f ctx input . g ctx input

-- > ext2 -- :: (Require (OpEqLabel prd prd 'True) (Text "prds" ': ctx))
-- >      :: (ReifyEmp (ChildrenLst prd)) => 
-- >      CRule ctx prd sc ip ic sp ic' sp'
-- > 
-- >      -> CRule ctx prd
-- >               sc ip
-- >               (ReifyEmpR (ChildrenLst prd)) ('[] :: [(k, Type)])
-- >               ic sp
-- >      -> CRule ctx prd
-- >               sc ip
-- >              (ReifyEmpR (ChildrenLst prd)) ( '[] :: [(k, Type)])
-- >               ic' sp'
-- > (f :: CRule ctx prd
-- >               sc ip
-- >               ic sp
-- >               ic' sp')
-- >   `ext2` g
-- >   = CRule $ \ctx ->  let _ = flip (runCRule (f `ext` g) ctx)
-- >                              (emptyFam (Label @ prd))
-- >                      in runCRule (f `ext` g) ctx


-- > data OpEqLabel prd1 prd2 (b :: Bool) where
-- >   OpEqLabel :: Label prd1 -> Label prd2 -> OpEqLabel prd1 prd2 (prd1 == prd2)


-- > instance (prd1 ~ prd2)
-- >   => Require (OpEqLabel prd1 prd2 'True) ctx where
-- >   type ReqR (OpEqLabel prd1 prd2 'True) = ()
-- >   req = undefined


-- > instance Require (OpError (Text "" :<>: ShowType prd1 :<>: Text " /= "
-- >                            :<>: ShowType prd2)) ctx
-- >   => Require (OpEqLabel prd1 prd2 'False) ctx where
-- >   type ReqR (OpEqLabel prd1 prd2 'False) = ()
-- >   req = undefined


-- > infixr 5 `ext2`

-- > fstProxy :: Proxy '(a, b) -> Proxy a
-- > fstProxy Proxy = Proxy

-- > sndProxy :: Proxy '(a, b) -> Proxy b
-- > sndProxy Proxy = Proxy

-- > pr2Lb :: Proxy a -> Label a
-- > pr2Lb Proxy = Label


-- > -- emptyFam :: Label prd -> Fam (EmptiesT (ChildrenLst prd)) ('[] :: [(k, Type)])
-- > emptyFam (Label :: Label prd)
-- >   = Fam (rempties (Proxy @ (ChildrenLst prd)))
-- >         EmptyAtt

-- > type family ChildrenLst (prd :: k) :: [(k, Type)]

-- > type family EmptiesT (chn :: [(k, Type)])
-- >     = (r :: [((k, Type), [(k, Type)])]) | r -> chn where
-- >   EmptiesT '[] = '[]
-- >   EmptiesT ( '(chi, t) ': chn) = '( '(chi, t), '[] ) ': EmptiesT chn


-- > class ReifyEmp (emp :: [(k, Type)]) where
-- >   type ReifyEmpR emp :: [((k, Type),[(k, Type)])]
-- >   rempties :: Proxy emp -> ChAttsRec (ReifyEmpR emp)

-- > instance ReifyEmp '[] where
-- >   type ReifyEmpR '[] = '[] 
-- >   rempties _ = EmptyCh

-- > instance
-- >   ( ReifyEmp chs
-- >   , LabelSet ('( '(l, t), '[]) : ReifyEmpR chs) )
-- >   => ReifyEmp ( '(l, t) ': chs) where
-- >   type ReifyEmpR( '(l, t) ': chs) = '( '(l, t), '[]) ': ReifyEmpR chs
-- >   rempties _ = Label @ '(l, t) .= EmptyAtt .*. rempties (Proxy @ chs)




-- -- > inhdef
-- -- >   :: -- ( Require

--   >          (OpExtend' (LabelSetF ('(att, v) : sp))
--   >                      AttReco att v sp) ctx
--   >      , ReqR (OpExtend' (LabelSetF ('(att, v) : sp)) AttReco att v sp)
--   >          ~ Rec AttReco sp') 

-- -- >      ( Require (OpLookup ChiReco chi ic) ctx
-- -- >      , ReqR (OpLookup ChiReco chi ic) ~ Rec AttReco catts)
-- -- >      => Label (att :: k)
-- -- >      -> Label (prd :: k)
-- -- >      -> Label (chi :: (k, Type))
-- -- >      -> (Proxy ctx -> Fam sc ip -> v)
-- -- >      -> CRule ctx prd sc ip ic sp ic' sp

-- > inhdef
-- >   :: (Require
-- >         (OpExtend' (LabelSetF ('(att, v) : r)) AttReco att v r) ctx,
-- >       Require (OpUpdate ChiReco chi v2 ic) ctx,
-- >       Require (OpLookup ChiReco chi ic) ctx,
-- >       ReqR (OpLookup ChiReco chi ic) ~ Rec AttReco r,
-- >       ReqR (OpUpdate ChiReco chi v2 ic) ~ Rec ChiReco ic',
-- >       ReqR (OpExtend' (LabelSetF ('(att, v) : r)) AttReco att v r)
-- >       ~ Rec AttReco v2
-- >      , ctx' ~ ((Text "inhdef::"
-- >        :<>: ShowType att :<>: ShowType prd
-- >        :<>: ShowType chi) ': ctx))
-- >      =>
-- >      Label att
-- >      -> Label prd
-- >      -> Label chi
-- >      -> (Proxy ctx' -> Fam sc ip -> v)
-- >      -> CRule ctx prd sc ip ic sp ic' sp
-- > inhdef (att :: Label att) (prd :: Label prd) (chi :: Label chi)
-- >        (f :: Proxy ctx' -> Fam sc ip -> v)
-- >   = CRule $ \(ctx :: Proxy ctx) inp (Fam ic sp :: Fam ic sp)
-- >        -> let
-- >         ic'   = req (Proxy @ ctx) (OpUpdate @chi @ChiReco chi catts' ic)
-- >         catts = req (Proxy @ ctx) (OpLookup @chi @ChiReco @ic chi ic)
-- >         catts'= req (Proxy @ ctx) (OpExtend @att @AttReco @v att
-- >                                    (f nctx inp) catts)
-- >         nctx  = Proxy @ ((Text "inhdef::"
-- >                          :<>: ShowType att :<>: ShowType prd
-- >                          :<>: ShowType chi) ': ctx)
-- >           in  Fam ic' sp


-- > data FcReco
-- > type TaggedFc = TagField FcReco
-- > type FcRecord = Rec FcReco

-- semantic functions of children are maps from attributions (ic)
-- to attributions (sc). We put this at kind level:

-- > type instance WrapField FcReco (v :: ([(k, Type)], [(k, Type)]))
-- >   = Attribution (Fst v) -> Attribution (Snd v)

-- > class Kn2 (fcr :: [((k, Type), ([(k, Type)], [(k, Type)]))]) where
-- >  type FSem fcr :: ([((k, Type), [(k, Type)])],[((k, Type), [(k, Type)])])
-- >      -- | res -> fcr
-- >  kn2 :: FcRecord fcr -> ChAttsRec (Fst (FSem fcr))
-- >      -> ChAttsRec (Snd (FSem fcr))

-- > instance Kn2 '[] where
-- >   type FSem '[] = '( '[], '[])
-- >   kn2 _ _ = EmptyCh

-- > instance ( lch ~ '(l, t)
-- >          , LabelSet ('( '(l, t), inp) : Fst (FSem fcs))
-- >          , LabelSet ('( '(l, t), out) : Snd (FSem fcs))
-- >          , Kn2 fcs
-- >          )
-- >   => Kn2 ( '( '(l, t), '(inp, out) ) ': fcs) where
-- >   type FSem ( '( '(l, t), '(inp, out) ) ': fcs)
-- >     = '( '( '(l, t), inp) ': Fst (FSem fcs), '( '(l, t), out) ': Snd (FSem fcs))
-- >   kn2 (ConsRec (TagField _ lch fch) fcr) (ConsCh pich icr)
-- >    = let scr = kn2 fcr icr
-- >          ich = unTaggedChAttr pich
-- >      in ConsCh (TaggedChAttr lch
-- >                 (fch ich)) scr

-- -- > 
-- -- > ICh ( '(lch, '(inp, out) ) ': fcs)
-- -- >     = '(lch, inp) ': ICh fcs
-- -- >   type SCh ( '(lch, '(inp, out) ) ': fcs)
-- -- >     = '(lch, out) ': SCh fcs



-- > class Kn (fcr :: [((k, Type), ([(k, Type)], [(k, Type)]))]) where
-- >  type ICh fcr :: [((k, Type), [(k, Type)])]
-- >  type SCh fcr :: [((k, Type), [(k, Type)])]
-- >  kn :: FcRecord fcr -> ChAttsRec (ICh fcr) -> ChAttsRec (SCh fcr)

-- > instance Kn '[] where
-- >  type ICh '[] = '[]
-- >  type SCh '[] = '[]
-- >  kn _ _ = emptyCh 

-- > instance ( lch ~ '(l, t)
-- >          , LabelSet ('( '(l, t), inp) ': ICh fcs)
-- >          , LabelSet ('( '(l, t), out) ': SCh fcs)
-- >          , Kn fcs
-- >          )
-- >   => Kn ( '(lch, '(inp, out) ) ': fcs) where
-- >   type ICh ( '(lch, '(inp, out) ) ': fcs)
-- >     = '(lch, inp) ': ICh fcs
-- >   type SCh ( '(lch, '(inp, out) ) ': fcs)
-- >     = '(lch, out) ': SCh fcs
-- >   kn (ConsRec (TagField _ lch fch) fcr) (ConsCh pich icr)
-- >    = let scr = kn fcr icr
-- >          ich = unTaggedChAttr pich
-- >      in ConsCh (TaggedChAttr lch
-- >                 ((fch :: Attribution inp -> Attribution out)
-- >                  ich)) scr



-- > infixr 4 .=..

-- --> (.=..) :: Label l -> (Attribution ip -> Attribution sp)
-- -->                      -> TagField FcReco l '(ip, sp)

-- > l .=.. v = TagField (Label @ FcReco) l v

-- > class Kn3 (fcr :: [((k, Type), Type)]) where
-- >   type ICh3 fcr :: [((k, Type), [(k, Type)])]
-- >   type SCh3 fcr :: [((k, Type), [(k, Type)])]
-- >   kn3 :: Record fcr -> ChAttsRec (ICh3 fcr) -> ChAttsRec (SCh3 fcr)

-- > instance Kn3 '[] where
-- >   type ICh3 '[] = '[]
-- >   type SCh3 '[] = '[] 
-- >   kn3 _ _ = emptyCh

-- > instance ( lch ~ '(l, t)
-- >          , Kn3 fc
-- >          , LabelSet ('(lch, sch) : SCh3 fc)
-- >          , LabelSet ('(lch, ich) : ICh3 fc)
-- >  --        , WrapField FcReco (Attribution ich -> Attribution sch)
-- >  --          ~ (Attribution ich -> Attribution sch)
-- >          ) => 
-- >   Kn3 ( '(lch , Attribution ich -> Attribution sch) ': fc) where
-- >   type ICh3 ( '(lch , Attribution ich -> Attribution sch) ': fc)
-- >     = '(lch , ich) ': ICh3 fc
-- >   type SCh3 ( '(lch , Attribution ich -> Attribution sch) ': fc)
-- >     = '(lch , sch) ': SCh3 fc
-- >   kn3 (ConsRec (TagField _ lch fch) fcr) (ConsCh pich icr)
-- >    = let scr = kn3 fcr icr
-- >          ich = unTaggedChAttr pich
-- >      in ConsCh (TaggedChAttr lch
-- >                 (fch ich)) scr

-- > knit3 (rule :: CRule '[] prd (SCh3 fc) ip
-- >               (EmptiesT (ChildrenLst prd)) '[] (ICh3 fc) sp)
-- >               (fc :: Record fc) ip
-- >   = let (Fam ic sp) = runCRule rule emptyCtx
-- >                        (Fam sc ip) (emptyFam (Label @prd))
-- >         sc          = kn3 fc ic
-- >     in  sp







-- knit :: ( Empties fc
--         , Kn fc ) =>
--   Rule (SCh fc) ip (EmptiesR fc) '[] (ICh fc) sp
--      -> Record fc -> Attribution ip -> Attribution sp
-- knit rule fc ip
--   = let ec          = empties fc
--         (Fam ic sp) = rule (Fam sc ip) (Fam ec emptyAtt)
--         sc          = kn fc ic
--     in  sp


-- -- ------------------------------------------------------------------------------

-- class Emp
t ies (fc :: [((k, Type),Type)]) where
  type EmptiesR fc :: [((k, Type), [(k, Type)])] -- KnownBug, k = k' from here
  empties :: Record fc -> ChAttsRec (EmptiesR fc)

instance Empties '[] where
  type EmptiesR '[] = '[]
  empties EmptyRec = emptyCh

instance (( Empties fcr
         , LabelSet ( '( '(lch, t), '[]) ': EmptiesR fcr)) )
  => Empties ( '( '(lch, t), Attribution e -> Attribution a) ': fcr) where
  type EmptiesR ( '( '(lch, t), Attribution e -> Attribution a) ': fcr)
     = '( '(lch, t), '[]) ': EmptiesR fcr
  empties (ConsRec pch fcr)
    = let lch = labelTChAtt pch
      in  (lch .= emptyAtt) .* (empties fcr)

-- the Kn class

class Kn (fcr :: [((k, Type), Type)]) where
  type ICh fcr :: [((k, Type), [(k, Type)])]
  type SCh fcr :: [((k, Type), [(k, Type)])]
  kn :: Record fcr -> ChAttsRec (ICh fcr) -> ChAttsRec (SCh fcr)

instance Kn '[] where
  type ICh '[] = '[]
  type SCh '[] = '[] 
  kn _ _ = emptyCh

instance ( Kn fc
         , LabelSet ('(lch, sch) : SCh fc)
         , LabelSet ('(lch, ich) : ICh fc)) => 
  Kn ( '(lch , Attribution ich -> Attribution sch) ': fc) where
  type ICh ( '(lch , Attribution ich -> Attribution sch) ': fc)
    = '(lch , ich) ': ICh fc
  type SCh ( '(lch , Attribution ich -> Attribution sch) ': fc)
    = '(lch , sch) ': SCh fc
  kn (ConsRec pfch fcr) (ConsRec pich icr)
   = let scr = kn fcr icr
         lch = labelTChAtt pfch
         fch = unTagged pfch
         ich = unTaggedChAttr pich
     in ConsRec (TaggedChAttr lch (fch ich)) scr


-----------------------------------------------------------------------------

-- | A /use/ rule declares a synthesized attribute that collects information
--   from some of the children.
--   The function 'use' takes the following arguments:
--   - att:  the attribute to be defined, 
--   - nts:  the list of non-terminals for which the attribute is defined,
--   - op :  a monoidal operator which combines the attribute values, 
--   - unit: and a unit value to be used in those cases where none of 
--           the children has such an attribute. 

use :: (Use att nts a sc, LabelSet ( '(att, a) ': sp)) =>
    Label att -> HList nts -> (a -> a -> a) -> a 
           -> Rule sc ip ic sp ic ( '(att, a) ': sp)
use att nts op unit (Fam sc _)
  = let res = usechi att nts op sc
    in  syndef att $ maybe unit id res

-- | The class to implement the dependent function /usechi/

class Use (att :: k) (nts :: [Type]) (a :: Type) sc -- TODO:
 where
  usechi :: Label att -> HList nts -> (a -> a -> a) -> ChAttsRec sc
         -> Maybe a


instance Use att nts a '[] where
  usechi _ _ _ _ = Nothing

instance ( HMember' t nts
         , HMemberRes' t nts ~ mnts
         , Use' mnts att nts a ( '( '(lch, t ), attr) ': scr))
  => Use att nts a ( '( '(lch, t ), attr) ': scr) where
  usechi att nts op (ConsRec lattr scr)
    = let k = ()
         --  mnts = hMember' (sndLabel (labelChAttr lattr)) nts
      in  usechi' (Proxy @ mnts) att nts op (ConsRec lattr scr)
    
-- | /usechi'/ to pattern match on /mnts/
class Use' (mnts :: Bool) (att :: k) (nts :: [Type]) (a :: Type) sc
 where
  usechi' :: Proxy mnts -> Label att -> HList nts -> (a -> a -> a)
          -> ChAttsRec sc -> Maybe a

-- instance ( LabelSet ( '(lch, b) ': scr) -- FIXME: needed since we use ConsRec 
--          , Use att nts a scr )
--   => Use' False att nts a ( '(lch, b) ': scr) where
--   usechi' _ att nts a (ConsCh _ scr) = usechi att nts a scr

instance Use att nts a scr
  => Use' False att nts a ( '(lch, attr) ': scr) where
  usechi' _ att nts op scr = usechi att nts op $ tailRec scr

instance ( HasFieldAttF att attr
         , LookupByLabelAttFR att attr ~ a
         , Use att nts a scr
         , LabelSet ( '( '(lch,t), attr) ': scr)) -- FIXME: pattern syn
  => Use' True att nts a ( '( '(lch,t), attr) ': scr) where
  usechi' _ att nts op (ConsCh lattr scr)
    = let attr = unTaggedChAttr lattr
          val  = attr #. att
      in  Just $ maybe val (op val) $ usechi att nts op scr


--------------------------------------------------------------------------------

-- | A /copy/ rule copies an inherited attribute from the parent to all its
-- children.
-- The function 'copy' takes
-- - 'att' : the name of an attribute 
-- - 'nts' : an heterogeneous list of non-terminals for which the attribute
--           has to be defined,
-- and generates a copy rule for this.


copy  :: ( Copy att nts (LookupByLabelAttFR att ip) ic
         , HasFieldAttF att ip) 
  =>   Label att -> HList nts
  -> Rule sc ip ic sp (CopyR att nts (LookupByLabelAttFR att ip) ic) sp
copy att nts (Fam _ ip) = defcp att nts (ip #. att)

defcp  ::  Copy att nts vp ic
       =>  Label att -> HList nts -> vp
       -> Fam ic sp -> Fam (CopyR att nts vp ic) sp
defcp att nts vp (Fam ic sp)
  = Fam (cpychi att nts vp ic) sp



-- | inserts the attribute in every children
class Copy (att :: k)
           (nts :: [Type])
           (vp  :: Type)
           (ic  :: [((k,Type),[(k,Type)])]) where
  type CopyR att nts vp ic :: [((k,Type), [(k,Type)])]
  cpychi :: Label att
         -> HList nts
         -> vp
         -> ChAttsRec ic
         -> ChAttsRec (CopyR att nts vp ic)

instance Copy att nts vp '[] where
  type CopyR att nts vp '[] = '[]
  cpychi _ _ _ _ = EmptyCh

instance ( Copy att nts vp ics
         , Copy' mnts mvch att vp '(lch,t) vch
         , mnts ~ HMemberRes' t nts
         , HMember' t nts
         , HasLabelAtt att vch
         , mvch ~ HasLabelAttR att vch
         , LabelSet ( '( '(lch, t), vch) : ics)
         , (LabelSet( '( '(lch, t), CopyR' mnts mvch att vp '(lch, t) vch)
                     ': CopyR att nts vp ics))
         )
  => Copy att nts vp ( '( '(lch,t), vch) ': ics) where
  type CopyR att nts vp ( '( '(lch,t), vch) ': ics)
    =  '( '(lch, t) ,CopyR' (HMemberRes' t nts)
                (HasLabelAttR att vch) att vp '(lch,t) vch)
       ': CopyR att nts vp ics
  cpychi att nts vp (ConsCh tgchatt ics)
    = let ics'  = cpychi att nts vp ics
          lcht  = labelChAttr tgchatt
          vch   = unTaggedChAttr tgchatt
          mnts  = hMember' (sndLabel lcht) nts
          mvch  = hasLabelAtt att vch
          attr  = cpychi' mnts mvch att vp lcht vch
      in  (lcht .= attr) .* ics'


class Copy' (mnts :: Bool)
            (mvch :: Bool)
            (att  :: k)
            (vp   :: Type)
            (lcht :: (k,Type))
            (vch  :: [(k, Type)])  where
  type CopyR' mnts mvch att vp lcht vch :: [(k, Type)]
  cpychi' :: Proxy mnts
          -> Proxy mvch
          -> Label att
          -> vp
          -> Label lcht
          -> Attribution vch
          -> Attribution (CopyR' mnts mvch att vp lcht vch)



instance Copy' False mvch att vp lcht pch where
  type CopyR' False mvch att vp lcht pch = pch
  cpychi' _ _ _ _ _ pch = pch

instance Copy' True True att vp lcht pch where
  type CopyR' True True att vp lcht pch = pch
  cpychi' _ _ _ _ _ pch = pch

instance (LabelSet ('(att, vp) : pch))
  => Copy' True False att vp lcht pch where
  type CopyR' True False att vp lcht pch
      = '(att, vp) ': pch
  cpychi' _ _ att vp _ pch = (att =. vp .*. pch) 



--------------------------------------------------------------------------


-- data Modes (att :: k) (nts :: [(k,Type)])
--            (op :: Type) (unit :: Type) where
--   FnSynT :: Label att -> Modes att nts op unit
--   -- | FnInhT att nts
--   -- | FnUseT att nts op unit
--   -- deriving Show


-- data family Demote (t :: Modes att nts op unit) :: Type
-- data instance Demote (FnSynT att)
--   = FnSyn att 
-- --data instance Demote (FnInhT att nts)  = FnInh att nts


-- -- class Apply ic f a where
-- --   type ApplyR ic f a

-- -- instance (Defs att nts vals ic)
-- --   => Apply ic (FnInhT att nts) (Fam sc ip -> Record vals) where
-- --   type ApplyR ic (FnInhT att nts) (Fam sc ip -> Record vals)
-- --     = forall sp. Rule sc ip ic sp (DefsR att nts vals ic) sp

-- data F att nts = F att nts

app att nts f = inhdef att nts . f
--app' (FnSyn att) f = syndef att . f



-- data DefMode
--   = FnInhMode
--   | FnSynMode
--   deriving Show

-- data family DemoteMode (mode :: DefMode)
--                        (att  :: k)
--                        (nts  :: [Type])
--                        (m    :: Type)          :: Type

-- data instance DemoteMode FnInhMode att nts m where
--   FnInh :: Label att -> HList nts -> DemoteMode FnInhMode att nts m

-- data instance DemoteMode FnSynMode att nts m where
--   FnSyn :: Label att -> DemoteMode FnSynMode att nts m

-- class Apply mode att nts m vals a ic sp where
--   type ApplyR mode att nts m vals a ic sp
--   apply :: DemoteMode mode att nts m
--         -> (a -> Record vals)
--         -> a
--         -> Fam ic sp
--         -> ApplyR mode att nts m vals a ic sp

-- instance (Defs att nts vals ic)
--   => Apply FnInhMode att nts m vals a ic sp where
--   type ApplyR FnInhMode att nts m vals a ic sp
--     = Fam (DefsR att nts vals ic) sp
--   apply (FnInh att nts) f = inhdef att nts . f


-- -- Instance Apply FnSynMode att nts m vals a ic sp where
-- --   type ApplyR FnSynMode att nts m vals a ic sp


-- class DefAspUse (att  :: k)
--                 (nts  :: [Type])
--                 (a    :: Type)
--                 (prds :: [Type]) where
--   type DefAspUseR att nts a prds :: [(Type, Type)]
--   defAspUse :: Label att -> HList nts
--             -> (a -> a -> a) -> a
--             -> HList prds
--             -> Aspect (DefAspUseR att nts a prds)

-- instance DefAspUse att nts a '[] where
--   type DefAspUseR att nts a '[] = '[]
--   defAspUse _ _ _ _ _ = EmptyR


-- instance (DefAspUse att nts a prds)
--   => DefAspUse att nts a (prd ': prds) where
--   type DefAspUseR att nts a (prd ': prds)
--     =( '(prd , Any)
--        ': DefAspUseR att nts a prds)
--   defAspUse att nts op unit (HCons prd prds)
--     = (prd .=. defAspUse1 att nts prd op unit) .*. defAspUse att nts op unit prds


-- class DefAspUse1 att nts prd a sc sp where
--   type DefAspUse1R att nts prd a sc sp :: Type
--   defAspUse1 :: Label att -> HList nts ->
--     Label prd -> (a -> a -> a) -> a -> Fam sc ip
--     -> (Fam ic sp -> Fam ic ( '(att, a) ': sp))

-- instance ( Use att nts a sc
--          , LabelSet ('(att, a) : sp))
--   => DefAspUse1 att nts prd a sc sp where
--   type DefAspUse1R att nts prd a sc sp = () 
--   defAspUse1 att nts prd op unit (Fam sc _)
--     = let res = usechi att nts op sc
--       in (syndef att (maybe unit id res))
          


-- getter
--syndef' :: Label att -> val -> Fam ic sp -> a -> Fam ic ('(att, val) : sp)
--syndef' = undefined

-- (.##) :: ChAttsRec r -> Label l -> Attribution ?
-}
