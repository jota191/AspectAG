{-|
Module      : Language.Grammars.AspectAG
Description : Main module, First-class attribute grammars
Copyright   : (c) Juan García Garland, Marcos Viera, 2019
License     : GPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX

-}

{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE IncoherentInstances       #-}
-- {-# LANGUAGE AllowAmbiguousTypes       #-}

module Language.Grammars.FastAG (
              module Language.Grammars.FastAG,
              module Language.Grammars.FastAG.HList,
              module Language.Grammars.FastAG.GenRecord,
              module Language.Grammars.FastAG.RecordInstances,
              module Language.Grammars.FastAG.TPrelude
            ) where


import Language.Grammars.FastAG.HList
import Data.Kind
import Data.Proxy
import Data.Ord
import Language.Grammars.FastAG.RecordInstances
import Language.Grammars.FastAG.TPrelude
import Language.Grammars.FastAG.GenRecord
import GHC.TypeLits
import Prelude hiding (lookup)

import Data.Maybe
import Data.Type.Equality
import Control.Monad.Reader

class SemLit a where
  sem_Lit :: a -> Attribution ('[] :: [(Att,Type)])
               -> Attribution '[ '( 'Att "term" a , a)]
  lit     :: Label ('Att "term" a)
instance SemLit a where
  sem_Lit a _ = (Label =. a) *. emptyAtt
  lit         = Label @ ('Att "term" a)


-- * Families and Rules

-- | In each node of the grammar, the "Fam" contains a single attribution
-- for the parent, and a collection (Record) of attributions for the children:
data Fam (prd :: Prod)
         (c   :: [(Child, [(Att, Type)])])
         (p   :: [(Att, Type)]) :: Type
 where
  Fam :: ChAttsRec prd c -> Attribution p -> Fam prd c p

emptyFam :: Fam prd '[] '[]
emptyFam = Fam EmptyRec EmptyRec

-- | Getters
chi :: Fam prd c p -> ChAttsRec prd c
chi (Fam c p) = c

par :: Fam prd c p -> Attribution p
par (Fam c p) = p

prd :: Fam prd c p -> Label prd
prd (Fam c p) = Label

-- | Rules are a function from the input family to the output family.
-- They are indexed by a production.
type Rule
  (prd  ::  Prod)
  (sc   :: [(Child, [(Att, Type)])])
  (ip   :: [(Att,       Type)])
  (ic   :: [(Child, [(Att, Type)])])
  (sp   :: [(Att,       Type)])
  (ic'  :: [(Child, [(Att, Type)])])
  (sp'  :: [(Att,       Type)])
  = Fam prd sc ip -> Fam prd ic sp -> Fam prd ic' sp'

-- | Empty Aspect.
emptyAspect :: Aspect '[]
emptyAspect  = EmptyRec

class ComAspect (r1 :: [(Prod, Type)]) (r2 :: [(Prod, Type)]) where
  type ComAspectR r1 r2 :: [(Prod, Type)]
  comAspect :: Aspect r1 -> Aspect r2 -> Aspect (ComAspectR r1 r2)

instance ComAspect '[] r where
  type ComAspectR '[] r = r
  comAspect _ r = r

instance
  ( ComAspect r (ExtAspectR rule r')
  , ExtAspect rule r') =>
  ComAspect ('(prd,rule) ': r) r' where
  type ComAspectR ('(prd,rule) ': r) r'
    = ComAspectR r (ExtAspectR rule r')
  comAspect (ConsRec (TagField Label Label rule) asp) asp'
    = comAspect asp (extAspect rule asp')


class ExtAspect (r :: Type) (asp :: [(Prod,Type)]) where
  type ExtAspectR r asp :: [(Prod,Type)]
  extAspect :: r -> Aspect asp -> Aspect (ExtAspectR r asp)

class ExtAspect' (cmp :: Ordering) (r :: Type) (asp :: [(Prod,Type)]) where
  type ExtAspectR' cmp r asp :: [(Prod,Type)]
  extAspect' :: Proxy cmp -> r -> Aspect asp -> Aspect (ExtAspectR' cmp r asp)

instance ExtAspect (Rule prd sc ip ic sp ic' sp') '[] where
  type ExtAspectR (Rule prd sc ip ic sp ic' sp') '[]
    = '[ '(prd, Rule prd sc ip ic sp ic' sp')]
  extAspect rule EmptyRec
    = ConsRec (TagField Label Label rule) EmptyRec

instance (ExtAspect' (CMP prd prd')
                     (Rule prd sc ip ic sp ic' sp')
                     ('(prd', rule) : asp)) =>
  ExtAspect (Rule prd sc ip ic sp ic' sp')
            ('(prd', rule) ': asp) where
  type ExtAspectR (Rule prd sc ip ic sp ic' sp')
                  ( '(prd', rule) ': asp)
    = ExtAspectR' (CMP prd prd')
      (Rule prd sc ip ic sp ic' sp')
                  ( '(prd', rule) ': asp)
  extAspect rule asp = extAspect' (Proxy @(CMP prd prd')) rule asp

instance ExtAspect' 'LT (Rule prd sc ip ic sp ic' sp')
                    ('(prd', rule) ': asp) where
  type ExtAspectR'  'LT (Rule prd sc ip ic sp ic' sp')
                    ('(prd', rule) ': asp)
    = '(prd, Rule prd sc ip ic sp ic' sp') ': ('(prd', rule) : asp)
  extAspect' _ rule asp
    = ConsRec (TagField (Label @PrdReco) (Label @prd)  rule) asp


instance ExtAspect rule asp =>
  ExtAspect' 'GT (rule)
                 ('(prd', rule') : asp) where
  type ExtAspectR'  'GT (rule)
                        ('(prd', rule') ': asp)
    = '(prd', rule') ': ExtAspectR (rule) asp
  extAspect' _ rule (ConsRec rul asp)
    = ConsRec rul (extAspect rule asp)

instance
 ( Update PrdReco prd (Rule prd sc ip ic sp ic'' sp'') a
 , Lookup PrdReco prd a
 , LookupR PrdReco prd a ~ Rule prd sc ip ic sp ic' sp' 
 , IC (LookupR PrdReco prd a) ~ ic
 , SP (LookupR PrdReco prd a) ~ sp
 ) =>
  ExtAspect' 'EQ (Rule prd sc ip ic' sp' ic'' sp'') a where
  type ExtAspectR' 'EQ (Rule prd sc ip ic' sp' ic'' sp'') a
    = UpdateR PrdReco prd
            (Rule prd sc ip
             (IC (LookupR PrdReco prd a))
             (SP (LookupR PrdReco prd a))
            ic'' sp'') a
  extAspect' _ rule asp
    = let prd     = Label @ prd
          oldRule = lookup prd asp
          newRule = rule `ext` oldRule
      in  update prd Proxy newRule asp

ext ::  Rule prd sc ip ic sp ic' sp'
    ->  Rule prd sc ip a b ic sp
    ->  Rule prd sc ip a b ic' sp'
f `ext` g
 = \input -> f input . g input
  
(.+:) = extAspect
infixr 3 .+:

(.:+.) = flip extAspect
infixl 3 .:+.

(.:+:) = comAspect
infixr 4 .:+:


type family IC (rule :: Type) where
  IC (Rule prd sc ip ic sp ic' sp') = ic

type family SP (rule :: Type) where
  SP (Rule prd sc ip ic sp ic' sp') = sp

syndef
     :: ( Extend AttReco ('Att att t) t sp
        , ExtendR AttReco ('Att att t) t sp ~ sp')
     => Label ('Att att t)
     -> Label prd
     -> (Fam prd sc ip -> t)
     -> Rule prd sc ip ic sp ic sp'
syndef att prd f
  = \inp (Fam ic sp)
   ->  Fam ic $ (extend att Proxy (f inp) sp)

syndefM
  :: ( Extend AttReco ('Att att t) t sp
     , ExtendR AttReco ('Att att t) t sp ~ sp')
  => Label ('Att att t)
  -> Label prd
  -> Reader (Fam prd sc ip) t
  -> Rule prd sc ip ic sp ic sp'
syndefM att prd = syndef att prd . runReader

syn = syndefM
inh = inhdefM

synmod ::
     (Update AttReco ('Att att t) t r)
  => Label ('Att att t)
  -> Label prd
  -> (Fam prd sc ip -> t)
  -> Rule prd sc ip ic' r ic' (UpdateR AttReco ('Att att t) t r)
synmod att prd f =
  \inp (Fam ic sp) ->
    Fam ic $ update att Proxy (f inp) sp 

synmodM att prd = synmod att prd . runReader

inhdef ::
     ( Update (ChiReco ('Prd prd nt)) ('Chi chi ('Prd prd nt) ntch) v2 ic
     , UpdateR (ChiReco ('Prd prd nt)) ('Chi chi ('Prd prd nt) ntch) v2 ic ~ ic'
     , ExtendR AttReco ('Att att t) t r ~ v2
     , Extend AttReco ('Att att t) t r
     , LookupR (ChiReco ('Prd prd nt))
               ('Chi chi ('Prd prd nt) ntch) ic ~ Attribution r
     , Lookup (ChiReco ('Prd prd nt)) ('Chi chi ('Prd prd nt) ntch) ic
     )
     => Label ('Att att t)
     -> Label ('Prd prd nt)
     -> Label ('Chi chi ('Prd prd nt) ntch)
     -> (Fam ('Prd prd nt) sc ip -> t)
     -> Rule ('Prd prd nt) sc ip ic sp ic' sp
inhdef att prd chi f
  = \inp (Fam ic sp)
     -> let ic'   = update chi Proxy catts' ic --req ctx (OpUpdate chi catts' ic)
            catts = lookup chi ic --req ctx (OpLookup chi ic)
            catts'= extend att Proxy (f inp) catts --req ctx (OpExtend  att (f Proxy inp) catts)
        in  Fam ic' sp

inhdefM ::( Update (ChiReco ('Prd prd nt)) ('Chi chi ('Prd prd nt) ntch) v2 ic
     , UpdateR (ChiReco ('Prd prd nt)) ('Chi chi ('Prd prd nt) ntch) v2 ic ~ ic'
     , ExtendR AttReco ('Att att t) t r ~ v2
     , Extend AttReco ('Att att t) t r
     , LookupR (ChiReco ('Prd prd nt))
               ('Chi chi ('Prd prd nt) ntch) ic ~ Attribution r
     , Lookup (ChiReco ('Prd prd nt)) ('Chi chi ('Prd prd nt) ntch) ic
     )
     => Label ('Att att t)
     -> Label ('Prd prd nt)
     -> Label ('Chi chi ('Prd prd nt) ntch)
     -> Reader (Fam ('Prd prd nt) sc ip) t
     -> Rule ('Prd prd nt) sc ip ic sp ic' sp
inhdefM att prd chi = inhdef att prd chi . runReader

data Lhs
lhs :: Label Lhs
lhs = Label

class At pos (att :: Att) m  where
  type ResAt pos att m
  at :: Label pos -> Label att -> m (ResAt pos att m)

instance
  ( LookupR AttReco ('Att att t) r ~ t
  , Lookup  AttReco ('Att att t) r
  , LookupR (ChiReco prd) ('Chi ch prd nt) chi ~ Attribution r
  , Lookup  (ChiReco prd) ('Chi ch prd nt) chi
  , nt ~ ('Left ('NT n))
  )=>
  At ('Chi ch prd nt) ('Att att t) (Reader (Fam prd chi par)) where
  type ResAt ('Chi ch prd nt) ('Att att t) (Reader (Fam prd chi par))
    = t
  at ch att
    = liftM (\(Fam chi _) -> let atts = lookup ch chi
                             in lookup att atts)
            ask

instance
  ( Lookup AttReco ('Att att t) par
  , LookupR AttReco ('Att att t) par ~ t
  )=>
  At Lhs ('Att att t) (Reader (Fam prd chi par)) where
  type ResAt Lhs ('Att att t) (Reader (Fam prd chi par))
    = t
  at lhs att
    = liftM (\(Fam chi par) -> lookup att par) ask


ter :: ( LookupR (ChiReco prd) ('Chi ch prd (Right ('T t))) chi ~ Attribution r
       , Lookup  (ChiReco prd) ('Chi ch prd (Right ('T t))) chi
       , LookupR AttReco ('Att "term" t) r ~ t
       , Lookup AttReco ('Att "term" t) r
       -- , pos ~ ('Chi ch prd (Right ('T t)))
       , m ~ Reader (Fam prd chi par)
       , ResAt ('Chi ch prd (Right ('T t))) ('Att "term" t) m ~ t
       )
    =>  Label ('Chi ch prd (Right ('T t)))
    -> m (ResAt ('Chi ch prd (Right ('T t))) ('Att "term" t) m)
ter (ch :: Label ('Chi ch prd (Right ('T t))))
  = liftM (\(Fam chi _)  -> let atts = lookup ch chi
                            in  lookup (lit @ t) atts)
          ask

singAsp r = r .+: emptyAspect

infixr 6 .+.
(.+.) = ext

class Kn (fcr :: [(Child, Type)]) (prd :: Prod) where
  type ICh fcr :: [(Child, [(Att, Type)])]
  type SCh fcr :: [(Child, [(Att, Type)])]
  kn :: Record fcr -> ChAttsRec prd (ICh fcr) -> ChAttsRec prd (SCh fcr)

instance Kn '[] prod where
  type ICh '[] = '[]
  type SCh '[] = '[] 
  kn _ _ = emptyCh


-------------------------------------------------------------------------
instance ( lch ~ 'Chi l prd nt
         , Kn fc prd
         , LabelSet ('(lch, sch) : SCh fc)
         , LabelSet ('(lch, ich) : ICh fc)
         , ExtendR (ChiReco prd) ('Chi l prd nt) sch (SCh fc)
                        ~ ('( 'Chi l prd nt, sch) : SCh fc)
         , Extend (ChiReco prd) ('Chi l prd nt) sch (SCh fc)  
         ) =>
  Kn ( '(lch , Attribution ich -> Attribution sch) ': fc) prd where
  type ICh ( '(lch , Attribution ich -> Attribution sch) ': fc)
    = '(lch , ich) ': ICh fc
  type SCh ( '(lch , Attribution ich -> Attribution sch) ': fc)
    = '(lch , sch) ': SCh fc
  kn ((ConsRec (TagField _ lch fch) (fcr :: Record fc)))
   = \((ConsCh pich icr) :: ChAttsRec prd ( '(lch, ich) ': ICh fc))
   -> let scr = kn fcr icr
          ich = unTaggedChAttr pich
      in extend lch Proxy (fch ich) scr



emptyCtx = Proxy @ '[]

knit' :: ( Kn fc prd
        , Empties fc prd)
 => Rule prd (SCh fc) ip (EmptiesR fc) '[] (ICh fc) sp
  -> Record fc -> Attribution ip -> Attribution sp
knit' (rule :: Rule prd (SCh fc) ip
              (EmptiesR fc) '[] (ICh fc) sp)
              (fc :: Record fc) ip
  = let (Fam ic sp) = rule (Fam sc ip) (Fam ec emptyAtt)
        sc          = kn fc ic
        ec          = empties fc
    in  sp


class Empties (fc :: [(Child,Type)]) (prd :: Prod) where
  type EmptiesR fc :: [(Child, [(Att, Type)])] 
  empties :: Record fc -> ChAttsRec prd (EmptiesR fc)

instance Empties '[] prd where
  type EmptiesR '[] = '[]
  empties _ = emptyCh

instance ( Empties fcr prd
         , chi ~ 'Chi ch prd nt
       --  , LabelSet ( '(chi, '[]) ': EmptiesR fcr)
         , Extend (ChiReco prd) ('Chi ch prd nt) '[] (EmptiesR fcr)
         )
 => Empties ( '(('Chi ch prd nt), Attribution e -> Attribution a) ': fcr) prd where
  type EmptiesR ( '(('Chi ch prd nt), Attribution e -> Attribution a) ': fcr)
    = ExtendR (ChiReco prd) ('Chi ch prd nt) '[] (EmptiesR fcr)
  empties (ConsRec pch fcr)
    = let lch = labelTChAtt pch
      in  extend lch Proxy emptyAtt (empties fcr) --(lch .= emptyAtt) .* (empties fcr)

knit(rule :: Rule prd (SCh fc) ip (EmptiesR fc) '[] (ICh fc) sp)
     (fc   :: Record fc)
     (ip   :: Attribution ip)
  = let (Fam ic sp) = rule (Fam sc ip) (Fam ec emptyAtt)
        sc          = kn fc ic
        ec          = empties fc
    in  sp


knitAspect (prd :: Label prd) asp fc ip
  = knit (lookup prd asp) fc ip

-----------------------------------------------------------------------------


tyAppAtt :: (forall b. Label ('Att name b)) -> Proxy a -> Label ('Att name a)
att `tyAppAtt` Proxy = att

tyAppChi :: (forall b. Label ('Chi name prd b))
  -> Proxy a -> Label ('Chi name prd a)
att `tyAppChi` Proxy = att

proxy2Label :: forall k (a :: k). Proxy a -> Label a
proxy2Label Proxy = Label

label2Proxy :: Label a -> Proxy a
label2Proxy Label = Proxy
----------------------------------------------------------------------------

