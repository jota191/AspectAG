{-|
Module      : Language.Grammars.AspectAG
Description : Main module, First-class attribute grammars
Copyright   : (c) Juan García-Garland, Marcos Viera, 2019, 2020
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
{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE UnicodeSyntax             #-}

module Language.Grammars.AspectAG
 --  (

 --    -- * Rules
 --    Rule, CRule(..),
    
 --    -- ** Defining Rules
 --    syndef, syndefM, syn,
    
 --    --synmod, synmodM,


 --    inh, inhdef, inhdefM,

 --    --inhmod, inhmodM, 

 --    emptyRule,
 --    emptyRuleAtPrd,
 --    ext,
    
 --    -- * Aspects 
 --    -- ** Building Aspects.
    
 --    emptyAspect,
 --    singAsp,
 --    extAspect,
 --    comAspect,
 --    (.+:),(◃),
 --    (.:+.),(▹),
 --    (.:+:),(⋈),
 --    (.+.), (⋄),
    
 --    Terminal, NonTerminal,
 --    Label, Prod(..), T(..), NT(..), Child(..), Att(..),
 --    (.#), (#.), (=.), (.=), (.*), (*.),
 --    emptyAtt,
 --    ter,
 --    at, lhs,
 --    sem_Lit,
 --    knitAspect,
 --    -- traceAspect,
 --    -- traceRule,
 --    copyAtChi,
 --    copyAtChis,
 --    -- use,
 --    -- emptyAspectC,
 --    -- emptyAspectForProds,
 --    -- module Data.GenRec,
 --    -- module Language.Grammars.AspectAG.RecordInstances,
 --    module Language.Grammars.AspectAG.HList
    
 -- )
  where


import Language.Grammars.AspectAG.HList
import Language.Grammars.AspectAG.RecordInstances

import Data.Type.Require hiding (emptyCtx)

import Data.GenRec
import Data.GenRec.Label

import Data.Kind
import Data.Proxy
import GHC.TypeLits
import Data.Functor.Identity

import Data.Maybe
import Data.Type.Equality
import Control.Monad.Reader

import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.Ord
import Data.Singletons.Prelude.Eq
import Data.Singletons.Prelude.Either
import Data.Singletons.CustomStar
import Data.Singletons.Decide

import Data.Singletons.Prelude.List (SList(SNil,SCons))

import GHC.Types
import Unsafe.Coerce

instance SingI (a :: Type) where {}

class SemLit a where
  sem_Lit :: a -> Attribution ('[] :: [(Att,Type)])
               -> Attribution '[ '( 'Att "term" a , a)]
  lit     :: Sing ('Att "term" a)
instance SemLit a where
  sem_Lit a _ = (SAtt (SSym :: Sing "term") sing =. a) *. emptyAtt
  lit         = SAtt (SSym @ "term") sing



type instance  WrapField PrdReco (CRule p a b c d e f :: Type)
  = CRule p a b c d e f


data Extensibility = Extensible | NonExtensible

-- * Families and Rules

-- | In each node of the grammar, the "Fam" contains a single attribution
-- for the parent, and a collection (Record) of attributions for
-- the children:
data family GFam (prd :: Prod)
                 (ext :: Extensibility)
                 (c :: k1) -- [(Child, [(Att, Type)])])
                 (p :: k2) -- [(Att, Type)])
     :: Type

data instance GFam prd Extensible
  (c :: [(Child, [(Att, Type)])])
  (p ::[(Att, Type)]) where
  Fam :: Sing prd -> ChAttsRec prd c -> Attribution p -> Fam prd c p

type Fam prd (c :: [(Child, [(Att, Type)])]) (p ::[(Att, Type)])
  = GFam prd Extensible c p

-- | getter
chi :: Fam prd c p -> ChAttsRec prd c
chi (Fam _ c _) = c

-- | getter
par :: Fam prd c p -> Attribution p
par (Fam _ _  p) = p

-- | getter (extracts a 'Label')
prd :: Fam prd c p -> Sing prd
prd (Fam l _ _) = l


type family GRule (prd  :: Prod) (e :: Extensibility)
  (sc :: ksc) (ip :: kip)  (ic :: kic)
  (sp :: ksp) (ic' :: kic')(sp' :: ks')

type instance GRule prd e
  (sc   :: k1 ) -- [(Child, [(Att, Type)])])
  (ip   :: k2 ) -- [(Att,       Type)])
  (ic   :: k3 ) -- [(Child, [(Att, Type)])])
  (sp   :: k4 ) -- [(Att,       Type)])
  (ic'  :: k5 ) --[(Child, [(Att, Type)])])
  (sp'  :: k6 ) -- [(Att,       Type)])
  = GFam prd e sc ip -> GFam prd e ic sp -> GFam prd e ic' sp'

-- | Rules are a function from the input family to the output family,
-- with an extra arity to make them composable.
-- They are indexed by a production.
type Rule
  (prd  :: Prod)
  (sc   :: [(Child, [(Att, Type)])])
  (ip   :: [(Att,       Type)])
  (ic   :: [(Child, [(Att, Type)])])
  (sp   :: [(Att,       Type)])
  (ic'  :: [(Child, [(Att, Type)])])
  (sp'  :: [(Att,       Type)])
  = GRule prd Extensible sc ip ic sp ic' sp'

-- | Rules with context (used to print domain specific type errors).
data CRule prd sc ip ic sp ic' sp'
  = CRule { prod :: Sing prd,
            mkRule :: Rule prd sc ip ic sp ic' sp'}

--emptyRule :: SingI prd => CRule prd ic sp '[] '[] '[] '[]
emptyRule =
  CRule sing (\fam inp -> inp)


emptyRuleAtPrd :: Sing prd -> CRule prd sc ip ic' sp' ic' sp'
emptyRuleAtPrd prd = CRule prd (\fam inp -> inp)

-- | Aspects, tagged with context. 'Aspect' is a record instance having
-- productions as labels, containing 'Rule's as fields.
--newtype CAspect (asp :: [(Prod, Type)] )
--  = CAspect { mkAspect :: Proxy ctx -> Aspect asp}

-- | Recall that Aspects are mappings from productions to rules. They
-- have a record-like interface to build them. This is the constructor
-- for the empty Aspect.
emptyAspect :: Aspect '[]
emptyAspect  = EmptyRec

-- | combination of two Aspects. It merges them. When both aspects
-- have rules for a given production, in the resulting Aspect the rule
-- at that field is the combination of the rules for the arguments
-- (with 'ext').
-- comAspect ::
--   ( Require (OpComAsp al ar) ctx
--   , ReqR (OpComAsp al ar) ~ Aspect asp
--   )
--   =>  CAspect ctx al -> CAspect ctx ar -> CAspect ctx asp
-- comAspect al ar
--   = CAspect $ \ctx -> req ctx (OpComAsp (mkAspect al ctx) (mkAspect ar ctx))



-- | Given two rules for a given (the same) production, it combines
-- them. Note that the production equality is visible in the context,
-- not sintactically. This is a use of the 'Require' pattern.
-- ext :: CRule prd sc ip ic sp ic' sp'
--     -> CRule prd sce ipe a b ice spe
--     -> CRule prd sc ip a b ic' sp'
ext :: () --RequireEq prd prd' '[]
     => CRule prd sc ip ic sp ic' sp'
     -> CRule prd sc ip a r ic sp
     -> CRule prd sc ip a r ic' sp'
(CRule p f) `ext` (CRule _ g)
 = CRule p $ f `rext` g 

rext :: GRule prd e sc ip ic sp ic' sp'
     -> GRule prd e sc ip a r ic sp
     -> GRule prd e sc ip a r ic' sp'
f `rext` g = \inp -> f inp . g inp


------------------------------------------
--f :: RequireEq a b '[] => a -> b -> a
--f x y = x
--
--g = f

-- g True "" does NOT give the nice error, that's why we annotate all..
------------------------------------------
infixr 6 ⋄
(⋄) :: RequireEq prd prd' '[]
    => CRule prd sc ip ic sp ic' sp'
    -> CRule prd sc ip a r ic sp
    -> CRule prd sc ip a r ic' sp'
(⋄) = ext

infixr 6 .+.
(.+.) :: RequireEq prd prd' '[]
      => CRule prd sc ip ic sp ic' sp'
      -> CRule prd sc ip a r ic sp
      -> CRule prd sc ip a r ic' sp'
(.+.) = ext


type family (r :: Type) :+. (r' :: Type) :: Type
type instance
 (CRule prd sc ip ic sp ic' sp') :+.
 (CRule prd sc ip a  b  ic  sp ) =
  CRule prd sc ip a  b  ic' sp'
-- type instance
--  (CRule prd  sc ip ic sp ic' sp') :+.
--  (CRule prd' sc ip a  b  ic  sp ) =
--   CRule prd  sc ip a  b  ic' sp'

type family
 ComRA (rule :: Type) (r :: [(Prod, Type)]) :: [(Prod, Type)]
 where
  ComRA (CRule prd sc ip ic sp ic' sp') '[] =
    '[ '(prd, CRule prd sc ip ic sp ic' sp')]
  ComRA (CRule prd sc ip ic sp ic' sp')
        ( '(prd', CRule prd' sc1 ip1 ic1 sp1 ic1' sp1') ': r) =
    FoldOrdering (Compare prd prd')
     {-LT-} (  '(prd, CRule prd sc ip ic sp ic' sp')
            ': '(prd', CRule prd' sc1 ip1 ic1 sp1 ic1' sp1')
            ': r)
    
     {-EQ-} ( '(prd, (CRule prd sc ip ic sp ic' sp')
                 :+. CRule prd sc1 ip1 ic1 sp1 ic1' sp1')
            ': r)

     {-GT-} ('(prd', CRule prd' sc1 ip1 ic1 sp1 ic1' sp1')
            ':  ComRA (CRule prd sc ip ic sp ic' sp') r)
  ComRA anything asp = TypeError (Text "cannot combine rule with aspect")

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
class ExtAspect r a where
  extAspect
   :: r
   -> Aspect (a :: [(Prod, Type)])
   -> Aspect (ComRA r a)
class ExtAspect' (ord :: Ordering) r a where
  extAspect'
   :: Sing ord
   -> r
   -> Aspect (a :: [(Prod, Type)])
   -> Aspect (ComRA r a)

instance ExtAspect (CRule prd sc ip ic sp ic' sp') '[] where
  extAspect cr@(CRule p r) EmptyRec = ConsRec (TagField Proxy p cr) EmptyRec

instance (ExtAspect' (Compare prd prd') (CRule prd sc ip ic sp ic' sp')
            ('(prd', CRule prd' sc1 ip1 ic1 sp1 ic1' sp1') ': a))
  =>
  ExtAspect (CRule prd sc ip ic sp ic' sp')
            ('(prd', CRule prd' sc1 ip1 ic1 sp1 ic1' sp1') ': a) where
  extAspect cr@((CRule p r) :: CRule prd sc ip ic sp ic' sp')
            re@(ConsRec lv@(TagField _ p' r') rs) =
    let cmp = sCompare p p'
    in extAspect' cmp cr re

instance (Compare prd prd' ~ 'LT)
  =>
  ExtAspect' 'LT (CRule prd sc ip ic sp ic' sp')
             ('(prd', CRule prd' sc1 ip1 ic1 sp1 ic1' sp1') ': a) where
  extAspect' prf cr@((CRule p r) :: CRule prd sc ip ic sp ic' sp')
                 re@(ConsRec lv@(TagField _ p' r') rs) =
    case prf of
      SLT -> ConsRec (TagField Proxy p cr) re
instance
  (Compare prd prd' ~ 'GT
  , ExtAspect (CRule prd sc ip ic sp ic' sp') a
  )
  =>
  ExtAspect' 'GT (CRule prd sc ip ic sp ic' sp')
             ('(prd', CRule prd' sc1 ip1 ic1 sp1 ic1' sp1') ': a) where
  extAspect' prf cr@((CRule p r) :: CRule prd sc ip ic sp ic' sp')
                 re@(ConsRec lv@(TagField _ p' r') rs) =
    case prf of
      SGT -> ConsRec lv $ extAspect cr rs

instance
  ( Compare prd prd' ~ EQ
  , ip ~ ipe
  , ic ~ ice, sp ~ spe , sc ~ sce
  )
  =>
  ExtAspect' 'EQ (CRule prd sc ip ic sp ic' sp')
             ('(prd', CRule prd sc ip ic1 sp1 ice spe) ': a) where
  extAspect' prf cr@((CRule p r) :: CRule prd sc ip ic sp ic' sp')
                 re@(ConsRec lv@(TagField _ p' r') rs) =
    case prf of
      SEQ -> case decideEquality p p' of
        Just Refl
          -> ConsRec (TagField Proxy p (cr `ext` r')) rs
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- | An operator, alias for 'extAspect'. It combines a rule with an
-- aspect, to build a bigger one.
(.+:) = extAspect
infixr 3 .+:

-- | Unicode version of 'extAspect' or '.+:' (\\triangleleft)
(◃) = extAspect
infixr 3 ◃

-- | The other way, combines an aspect with a rule. It is a `flip`ped
-- 'extAspect'.
(.:+.) = flip extAspect
infixl 3 .:+.

-- | Unicode operator for '.:+.' or `flip extAspect`.
(▹) = flip extAspect
infixl 3 ▹


type family
  ComAsp (r1 :: [(Prod, Type)]) (r2 :: [(Prod, Type)]) :: [(Prod, Type)]
 where
  ComAsp '[] r2 = r2
  ComAsp r1 '[] = r1
  ComAsp ('(prd1, CRule prd1 sc1 ip1 ic1 sp1 ic1' sp1') ': r1)
         ('(prd2, CRule prd2 sc2 ip2 ic2 sp2 ic2' sp2') ': r2) =
    FoldOrdering (Compare prd1 prd2)
    {-LT-} ('(prd1, CRule prd1 sc1 ip1 ic1 sp1 ic1' sp1')
           ': ComAsp r1 ('(prd2, CRule prd2 sc2 ip2 ic2 sp2 ic2' sp2') ': r2)
           ) 
    -- {-EQ-} ( '(prd1, CRule prd1 sc1 ip1 ic1 sp1 ic1' sp1'
    --                  :+. CRule prd2 sc2 ip2 ic2 sp2 ic2' sp2')
    --        ': ComAsp r1 r2
    --        )
    {-EQ-} ( '(prd1, CRule prd1 sc1 ip1 ic1 sp1 ic1' sp1'
                     :+. CRule prd1 sc1 ip1 ic2 sp2 ic2' sp2')
           ': ComAsp r1 r2
           )
    {-GT-} ('(prd2, CRule prd2 sc2 ip2 ic2 sp2 ic2' sp2')
           ': ComAsp ('(prd1, CRule prd1 sc1 ip1 ic1 sp1 ic1' sp1') ': r1) r2
           )

class ComAspect (r1 :: [(Prod, Type)])(r2 :: [(Prod, Type)]) where
  comAspect :: Aspect r1 -> Aspect r2 -> Aspect (ComAsp r1 r2)
instance ComAspect '[] r2 where
  comAspect _ r = r
instance ComAspect r1 '[] where
  comAspect r _= r

instance
  (ComAspect' (Compare prd1 prd2)
       ('(prd1, CRule prd1 sc1 ip1 ic1 sp1 ic1' sp1') ': r1)
       ('(prd2, CRule prd2 sc2 ip2 ic2 sp2 ic2' sp2') ': r2) )
  => ComAspect
       ('(prd1, CRule prd1 sc1 ip1 ic1 sp1 ic1' sp1') ': r1)
       ('(prd2, CRule prd2 sc2 ip2 ic2 sp2 ic2' sp2') ': r2) where
  comAspect r1@(ConsRec (TagField _ prd1 crule1) asp1) 
            r2@(ConsRec (TagField _ prd2 crule2) asp2) =
    comAspect' (sCompare prd1 prd2) r1 r2

class
  ComAspect' (ord :: Ordering)
             (r1 :: [(Prod, Type)])
             (r2 :: [(Prod, Type)]) where
  comAspect' :: Sing ord -> Aspect r1 -> Aspect r2
             -> Aspect (ComAsp r1 r2)

instance
  ( Compare prd1 prd2 ~ LT
  , ComAspect r1 ('(prd2, CRule prd2 sc2 ip2 ic2 sp2 ic2' sp2') ': r2))
  => ComAspect' LT
            ('(prd1, CRule prd1 sc1 ip1 ic1 sp1 ic1' sp1') ': r1) 
            ('(prd2, CRule prd2 sc2 ip2 ic2 sp2 ic2' sp2') ': r2) where
  comAspect' _ r1@(ConsRec cr1@(TagField _ prd1 crule1) asp1) 
               r2@(ConsRec cr2@(TagField _ prd2 crule2) asp2) =
    ConsRec cr1 $ comAspect asp1 r2
instance
  ( Compare prd1 prd2 ~ EQ
  , prd1 ~ prd2
  , ComAspect r1 r2
  , sc ~ sc1, ip ~ ip1, ic ~ ic1, sp ~ sp1
  )
  => ComAspect' EQ
            ('(prd1, CRule prd1 sc  ip  ic  sp  ic1' sp1') ': r1)
            ('(prd2, CRule prd2 sc1 ip1 ic2 sp2 ic1  sp1) ': r2) where
  comAspect' _ r1@(ConsRec cr1@(TagField p prd1 crule1) asp1) 
               r2@(ConsRec cr2@(TagField _ prd2 crule2) asp2) =
       ConsRec (TagField p prd1 (crule1 `ext` crule2))$ comAspect asp1 asp2
instance
  ( Compare prd1 prd2 ~ GT
  , ComAspect ('(prd1, CRule prd1 sc1 ip1 ic1 sp1 ic1' sp1') ': r1) r2)
  => ComAspect' GT
            ('(prd1, CRule prd1 sc1 ip1 ic1 sp1 ic1' sp1') ': r1) 
            ('(prd2, CRule prd2 sc2 ip2 ic2 sp2 ic2' sp2') ': r2) where
  comAspect' _ r1@(ConsRec cr1@(TagField _ prd1 crule1) asp1) 
               r2@(ConsRec cr2@(TagField _ prd2 crule2) asp2) =
    ConsRec cr2 $ comAspect r1 asp2


-- | Operator for 'comAspect'. It takes two 'CAspect's to build the
-- combination of both.
(.:+:) = comAspect
infixr 4 .:+:

-- | Unicode operator for 'comAspect' or '.:+:'. (\\bowtie)
(⋈) = comAspect
infixr 4 ⋈

-- | Singleton Aspect. Wraps a rule to build an Aspect from it.
singAsp r
  = r  .+: emptyAspect


syndef att prd f
  = CRule prd $ \inp (Fam prd' ic sp)
   ->  Fam prd ic $ att .=. (f inp) .*. sp


syndefM att prd = syndef att prd . runReader
syn = syndefM

-- inhdef
--   :: (Update (ChiReco prd) l
--              (Extend AttReco att val (Lookup (ChiReco prd) l r))
--              r ~ chis
--      , att ~ ('Att attsym val)
--      , prd ~ ('Prd prdsym nt)
--      , l ~ 'Chi chisym ('Prd prdsym nt) ntch -- ('Left n)
--      )
--   => Sing att
--   -> Sing prd
--   -> Sing l
--   -> (Fam prd sc ip -> val)
--   -> CRule prd sc ip r sp'
--           chis
--           sp'
inhdef att prd chi f
  = CRule prd $ \inp (Fam prd ic sp)
       -> let ic'   = update chi Proxy catts' ic
              catts = ic .# chi
              catts'= att =. f inp *. catts
          in  Fam prd ic' sp
inhdefM att prd chi =
  inhdef att prd chi . runReader

inh = inhdefM

class At pos att m where
 type ResAt pos att m
 at :: Sing pos -> Sing att -> m (ResAt pos att m)



instance
  At ('Chi ch prd nt) ('Att att t)
        (Reader (Fam prd chi par))  where
  type ResAt ('Chi ch prd nt) ('Att att t) (Reader (Fam prd chi par))
    = Lookup AttReco ('Att att t) (Lookup (ChiReco prd) ('Chi ch prd nt) chi)
  at ch att
    = liftM (\(Fam _ chi _)  -> let atts = chi # ch
                                in  atts # att)
      ask

instance
  At 'Lhs ('Att att t) (Reader (Fam prd chi par))  where
  type ResAt 'Lhs ('Att att t) (Reader (Fam prd chi par))
    = Lookup AttReco ('Att att t) par
  at lhs att
    = liftM (\(Fam _ _ par) -> par #. att) ask

ter :: Sing ('Chi ch prd (Right ('T t)))
    -> Reader (Fam prd chi par)
       (ResAt ('Chi ch prd (Right ('T t))) ('Att "term" t)
         (Reader (Fam prd chi par))) 
ter (ch :: Sing ('Chi ch prd (Right ('T t))))
  = liftM (\(Fam _ chi _)  -> let atts = chi # ch
                              in  atts # (lit @ t))
          ask

class Kn (fcr :: [(Child, Type)]) (prd :: Prod) where
  type ICh fcr :: [(Child, [(Att, Type)])]
  type SCh fcr :: [(Child, [(Att, Type)])]
  kn :: Record fcr -> ChAttsRec prd (ICh fcr) -> ChAttsRec prd (SCh fcr)

instance Kn '[] prod where
  type ICh '[] = '[]
  type SCh '[] = '[] 
  kn _ _ = emptyCh

instance (-- lch ~ 'Chi l prd nt
          Kn fc prd
         ) =>
  Kn ( '(lch , Attribution ich -> Attribution sch) ': fc) prd where
  type ICh ( '(lch , Attribution ich -> Attribution sch) ': fc)
    = '(lch , ich) ': ICh fc
  type SCh ( '(lch , Attribution ich -> Attribution sch) ': fc)
    = '(lch , sch) ': SCh fc
  kn ((ConsRec (TagField _ lch fch) (fcr :: Record fc)))
   = \((ConsRec pich icr) :: ChAttsRec prd ( '(lch, ich) ': ICh fc))
   -> let scr = kn fcr icr
          ich = unTaggedChAttr pich
      in ConsRec (TaggedChAttr lch
               (fch ich)) scr
class Empties (fc :: [(Child,Type)]) (prd :: Prod) where
  type EmptiesR fc :: [(Child, [(Att, Type)])] 
  empties :: Record fc -> ChAttsRec prd (EmptiesR fc)

instance Empties '[] prd where
  type EmptiesR '[] = '[]
  empties _ = emptyCh

instance
  ( Empties fcr prd
 --  , chi ~ 'Chi ch prd nt
  )
  =>
  Empties ( '(chi, Attribution e -> Attribution a) ': fcr) prd where
  type EmptiesR ( '(chi, Attribution e -> Attribution a) ': fcr) =
    '(chi, '[]) ': EmptiesR fcr
  empties (ConsRec (TagField labelc
                   (labelch :: Sing chi) fch) r) =
    ConsRec (TagField (Proxy @(ChiReco prd)) labelch emptyAtt) $ empties r


knit (rule :: CRule prd (SCh fc) ip (EmptiesR fc) '[] (ICh fc) sp)
     (fc   :: Record fc)
     (ip   :: Attribution ip)
  = let (Fam p ic sp) = mkRule rule
                        (Fam p sc ip) (Fam p ec emptyAtt)
        sc            = kn fc ic
        ec            = empties fc
    in  sp


knitAspect (prd :: Sing prd) (asp :: Aspect asp) fc ip
  = knit (asp # prd) fc ip

-- * common patterns

copyAtChi
  :: (KnownSymbol prd, SingI nt)
  => Sing ('Att att t)
  -> Sing ('Chi ch ('Prd prd nt) ('Left nt'))
  -> CopyAtChi ('Att att t) ('Chi ch ('Prd prd nt) ('Left nt')) sc ip ic sp'
copyAtChi att chi = inh att (prodFromChi chi) chi (at lhs att) 

type family CopyAtChi att chi sc ip ic sp' where
  CopyAtChi ('Att att t) ('Chi ch ('Prd prd nt) ('Left nt')) sc ip ic sp' =
    CRule ('Prd prd nt) sc ip ic sp'
            (Update
              (ChiReco ('Prd prd nt))
              ('Chi ch ('Prd prd nt) ('Left nt'))
              (Extend AttReco ('Att att t)
                (ResAt 'Lhs ('Att att t)
                 (ReaderT (Fam ('Prd prd nt) sc ip) Identity))
                (Lookup
                   (ChiReco ('Prd prd nt))
                   ('Chi ch ('Prd prd nt) ('Left nt')) ic))
             ic) sp'

-- ** copy at chis

class
  SameShape4 chis polyArgs
  => 
  CopyAtChis (att  :: Att)
             (chis :: [Child])
             (polyArgs :: [([(Child, [(Att, Type)])], [(Att, Type)],
                             [(Child, [(Att, Type)])], [(Att, Type)])])
                      where
  type CopyAtChisR att chis polyArgs :: [(Prod, Type)]
  copyAtChis :: Sing att -> SList chis -> Proxy polyArgs
             -> Aspect (CopyAtChisR att chis polyArgs)

instance CopyAtChis att '[] '[] where
  type CopyAtChisR att '[] '[] = '[]
  copyAtChis _ _ _ = emptyAspect

instance
  ( CopyAtChis ('Att att t) chis polys
  , SingI nt
  , ExtAspect (CopyAtChi ('Att att t) ('Chi ch ('Prd prd nt) tnt) sc ip ic sp')
    (CopyAtChisR ('Att att t) chis polys)
  )
  =>
  CopyAtChis ('Att att t)
             (Chi ch ('Prd prd nt) tnt ': chis)
             ('(sc, ip, ic, sp') ': polys) where
  type CopyAtChisR ('Att att t)
                   (Chi ch ('Prd prd nt) tnt ': chis)
                   ('(sc, ip, ic, sp') ': polys) =
    ComRA (CopyAtChi ('Att att t) ('Chi ch ('Prd prd nt) tnt) sc ip ic sp')
    (CopyAtChisR ('Att att t) chis polys)
  copyAtChis att@(SAtt syatt st)
            (SCons chi@(SChi SSym (SPrd SSym (nt :: Sing nt)) (SLeft t)) chis)
            (proxy :: Proxy ( '(sc, ip, ic, sp') ': polys)) =
    copyAtChi @_ @_ @_ @_ @_ @_ @sc @ip @ic @sp' (SAtt syatt st) chi
    .+: copyAtChis att chis (Proxy @ polys)

-- | SameShape forces its second arg to have the same shape of first arg 
class SameShape (es1 :: [k]) (es2 :: [m])
instance (es2 ~ '[]) => SameShape '[] es2
instance (SameShape xs ys, es2 ~ ( y ': ys))
  => SameShape (x ': xs) es2

-- | SameShape4 forces its second arg to have the same length of fitrst arg,
-- plus being a list of 4-tuples
class SameShape4 (es1 :: [k]) (es2 :: [m])
instance (es2 ~ '[]) => SameShape4 '[] es2
instance (SameShape4 xs ys, es2 ~ ( '(y1, y2, y3, y4) ': ys))
  => SameShape4 (x ': xs) es2
