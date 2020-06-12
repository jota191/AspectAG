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
  (

    -- -- * Rules
    -- Rule, CRule(..),
    
    -- -- ** Defining Rules
    -- syndef, syndefM, syn,
    
    -- synmod, synmodM,


    -- inh, inhdef, inhdefM,

    -- inhmod, inhmodM, 

    -- emptyRule,
    -- emptyRuleAtPrd,
    -- ext,
    
    -- -- * Aspects 
    -- -- ** Building Aspects.
    
    -- emptyAspect,
    -- singAsp,
    -- extAspect,
    -- comAspect,
    -- (.+:),(◃),
    -- (.:+.),(▹),
    -- (.:+:),(⋈),
    
    
    -- CAspect(..),
    -- Label(Label), Prod(..), T(..), NT(..), Child(..), Att(..),
    -- (.#), (#.), (=.), (.=), (.*), (*.),
    -- emptyAtt,
    -- ter,
    -- at, lhs,
    -- sem_Lit,
    -- knitAspect,
    -- traceAspect,
    -- traceRule,
    -- copyAtChi,
    -- use,
    -- emptyAspectC,
    -- emptyAspectForProds,
    -- module Data.GenRec,
    -- module Language.Grammars.AspectAG.HList
  )
  where


import Language.Grammars.AspectAG.HList
import Language.Grammars.AspectAG.RecordInstances

import Data.Type.Require hiding (emptyCtx)

import Data.GenRec
import Data.GenRec.Label

import Data.Kind
import Data.Proxy
import GHC.TypeLits

import Data.Maybe
import Data.Type.Equality
import Control.Monad.Reader

import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.Ord
import Data.Singletons.Prelude.Eq
import Data.Singletons.CustomStar


class SemLit a where
  sem_Lit :: a -> Attribution ('[] :: [(Att,Type)])
               -> Attribution '[ '( 'Att "term" a , a)]
  lit     :: Sing ('Att "term" a)
instance SemLit a where
  sem_Lit a _ = (SAtt (SSym :: Sing "term") undefined =. a) *. emptyAtt
  lit         = SAtt (SSym @ "term") undefined


-- * Families and Rules

-- | In each node of the grammar, the "Fam" contains a single attribution
-- for the parent, and a collection (Record) of attributions for
-- the children:
data Fam (prd :: Prod)
         (c :: [(Child, [(Att, Type)])])
         (p :: [(Att, Type)]) :: Type
 where
  Fam :: Sing prd -> ChAttsRec prd c -> Attribution p -> Fam prd c p


-- | getter
chi :: Fam prd c p -> ChAttsRec prd c
chi (Fam _ c _) = c

-- | getter
par :: Fam prd c p -> Attribution p
par (Fam _ _  p) = p

-- | getter (extracts a 'Label')
prd :: Fam prd c p -> Sing prd
prd (Fam l _ _) = l

-- | Rules are a function from the input family to the output family,
-- with an extra arity to make them composable.  They are indexed by a production.
type Rule
  (prd  :: Prod)
  (sc   :: [(Child, [(Att, Type)])])
  (ip   :: [(Att,       Type)])
  (ic   :: [(Child, [(Att, Type)])])
  (sp   :: [(Att,       Type)])
  (ic'  :: [(Child, [(Att, Type)])])
  (sp'  :: [(Att,       Type)])
  = Fam prd sc ip -> Fam prd ic sp -> Fam prd ic' sp'

-- | Rules with context (used to print domain specific type errors).
data CRule prd sc ip ic sp ic' sp'
  = CRule { prod :: Sing prd,
            mkRule :: Rule prd sc ip ic sp ic' sp'}

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



ext' ::  CRule prd sc ip ic sp ic' sp'
     ->  CRule prd sc ip a b ic sp
     ->  CRule prd sc ip a b ic' sp'
(CRule p f) `ext'` (CRule _ g)
 = CRule p $ \input -> f input . g input


-- | Given two rules for a given (the same) production, it combines
-- them. Note that the production equality is visible in the context,
-- not sintactically. This is a use of the 'Require' pattern.
ext ::  RequireEq prd prd' (Text "ext":ctx) 
     => CRule prd sc ip ic sp ic' sp'
     -> CRule prd' sc ip a b ic sp
     -> CRule prd sc ip a b ic' sp'
ext = ext'

type family (r :: Type) :+. (r' :: Type) :: Type
type instance
 (CRule prd sc ip ic sp ic' sp') :+.
 (CRule prd sc ip a  b  ic  sp ) =
  CRule prd sc ip a  b  ic' sp'

type family
 ComRA (prd :: Prod) (rule :: Type) (r :: [(Prod, Type)]) :: [(Prod, Type)]
 where
  ComRA prd rule '[] = '[ '(prd, rule)]
  ComRA prd (CRule prd sc ip ic sp ic' sp')
         ( '(prd', CRule prd sc ip a  b  ic  sp ) ': r) =
    FoldOrdering (Compare prd prd')
     {-LT-} (  '(prd, CRule prd sc ip ic sp ic' sp')
            ': '(prd', CRule prd sc ip a  b  ic  sp )
            ': r)
    
     {-EQ-} ( '(prd, (CRule prd sc ip ic sp ic' sp')
                 :+. (CRule prd sc ip a  b  ic  sp))
            ': r)

     {-GT-} ('(prd', CRule prd sc ip a  b  ic  sp)
            ':  ComRA prd (CRule prd sc ip ic sp ic' sp') r)


class ExtAspect a where
  extAspect
   :: CRule prd sc ip ic sp ic' sp'
   -> Aspect (a :: [(Prod, Type)])
   -> Aspect (ComRA prd (CRule prd sc ip ic sp ic' sp') a)

instance ExtAspect '[] where
  extAspect cr@(CRule p r) EmptyRec = ConsRec (TagField Proxy p cr) EmptyRec

instance ( CRule prd sc ip a1 b  ic  sp  ~ WrapField PrdReco v
         , ExtAspect a)
  =>
  ExtAspect ('(prd, CRule prd sc ip a1 b  ic  sp ) ': a) where
  extAspect cr@((CRule p r) :: CRule prd sc ip ic sp ic' sp')
            re@(ConsRec lv@(TagField _ p' (r' :: CRule prd sc ip a1 b  ic  sp )) rs) =
    case sCompare p p' of
      SLT -> ConsRec (TagField Proxy p cr) re
      SEQ -> ConsRec (TagField Proxy p ((cr `ext'` r') :: CRule prd sc ip a  b  ic' sp')) rs
      SGT -> ConsRec lv (extAspect cr rs)

-- extAspect
--   :: CRule prd sc ip ic sp ic' sp'
--   -> Aspect (a :: [(Prod, Type)])
--   -> Aspect (ComRA prd (CRule prd sc ip ic sp ic' sp') a)
-- extAspect cr@(CRule p r) EmptyRec = ConsRec (TagField Proxy p cr) EmptyRec
-- extAspect cr@(CRule p r) re@(ConsRec (TagField _ p' r') rs) =
--   case sCompare p p' of
--     SLT -> ConsRec (TagField Proxy p cr) re
--     SEQ -> ConsRec (TagField Proxy p (cr `ext` r')) rs


{-
-- | The "cons" for 'CAspect's. It adds a 'Rule' `rule`
-- to a 'CAspect'. If there is no rule for that production in the
-- argument it is a record extension. If the production is there, the
-- rules are combined.
extAspect
  :: ExtAspect ctx prd sc ip ic sp ic' sp' a asp =>
     CRule ctx prd sc ip ic sp ic' sp'
     -> CAspect ctx a -> CAspect ctx asp
extAspect rule (CAspect fasp)
  = CAspect $ \ctx -> req ctx (OpComRA rule (fasp ctx))

type ExtAspect ctx prd sc ip ic sp ic' sp' a asp
  = (Require
        (OpComRA ctx prd (CRule ctx prd sc ip ic sp ic' sp') a) ctx,
      ReqR (OpComRA ctx prd (CRule ctx prd sc ip ic sp ic' sp') a)
      ~ Rec PrdReco asp) 

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


-- | Operator for 'comAspect'. It takes two 'CAspect's to build the
-- combination of both.
(.:+:) = comAspect
infixr 4 .:+:

-- | Unicode operator for 'comAspect' or '.:+:'. (\\bowtie)
(⋈) = comAspect
infixr 4 ⋈

-- | Singleton Aspect. Wraps a rule to build an Aspect from it.
singAsp r
  = r .+: emptyAspect

infixr 6 .+.
(.+.) = ext

-- | combine a rule with an aspect (wrapper)
data OpComRA (ctx  :: [ErrorMessage])
             (prd  :: Prod)
             (rule :: Type) -- TODO : doc this
             (a    :: [(Prod, Type)]) where
  OpComRA :: CRule ctx prd sc ip ic sp ic' sp'
          -> Aspect a -> OpComRA ctx prd (CRule ctx prd sc ip ic sp ic' sp') a

-- | combine a rule with an aspect (inner)
data OpComRA' (cmp  :: Ordering)
              (ctx  :: [ErrorMessage])
              (prd  :: Prod)
              (rule :: Type) -- TODO : doc this
              (a    :: [(Prod, Type)]) where
  OpComRA' :: Proxy cmp
           -> CRule ctx prd sc ip ic sp ic' sp'
           -> Aspect a
           -> OpComRA' cmp ctx prd (CRule ctx prd sc ip ic sp ic' sp') a

cRuleToTagField :: (CRule ctx prd sc ip ic sp ic' sp')
                -> TagField PrdReco prd (CRule ctx prd sc ip ic sp ic' sp')
cRuleToTagField =
  TagField Label Label

instance
  Require (OpComRA ctx prd (CRule ctx prd sc ip ic sp ic' sp') '[]) ctx where
  type ReqR (OpComRA ctx prd (CRule ctx prd sc ip ic sp ic' sp') '[]) =
    Aspect '[ '(prd, CRule ctx prd sc ip ic sp ic' sp')]
  req ctx (OpComRA rule EmptyRec) =
    ConsRec (cRuleToTagField rule) EmptyRec

instance
  Require (OpComRA' (Cmp prd prd') ctx prd rule ( '(prd', rule') ': asp )) ctx
  =>
  Require (OpComRA ctx prd rule ( '(prd', rule') ': asp )) ctx where
  type ReqR (OpComRA ctx prd rule ( '(prd', rule') ': asp )) =
    ReqR (OpComRA' (Cmp prd prd') ctx prd rule ( '(prd', rule') ': asp ))
  req ctx (OpComRA rule asp) =
    req ctx (OpComRA' (Proxy @ (Cmp prd prd')) rule asp)

instance
  ( Require (OpUpdate PrdReco prd (CRule ctx prd sc ip ic sp ic'' sp'') a) ctx
  , Require (OpLookup PrdReco prd a) ctx
  , ReqR (OpLookup PrdReco prd a) ~ CRule ctx prd sc ip ic sp ic' sp'
  , (IC (ReqR (OpLookup PrdReco prd a))) ~ ic
  , (SP (ReqR (OpLookup PrdReco prd a))) ~ sp
  ) =>
  Require
   (OpComRA' 'EQ ctx prd (CRule ctx prd sc ip ic' sp' ic'' sp'') a) ctx where
  type ReqR (OpComRA' 'EQ ctx prd (CRule ctx prd sc ip ic' sp' ic'' sp'') a) =
    ReqR (OpUpdate PrdReco prd
            (CRule ctx prd sc ip
             (IC (ReqR (OpLookup PrdReco prd a)))
             (SP (ReqR (OpLookup PrdReco prd a)))
            ic'' sp'') a)
  req ctx (OpComRA' _ crule asp) =
    let prd     = Label @ prd
        oldRule = req ctx (OpLookup prd asp)
        newRule = crule `ext` oldRule
    in  req ctx (OpUpdate prd newRule asp)

instance
  ( Require (OpComRA ctx prd rule asp) ctx
  -- , ReqR (OpComRA ctx prd rule asp) ~ Rec
  --                           PrdReco
  --                           (UnWrap
  --                              (ReqR (OpComRA ctx prd (CRule ctx prd sc ip ic sp ic' sp') asp)))
  , ReqR (OpComRA ctx prd rule asp) ~ Aspect a0
  )
  =>
  Require (OpComRA' 'GT ctx prd rule ( '(prd' , rule') ': asp)) ctx where
  type ReqR (OpComRA' 'GT ctx prd rule ( '(prd' , rule') ': asp)) =
    Aspect ( '(prd' , rule') ': UnWrap (ReqR (OpComRA ctx prd rule asp)))
  req ctx (OpComRA' _ crule (ConsRec crule' asp)) =
    ConsRec crule' $ req ctx (OpComRA crule asp)

instance 
  Require (OpComRA' 'LT ctx prd rule ( '(prd' , rule') ': asp)) ctx where
  type ReqR (OpComRA' 'LT ctx prd rule ( '(prd' , rule') ': asp)) =
    Aspect ( '(prd, rule) ': '(prd' , rule') ': asp)
  req ctx (OpComRA' _ crule asp) =
    ConsRec (TagField Label Label crule) asp




data OpComAsp  (al :: [(Prod, Type)])
               (ar :: [(Prod, Type)]) where
  OpComAsp :: Aspect al -> Aspect ar -> OpComAsp al ar

instance
  Require (OpComAsp '[] ar) ctx where
  type ReqR (OpComAsp '[] ar) = Aspect ar
  req ctx (OpComAsp _ ar) = ar

instance
 ( (ReqR (OpComRA ctx prd (CRule ctx prd sc ip ic sp ic' sp') ar))
   ~ (Rec PrdReco
    (UnWrap
      (ReqR (OpComRA ctx prd (CRule ctx prd sc ip ic sp ic' sp') ar))))
 , ReqR (OpComRA ctx prd (CRule ctx prd sc ip ic sp ic' sp') ar)
   ~ Rec PrdReco ar0
 , (Require (OpComAsp al ar0) ctx)
 , (Require
     (OpComRA ctx prd (CRule ctx prd sc ip ic sp ic' sp') ar) ctx)
 ) =>
  Require (OpComAsp
           ('(prd, CRule ctx prd sc ip ic sp ic' sp') ': al) ar) ctx where
  type ReqR (OpComAsp ('(prd, CRule ctx prd sc ip ic sp ic' sp') ': al) ar) =
    ReqR (OpComAsp al
      (UnWrap (ReqR
                (OpComRA ctx prd (CRule ctx prd sc ip ic sp ic' sp') ar))))
  req ctx (OpComAsp (ConsRec (TagField _ _ rul) al) ar)
    = req ctx (OpComAsp al (req ctx (OpComRA rul ar)))

type family IC (rule :: Type) where
  IC (Rule prd sc ip ic sp ic' sp') = ic
  IC (CRule ctx prd sc ip ic sp ic' sp') = ic
type family SP (rule :: Type) where
  SP (Rule prd sc ip ic sp ic' sp') = sp
  SP (CRule ctx prd sc ip ic sp ic' sp') = sp


type family Syndef t t' ctx ctx' att sp sp' prd :: Constraint where
  Syndef t t' ctx ctx' att sp sp' prd =
     ( RequireEq t t' ctx'
     , RequireR (OpExtend AttReco ('Att att t) t sp) ctx (Attribution sp')
     , ctx'
         ~ ((Text "syndef("
             :<>: ShowTE ('Att att t) :<>: Text ", "
             :<>: ShowTE prd :<>: Text ")") ': ctx)
     )

-- | The function 'syndef' adds the definition of a synthesized
--   attribute.  It takes an attribute label 'att' representing the
--   name of the new attribute; a production label 'prd' representing
--   the production where the rule is defined; a value 't'' to be
--   assigned to this attribute, given a context and an input
--   family. It updates the output constructed thus far.
syndef
  :: Syndef t t' ctx ctx' att sp sp' prd
  => forall sc ip ic . Label ('Att att t)
  -> Label prd
  -> (Proxy ctx' -> Fam prd sc ip -> t')
  -> CRule ctx prd sc ip ic sp ic sp'
syndef att prd f
  = CRule $ \ctx inp (Fam ic sp)
   ->  Fam ic $ req ctx (OpExtend att (f Proxy inp) sp)

-- | As 'syndef', the function 'syndefM' adds the definition of a
--   synthesized attribute.  It takes an attribute label 'att'
--   representing the name of the new attribute; a production label
--   'prd' representing the production where the rule is defined; a
--   value 't'' to be assigned to this attribute, given a context and
--   an input family. It updates the output constructed thus far. This
--   function captures the monadic behaviour of the family
--   updating. For instance, the following definition specifies a rule
--   for an attribute `att_size :: Label (Att "size" Int)` at the
--   prduction `p_cons :: Label (Prd "cons" (NT "List"))`. The value
--   is computed from the very same attribute value at a child
--   `ch_tail :: Chi "tail" (Prd "cons" (NT "List") (Left NT))`
--
-- @
-- foo = syndefM att_size p_cons $ do sizeatchi <- at ch_tail att_size
--                                    return (sizeatchi + 1)
-- @
syndefM
  :: Syndef t t' ctx ctx' att sp sp' prd
  => Label ('Att att t)
  -> Label prd
  -> Reader (Proxy ctx', Fam prd sc ip) t'
  -> CRule ctx prd sc ip ic sp ic sp'
syndefM att prd = syndef att prd . def


-- | This is simply an alias for 'syndefM'
syn = syndefM


-- | This is simply an alias for 'inhdefM'
inh = inhdefM


synmod
  :: RequireR (OpUpdate AttReco ('Att att t) t r) ctx (Attribution sp')
  => Label ('Att att t)
     -> Label prd
     -> (Proxy
           ((('Text "synmod(" ':<>: ShowTE ('Att att t)) :<>: Text ", "
                              ':<>: ShowTE prd :<>: Text ")")
              : ctx)
         -> Fam prd sc ip -> t)
     -> CRule ctx prd sc ip ic' r ic' sp'
synmod att prd f
  = CRule $ \ctx  inp (Fam ic sp)
           -> Fam ic $ req ctx (OpUpdate att (f Proxy inp) sp)


synmodM
  :: RequireR (OpUpdate AttReco ('Att att t) t r) ctx (Attribution sp')
  => Label ('Att att t)
     -> Label prd
     -> Reader ( Proxy ((('Text "synmod(" ':<>: ShowTE ('Att att t)) :<>: Text ", "
                                          ':<>: ShowTE prd :<>: Text ")")
                       : ctx)
               , Fam prd sc ip)
               t
     -> CRule ctx prd sc ip ic' r ic' sp'
synmodM att prd = synmod att prd . def


type family Inhdef t t' ctx ctx' att r v2 prd nt chi ntch ic ic' n where
  Inhdef t t' ctx ctx' att r v2 prd nt chi ntch ic ic' n =
    ( RequireEq t t' ctx'
    , RequireR  (OpExtend AttReco ('Att att t) t r) ctx (Attribution v2)
    , RequireR (OpUpdate (ChiReco ('Prd prd nt))
                 ('Chi chi ('Prd prd nt) ntch) v2 ic) ctx
                 (ChAttsRec ('Prd prd nt) ic')
    , RequireR (OpLookup (ChiReco ('Prd prd nt))
                 ('Chi chi ('Prd prd nt) ntch) ic) ctx
                 (Attribution r)
    , RequireEq ntch ('Left n) ctx'
    , ctx' ~ ((Text "inhdef("
                :<>: ShowTE ('Att att t)  :<>: Text ", "
                :<>: ShowTE ('Prd prd nt) :<>: Text ", "
                :<>: ShowTE ('Chi chi ('Prd prd nt) ntch) :<>: Text ")")
                ': ctx)
    )
  

inhdef
  :: Inhdef t t' ctx ctx' att r v2 prd nt chi ntch ic ic' n
     =>
     Label ('Att att t)
     -> Label ('Prd prd nt)
     -> Label ('Chi chi ('Prd prd nt) ntch)
     -> (Proxy ctx' -> Fam ('Prd prd nt) sc ip -> t')
     -> forall sp . CRule ctx ('Prd prd nt) sc ip ic sp ic' sp
inhdef  att prd chi f
  = CRule $ \ctx inp (Fam ic sp)
       -> let ic'   = req ctx (OpUpdate chi catts' ic)
              catts = req ctx (OpLookup chi ic)
              catts'= req ctx (OpExtend  att (f Proxy inp) catts)
          in  Fam ic' sp



inhdefM
  :: Inhdef t t' ctx ctx' att r v2 prd nt chi ntch ic ic' n
  =>
  Label ('Att att t)
  -> Label ('Prd prd nt)
  -> Label ('Chi chi ('Prd prd nt) ntch)
  -> Reader (Proxy ctx', Fam ('Prd prd nt) sc ip) t'
  -> CRule ctx ('Prd prd nt) sc ip ic sp ic' sp
inhdefM att prd chi = inhdef att prd chi . def




inhmod
  :: ( RequireEq t t' ctx'
     , RequireR (OpUpdate AttReco ('Att att t) t r) ctx
                (Attribution v2)
     , RequireR (OpUpdate (ChiReco ('Prd prd nt))
                ('Chi chi ('Prd prd nt) ntch) v2 ic) ctx
                (ChAttsRec ('Prd prd nt) ic')
     , RequireR (OpLookup (ChiReco ('Prd prd nt))
                ('Chi chi ('Prd prd nt) ntch) ic) ctx
                (Attribution r)
     , RequireEq ntch ('Left n) ctx'
     , ctx' ~ ((Text "inhmod("
                :<>: ShowTE ('Att att t)  :<>: Text ", "
                :<>: ShowTE ('Prd prd nt) :<>: Text ", "
                :<>: ShowTE ('Chi chi ('Prd prd nt) ntch) :<>: Text ")")
                ': ctx))
     =>
     Label ('Att att t)
     -> Label ('Prd prd nt)
     -> Label ('Chi chi ('Prd prd nt) ntch)
     -> (Proxy ctx' -> Fam ('Prd prd nt) sc ip -> t')
     -> CRule ctx ('Prd prd nt) sc ip ic sp ic' sp
inhmod att prd chi f
  = CRule $ \ctx inp (Fam ic sp)
       -> let ic'   = req ctx (OpUpdate chi catts' ic)
              catts = req ctx (OpLookup  chi ic)
              catts'= req ctx (OpUpdate  att (f Proxy inp) catts)
          in  Fam ic' sp


inhmodM
  :: ( RequireEq t t' ctx'
     , RequireR (OpUpdate AttReco ('Att att t) t r) ctx
                (Attribution v2)
     , RequireR (OpUpdate (ChiReco ('Prd prd nt))
                ('Chi chi ('Prd prd nt) ntch) v2 ic) ctx
                (ChAttsRec ('Prd prd nt) ic')
     , RequireR (OpLookup (ChiReco ('Prd prd nt))
                ('Chi chi ('Prd prd nt) ntch) ic) ctx
                (Attribution r)
     , RequireEq ntch ('Left n) ctx'
     , ctx' ~ ((Text "inhmod("
                :<>: ShowTE ('Att att t)  :<>: Text ", "
                :<>: ShowTE ('Prd prd nt) :<>: Text ", "
                :<>: ShowTE ('Chi chi ('Prd prd nt) ntch) :<>: Text ")")
                ': ctx))
     =>
     Label ('Att att t)
     -> Label ('Prd prd nt)
     -> Label ('Chi chi ('Prd prd nt) ntch)
     -> Reader (Proxy ctx', Fam ('Prd prd nt) sc ip) t'
     -> CRule ctx ('Prd prd nt) sc ip ic sp ic' sp
inhmodM att prd chi = inhmod att prd chi . def

data Lhs
lhs :: Label Lhs
lhs = Label

class At pos att m  where
 type ResAt pos att m
 at :: Label pos -> Label att -> m (ResAt pos att m)


instance ( RequireR (OpLookup (ChiReco prd) ('Chi ch prd nt) chi) ctx
                    (Attribution r)
         , RequireR (OpLookup AttReco ('Att att t) r) ctx t'
         , RequireEq prd prd' ctx
         , RequireEq t t' ctx
         , RequireEq ('Chi ch prd nt) ('Chi ch prd ('Left ('NT n)))  ctx
         )
      => At ('Chi ch prd nt) ('Att att t)
            (Reader (Proxy ctx, Fam prd' chi par))  where
 type ResAt ('Chi ch prd nt) ('Att att t) (Reader (Proxy ctx, Fam prd' chi par))
         = t 
 at ch att
  = liftM (\(ctx, Fam chi _)  -> let atts = req ctx (OpLookup ch chi)
                                 in  req ctx (OpLookup att atts))
          ask



instance
         ( RequireR (OpLookup AttReco ('Att att t) par) ctx t'
         , RequireEq t t' ctx
         )
 => At Lhs ('Att att t) (Reader (Proxy ctx, Fam prd chi par))  where
 type ResAt Lhs ('Att att t) (Reader (Proxy ctx, Fam prd chi par))
    = t
 at lhs att
  = liftM (\(ctx, Fam _ par) -> req ctx (OpLookup att par)) ask

def :: Reader (Proxy ctx, Fam prd chi par) a
    -> (Proxy ctx -> (Fam prd chi par) -> a)
def = curry . runReader

ter :: ( RequireR (OpLookup (ChiReco prd) pos chi) ctx
                  (Attribution r)
       , RequireR (OpLookup AttReco ('Att "term" t) r) ctx t'
       , RequireEq prd prd' ctx
       , RequireEq t t' ctx
       , RequireEq pos ('Chi ch prd (Right ('T t))) ctx
       , m ~ Reader (Proxy ctx, Fam prd' chi par) )
    =>  Label pos -> m (ResAt pos ('Att "term" t) m) 
 -- ter (ch :: Label ('Chi ch prd (Right ('T a))))  = at ch (lit @ a)
ter (ch :: Label ('Chi ch prd (Right ('T t))))
  = liftM (\(ctx, Fam chi _)  -> let atts = req ctx (OpLookup ch chi)
                                 in  req ctx (OpLookup (lit @ t) atts))
          ask



class Kn (fcr :: [(Child, Type)]) (prd :: Prod) where
  type ICh fcr :: [(Child, [(Att, Type)])]
  type SCh fcr :: [(Child, [(Att, Type)])]
  kn :: Record fcr -> ChAttsRec prd (ICh fcr) -> ChAttsRec prd (SCh fcr)

instance Kn '[] prod where
  type ICh '[] = '[]
  type SCh '[] = '[] 
  kn _ _ = emptyCh

instance ( lch ~ 'Chi l prd nt
         , Kn fc prd
         -- , LabelSet ('(lch, sch) : SCh fc)
         -- , LabelSet ('(lch, ich) : ICh fc)
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



emptyCtx = Proxy @ '[]

knit'
  :: ( Kn fc prd
     , Empties fc prd)
  => CRule '[] prd (SCh fc) ip (EmptiesR fc) '[] (ICh fc) sp
  -> Record fc -> Attribution ip -> Attribution sp
knit' (rule :: CRule '[] prd (SCh fc) ip
              (EmptiesR fc) '[] (ICh fc) sp)
              (fc :: Record fc) ip =
  let (Fam ic sp) = mkRule rule emptyCtx
                    (Fam sc ip) (Fam ec emptyAtt)
      sc          = kn fc ic
      ec          = empties fc
  in  sp


class Empties (fc :: [(Child,Type)]) (prd :: Prod) where
  type EmptiesR fc :: [(Child, [(Att, Type)])] 
  empties :: Record fc -> ChAttsRec prd (EmptiesR fc)

instance Empties '[] prd where
  type EmptiesR '[] = '[]
  empties _ = emptyCh

instance
  ( Empties fcr prd
  , chi ~ 'Chi ch prd nt
  )
  =>
  Empties ( '(chi, Attribution e -> Attribution a) ': fcr) prd where
  type EmptiesR ( '(chi, Attribution e -> Attribution a) ': fcr) =
    '(chi, '[]) ': EmptiesR fcr
  empties (ConsRec (TagField labelc
                   (labelch :: Label chi) fch) r) =
    ConsRec (TagField (Label @(ChiReco prd)) labelch emptyAtt) $ empties r


knit (ctx  :: Proxy ctx)
     (rule :: CRule ctx prd (SCh fc) ip (EmptiesR fc) '[] (ICh fc) sp)
     (fc   :: Record fc)
     (ip   :: Attribution ip)
  = let (Fam ic sp) = mkRule rule ctx
                       (Fam sc ip) (Fam ec emptyAtt)
        sc          = kn fc ic
        ec          = empties fc
    in  sp


knitAspect (prd :: Label prd) asp fc ip
  = let ctx  = Proxy @ '[]
        ctx' = Proxy @ '[Text "knit" :<>: ShowTE prd]
    in  knit ctx (req ctx' (OpLookup prd ((mkAspect asp) ctx))) fc ip

-- | use
class Use (att :: Att) (prd :: Prod) (nts :: [NT]) (a :: Type) sc
 where
  usechi :: Label att -> Label prd -> KList nts -> (a -> a -> a) -> ChAttsRec prd sc
         -> Maybe a

class Use' (mnts :: Bool) (att :: Att) (prd :: Prod) (nts :: [NT])
           (a :: Type) sc
 where
  usechi' :: Proxy mnts -> Label att -> Label prd -> KList nts
   -> (a -> a -> a)
   -> ChAttsRec prd sc -> Maybe a

instance Use prd att nts a '[] where
  usechi _ _ _ _ _ = Nothing

instance
  ( HMember' nt nts
  , HMemberRes' nt nts ~ mnts
  , Use' mnts att prd nts a ( '( 'Chi ch prd ('Left nt), attr) ': cs))
  =>
  Use att prd nts a ( '( 'Chi ch prd ('Left nt), attr) ': cs) where
  usechi att prd nts op ch
    = usechi' (Proxy @ mnts) att prd nts op ch

instance
  Use att prd nts a cs
  =>
  Use att prd nts a ( '( 'Chi ch prd ('Right t), attr) ': cs) where
  usechi att prd nts op (ConsRec _ ch)
    = usechi att prd nts op ch


instance
  Use att prd nts a cs
  =>
  Use' False att prd nts a ( '( 'Chi ch prd ('Left nt), attr) ': cs) where
  usechi' _ att prd nts op (ConsRec _ cs) = usechi att prd nts op cs

instance
  ( Require (OpLookup AttReco att attr)
            '[('Text "looking up attribute " ':<>: ShowTE att)
              ':$$: ('Text "on " ':<>: ShowTE attr)]
  , ReqR (OpLookup AttReco att attr) ~ a
  , Use att prd nts a cs
  , WrapField (ChiReco prd) attr ~ Attribution attr)  --ayudín
  =>
  Use' True att prd nts a ( '( 'Chi ch prd ('Left nt), attr) : cs) where
  usechi' _ att prd nts op (ConsRec lattr scr) =
    let attr = unTaggedChAttr lattr
        val  = attr #. att
    in  Just $ maybe val (op val) $ usechi att prd nts op scr


-- | Defines a rule to compute an attribute 'att' in the production
-- 'prd', by applying an operator to the values of 'att' in each non
-- terminal in the list 'nts'.

use
  :: UseC att prd nts t' sp sc sp' ctx
  => Label ('Att att t')
  -> Label prd
  -> KList nts
  -> (t' -> t' -> t')
  -> t'
  -> forall ip ic' . CRule ctx prd sc ip ic' sp ic' sp'
use att prd nts op unit
  = syndef att prd
  $ \_ fam -> maybe unit id (usechi att prd nts op $ chi fam)


type UseC att prd nts t' sp sc sp' ctx =
  ( Require (OpExtend  AttReco ('Att att t') t' sp) ctx
  ,  Use ('Att att t') prd nts t' sc
  ,  ReqR (OpExtend AttReco ('Att att t') t' sp)
     ~ Rec AttReco sp'
  )

class EmptyAspectSameShape (es1 :: [k]) (es2 :: [m])

instance (es2 ~ '[]) => EmptyAspectSameShape '[] es2
instance (EmptyAspectSameShape xs ys, es2 ~ ( '(y1,y2,y3,y4) ': ys))
  => EmptyAspectSameShape (x ': xs) es2


-- require KLIST de prods?, NO, eso está en el kind!
class
  EmptyAspectSameShape prds polyArgs
  =>
  EmptyAspect (prds :: [Prod])
              (polyArgs :: [([(Child, [(Att, Type)])], [(Att, Type)],
                             [(Child, [(Att, Type)])], [(Att, Type)] )])
              ctx where
  type EmptyAspectR prds polyArgs ctx :: [(Prod, Type)]
  emptyAspectC :: KList prds -> Proxy polyArgs
    -> CAspect ctx (EmptyAspectR prds polyArgs ctx)

instance
  EmptyAspect '[] '[] ctx where
  type EmptyAspectR '[] '[] ctx = '[]
  emptyAspectC _ _ = emptyAspect

instance
  ( EmptyAspect prds polys ctx
  , ExtAspect ctx prd sc ip ic sp ic sp
    (EmptyAspectR prds polys ctx)
    (EmptyAspectR (prd ': prds) ( '(sc, ip, ic, sp) ': polys) ctx)
  )
  =>
  EmptyAspect (prd ': prds) ( '(sc, ip, ic, sp) ': polys) ctx where
  type EmptyAspectR (prd ': prds) ( '(sc, ip, ic, sp) ': polys) ctx =
    UnWrap (ReqR (OpComRA '[] prd ((CRule '[] prd sc ip ic sp ic sp))
                  (EmptyAspectR prds polys ctx)))
  emptyAspectC (KCons prd prds) (p :: Proxy ( '(sc, ip, ic, sp) ': polys)) =
    (emptyRule :: CRule ctx prd sc ip ic sp ic sp) 
    .+: emptyAspectC @prds @polys prds (Proxy @ polys)

emptyAspectForProds prdList = emptyAspectC prdList Proxy

-- ** copy rules

-- | a rule to copy one attribute `att` from the parent to the children `chi`

copyAtChi att chi
  = inh att (prdFromChi chi) chi (at lhs att)

-- | to copy at many children
class CopyAtChiList (att :: Att)
                    (chi :: [Child])
                    (polyArgs :: [([(Child, [(Att, Type)])], [(Att, Type)],
                                   [(Child, [(Att, Type)])], [(Att, Type)],
                                   [(Child, [(Att, Type)])], [(Att, Type)] )])
                     ctx where
  type CopyAtChiListR att chi polyArgs ctx :: [(Prod, Type)]
  copyAtChiList :: Label att -> KList chi -> Proxy polyArgs
                -> CAspect ctx (CopyAtChiListR att chi polyArgs ctx)

instance CopyAtChiList att '[] '[] ctx where
  type CopyAtChiListR att '[] '[] ctx = '[]
  copyAtChiList _ _ _ = emptyAspect

-- instance
--   ( CopyAtChiList ('Att att t) chi polys ctx
--   , prd ~ Prd p nt
--   , tnt ~ Left nc
--   )
--   =>
--   CopyAtChiList ('Att att t) (Chi ch prd tnt ': chi)
--    ('(sc, ip, ic, sp, ic', sp') ': polys) ctx where
--   type CopyAtChiListR ('Att att t) (Chi ch prd tnt ': chi)
--    ('(sc, ip, ic, sp, ic', sp') ': polys) ctx =
--     UnWrap (ReqR (OpComRA '[] prd ((CRule '[] prd sc ip ic sp ic' sp'))
--                   (CopyAtChiListR ('Att att t) chi polys ctx)))
--   copyAtChiList att (KCons chi chs :: KList ('Chi ch prd tnt ': chs) )
--    (p :: Proxy ( '(sc, ip, ic, sp, ic', sp') ': polys))
--     = copyAtChi att chi
--     .+: copyAtChiList @('Att att t) @chs att chs (Proxy @polys)
-}
