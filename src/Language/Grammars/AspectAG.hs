
{-|

Module      : Language.Grammars.AspectAG
Description : Main module, First-class attribute grammars
Copyright   : (c) Juan García Garland, 2018 
License     : LGPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX


The original version of the library is documented in the paper:
/Attribute Grammars Fly First-Class.
How to do aspect oriented programming in Haskell/

This was implemented from scratch using the improvements on GHC on the last
10 years, allowing a broad set of techniques for doing type level programming.

-}

{-# LANGUAGE TypeFamilies,
             FlexibleContexts,
             ScopedTypeVariables,
             NoMonomorphismRestriction,
             UnicodeSyntax,
             DataKinds,
             TypeOperators,
             PolyKinds,
             GADTs,
             MultiParamTypeClasses,
             FlexibleContexts,
             FlexibleInstances,
             UndecidableInstances
#-}

module Language.Grammars.AspectAG (
              module Language.Grammars.AspectAG,
              module Language.Grammars.AspectAG.Utils.Attribute,
              module Language.Grammars.AspectAG.Utils.Attribution,
              module Language.Grammars.AspectAG.Utils.ChildAtts,
              module Language.Grammars.AspectAG.Utils.Record,
              module Language.Grammars.AspectAG.Utils.TagUtils,
              module Language.Grammars.AspectAG.Utils.HList,
              module Language.Grammars.AspectAG.Utils.Notation
            ) where


import Language.Grammars.AspectAG.Utils.HList
import Language.Grammars.AspectAG.Utils.Attribution
import Language.Grammars.AspectAG.Utils.Record
import Language.Grammars.AspectAG.Utils.Attribute
import Data.Kind
import Data.Tagged hiding (unTagged)
import Language.Grammars.AspectAG.Utils.TPrelude
import Data.Proxy
import Language.Grammars.AspectAG.Utils.ChildAtts
import Language.Grammars.AspectAG.Utils.TagUtils
import Language.Grammars.AspectAG.Utils.Notation
import GHC.TypeLits

-- | In each node of the grammar, the "Fam" contains a single attribution
--for the parent, and a collection (Record) of attributions for the children:
data Fam (c::[(k',[(k,Type)])]) (p :: [(k,Type)]) :: Type where
  Fam :: ChAttsRec c  -> Attribution p -> Fam c p


-- |Rules, aka definition of attribution computations
--Rules are defined as a mapping from an input family to an output family,
--the added arity is for make them composable

type Rule (sc  :: [(k',  [(k,  Type)])])
          (ip  :: [(k,        Type)])
          (ic  :: [(k', [(k, Type)])])
          (sp  :: [(k,       Type)])
          (ic' :: [(k', [(k, Type)])])
          (sp' :: [(k,       Type)])
  = Fam sc ip -> Fam ic sp -> Fam ic' sp'

-- | Composition of rules
ext :: Rule sc ip ic sp ic' sp'
  -> (Fam sc ip -> a0 -> Fam ic sp)
  -> (Fam sc ip -> a0 -> Fam ic' sp')
(f `ext` g) input = f input . g input


-- | Type level getters for Rules
type family Syn1 (rule :: Type) :: [(k', [(k, Type)])] where
  Syn1 (Rule sc ip ic  sp  ic'' sp'') = sc
type family Inh1 (rule :: Type) :: [(k, Type)] where
  Inh1 (Rule sc ip ic  sp  ic'' sp'') = ip
type family Syn2 (rule :: Type) :: [(k', [(k, Type)])] where
  Syn2 (Rule sc ip ic  sp  ic'' sp'') = ic
type family Inh2 (rule :: Type) :: [(k, Type)] where
  Inh2 (Rule sc ip ic  sp  ic'' sp'') = sp
type family Syn3 (rule :: Type) :: [(k', [(k, Type)])] where
  Syn3 (Rule sc ip ic  sp  ic'' sp'') = ic''
type family Inh3 (rule :: Type) :: [(k, Type)] where
  Inh3 (Rule sc ip ic  sp  ic'' sp'') = sp''




-- |The function 'syndef' adds the definition of a synthesized attribute.
--It takes a label 'att' representing the name of the new attribute, 
--a value 'val' to be assigned to this attribute, and it builds a function which 
--updates the output constructed thus far.
syndef  :: LabelSet ( '(att,val) ': sp) =>
    Label att -> val -> (Fam ic sp -> Fam ic ( '(att,val) ': sp))
syndef latt val (Fam ic sp) = Fam ic (latt =. val *. sp)

-- | The function 'synmod' modifies the definition of a synthesized attribute.
--   It takes a label 'att' representing the name of the attribute, 
--   a value 'val' to be assigned to this attribute, and it builds a function
--   which  updates the output constructed thus far.
synmod  ::  UpdateAtLabelAtt att val sp sp'
  =>  Label att -> val -> Fam ic sp -> Fam ic sp'
synmod att v (Fam ic sp) = Fam ic (updateAtLabelAtt att v sp)

------------------------------------------------------------------------------

-- | The function 'inhdef' introduces a new inherited attribute for 
--   a collection of non-terminals.
--   It takes the following parameters:
--     'att': the attribute which is being defined,
--     'nts': the non-terminals with which this attribute is being associated
--     'vals': a record labelled with child names and containing values, 
--              describing how to compute the attribute being defined at each 
--              of the applicable child  positions.
--   It builds a function which updates the output constructed thus far.
inhdef :: Defs att nts vals ic
  => Label att -> HList nts -> Record vals
  -> (Fam ic sp -> Fam (DefsR att nts vals ic) sp)
inhdef att nts vals (Fam ic sp) = Fam (defs att nts vals ic) sp


-- | singledef is an auxiliar function to implement Defs.
--   it inserts a definition into the attribution of the corresponding child
-- mch  ~ memnership of chld
-- mnts ~ membership of nonterminals

class SingleDef (mch::Bool)(mnts::Bool) att pv (ic ::[(k',[(k,Type)])]) where
  type SingleDefR mch mnts att pv ic :: [(k',[(k,Type)])]
  singledef :: Proxy mch -> Proxy mnts -> Label att -> pv -> ChAttsRec ic
                -> ChAttsRec (SingleDefR mch mnts att pv ic)

instance ( HasChildF lch ic
         , och ~ LookupByChildFR lch ic
         , UpdateAtChildF lch ( '(att,vch) ': och) ic
         , LabelSet ( '(att, vch) ': och)) =>
  SingleDef 'True 'True att (Tagged lch vch) ic where
  type SingleDefR 'True 'True att (Tagged lch vch) ic
    = UpdateAtChildFR lch ( '(att,vch) ': (LookupByChildFR lch ic)) ic
  singledef _ _ att pch ic
    = updateAtChildF (Label :: Label lch) ( att =. vch *. och) ic
    where lch = labelTChAtt pch
          vch = unTaggedChAtt pch
          och = lookupByChildF lch ic


-- | The class 'Defs' is defined by induction over the record 'vals' 
--   containing the new definitions. 
--   The function 'defs' inserts each definition into the attribution 
--   of the corresponding child.

class Defs att (nts :: [Type])
            (vals :: [(k,Type)]) (ic :: [(k',[(k,Type)])]) where
  type DefsR att nts vals ic :: [(k',[(k,Type)])]
  defs :: Label att -> HList nts -> Record vals -> ChAttsRec ic
       -> ChAttsRec (DefsR att nts vals ic)

instance Defs att nts '[] ic where
  type DefsR att nts '[] ic = ic
  defs _ _ _ ic = ic


instance ( Defs att nts vs ic
         , ic' ~ DefsR att nts vs ic
         , HMember t nts
         , HMemberRes t nts ~ mnts
         , HasLabelChildAttsRes (lch,t) ic' ~ mch
         , HasLabelChildAtts (lch,t) ic'
         , SingleDef mch mnts att (Tagged (lch,t) vch) ic') => 
  Defs att nts ( '((lch,t), vch) ': vs) ic where
  type DefsR att nts ( '((lch,t), vch) ': vs) ic
    = SingleDefR (HasLabelChildAttsRes (lch,t) (DefsR att nts vs ic))
                 (HMemberRes t nts)
                 att
                 (Tagged (lch,t) vch)
                 (DefsR att nts vs ic)
  defs att nts (ConsR pch vs) ic = singledef mch mnts att pch ic' 
      where ic'  = defs att nts vs ic
            lch  = labelLVPair pch
            mch  = hasLabelChildAtts lch ic'
            mnts = hMember (sndLabel lch) nts

-- * Aspects: Aspects are record that have a rule for each production:

-- | aspects are actually records
type Aspect = Record


-- | Let a Type for the fields:
type Prd prd rule = Tagged prd rule

labelPrd (Tagged v :: Tagged l v) = Label :: Label l 
rulePrd (Tagged v)= v


-- | Lets define the combination of aspects. When labels are only present once,
--  the new aspect has a copy of the field. In the other hand, when a label is
--  repeated, rules are combined with the function ext.
class Com (r :: [(k,Type)]) (s :: [(k, Type)]) where
  type (.++.) r s :: [(k,Type)]
  (.+.) :: Aspect r -> Aspect s -> Aspect (r .++. s)


-- | ComSingle inserts one Rule in an aspect
-- The boolean parameter is True if prd is a label in the record.
class ComSingle (b::Bool) (prd :: k) (rule :: Type) (r :: [(k,Type)]) where
  type ComSingleR b prd rule r :: [(k, Type)]
  comSingle :: Proxy b -> Prd prd rule -> Aspect r
            -> Aspect (ComSingleR b prd rule r)


-- | When there is no production with the name prd, the map is simply extended
instance ( LabelSet ('(prd, rule) ': r)) => 
  ComSingle 'False prd rule r where
  type ComSingleR 'False prd rule r = '(prd, rule) ': r
  comSingle _ prd asp = prd .*. asp

-- | When the production is already defined, the new
-- rule must be combined with the previous one
instance ( UpdateAtLabelRecF prd (Rule sc ip ic  sp  ic'' sp'') r
         , HasFieldRec prd r
         , LookupByLabelRec prd r ~ (Rule sc ip ic' sp' ic'' sp'')
         , ic'' ~ (Syn3 (LookupByLabelRec prd r))
         , sp'' ~ (Inh3  (LookupByLabelRec prd r))
         ) =>
  ComSingle 'True prd (Rule sc ip ic  sp  ic'  sp') r where
  type ComSingleR 'True prd (Rule sc ip ic  sp  ic'  sp') r
    = UpdateAtLabelRecFR prd (Rule sc ip ic sp (Syn3 (LookupByLabelRec prd r))
                                               (Inh3 (LookupByLabelRec prd r))) r
  comSingle _ f r = updateAtLabelRecF l (oldR `ext` newR) r 
    where l    = labelPrd f
          oldR = lookupByLabelRec l r
          newR = rulePrd f


-- | Unicode pretty operator
(⊕) :: (Com r s) => Aspect r -> Aspect s -> Aspect (r .++. s)
(⊕) = (.+.)


-- | The proper Com, by induction over the second Aspect.

-- | The empty record is a neutral element by right
instance Com r '[] where
  type r .++. '[] = r
  r .+. _ = r

-- | For the recursive step, take the head of the second argument,
-- use comsingle on the first parameter, call (.+.) with the result
-- and the tail
instance ( Com (ComSingleR (HasLabelRecRes prd r) prd rule r)  r'
         , HasLabelRecRes prd r ~ b
         , HasLabelRec prd r
         , ComSingle b prd rule r)
  => Com r ( '(prd, rule) ': r') where
     type r .++. ( '(prd, rule) ': r')
       = (ComSingleR (HasLabelRecRes prd r) prd rule r) .++. r'
     r .+. (pr `ConsR` r') = let b   = hasLabelRec (labelPrd pr) r
                                 r'''= comSingle b pr r
                                 r'' = r''' .+. r'
                             in  r''



------------------------------------------------------------------------------



class Empties (fc :: [(k,Type)]) where
  type EmptiesR fc :: [(k, [(k, Type)])] -- KnownBug, k = k' from here
  empties :: Record fc -> ChAttsRec (EmptiesR fc)


instance Empties '[] where
  type EmptiesR '[] = '[]
  empties EmptyR = EmptyCh


instance ( Empties fcr
         , LabelSet ( '(lch, '[]) ': EmptiesR fcr)) =>
  Empties ( '(lch, fch) ': fcr) where
  type EmptiesR ( '(lch, fch) ': fcr) = '(lch, '[]) ': EmptiesR fcr
  empties (ConsR pch fcr)
    = let lch = labelTChAtt pch
      in  (lch .= emptyAtt) .* (empties fcr)


-- the Kn class

class Kn (fcr :: [(k, Type)]) where
  type ICh fcr :: [(k, [(k, Type)])]
  type SCh fcr :: [(k, [(k, Type)])]
  kn :: Record fcr -> ChAttsRec (ICh fcr) -> ChAttsRec (SCh fcr)

instance Kn '[] where
  type ICh '[] = '[]
  type SCh '[] = '[] 
  kn _ _ = EmptyCh

instance ( Kn fc
         , LabelSet ('(lch, sch) : SCh fc)
         , LabelSet ('(lch, ich) : ICh fc)) => 
  Kn ( '(lch , Attribution ich -> Attribution sch) ': fc) where
  type ICh ( '(lch , Attribution ich -> Attribution sch) ': fc)
    = '(lch , ich) ': ICh fc
  type SCh ( '(lch , Attribution ich -> Attribution sch) ': fc)
    = '(lch , sch) ': SCh fc
  kn (ConsR pfch fcr) (ConsCh pich icr)
   = let scr = kn fcr icr
         lch = labelTChAtt pfch
         fch = unTagged pfch
         ich = unTaggedChAttr pich
     in ConsCh (TaggedChAttr lch (fch ich)) scr


-- | The function 'knit' takes the combined rules for a node and the 
--   semantic functions of the children, and builds a
--   function from the inherited attributes of the parent to its
--   synthesized attributes.
knit :: ( Empties fc
        , Kn fc ) =>
  Rule (SCh fc) ip (EmptiesR fc) '[] (ICh fc) sp
     -> Record fc -> Attribution ip -> Attribution sp
knit rule fc ip
  = let ec          = empties fc
        (Fam ic sp) = rule (Fam sc ip) (Fam ec emptyAtt)
        sc          = kn fc ic
    in  sp

