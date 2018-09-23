{-|

Module      : Language.Grammars.AspectAG
Description : Main module, First-class attribute grammars
Copyright   : (c) Juan García Garland, 2018 
License     : LGPL
Maintainer  : jpgarcia@fing.edu.uy
Stability   : experimental
Portability : POSIX


The original version of the library is documented in the paper:
/Attribute Grammars Fly First-Class. How to do aspect oriented programming in Haskell/

This was implemented from scratch using the improvements on GHC on the last
10 years, allowing a broad set of techniques for doing type level programming.

-}

{-# LANGUAGE TypeInType,
             GADTs,
             KindSignatures,
             TypeOperators,
             TypeFamilies,
             MultiParamTypeClasses,
             FlexibleInstances,
             FlexibleContexts,
             StandaloneDeriving,
             UndecidableInstances,
             FunctionalDependencies,
             ConstraintKinds,
             ScopedTypeVariables,
             DataKinds
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

--type Rule sc ip ic sp ic' sp'
--  = Fam sc ip -> (Fam ic sp -> Fam ic' sp')

-- | Composition of rules
ext :: Rule sc ip ic sp ic' sp'
  -> (Fam sc ip -> a0 -> Fam ic sp)
  -> (Fam sc ip -> a0 -> Fam ic' sp')
(f `ext` g) input = f input . g input


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
inhdef :: Defs att nts vals ic ic'
  => Label att -> HList nts -> Record vals -> (Fam ic sp -> Fam ic' sp)
inhdef att nts vals (Fam ic sp) = Fam (defs att nts vals ic) sp






--mch --> memnership of chld
--mnts--> membership of nonterminals

-- TODO this pv is a pair label-value, I should improve the typing
--at type level, Attribute, Tagged and that kind of stuff can be improved

-- | singledef is auxiliar, for Defs.
--   inserts a definition into the attribution of the corresponding child
class SingleDef (mch::Bool)(mnts::Bool) att pv (ic ::[(k,[(k,Type)])])
                 (ic' ::[(k,[(k,Type)])]) | mch mnts att pv ic -> ic' where
  singledef :: Proxy mch -> Proxy mnts -> Label att -> pv -> ChAttsRec ic
               -> ChAttsRec ic'


instance ( HasChild lch ic och
         , UpdateAtChild lch ( '(att,vch) ': och) ic ic'
         , LabelSet ( '(att, vch) ': och))
  => SingleDef True True att (Tagged lch vch) ic ic' where
  singledef _ _ att pch ic =
    updateAtChild (Label :: Label lch) ( att =. vch *. och) ic
    where lch = labelTChAtt pch
          vch = unTaggedChAtt pch
          och = lookupByChild lch ic


-- | The class 'Defs' is defined by induction over the record 'vals' 
--   containing the new definitions. 
--   The function 'defs' inserts each definition into the attribution 
--   of the corresponding child. 
class Defs att (nts :: [Type]) (vals :: [(k,Type)])
           (ic :: [(k,[(k,Type)])]) (ic' :: [(k,[(k,Type)])])
          | att nts vals ic -> ic' where
  defs :: Label att -> HList nts -> Record vals -> ChAttsRec ic
       -> ChAttsRec ic'

instance Defs att nts '[] ic ic where
  defs _ _ _ ic = ic

-- TODO: duplicated context
instance ( Defs att nts vs ic ic'
         , HasLabelChildAttsRes (lch,t) ic' ~ mch
         , HasLabelChildAtts (lch,t) ic'
         , HMemberRes t nts ~ mnts
         , HMember t nts
         , SingleDef mch mnts att (Tagged (lch,t) vch) ic' ic'')
    => Defs att nts ( '((lch,t), vch) ': vs) ic ic'' where
  defs att nts (ConsR pch vs) ic = singledef mch mnts att pch ic' 
      where ic'  = defs att nts vs ic         -- :: ChAttsRec ic'
            lch  = labelLVPair pch            -- :: Label (lch,t)
            mch  = hasLabelChildAtts lch ic'  -- :: Proxy mch
            mnts = hMember (sndLabel lch) nts -- :: Proxy mnts



-- * Aspects: Aspects are record that have a rule for each production:

---- TODO: use specialized datatypes?

-- | aspects are actually records
type Aspect = Record


-- | Let a Type for the fields:
type Prd prd rule = Tagged prd rule

labelPrd (Tagged v :: Tagged l v)= Label :: Label l 
rulePrd (Tagged v)= v


-- | Lets define the combination of aspects. When labels are only present once,
--  the new aspect has a copy of the field. In the other hand, when a label is
--  repeated, rules are combined with the function ext.
class Com (r₁ :: [(k,Type)]) (r₂ :: [(k, Type)]) (r₃ :: [(k,Type)])
  | r₁ r₂ -> r₃ where
  (.+.) :: Aspect r₁ ->  Aspect r₂ ->  Aspect r₃



-- |Unicode pretty operator
(⊕) :: (Com r s t) => Aspect r -> Aspect s -> Aspect t
(⊕) = (.+.)


-- | Comsingle combinates a rule with an aspect.
-- Since we'll need to decide what to do depending on context, we use the
--   usual technique.
class ComSingle (b::Bool) (prd :: k) (rule :: Type) (r₁ :: [(k,Type)])
                (r₂ :: [(k,Type)]) | b prd rule r₁ -> r₂ where
  comSingle :: Proxy b -> Prd prd rule -> Aspect r₁ -> Aspect r₂

--The boolean parameter is the indicator of prd being a label in the record.

instance (LabelSet ('(prd, rule) : r₁))
   => ComSingle 'False prd rule r₁ ( '(prd,rule) ': r₁) where
  comSingle _ prd asp = prd `ConsR` asp

-- 
instance ( HasFieldRec prd r₁,
           LookupByLabelRec prd r₁ ~ (Rule sc ip ic' sp' ic'' sp'')
         , UpdateAtLabelRec prd (Rule sc ip ic  sp  ic'' sp'') r₁ r₂
         )
  => ComSingle 'True prd        (Rule sc ip ic  sp  ic'  sp') r₁ r₂ where
  comSingle _ f r = updateAtLabelRec l (oldR `ext` newR) r :: Aspect r₂ 
    where l    = labelPrd f                                :: Label prd
          oldR = lookupByLabelRec l r    
          newR = rulePrd f


-- | The proper Com, by induction over the second Aspect.

-- | The empty record is a neutral element by right
instance Com r '[] r where
  r .+. _ = r

-- | For the recursive step, take the head of the second argument,
-- use comsingle on the first parameter, call (.+.) with the result
-- and the tail
instance ( Com r''' r' r''
         , HasLabelRecRes prd r ~ b
         , HasLabelRec prd r
         , ComSingle b prd rule r r''')
  => Com r ( '(prd, rule) ': r') r'' where
     r .+. (pr `ConsR` r') = let 
                                 b   = hasLabelRec (labelPrd pr) r
                                 r'''= comSingle b pr r
                                 r'' = r''' .+. r'
                             in  r''

------------------------------------------------------------------------------



class Empties (fc :: [(k,Type)]) where
  type EmptiesR fc :: [(k, [(k, Type)])]
  empties :: Record fc -> ChAttsRec (EmptiesR fc)


instance Empties '[] where
  type EmptiesR '[] = '[]
  empties EmptyR = EmptyCh


instance (Empties fcr,
          LabelSet ( '(lch, '[]) ': EmptiesR fcr)) =>
  Empties ( '(lch, fch) ': fcr) where
  type EmptiesR ( '(lch, fch) ': fcr) = '(lch, '[]) ': EmptiesR fcr
  empties (ConsR pch fcr)
    = let lch = labelTChAtt pch -- TODO: name
      in  ConsCh (TaggedChAttr lch EmptyAtt) (empties fcr)


---- the Kn class

class Kn (fcr :: [(k, Type)])
         (icr :: [(k, [(k, Type)])])
         (scr :: [(k, [(k, Type)])]) | fcr -> scr icr where 
  kn :: Record fcr -> ChAttsRec icr -> ChAttsRec scr

instance Kn '[] '[] '[] where
  kn _ _ = EmptyCh


instance ( Kn fc ic sc
         , LabelSet ('(lch, sch) : sc)
         , LabelSet ('(lch, ich) : ic))
  =>  Kn ( '(lch , Attribution ich -> Attribution sch) ': fc)
         ( '(lch , ich) ': ic)
         ( '(lch , sch) ': sc) where
  kn (ConsR pfch fcr) (ConsCh pich icr)
   = let scr = kn fcr icr
         lch = labelTChAtt pfch    :: Label lch-- TODO: name
         fch = unTagged pfch       :: Attribution ich -> Attribution sch
         ich = unTaggedChAttr pich :: Attribution ich
     in ConsCh (TaggedChAttr lch (fch ich)) scr


-- | The function 'knit' takes the combined rules for a node and the 
--   semantic functions of the children, and builds a
--   function from the inherited attributes of the parent to its
--   synthesized attributes.
knit :: ( Empties fc ,EmptiesR fc ~ ec
        , Kn fc ic sc )
  => Rule sc ip ec '[] ic sp
     -> Record fc -> Attribution ip -> Attribution sp
knit rule fc ip
  = let ec          = empties fc
        (Fam ic sp) = rule (Fam sc ip) (Fam ec EmptyAtt)
        sc          = kn fc ic
    in  sp

