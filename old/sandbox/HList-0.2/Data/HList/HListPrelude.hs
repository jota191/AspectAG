{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances,
  UndecidableInstances, FlexibleContexts #-}

{-
   The HList library

   (C) 2004, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

   Basic declarations for typeful heterogeneous lists.
 -}

module Data.HList.HListPrelude where

import Data.HList.FakePrelude

{-----------------------------------------------------------------------------}

-- Heterogeneous type sequences

data HNil      = HNil      deriving (Eq,Show,Read)
data HCons e l = HCons e l deriving (Eq,Show,Read)


{-----------------------------------------------------------------------------}

-- The set of all types of heterogeneous lists

class HList l
instance HList HNil
instance HList l => HList (HCons e l)


{-----------------------------------------------------------------------------}

-- Public constructors

hNil  :: HNil
hNil  =  HNil

hCons :: HList l => e -> l -> HCons e l
hCons e l = HCons e l


{-----------------------------------------------------------------------------}

-- Basic list functions

class HHead l h | l -> h
 where
  hHead :: l -> h

instance HHead (HCons e l) e
 where
  hHead (HCons e _) = e

class HTail l l' | l -> l'
 where
  hTail :: l -> l'

instance HTail (HCons e l) l
 where
  hTail (HCons _ l) = l



{-----------------------------------------------------------------------------}

-- A class for extension

class HExtend e l l' | e l -> l', l' -> e l
 where
  hExtend :: e -> l -> l'

instance HExtend e HNil (HCons e HNil)
 where
  hExtend e l = HCons e l

instance HList l => HExtend e (HCons e' l) (HCons e (HCons e' l))
 where
  hExtend e l = HCons e l


{-----------------------------------------------------------------------------}

-- Appending HLists

-- The normal append for comparison

append :: [a] -> [a] -> [a]
append [] l = l
append (x:l) l' = x : append l l'


-- The class HAppend

class HAppend l l' l'' | l l' -> l''
 where
  hAppend :: l -> l' -> l''


-- The instance following the normal append

instance HList l => HAppend HNil l l
 where
  hAppend HNil l = l

instance (HList l, HAppend l l' l'')
      => HAppend (HCons x l) l' (HCons x l'')
 where
  hAppend (HCons x l) l' = HCons x (hAppend l l')


{-----------------------------------------------------------------------------}

-- Reversing HLists

class HReverse l1 l2 | l1 -> l2, l2 -> l1
 where
  hReverse:: l1 -> l2

instance (HReverse' HNil l2 l3, HReverse' HNil l3 l2)
      =>  HReverse l2 l3
 where
  hReverse l1 = hReverse' HNil l1


-- l3 = (reverse l2) ++ l1

class HReverse' l1 l2 l3 | l1 l2 -> l3
 where
  hReverse':: l1 -> l2 -> l3

instance HReverse' l1 HNil l1
 where
  hReverse' l1 HNil = l1

instance HReverse' (HCons a l1) l2' l3
      => HReverse' l1 (HCons a l2') l3
 where
  hReverse' l1 (HCons a l2') = hReverse' (HCons a l1) l2'


-- Naive HReverse

class NaiveHReverse l l' | l -> l'
 where
  naiveHReverse :: l -> l'

instance NaiveHReverse HNil HNil
 where
  naiveHReverse HNil = HNil

instance ( NaiveHReverse l l'
         , HAppend l' (HCons e HNil) l''
         )
      =>   NaiveHReverse (HCons e l) l''
 where
  naiveHReverse (HCons e l)
   = hAppend (naiveHReverse l) (HCons e HNil)


{-----------------------------------------------------------------------------}

--
-- A nicer notation for lists
--

-- List termination
hEnd :: HCons t t1 -> HCons t t1
hEnd t@(HCons _ _) = t

{-
   Note:
        - x :: HCons a b
            means: forall a b. x :: HCons a b
        - hEnd x
            means: exists a b. x :: HCons a b
-}


-- Building non-empty lists

hBuild   :: (HBuild' HNil a r) => a -> r
hBuild x =  hBuild' HNil x

class HBuild' l a r | r-> a l
 where
  hBuild' :: l -> a -> r

instance HReverse (HCons a l) (HCons a' l')
      => HBuild' l a (HCons a' l')
 where
  hBuild' l x = hReverse (HCons x l)

instance HBuild' (HCons a l) b r
      => HBuild' l a (b->r)
 where
  hBuild' l x y = hBuild' (HCons x l) y

{-

HList> let x = hBuild True in hEnd x
HCons True HNil

HList> let x = hBuild True 'a' in hEnd x
HCons True (HCons 'a' HNil)

HList> let x = hBuild True 'a' "ok" in hEnd x
HCons True (HCons 'a' (HCons "ok" HNil))

HList> hEnd (hBuild (Key 42) (Name "Angus") Cow (Price 75.5))
HCons (Key 42) (HCons (Name "Angus") (HCons Cow (HCons (Price 75.5) HNil)))

HList> hEnd (hBuild (Key 42) (Name "Angus") Cow (Price 75.5)) == angus
True

-}

{-----------------------------------------------------------------------------}

-- A heterogeneous apply operator

class Apply f a r | f a -> r where
  apply :: f -> a -> r
  apply = undefined                     -- In case we use Apply for
                                        -- type-level computations only


-- Normal function application

instance Apply (x -> y) x y where
  apply f x = f x


-- Identity

data Id = Id

instance Apply Id x x where
  apply _ x = x


{-----------------------------------------------------------------------------}

-- A heterogeneous fold for all types

class HList l => HFoldr f v l r | f v l -> r
 where
  hFoldr :: f -> v -> l -> r

instance HFoldr f v HNil v
 where
  hFoldr _ v _ = v

instance ( HFoldr f v l r
         , Apply f (e,r) r'
         )
      => HFoldr f v (HCons e l) r'
 where
  hFoldr f v (HCons e l) = apply f (e,hFoldr f v l)


{-----------------------------------------------------------------------------}

class HMap f l l' | f l -> l'
 where
  hMap :: f -> l -> l'

instance HMap f HNil HNil
 where
  hMap _ _ = HNil

instance (
           Apply f x y,
           HMap f xs ys
         )
      => HMap f (HCons x xs) (HCons y ys)
 where
  hMap f ~(HCons x xs) = HCons (apply f x) (hMap f xs)

{-----------------------------------------------------------------------------}

-- Map a heterogeneous list to a homogeneous one

class HMapOut f r e
 where
  hMapOut :: f -> r -> [e]

instance HMapOut f HNil e
 where
  hMapOut _ _ = []

instance ( HMapOut f l e'
         , Apply f e e'
         )
      =>   HMapOut f (HCons e l) e'
 where
  hMapOut f ~(HCons e l) = apply f e : hMapOut f l


{-----------------------------------------------------------------------------}

-- A heterogenous version of mapM.
-- mapM :: forall b m a. (Monad m) => (a -> m b) -> [a] -> m [b]
-- Likewise for mapM_.

hMapM   :: (Monad m, HMapOut f l (m e)) => f -> l -> [m e]
hMapM f =  hMapOut f

-- GHC doesn't like its own type.
-- hMapM_  :: forall m a f e. (Monad m, HMapOut f a (m e)) => f -> a -> m ()
-- Without explicit type signature, it's Ok. Sigh.
-- Anyway, Hugs does insist on a better type. So we restrict as follows:
--
hMapM_   :: (Monad m, HMapOut f l (m ())) => f -> l -> m ()
hMapM_ f =  sequence_ .  disambiguate . hMapM f
 where
  disambiguate :: [q ()] -> [q ()]
  disambiguate =  id


{-----------------------------------------------------------------------------}

-- A reconstruction of append

append' :: [a] -> [a] -> [a]
append' l l' = foldr (:) l' l

hAppend' :: (HFoldr ApplyHCons v l r) => l -> v -> r
hAppend' l l' = hFoldr ApplyHCons l' l

data ApplyHCons = ApplyHCons

instance HList l => Apply ApplyHCons (e,l) (HCons e l)
 where
  apply ApplyHCons (e,l) = hCons e l


{-----------------------------------------------------------------------------}

-- A heterogeneous map for all types

data HMap' f = HMap' f

hMap' :: (HFoldr (HMap' f) HNil l r) => f -> l -> r
hMap' f = hFoldr (HMap' f) hNil

instance Apply f e e'
      => Apply (HMap' f) (e,l) (HCons e' l)
 where
  apply (HMap' f) (e,l) = HCons e' l
   where
    e' = apply f e


{-----------------------------------------------------------------------------}

-- A function for showing

data HShow  = HShow
data HSeq x = HSeq x

instance Show x => Apply HShow x (IO ())
 where
  apply _ x = do putStrLn $ show x

instance ( Monad m
         , Apply f x (m ())
         )
      => Apply (HSeq f) (x,m ()) (m ())
 where
  apply (HSeq f) (x,c) = do apply f x; c


{-----------------------------------------------------------------------------}

-- Type-level equality for lists

instance HEq HNil HNil HTrue
instance HList l => HEq HNil (HCons e l) HFalse
instance HList l => HEq (HCons e l) HNil HFalse
instance (HList l, HList l', HEq e e' b, HEq l l' b', HAnd b b' b'')
      => HEq (HCons e l) (HCons e' l') b''


{-----------------------------------------------------------------------------}

-- Staged equality for lists

instance HStagedEq HNil HNil
 where
  hStagedEq _ _ = True

instance HStagedEq HNil (HCons e l)
 where
  hStagedEq _ _ = False

instance HStagedEq (HCons e l) HNil
 where
  hStagedEq _ _ = False

instance ( TypeEq e e' b
         , HStagedEq l l'
         , HStagedEq' b e e'
         )
      =>   HStagedEq (HCons e l) (HCons e' l')
 where
  hStagedEq (HCons e l) (HCons e' l') = (hStagedEq' b e e') && b'
   where
    b  = typeEq e e'
    b' = hStagedEq l l'

class HStagedEq' b e e'
 where
  hStagedEq' :: b -> e -> e' -> Bool

instance HStagedEq' HFalse e e'
 where
  hStagedEq' _ _ _ = False

instance Eq e => HStagedEq' HTrue e e
 where
  hStagedEq' _ = (==)


{-----------------------------------------------------------------------------}


-- Ensure a list to contain HNats only

class HList l => HNats l
instance HNats HNil
instance (HNat n, HNats ns) => HNats (HCons n ns)


-- Static set property based on HEq

class HSet l
instance HSet HNil
instance (HMember e l HFalse, HSet l) => HSet (HCons e l)


-- Find an element in a set based on HEq
class HNat n => HFind e l n | e l -> n
 where
  hFind :: e -> l -> n

instance ( HEq e e' b
         , HFind' b e l n
         )
      =>   HFind e (HCons e' l) n
 where
  hFind e (HCons e' l) = n
   where
    b  = hEq e e'
    n  = hFind' b e l

class HNat n => HFind' b e l n | b e l -> n
 where
  hFind' :: b -> e -> l -> n

instance HFind' HTrue e l HZero
 where
  hFind' _ _ _ = hZero

instance HFind e l n
      => HFind' HFalse e l (HSucc n)
 where
  hFind' _ e l = hSucc (hFind e l)


-- Membership test

class HBool b => HMember e l b | e l -> b
instance HMember e HNil HFalse
instance (HEq e e' b, HMember e l b', HOr b b' b'')
      =>  HMember e (HCons e' l) b''

hMember :: HMember e l b => e -> l -> b
hMember _ _ = undefined


-- Another type-level membership test
-- Check to see if an element e occurs in a list l
-- If not, return HNothing
-- If the element does occur, return HJust l'
-- where l' is a type-level list without e

class HMemberM e l r | e l -> r
instance HMemberM e HNil HNothing
instance (HEq e e' b, HMemberM' b e (HCons e' l) res)
      =>  HMemberM e (HCons e' l) res
class HMemberM' b e l r | b e l -> r
instance HMemberM' HTrue e (HCons e l) (HJust l)
instance (HMemberM e l r, HMemberM' r e (HCons e' l) res)
    => HMemberM' HFalse e (HCons e' l) res
instance HMemberM' HNothing e l HNothing
instance HMemberM' (HJust l') e (HCons e' l) (HJust (HCons e' l'))



-- Membership test based on type equality

class HBool b => HTMember e l b | e l -> b
instance HTMember e HNil HFalse
instance (TypeEq e e' b, HTMember e l b', HOr b b' b'')
      =>  HTMember e (HCons e' l) b''

hTMember :: HTMember e l b => e -> l -> b
hTMember _ _ = undefined


-- Intersection based on HTMember

class HTIntersect l1 l2 l3 | l1 l2 -> l3
 where
  hTIntersect :: l1 -> l2 -> l3

instance HTIntersect HNil l HNil
 where
  hTIntersect _ _ = HNil

instance ( HTMember h l1 b
         , HTIntersectBool b h t l1 l2
         )
         => HTIntersect (HCons h t) l1 l2
 where
  hTIntersect (HCons h t) l1 = hTIntersectBool b h t l1
   where
    b = hTMember h l1

class HBool b => HTIntersectBool b h t l1 l2 | b h t l1 -> l2
 where
 hTIntersectBool :: b -> h -> t -> l1 -> l2

instance HTIntersect t l1 l2
      => HTIntersectBool HTrue h t l1 (HCons h l2)
 where
  hTIntersectBool _ h t l1 = HCons h (hTIntersect t l1)

instance HTIntersect t l1 l2
      => HTIntersectBool HFalse h t l1 l2
 where
  hTIntersectBool _ _ t l1 = hTIntersect t l1


-- Turn a heterogeneous list into a homogeneous one

class HList2List l e
 where
  hList2List :: l -> [e]

instance HList2List HNil e
 where
  hList2List HNil = []

instance HList2List l e
      => HList2List (HCons e l) e
 where
  hList2List (HCons e l) = e:hList2List l


{-----------------------------------------------------------------------------}

-- Turn list in a list of justs

class ToHJust l l' | l -> l'
 where
  toHJust :: l -> l'

instance ToHJust HNil HNil
 where
  toHJust HNil = HNil

instance ToHJust l l' => ToHJust (HCons e l) (HCons (HJust e) l')
 where
  toHJust (HCons e l) = HCons (HJust e) (toHJust l)


{-----------------------------------------------------------------------------}

-- Extract justs from list of maybes

class FromHJust l l' | l -> l'
 where
  fromHJust :: l -> l'

instance FromHJust HNil HNil
 where
  fromHJust HNil = HNil

instance FromHJust l l' => FromHJust (HCons HNothing l) l'
 where
  fromHJust (HCons _ l) = fromHJust l

instance FromHJust l l' => FromHJust (HCons (HJust e) l) (HCons e l')
 where
  fromHJust (HCons (HJust e) l) = HCons e (fromHJust l)


{-----------------------------------------------------------------------------}

-- Annotated lists

data HAddTag t = HAddTag t
data HRmTag    = HRmTag

hAddTag :: (HMap (HAddTag t) l l') => t -> l -> l'
hAddTag t l = hMap (HAddTag t) l
hRmTag :: (HMap HRmTag l l') => l -> l'
hRmTag l    = hMap HRmTag l

instance Apply (HAddTag t) e (e,t)
 where
  apply (HAddTag t) e = (e,t)

instance Apply HRmTag (e,t) e
 where
  apply HRmTag (e,_) = e


-- Annotate list with a type-level Boolean
hFlag :: (HMap (HAddTag HTrue) l l') => l -> l'
hFlag l = hAddTag hTrue l


{-----------------------------------------------------------------------------}

-- Splitting by HTrue and HFalse

class HSplit l l' l'' | l -> l' l''
 where
  hSplit :: l -> (l',l'')

instance HSplit HNil HNil HNil
 where
  hSplit HNil = (HNil,HNil)

instance HSplit l l' l''
      => HSplit (HCons (e,HTrue) l) (HCons e l') l''
 where
  hSplit (HCons (e,_) l) = (HCons e l',l'')
   where
    (l',l'') = hSplit l

instance HSplit l l' l''
      => HSplit (HCons (e,HFalse) l) l' (HCons e l'')
 where
  hSplit (HCons (e,_) l) = (l',HCons e l'')
   where
    (l',l'') = hSplit l

{-

Let expansion makes a difference to Hugs:

HListPrelude> let x = (hFlag (HCons "1" HNil)) in hSplit x
(HCons "1" HNil,HNil)
HListPrelude> hSplit (hFlag (HCons "1" HNil))
ERROR - Unresolved overloading
*** Type       : HSplit (HCons ([Char],HTrue) HNil) a b => (a,b)
*** Expression : hSplit (hFlag (HCons "1" HNil))


-}


{-----------------------------------------------------------------------------}
