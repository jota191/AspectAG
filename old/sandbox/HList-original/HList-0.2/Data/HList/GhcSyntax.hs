{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-
   (C) 2004, Oleg Kiselyov, Ralf Laemmel, Keean Schupke

   Some dedicated infix operators at the type and the value level.
-}

module Data.HList.GhcSyntax where

import Data.HList.HArray (HUpdateAtHNat())
import Data.HList.FakePrelude
import Data.HList.HListPrelude
import Data.HList.HOccurs
import Data.HList.Record
import Data.HList.GhcRecord
import Data.HList.TIP
import Data.HList.TIC


{-----------------------------------------------------------------------------}

-- Convenience notation for type sequences

infixr 2 :*:
infixr 2 .*.

type e :*: l = HCons e l

{-|

  (.*.) -- Add a field to a record. Analagous to (++) for
           lists. 

  record .*. field1
         .*. field2
--}
(.*.) :: HExtend e l l' => e -> l -> l'
(.*.) =  hExtend


{-----------------------------------------------------------------------------}

-- Convenience notation for records
-- Many signatures are deliberately omitted. They should be inferred.
-- There is no point of writing the same thing in terms and in types.

infixr 4 :=:
type l :=: v = LVPair l v

infixr 4 .=.
{-|

  (.=.) -- Create a value with the given label. Analagous to a data
           constructor such as 'Just', 'Left', or 'Right'. Higher fixity
           than record-modification operations like (.*.), (.-.), etc. to
           support expression like the below w/o parentheses:

  label1 .=. value1 .*. 
  label2 .=. value2 .*. 
  emptyRecord

--}
(.=.) :: l -> v -> LVPair l v
l .=. v = newLVPair l v

infixr 9 .!.
{-|
  (.!.) -- Lookup a value in a record, by its label. Analagous to (!!), the
           list indexing operation. Highest fixity, like (!!).

  record1 .*. label1 .=. record2 .!. label1
          .*. label2 .=. record2 .!. label2
--}
(.!.) :: (HasField l r v) => r -> l -> v
r .!. l =  hLookupByLabel l r

infixl 2 .-.
{-|
  (.-.) -- Remove a field from a record. At the same
           level as other record modification options (.*.). Analagous
           to (\\) in lists.

  record1 .-. label1

  label1 .=. value1 .*. 
  label2 .=. value2 .-.
  label2 .*. 
  emptyRecord 

  label1 .=. value1 .-.
  label1 .*. 
  label2 .=. value2 .*. 
  emptyRecord 

  record1 .*. label1 .=. record2 .!. label1
          .*. label2 .=. record2 .!. label2 
          .-. label1
--}
r .-. l =  hDeleteAtLabel l r

infixl 2 .@.
{-|
  (.@.) -- Update a field with a particular value. Another record-level
           operation, so it has the same fixity as (.*.) and (.-.). No
           real list analogue, since there is no Prelude defined
           update.

  record1 .@. label1 .=. value1

  record1 .@. label1 .=. record2 .!. label1

  record1 .*. label1 .=. record2 .!. label1
          .*. label2 .=. record2 .!. label2 
          .@. label1 .=. value2
-}
r .@. f@(LVPair v) =  hUpdateAtLabel (labelLVPair f) v r

infixr 2 .^.
{-|

  (.^.) -- This is a variation on updating (according to GhcRecord.hs),
           so use the same fixity as (.\@.).
-}
f@(LVPair v) .^. r = hUnproxyLabel (labelLVPair f) v r

infixr 2 .<.
{-| 
  (.<.) -- Another variation on update, so give it the same fixity as (.\@.).

-}
f@(LVPair v) .<. r = hTPupdateAtLabel (labelLVPair f) v r

infixl 2 .<++.
{-|
  (.<++.) -- Similar to list append, so give this slightly lower fixity than
             (.*.), so we can write:

   record1 .*. field1 .<++. record2 .*. field2
-}
r .<++. r' = hLeftUnion r r'


{-----------------------------------------------------------------------------}

-- Convenience notation for TIRs

infixr 2 :+:
infixr 2 .+.

type e :+: l = HCons (Proxy e) l

{-|
  (.+.) -- Type-indexed rows append. Very similar to .*., so 
           keep the same fixity.
-}
e .+. r = hExtend (toProxy e) r


{-----------------------------------------------------------------------------}
