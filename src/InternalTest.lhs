

> {-# LANGUAGE DataKinds,
>              TypeOperators,
>              PolyKinds,
>              GADTs,
>              TypeInType,
>              RankNTypes,
>              StandaloneDeriving,
>              FlexibleInstances,
>              FlexibleContexts,
>              ConstraintKinds,
>              MultiParamTypeClasses,
>              FunctionalDependencies,
>              UndecidableInstances,
>              ScopedTypeVariables,
>              TypeFamilies
> #-}

> module InternalTest where
> import Data.Kind 
> import Data.Type.Equality
> import Data.Proxy
> import Errors
> import Eq
> import Attribute
> import TPrelude
> import Data.Tagged
> import Attribution
> import Record
> import ChildAtts


Some tests:

-- Attribution

> data Label1; data Label2; data Label3;data Label4
> label1 = Label :: Label Label1
> label2 = Label :: Label Label2
> label3 = Label :: Label Label3
> label4 = Label :: Label Label4
> att1 = Attribute 3   :: Attribute Label1 Int 
> att2 = Attribute '4' :: Attribute Label2 Char
> att3 = Attribute '4' :: Attribute Label3 Char

> attrib1 = ConsAtt att2 EmptyAtt
> -- test2 = ConsAtt att2 test1 does not compile because of label duplication
> attrib2 = ConsAtt att1 attrib1
> attrib3 = ConsAtt att3 attrib2

> --test_update_1 = updateAtLabelAtt label4 False attrib3 --should fail
> test_update_2 = updateAtLabelAtt label2 False attrib3 
> test_update_3 = updateAtLabelAtt label2 "hola" attrib3
> test_update_4 = updateAtLabelAtt label2 '9' attrib3 
> test_update_5 = updateAtLabelAtt label3 "hola" attrib3 
> test_update_6 = updateAtLabelAtt label3 '9' attrib3 


--Record

> tagged1 = Tagged 3   :: Tagged Label1 Int 
> tagged2 = Tagged '4' :: Tagged Label2 Char
> tagged3 = Tagged '4' :: Tagged Label3 Char

> record1 = ConsR tagged2 EmptyR
> -- test2 = ConsR att2 test1 does not compile because of label duplication
> record2 = ConsR tagged1 record1
> record3 = ConsR tagged3 record2
> 


> --test_update_1 = updateAtLabelRec label4 False record3 --should fail
> test_update_R_2 = updateAtLabelRec label2 False record3 
> test_update_R_3 = updateAtLabelRec label2 "hola" record3
> test_update_R_4 = updateAtLabelRec label2 '9' record3 
> test_update_R_5 = updateAtLabelRec label3 "hola" record3 
> test_update_R_6 = updateAtLabelRec label3 '9' record3 




--ChildAtts

> data LabelL; data LabelR
> labelL = Label :: Label LabelL
> labelR = Label :: Label LabelR


> childAttLR = ConsCh (TaggedChAttr labelL attrib1)$
>              ConsCh (TaggedChAttr labelR attrib2) EmptyCh

> -- duplicatedLabel
> -- childAttRRFail = ConsCh (TaggedChAttr labelR attrib1)$
> --              ConsCh (TaggedChAttr labelR attrib2) EmptyCh

> attrib1g = hLookupByChild labelL childAttLR
> attrib2g = hLookupByChild labelR childAttLR
>  -- no instance
>  -- attrib2g = hLookupByChild label3 childAttLR

> test_update_ChAtts_1 = updateAtChild labelL attrib3 childAttLR
> test_update_ChAtts_2 = updateAtChild labelR attrib3 childAttLR


-- test2 = (Proxy :: Proxy 'True ,True) .*. (Proxy :: Proxy 'False,'r') .*. EmptyR
--   :: HRecord '[ '( 'True ,Bool), '( 'False ,Char)]
