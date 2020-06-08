module Data.Bool.Extra

%default total

public export
notInvolutive : (x : Bool) -> not (not x) = x
notInvolutive True  = Refl
notInvolutive False = Refl

-- AND

public export
andSameNeutral : (x : Bool) -> x && x = x
andSameNeutral False = Refl
andSameNeutral True = Refl

public export
andFalseFalse : (x : Bool) -> x && False = False
andFalseFalse False = Refl
andFalseFalse True = Refl

public export
andTrueNeutral : (x : Bool) -> x && True = x
andTrueNeutral False = Refl
andTrueNeutral True = Refl

public export
andAssociative : (x, y, z : Bool) -> x && (y && z) = (x && y) && z
andAssociative True  _ _ = Refl
andAssociative False _ _ = Refl

public export
andCommutative : (x, y : Bool) -> x && y = y && x
andCommutative x True  = andTrueNeutral x
andCommutative x False = andFalseFalse x

public export
andNotFalse : (x : Bool) -> x && not x = False
andNotFalse False = Refl
andNotFalse True = Refl

-- OR

public export
orSameNeutral : (x : Bool) -> x || x = x
orSameNeutral False = Refl
orSameNeutral True = Refl

public export
orFalseNeutral : (x : Bool) -> x || False = x
orFalseNeutral False = Refl
orFalseNeutral True = Refl

public export
orTrueTrue : (x : Bool) -> x || True = True
orTrueTrue False = Refl
orTrueTrue True = Refl

public export
orAssociative : (x, y, z : Bool) -> x || (y || z) = (x || y) || z
orAssociative True  _ _ = Refl
orAssociative False _ _ = Refl

public export
orCommutative : (x, y : Bool) -> x || y = y || x
orCommutative x True  = orTrueTrue x
orCommutative x False = orFalseNeutral x

public export
orNotTrue : (x : Bool) -> x || not x = True
orNotTrue False = Refl
orNotTrue True = Refl

-- interaction & De Morgan's laws

public export
orSameAndRightNeutral : (x, y : Bool) -> x || (x && y) = x
orSameAndRightNeutral False _ = Refl
orSameAndRightNeutral True  _ = Refl

public export
andDistribOrR : (x, y, z : Bool) -> x && (y || z) = (x && y) || (x && z)
andDistribOrR False _ _ = Refl
andDistribOrR True  _ _ = Refl

public export
orDistribAndR : (x, y, z : Bool) -> x || (y && z) = (x || y) && (x || z)
orDistribAndR False _ _ = Refl
orDistribAndR True  _ _ = Refl

public export
notAndIsOr : (x, y : Bool) -> not (x && y) = not x || not y
notAndIsOr False _ = Refl
notAndIsOr True  _ = Refl

public export
notOrIsAnd : (x, y : Bool) -> not (x || y) = not x && not y
notOrIsAnd False _ = Refl
notOrIsAnd True  _ = Refl
