module Wiki.Generators

import public QuickCheck
import Stage0.Interfaces
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.DiffInt
import Stage0.SignedFraction
import Stage1.Basis.Coordinate
import Stage1.UnixelFraction
import Stage0.Singleton.Bit
import Stage0.Multiset

%default total

public export
Arbitrary BoxInt where
  arbitrary = map MkBoxInt arbitrary
  coarbitrary b gen = coarbitrary (unwrapBox b) gen

public export
Arbitrary BoxNat where
  arbitrary = map (MkBoxNat . integerToNat . abs) arbitrary
  coarbitrary b gen = coarbitrary (cast {to=Integer} (unwrapBoxNat b)) gen

public export
Arbitrary DiffInt where
  arbitrary = do
    p <- arbitrary {a=BoxNat}
    n <- arbitrary {a=BoxNat}
    pure (MkDiffInt p n)
  coarbitrary (MkDiffInt p n) gen = coarbitrary (cast {to=Integer} (unwrapBoxNat p), cast {to=Integer} (unwrapBoxNat n)) gen

public export
Arbitrary MSetFraction where
  arbitrary = do
    n <- arbitrary {a=BoxInt}
    d <- arbitrary {a=BoxNat}
    pure (mkMSF n (S (unwrapBoxNat d)))
  coarbitrary (MkMSF n d) gen = coarbitrary (unwrapBox n, cast {to=Integer} d) gen

public export
Arbitrary UnixelFraction where
  arbitrary = do
    n <- arbitrary {a=BoxInt}
    d <- arbitrary {a=BoxNat}
    pure (mkUnixelFraction n (S (unwrapBoxNat d)))
  coarbitrary (MkUnixelFraction n (MkUnixel d)) gen = coarbitrary (unwrapBox n, cast {to=Integer} d) gen

public export
qcBit : (Bit -> Bool) -> QCRes
qcBit f =
  let prop = \n => f (natToBit n)
  in quickCheck (MkFn prop)

public export
qcBit2 : (Bit -> Bit -> Bool) -> QCRes
qcBit2 f =
  let prop = \n1, n2 => f (natToBit n1) (natToBit n2)
  in quickCheck (MkFn (\n1 => MkFn (\n2 => prop n1 n2)))

public export
qcBit3 : (Bit -> Bit -> Bit -> Bool) -> QCRes
qcBit3 f =
  let prop = \n1, n2, n3 => f (natToBit n1) (natToBit n2) (natToBit n3)
  in quickCheck (MkFn (\n1 => MkFn (\n2 => MkFn (\n3 => prop n1 n2 n3))))
