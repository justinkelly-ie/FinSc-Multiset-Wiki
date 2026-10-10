# 🪙 Bit Gate & Channel Specification

Documents and verifies discrete $\mathbb{F}_2$ **Field Homomorphisms** into $(\mathbb{Z}_2, +_2, \cdot_2)$, box conversion channels, bit normalization, and linear `Bit` resource comonoid channels using QuickCheck property testing.

```idris
module Wiki.BitGateChannelSpec

import Stage0.Singleton.Bit
import Stage0.BoxInt
import Stage0.BoxInt
import Stage0.Interfaces
import Data.Linear
import Wiki.Generators

%default total

||| Homomorphic Law 1: bitToInteger is a Field Homomorphism from Bit (F2) to Z2
||| bitToInteger(addBit b1 b2) == (bitToInteger b1 + bitToInteger b2) mod 2
||| bitToInteger(mulBit b1 b2) == bitToInteger b1 * bitToInteger b2
public export
prop_bitFieldHomomorphism : Bit -> Bit -> Bool
prop_bitFieldHomomorphism b1 b2 =
  let addObs = bitToInteger (addBit b1 b2)
      multObs = bitToInteger (mulBit b1 b2)
      expectedAdd = mod (bitToInteger b1 + bitToInteger b2) 2
      expectedMult = bitToInteger b1 * bitToInteger b2
  in (addObs == expectedAdd) && (multObs == expectedMult)

||| Algebraic Law 2: F2 Addition Commutativity, Identity, and Characteristic 2 Self-Inverse
public export
prop_f2AdditionFieldLaws : Bit -> Bit -> Bool
prop_f2AdditionFieldLaws b1 b2 =
  let comm = (addBit b1 b2 == addBit b2 b1)
      unit = (addBit b1 Zero == b1)
      selfInv = (addBit b1 b1 == Zero)
  in comm && unit && selfInv

||| Algebraic Law 3: F2 Multiplication Associativity, Unit, and Distributivity Over Addition
public export
prop_f2MultiplicationFieldLaws : Bit -> Bit -> Bit -> Bool
prop_f2MultiplicationFieldLaws b1 b2 b3 =
  let assoc = (mulBit (mulBit b1 b2) b3 == mulBit b1 (mulBit b2 b3))
      unit = (mulBit b1 One == b1)
      distr = (mulBit b1 (addBit b2 b3) == addBit (mulBit b1 b2) (mulBit b1 b3))
  in assoc && unit && distr

||| Property 4: Bit to BoxInt Conversion & Normalization
public export
prop_bitBoxConversion : Bit -> Bool
prop_bitBoxConversion b =
  let bx = bitToBoxInt b
      expected = if isOne b then intToBoxInt 1 else intToBoxInt 0
  in (bx == expected) && (normalize b == b)

||| Property 5: Linear Bit Comonoid & LEq Channels
public export
prop_linearBitChannels : Bit -> Bool
prop_linearBitChannels b =
  let Builtin.(#) b1 b2 = lcomult b
      Builtin.(#) eqMatch (Builtin.(#) _ _) = lEq b b
  in (b1 == b) && (b2 == b) && eqMatch

||| QuickCheck suite execution for Bit Gate Channel specification
public export
auditBitGateChannelProof : IO Bool
auditBitGateChannelProof = do
  let r0 = qcBit2 prop_bitFieldHomomorphism
  let r1 = qcBit2 prop_f2AdditionFieldLaws
  let r2 = qcBit3 prop_f2MultiplicationFieldLaws
  let r3 = qcBit prop_bitBoxConversion
  let r4 = qcBit prop_linearBitChannels
  pure (r0.pass == Just True && r1.pass == Just True && r2.pass == Just True &&
        r3.pass == Just True && r4.pass == Just True)
```
