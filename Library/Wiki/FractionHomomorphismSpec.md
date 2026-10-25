# ⚖️ Fraction Homomorphism & Algebraic Preservation Specification

Documents and formally tests the functorial preservation laws between discrete **MSet Fractions** (`MSetFraction`, Layer 0a carrier) and **Unixel Geometric Fractions** (`UnixelFraction`, Layer 0b carrier) under QuickCheck generative randomized property testing.

## 1. Mathematical Foundation

The canonical embedding $\phi : \text{UnixelFraction} \to \text{MSetFraction}$ maps a geometric rational coordinate $[n / d]$ with signed weight $n \in \text{BoxInt}$ and positive scale $d \in \text{Unixel}$ to its algebraic multiset fraction representation.

The fundamental homomorphism theorems verified here include:
1. **Additive Homomorphism**: $\phi(q_1 + q_2) \sim \phi(q_1) + \phi(q_2)$
2. **Subtractive Homomorphism**: $\phi(q_1 - q_2) \sim \phi(q_1) - \phi(q_2)$
3. **Multiplicative Homomorphism**: $\phi(q_1 \cdot q_2) \sim \phi(q_1) \cdot \phi(q_2)$
4. **Division Homomorphism**: $\phi(q_1 / q_2) \sim \phi(q_1) / \phi(q_2)$ (including signed divisor magnitude preservation)
5. **Equivalence Congruence**: $q_1 \sim_{\text{rationalEquiv}} q_2 \iff \phi(q_1) \sim_{\text{eqMSF}} \phi(q_2)$
6. **Round-Trip Retraction**: $\psi(\phi(q)) = q$ and $\phi(\psi(m)) = m$

```idris
module Wiki.FractionHomomorphismSpec

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.SignedFraction
import Stage1.UnixelFraction
import Wiki.Generators

%default total

||| Property 1: Addition Homomorphism Preservation
||| toMSetFraction (q1 + q2) ~ addMSF (toMSetFraction q1) (toMSetFraction q2)
public export
prop_fractionAddHomomorphism : UnixelFraction -> UnixelFraction -> Bool
prop_fractionAddHomomorphism q1 q2 =
  let lhs = toMSetFraction (addUnixelFraction q1 q2)
      rhs = addMSF (toMSetFraction q1) (toMSetFraction q2)
  in eqMSF lhs rhs

||| Property 2: Subtraction Homomorphism Preservation
||| toMSetFraction (q1 - q2) ~ subMSF (toMSetFraction q1) (toMSetFraction q2)
public export
prop_fractionSubHomomorphism : UnixelFraction -> UnixelFraction -> Bool
prop_fractionSubHomomorphism q1 q2 =
  let lhs = toMSetFraction (subUnixelFraction q1 q2)
      rhs = subMSF (toMSetFraction q1) (toMSetFraction q2)
  in eqMSF lhs rhs

||| Property 3: Multiplication Homomorphism Preservation
||| toMSetFraction (q1 * q2) ~ mulMSF (toMSetFraction q1) (toMSetFraction q2)
public export
prop_fractionMulHomomorphism : UnixelFraction -> UnixelFraction -> Bool
prop_fractionMulHomomorphism q1 q2 =
  let lhs = toMSetFraction (mulUnixelFraction q1 q2)
      rhs = mulMSF (toMSetFraction q1) (toMSetFraction q2)
  in eqMSF lhs rhs

||| Property 4: Division Homomorphism Preservation (for non-zero divisors)
||| toMSetFraction (q1 / q2) ~ divMSF (toMSetFraction q1) (toMSetFraction q2)
public export
prop_fractionDivHomomorphism : UnixelFraction -> UnixelFraction -> Bool
prop_fractionDivHomomorphism q1 q2 =
  if boxIsZero q2.num
    then True
    else
      let lhs = toMSetFraction (divUnixelFraction q1 q2)
          rhs = divMSF (toMSetFraction q1) (toMSetFraction q2)
      in eqMSF lhs rhs

||| Property 5: Equivalence Congruence
||| rationalEquiv q1 q2 <=> eqMSF (toMSetFraction q1) (toMSetFraction q2)
public export
prop_fractionEqCongruence : UnixelFraction -> UnixelFraction -> Bool
prop_fractionEqCongruence q1 q2 =
  let qEquiv = rationalEquiv q1 q2
      mEquiv = eqMSF (toMSetFraction q1) (toMSetFraction q2)
  in qEquiv == mEquiv

||| Property 6: Round-Trip Isomorphism
||| fromMSetFraction (toMSetFraction q) == q
public export
prop_fractionRoundTrip : UnixelFraction -> Bool
prop_fractionRoundTrip q =
  let m = toMSetFraction q
      q' = fromMSetFraction m
  in q == q'

||| Property 7: MSetFraction Round-Trip Isomorphism
||| toMSetFraction (fromMSetFraction m) == m
public export
prop_msfRoundTrip : MSetFraction -> Bool
prop_msfRoundTrip m =
  let q = fromMSetFraction m
      m' = toMSetFraction q
  in m == m'

||| QuickCheck test runner for Fraction Homomorphism Specification
public export
auditFractionHomomorphismProof : IO Bool
auditFractionHomomorphismProof = do
  let r1 = qc2 prop_fractionAddHomomorphism
  let r2 = qc2 prop_fractionSubHomomorphism
  let r3 = qc2 prop_fractionMulHomomorphism
  let r4 = qc2 prop_fractionDivHomomorphism
  let r5 = qc2 prop_fractionEqCongruence
  let r6 = qc prop_fractionRoundTrip
  let r7 = qc prop_msfRoundTrip
  pure (r1.pass == Just True && r2.pass == Just True && r3.pass == Just True &&
        r4.pass == Just True && r5.pass == Just True && r6.pass == Just True &&
        r7.pass == Just True)
```
