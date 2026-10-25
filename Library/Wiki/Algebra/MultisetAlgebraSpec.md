# 🗂️ Multiset Monoid Algebra & Homomorphism Specification
**Dependencies:** Stage0.Multiset, Wiki.Generators


Documents and verifies discrete multiset **Commutative Monoid Homomorphisms** $(M(T), +, 0)$, zero-annihilation normalization (`annihilateMultiset`), and linear observable metric counts (`multiplicityAll`) using QuickCheck property testing.

## 1. Mathematical Foundation & Monoid Homomorphisms

A multiset `Box tok` over token domain `tok` forms a free commutative monoid $(M(\text{tok}), +, 0)$ under multiset addition (`addMultiset`). The total multiplicity observable `multiplicityAll : Box tok -> Integer` satisfies the linear monoid homomorphism axioms:

1. **Additive Homomorphism**: $\text{multiplicityAll}(m_1 + m_2) = \text{multiplicityAll}(m_1) + \text{multiplicityAll}(m_2)$
2. **Scalar Scaling Homomorphism**: $\text{multiplicityAll}(s \cdot m) = |s| \cdot \text{multiplicityAll}(m)$
3. **Additive Inverse Annihilation**: $\text{annihilateMultiset}(m + (-m)) = 0$
4. **Commutativity & Associativity**: $m_1 + m_2 = m_2 + m_1$ and $(m_1 + m_2) + m_3 = m_1 + (m_2 + m_3)$

```idris
module Wiki.MultisetAlgebraSpec

import Stage0.Multiset
import Wiki.Generators

%default total

||| Homomorphic Law 1: multiplicityAll is a Monoid Homomorphism
||| multiplicityAll(scaleMultiset s m) == abs(s) * multiplicityAll(m)
public export
prop_multiplicityHomomorphism : Integer -> Integer -> Bool
prop_multiplicityHomomorphism s v =
  let m = AddM "a" v ZeroM
      scaled = scaleMultiset s m
  in multiplicityAll scaled == abs s * multiplicityAll m

||| Algebraic Law 2: Additive Commutativity (m1 + m2 == m2 + m1)
public export
prop_multisetAddCommutative : Integer -> Integer -> Bool
prop_multisetAddCommutative v1 v2 =
  let m1 = AddM "a" v1 ZeroM
      m2 = AddM "b" v2 ZeroM
  in addMultiset m1 m2 == addMultiset m2 m1

||| Algebraic Law 3: Additive Associativity ((m1 + m2) + m3 == m1 + (m2 + m3))
public export
prop_multisetAddAssociative : Integer -> Integer -> Integer -> Bool
prop_multisetAddAssociative v1 v2 v3 =
  let m1 = AddM "a" v1 ZeroM
      m2 = AddM "b" v2 ZeroM
      m3 = AddM "c" v3 ZeroM
  in addMultiset (addMultiset m1 m2) m3 == addMultiset m1 (addMultiset m2 m3)

||| Algebraic Law 4: Additive Identity (m + 0 == m)
public export
prop_multisetAddIdentity : Integer -> Bool
prop_multisetAddIdentity v =
  let m = AddM "a" v ZeroM
  in (addMultiset m ZeroM == m) && (addMultiset ZeroM m == m)

||| Property 5: Annihilate Multiset Zero Normalization (Dirac Elimination)
public export
prop_annihilateZeroNormalization : Integer -> Bool
prop_annihilateZeroNormalization val =
  let m = AddM "a" val (AddM "a" (-val) ZeroM)
      filtered = annihilateMultiset m
  in filtered == ZeroM

||| Property 6: Multiplicity Observable Metric Sum
public export
prop_multiplicityObservable : Integer -> Integer -> Bool
prop_multiplicityObservable v1 v2 =
  let m = AddM "x" v1 (AddM "y" v2 ZeroM)
  in multiplicityAll m == abs v1 + abs v2

||| Property 7: Subtraction and Negation Equivalences
public export
prop_subMultisetEquivalence : Integer -> Integer -> Bool
prop_subMultisetEquivalence v1 v2 =
  let m1 = AddM "a" v1 ZeroM
      m2 = AddM "a" v2 ZeroM
      diff = subMultiset m1 m2
  in diff == AddM "a" (v1 - v2) ZeroM

||| Property 8: Additive Inverse Annihilation (m + (-m) == 0)
public export
prop_addAnnihilation : Integer -> Bool
prop_addAnnihilation val =
  let m = AddM "a" val ZeroM
      sum = addMultiset m (negateMultiset m)
  in annihilateMultiset sum == ZeroM

||| QuickCheck suite execution for Multiset Algebra specification
public export
auditMultisetAlgebraProof : IO Bool
auditMultisetAlgebraProof = do
  let r0 = qc2 prop_multiplicityHomomorphism
  let r1 = qc2 prop_multisetAddCommutative
  let r2 = qc3 prop_multisetAddAssociative
  let r3 = qc prop_multisetAddIdentity
  let r4 = qc prop_annihilateZeroNormalization
  let r5 = qc2 prop_multiplicityObservable
  let r7 = qc2 prop_subMultisetEquivalence
  let r8 = qc prop_addAnnihilation
  pure (r0.pass == Just True && r1.pass == Just True && r2.pass == Just True && r3.pass == Just True &&
        r4.pass == Just True && r5.pass == Just True && r7.pass == Just True && r8.pass == Just True)
```
