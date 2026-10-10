# 📐 ScaleTransform Functorial & Category Homomorphism Specification

Documents and verifies the `ScaleTransform` functorial identity, additive monoid homomorphism axioms, and category-level scale composition laws ($\mathbf{T}_{total} = \mathbf{T}_2 \circ \mathbf{T}_1$) using QuickCheck property testing.

## 1. Mathematical Foundation & Category Homomorphisms

A scale transformation $\mathbf{T} : M(A) \to M(B)$ preserves the multiset structure via functorial homomorphisms:

1. **Additive Homomorphism**: $\mathbf{T}(m_1 + m_2) = \mathbf{T}(m_1) + \mathbf{T}(m_2)$
2. **Scalar Linearity**: $\mathbf{T}(s \cdot m) = s \cdot \mathbf{T}(m)$
3. **Functorial Composition Law**: $(\mathbf{T}_2 \circ \mathbf{T}_1)(m) = \mathbf{T}_2(\mathbf{T}_1(m))$
4. **Galois Adjunction Duality**: $\mathbf{T}^{-1}(\mathbf{T}(m)) = m$

```idris
module Wiki.ScaleTransformSpec

import Stage1.ScaleTransform
import Stage0.BoxInt
import Wiki.Generators

%default total

||| Property 1: Identity ScaleTransform Law (Random BoxInt)
public export
prop_scaleTransformIdentity : BoxInt -> Bool
prop_scaleTransformIdentity x =
  scaleTransform x == x

||| Property 2: Functorial ScaleTransform Composition Law (Random BoxInt)
public export
prop_scaleTransformComposition : BoxInt -> Bool
prop_scaleTransformComposition x =
  composeScaleTransform {b = BoxInt} x == x

||| Property 3: Invertible ScaleTransform Reflexivity (Random BoxInt)
public export
prop_invertibleScaleTransformIdentity : BoxInt -> Bool
prop_invertibleScaleTransformIdentity x =
  invertScaleTransform (scaleTransform {domainB = BoxInt} x) == x

||| Property 4: Invertible ScaleTransform Composition Law (Random BoxInt)
public export
prop_invertibleScaleTransformComposition : BoxInt -> Bool
prop_invertibleScaleTransformComposition x =
  composeInvertibleScaleTransform {b = BoxInt} x == x

||| Property 5: ScaleTransform Additive Monoid Homomorphism: T(x + y) == T(x) + T(y)
public export
prop_scaleTransformAdditiveHomomorphism : BoxInt -> BoxInt -> Bool
prop_scaleTransformAdditiveHomomorphism x y =
  let lhs = scaleTransform (boxAdd x y)
      rhs = boxAdd (scaleTransform x) (scaleTransform y)
  in lhs == rhs

||| Property 6: ScaleTransform Scalar Linearity: T(s * x) == s * T(x)
public export
prop_scaleTransformScalarLinearity : BoxInt -> BoxInt -> Bool
prop_scaleTransformScalarLinearity s x =
  let lhs = scaleTransform (boxMult s x)
      rhs = boxMult s (scaleTransform x)
  in lhs == rhs

||| Property 7: InvertibleScaleTransform Galois Inversion Roundtrip: T^-1(T(x)) == x
public export
prop_invertibleScaleTransformGaloisInversion : BoxInt -> Bool
prop_invertibleScaleTransformGaloisInversion x =
  let f_star = scaleTransform {domainB = BoxInt} x
      f_upper = invertScaleTransform f_star
  in f_upper == x

||| QuickCheck suite execution for ScaleTransform specification
public export
auditScaleTransformProof : IO Bool
auditScaleTransformProof = do
  let r1 = qc prop_scaleTransformIdentity
  let r2 = qc prop_scaleTransformComposition
  let r3 = qc prop_invertibleScaleTransformIdentity
  let r4 = qc prop_invertibleScaleTransformComposition
  let r5 = qc2 prop_scaleTransformAdditiveHomomorphism
  let r6 = qc2 prop_scaleTransformScalarLinearity
  let r7 = qc prop_invertibleScaleTransformGaloisInversion
  pure (r1.pass == Just True && r2.pass == Just True && r3.pass == Just True &&
        r4.pass == Just True && r5.pass == Just True && r6.pass == Just True && r7.pass == Just True)
```
