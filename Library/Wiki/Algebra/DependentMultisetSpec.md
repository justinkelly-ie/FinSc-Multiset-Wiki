# 🧩 Dependent Type-Indexed Multiset Specification

**Dependencies:** Stage0.DepMultiset, Stage0.Multiset, Wiki.Generators

Documents and verifies compile-time type-indexed multisets (`DepMultiset`), freezing runtime conversions, **Functorial Homomorphisms** (`freezeDep(depMap f m) == mapMultiset f (freezeDep m)`), dependent folds, and non-empty `DepMultiset1` guarantees using QuickCheck property testing.

```idris
module Wiki.DependentMultisetSpec

import Stage0.DepMultiset
import Stage0.Multiset
import Wiki.Generators

%default total

||| Homomorphic Law 1: freezeDep is a Functorial Homomorphism
||| freezeDep(depMap f m) == mapMultiset f (freezeDep m)
public export
prop_freezeDepHomomorphism : Integer -> Bool
prop_freezeDepHomomorphism val =
  let dep = DepAddM "x" val DepEmptyM
      mappedDep = depMap (\s => s ++ "_mapped") dep
      frozenObs = freezeDep mappedDep
      expectedObs = mapMultiset (\s => s ++ "_mapped") (freezeDep dep)
  in frozenObs == expectedObs

||| Property 2: Freeze Dependent Multiset Runtime Conversion Homomorphism
public export
prop_freezeDepConversion : Integer -> Bool
prop_freezeDepConversion val =
  let dep = DepAddM "x" val DepEmptyM
      frozen = freezeDep dep
  in frozen == AddM "x" val ZeroM

||| Property 3: Dependent Map and Fold Finitism
public export
prop_depMapAndFold : Integer -> Integer -> Bool
prop_depMapAndFold item count =
  let dep = DepAddM item count DepEmptyM
      mapped = depMap (\n => n * 2) dep
      totalSum = depFoldl 0 (\acc, i, c => acc + (i * c)) mapped
  in totalSum == (item * 2) * count

||| Property 4: Non-Empty DepMultiset1 Guarantee & Freeze
public export
prop_depMultiset1Freeze : Integer -> Bool
prop_depMultiset1Freeze count =
  let dep1 = DepBaseM "elem" count
      frozen1 = freezeDep1 dep1
  in case frozen1 of
       BaseM "elem" c => c == count
       _ => False

||| QuickCheck suite execution for Dependent Multiset specification
public export
auditDependentMultisetProof : IO Bool
auditDependentMultisetProof = do
  let r0 = qc prop_freezeDepHomomorphism
  let r1 = qc prop_freezeDepConversion
  let r2 = qc2 prop_depMapAndFold
  let r3 = qc prop_depMultiset1Freeze
  pure (r0.pass == Just True && r1.pass == Just True && r2.pass == Just True && r3.pass == Just True)
```
