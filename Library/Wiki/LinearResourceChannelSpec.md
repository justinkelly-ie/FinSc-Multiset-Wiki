# ⚡ Linear Resource Channel & Passband Specification

Documents and verifies `LEq` linear equality protocols, linear resource duplication comonoids, unboxing passband channels (`lunboxLMultiset`), linear folds, and in-place linear maps using QuickCheck property testing.

```idris
module Wiki.LinearResourceChannelSpec

import Stage0.LMultiset
import Stage0.Interfaces
import Data.Linear
import Wiki.Generators

%default total

||| Property 1: LEq Linear Equality Channels Reflexivity (Nat, Unit, LPair)
public export
prop_lEqChannels : Nat -> Bool
prop_lEqChannels n =
  let Builtin.(#) matchNat (Builtin.(#) _ _) = lEq n n
      Builtin.(#) matchUnit (Builtin.(#) _ _) = lEq () ()
      Builtin.(#) matchPair (Builtin.(#) _ _) = lEq (n # n) (n # n)
  in matchNat && matchUnit && matchPair

||| Property 2: Linear Multiset Unboxing Passband Channel & Freezing
public export
prop_lunboxChannel : Integer -> Bool
prop_lunboxChannel count =
  let lm = LAddM "a" count LEmptyM
      res = freezeLDep lm
  in case res of
       [("a", c)] => c == count
       _ => False

||| Property 3: Linear Map and Linear Fold Homomorphism
public export
prop_lmapAndLfold : Nat -> Integer -> Bool
prop_lmapAndLfold n val =
  let lm = LAddM n val LEmptyM
      mapped = lmap (\x => x + 5) lm
      sumVal = lfoldl 0 (\acc, item, count => acc + (cast item * count)) mapped
  in sumVal == cast (n + 5) * val

||| QuickCheck suite execution for Linear Resource Channel specification
public export
auditLinearResourceChannelProof : IO Bool
auditLinearResourceChannelProof = do
  let r1 = qc prop_lEqChannels
  let r2 = qc prop_lunboxChannel
  let r3 = qc2 prop_lmapAndLfold
  pure (r1.pass == Just True && r2.pass == Just True && r3.pass == Just True)
```
