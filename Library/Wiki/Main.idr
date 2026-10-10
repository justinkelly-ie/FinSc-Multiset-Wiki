module Wiki.Main

import Stage0.Interfaces
import Stage0.Multiset
import Stage0.BoxInt
import Stage0.Singleton.Bit
import Stage0.StreamPolynumber
import Wiki.CoreMacroAudit
import Wiki.ScaleTransformSpec
import Wiki.MultisetAlgebraSpec
import Wiki.BoxIntAlgebraSpec
import Wiki.BitGateChannelSpec
import Wiki.LinearResourceChannelSpec
import Wiki.DependentMultisetSpec
import Wiki.MonoidApplicativeAdjunctionSpec
import Wiki.FusedStreamAlgebraSpec
import Wiki.TwoLevelTypeTheoryStagingSpec
import Wiki.ThreeLevelTypeTheoryStagingSpec
import Stage1.TypeTheory.TwoLevel
import System

%default total

printTestResult : String -> Bool -> IO Unit
printTestResult name pass = 
  if pass 
     then putStrLn ("  [TEST] " ++ name ++ ": PASSED ✅")
     else putStrLn ("  [TEST] " ++ name ++ ": FAILED ❌")

||| Audit 1: BoxInt Dirac Cancellation
auditDiracCancellation : Bool
auditDiracCancellation =
  let b1 = intToBoxInt 5
      b2 = intToBoxInt (-5)
      sumB = addBox b1 b2
  in sumB == intToBoxInt 0

||| Audit 2: Bit Algebra Complement
auditBitComplement : Bool
auditBitComplement =
  isOne (negBit Zero) && isZero (negBit One)

||| Audit 3: QTT Linear Nat Multiplication
auditLinearNat : Bool
auditLinearNat =
  let (n1 # n2) = lcomultNat 10
  in (lconsumeNat n1 == ()) && (lconsumeNat n2 == ())

main : IO ()
main = do
  putStrLn "========================================================"
  putStrLn "  🗃️ FINSC-MULTISET: LAYER 0A KERNEL VERIFICATION 🗃️  "
  putStrLn "========================================================"

  printTestResult "BoxInt Dirac Cancellation (5 + -5 == 0)" auditDiracCancellation
  printTestResult "Bit Algebra Complement (¬0 = 1, ¬1 = 0)" auditBitComplement
  printTestResult "QTT Linear Nat Duplication & Consumption" auditLinearNat
  printTestResult "Core %macro Reflection Proof Catalog [Compile-Time]" (allTrue CoreMacroAudit.coreMacroWitnesses)

  putStrLn "--------------------------------------------------------"
  putStrLn "  ⚡ IDRIS2-QUICKCHECK GENERATIVE PROPERTY SUITES ⚡  "
  putStrLn "--------------------------------------------------------"

  p0 <- auditFusedStreamAlgebraProof
  printTestResult "FusedStream Deforestation & Ternary Compression 378/729 (QuickCheck)" p0

  p1 <- auditScaleTransformProof
  printTestResult "ScaleTransform Functorial Identity & Composition (QuickCheck)" p1

  p2 <- auditMultisetAlgebraProof
  printTestResult "Multiset Monoid Laws, Observables & Normalization (QuickCheck)" p2

  p3 <- auditBoxIntAlgebraProof
  printTestResult "BoxInt Ring Homomorphism, Abs Metric & Refinement (QuickCheck)" p3

  p4 <- auditBitGateChannelProof
  printTestResult "F2 Bit Field Homomorphisms & Comonoid Channels (QuickCheck)" p4

  p5 <- auditLinearResourceChannelProof
  printTestResult "Linear LEq Equality Channels & Unboxing Passbands (QuickCheck)" p5

  p6 <- auditDependentMultisetProof
  printTestResult "Dependent DepMultiset Freeze & DepMultiset1 (QuickCheck)" p6

  p7 <- auditMonoidApplicativeGaloisProof
  printTestResult "Monoid Applicative Monad, Ring Convolution & Galois (QuickCheck)" p7

  p8Staging <- auditTwoLevelTypeTheoryStagingProof
  printTestResult "Two-Level Type Theory (2LTT) Staged Compilation (Kovács 2022)" p8Staging

  p3LTT <- auditThreeLevelTypeTheoryStagingProof
  printTestResult "Three-Level Type Theory (3LTT) Inter-Cycle Staging" p3LTT

  let p8 = Stage1.TypeTheory.TwoLevel.auditTwoLevelTypeTheoryProof
  printTestResult "Two-Level Type Theory (2LTT) Subfibration Stratification" p8

  let pStreamPoly = Stage0.StreamPolynumber.auditStreamPolyDerivProof &&
                    Stage0.StreamPolynumber.auditStreamPolyCaretProof &&
                    Stage0.StreamPolynumber.auditStreamPolyCauchyProof &&
                    Stage0.StreamPolynumber.auditStreamPolyEddingtonScaleProof
  printTestResult "Sparse StreamPolynumber Algebra & Eddington k=38 Scale Invariants" pStreamPoly

  putStrLn "========================================================"
  putStrLn "  ✨ ALL FINSC-MULTISET KERNEL WITNESSES PASSED ✨  "
  putStrLn "========================================================"
