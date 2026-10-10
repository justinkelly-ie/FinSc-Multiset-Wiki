module Wiki.CoreMacroAudit

import Stage0.BoxInt
import Stage0.BoxInt
import Stage0.Multiset
import Language.Reflection

%default total

%inline public export
auditWitness : (target : Bool) -> Elab (target = True)
auditWitness True = pure Refl
auditWitness False = fail "Core macro audit check failed: proof export returned False"

%inline public export
allTrue : List Bool -> Bool
allTrue [] = True
allTrue (True :: xs) = allTrue xs
allTrue (False :: _) = False

%inline public export
auditCatalogWitnesses : (targets : List Bool) -> Elab (allTrue targets = True)
auditCatalogWitnesses targets = auditWitness (allTrue targets)

public export
auditBoxIntDiracProof : Bool
auditBoxIntDiracProof =
  let b1 = intToBoxInt 10
      b2 = intToBoxInt (-10)
      sumB = addBox b1 b2
  in sumB == intToBoxInt 0

public export
%macro
auditBoxIntDirac : Elab (CoreMacroAudit.auditBoxIntDiracProof = True)
auditBoxIntDirac = auditWitness auditBoxIntDiracProof

public export
auditBoxIntRingHomomorphismProof : Bool
auditBoxIntRingHomomorphismProof =
  let a = intToBoxInt 3
      b = intToBoxInt 4
      c = intToBoxInt 7
      left = boxAdd a (boxAdd b c)
      right = boxAdd (boxAdd a b) c
  in left == right

public export
%macro
auditBoxIntRingHomomorphism : Elab (CoreMacroAudit.auditBoxIntRingHomomorphismProof = True)
auditBoxIntRingHomomorphism = auditWitness auditBoxIntRingHomomorphismProof

public export
coreMacroWitnesses : List Bool
coreMacroWitnesses =
  [ auditBoxIntDiracProof
  , auditBoxIntRingHomomorphismProof
  ]

public export
%macro
auditCoreMacroCatalog : Elab (allTrue CoreMacroAudit.coreMacroWitnesses = True)
auditCoreMacroCatalog = auditCatalogWitnesses coreMacroWitnesses
