# FinSc‑Multiset‑Wiki Library

This library contains the documentation wiki for the **FinSc‑Multiset** project.  It is organised as a collection of Markdown specification files (`*.md`) together with a small set of Idris source files that support the wiki tests.

## Top‑level layout

```
FinSc‑Multiset‑Wiki/
├─ Library/
│   └─ Wiki/
│       ├─ Algebra/                # Algebraic specifications
│       ├─ Stream/                 # Stream‑related specifications
│       ├─ TypeTheory/             # Type‑theory / staging specifications
│       ├─ CoreMacroAudit.idr      # %macro‑based compile‑time audits
│       ├─ Generators.idr         # QuickCheck generators used by the specs
│       └─ Main.idr               # Driver module that runs all spec tests
```

### `Wiki/Algebra/`
| File | Purpose |
|------|---------|
| **BitAndLinearResourceSpec.md** | Specifies the bit resource, linear resource channels and their interaction. |
| **BitGateChannelSpec.md** | Formalises the `Bit` field homomorphisms and channel constructions. |
| **BoxIntAlgebraSpec.md** | Ring‑homomorphism properties of `BoxInt`. |
| **DependentMultisetSpec.md** | Compile‑time verification of dependent multisets (`DepMultiset`). |
| **LinearResourceChannelSpec.md** | Linear equality (`LEq`) channels and pass‑band unboxing proofs. |
| **MonoidApplicativeAdjunctionSpec.md** | Applicative/monad laws, monoid‑ring convolution and multiset adjunctions. |
| **MultisetAlgebraSpec.md** | Basic commutative‑monoid algebra of multisets. |
| **ScaleTransformSpec.md** | Functorial and categorical laws for `ScaleTransform`. |

### `Wiki/Stream/`
| File | Purpose |
|------|---------|
| **FusedStreamAlgebraSpec.md** | Deforested stream algebra, maxel operators and vacuum‑compression proof. |

### `Wiki/TypeTheory/`
| File | Purpose |
|------|---------|
| **TwoLevelTypeTheoryStagingSpec.md** | Specification of 2‑level type‑theory staging (2LTT) and its metatheory. |
| **ThreeLevelTypeTheoryStagingSpec.md** | Specification of 3‑level type‑theory staging (3LTT) and inter‑cycle semantics. |

### Idris source files
- **Main.idr** – Imports all wiki specifications and runs their QuickCheck/property tests.
- **CoreMacroAudit.idr** – Holds the `%macro` audit definitions used by the wiki.
- **Generators.idr** – Provides the QuickCheck generators referenced by the markdown specs.

The wiki files are meant to be compiled and executed via the `Main.idr` driver inside the Fedora toolbox (see the project README for build instructions).

---

*Generated automatically by Antigravity.*
