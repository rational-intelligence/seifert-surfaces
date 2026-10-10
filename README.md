# Seifert surfaces: partial Lean formalization

A **partial** Lean 4 formalization of *Contractibility of the Complex of
Incompressible Seifert Surfaces: The Knot Case of Kakimizu’s Problem*
(Apex Intelligence, 11 September 2026).

**20 of 46 original assertions were historically accepted. 26 remain open.**
Theorem B is complete; headline Theorems A, C and D remain unfinished.
This clean release freshly compiles six originals from source: **B, 2.2, 2.4,
C.7, C.8 and C.9**. The other fourteen historically accepted originals are
preserved as source archives with documented rebuild gaps. These are distinct
verification claims; see [the full result checklist](docs/PAPER_RESULTS.md).

Proof development stopped at canonical revision
`a2bf8eb443d6e3a8656c3893709a30ad920e153d`. Packaging changes no theorem statements
or proof logic and creates no additional original result credit.

## What can be built

[MainTheorems.lean](MainTheorems.lean) imports the exchange-complex results:
every exchange complex has contractible weak geometric realization, its
well-founded complexity admits an injective refinement, and the qualified
downward full subcomplexes and descending links inherit exchange structure.
There is no finite-vertex or finite-descending-link hypothesis in Theorem B.

The separate `ConformalOriginals` Lake target proves C.7’s smooth metric
representative, C.8’s local reflection normal form and C.9’s boundary
compatibility result. C.9 retains the manuscript’s L2′/L2″ conditions.

```lean
import MainTheorems
#check SeifertSurfaces.exchange_complex_contractible
```

In a separate consumer file:

```lean
import OriginalC9Final3
#check SeifertSurfaces.AppendixC.Original.paper_C7
#check SeifertSurfaces.AppendixC.Original.paper_C8
#check SeifertSurfaces.AppendixC.Original.paper_C9
```

## Build and verification

Install Lean through [elan](https://github.com/leanprover/elan), Git and Python 3,
then run:

```sh
git clone https://github.com/rational-intelligence/seifert-surfaces.git
cd seifert-surfaces
lake exe cache get
lake build MainTheorems ConformalOriginals
python3 tools/verify.py
```

Lean is pinned to **4.35.0-rc3** and Mathlib to
`3f6737de4761ec7bf368491fe9faccc991ebd6ca`; the Lake manifest pins transitive
dependencies. The portable entries use no historical workspace path or
distributed project object file. Verification checks source custody hashes,
the portable source scan, compilation, and the exact documented roots’ axiom
sets. `python3 tools/verify.py --sources-only` checks custody without Lean.

[VERIFICATION.json](docs/VERIFICATION.json) records the release checks.
Only `propext`, `Classical.choice` and `Quot.sound` occur in the audited fresh
root closures. Lean’s compiler kernel adjudicates these proofs; this release
does not independently rebuild the pinned Mathlib dependency.

## Source layout and boundaries

| Location | Contents |
| --- | --- |
| [seifert-surfaces/core/](seifert-surfaces/core/) | Exchange complexes, weak realizations, ordinal/CW machinery, and retained arithmetic/topological support. |
| [seifert-surfaces/conformal/](seifert-surfaces/conformal/) | Source-buildable C.7/C.8/C.9 import chain. |
| [seifert-surfaces/historical/](seifert-surfaces/historical/) | Exact original and available provider sources from the other historical native contexts; excluded from Lake build targets. |
| [docs/](docs/) | All-46 result checklist, exact declarations, native contexts, custody hashes and historical acceptance summaries. |
| [tools/](tools/) | Portable source verification and Lean axiom audit entries. |

The historical contexts include compiler replay, adjacent serialized proof
data and different providers sharing module names. Project objects, old caches,
giant audit dumps and original Git history are omitted. Some documentary
provider sources retain unaccepted placeholders. Their accepted historical
root closures were audited separately; the documentary tree is not claimed
globally complete or buildable. See [BUILD_STATUS.md](docs/BUILD_STATUS.md)
for concrete source rebuild boundaries.

Original 5.5/5.7 and the B.2/B.3 providers must retain their separate native
environments. A.2/A.5/A.7 assume supplied minimizers; C.6/C.11 assume a full
Lemaire minimizer. Those accepted implications do not establish the open
existence or headline results. The exchange-pair and geometric producers
needed for Theorem A remain unfinished.

[SOURCE_ISSUES.md](SOURCE_ISSUES.md) records manuscript qualifications;
[FORMALIZATION_ISSUES.md](FORMALIZATION_ISSUES.md) records separate Lean
interface and native-context issues. [THIRD_PARTY.md](THIRD_PARTY.md) and
[NOTICE](NOTICE) preserve attribution. The copied Apache license text applies
to its named provider sources; this release introduces no blanket license for
the Seifert formalization.
