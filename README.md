# Seifert surfaces: partial Lean formalization

A **partial** Lean 4 formalization of *Contractibility of the Complex of
Incompressible Seifert Surfaces: The Knot Case of Kakimizu’s Problem*
(Apex Intelligence, 11 September 2026).

**20 of 46 original assertions are verified; 26 remain open.** Theorem B is
complete. Headline Theorems A, C and D remain open. Start with
[MainTheorems.lean](MainTheorems.lean): one public entry imports all 20 accepted
originals and their proof dependencies in one Lean project. See the
[all-46 result checklist](docs/PAPER_RESULTS.md) for exact statements and scope.

Proof development stopped at canonical revision
`a2bf8eb443d6e3a8656c3893709a30ad920e153d`. This release preserves the accepted
public statements and their reviewed proof content; packaging adds no original
result credit. Some proof dependencies are restored closed proof terms from the
previously checked development. These are repository-local textual source,
submitted to Lean’s normal kernel, rather than newly derived mathematical proofs.

## Main and supporting results

Theorem B proves contractibility of the weak geometric realization of every
exchange complex, without finite-vertex or finite-descending-link hypotheses.
Lemma 2.2 supplies an injective well-ordered complexity. Lemma 2.4 proves
heredity for the qualified full subcomplexes and descending links.

The same entry includes the push-off and tangency results 5.5/5.7, the link
connectedness and compression results 6.1/6.2, the conditional minimal-surface
results A.2–A.5 and A.7, the intersection estimates B.1–B.3, and the barrier and
conformal-structure results C.6–C.9 and C.11.

A.2/A.5 require an attained minimizer in the specified class; A.7 assumes the
supplied A.6 minimizer. C.6/C.11 require a full Lemaire minimizer. C.9 retains
the manuscript’s L2′/L2″ compatibility alternatives. These implications do not
establish the open minimizer-existence or headline results. Corollary 2.3 remains
open as an original: the qualified nonempty-downset support receives zero
additional original credit.

```lean
import MainTheorems

#check SeifertSurfaces.exchange_complex_contractible
#check SeifertSurfaces.OriginalEndpoints.original_5_5
#check SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.A5_original
#check SeifertSurfaces.AppendixC.Original.paper_C9
```

## Build and verification

Install [elan](https://github.com/leanprover/elan), Git and Python 3, then run
from the repository root:

```sh
lake exe cache get
lake build MainTheorems
python3 tools/verify.py
```

Lean is pinned to **4.35.0-rc3**, Mathlib to
`3f6737de4761ec7bf368491fe9faccc991ebd6ca`, and the Lake manifest pins transitive
packages. Runtime compilation uses repository-local project source and these
pinned dependencies. It requires no historical project object, original
workspace, or independent verification environment.

The public verifier checks source custody hashes, scans Lean tokens and recognized
serialized declaration payloads, builds the common entry, and audits exactly
**25 original declaration heads plus one qualified support head** from
[RECEIVING_MANIFEST.json](tools/RECEIVING_MANIFEST.json). Their axiom sets stay
within `propext`, `Classical.choice` and `Quot.sound`. It then executes the 15
literal/operative receiving scripts and the actual-common kernel audit with
its logical result validator: exactly 507 records and 48 required safe-operative
equalities, including the safe-to-partial reference boundary. This one public
command is the authoritative receiving verification pass.

`python3 tools/verify.py --sources-only` checks custody, source tokens and
recognized serialized payloads without compiling. Payload scanning rejects
serialized axioms and `sorryAx` in the recognized forms. Closed expressions
still require the normal Lean kernel and complete root axiom audit; scanning
alone is not proof verification.

[VERIFICATION.json](docs/VERIFICATION.json) records the final receiving checks
and exact bounded fidelity receipts. [BUILD_STATUS.md](docs/BUILD_STATUS.md)
explains restored proof terms and the source-build boundary. The pinned Mathlib
cache is reused; this release does not claim an independent source rebuild of
Mathlib.

## Source layout

| Location | Contents |
| --- | --- |
| [seifert-surfaces/unified/](seifert-surfaces/unified/) | Common proof-source tree and selected shared provider owners. |
| [seifert-surfaces/core/](seifert-surfaces/core/), [seifert-surfaces/conformal/](seifert-surfaces/conformal/) | Preserved baseline copies; current compilation uses the unified tree. |
| [seifert-surfaces/historical/](seifert-surfaces/historical/) | Documentary original/provider sources and compact provenance; excluded from the public import closure. |
| [docs/](docs/) | Result checklist, exact declaration inventory, custody hashes, contexts and verification receipts. |
| [tools/](tools/) | Public verifier and root axiom audit entry. |

Historical provider sources may retain unaccepted sibling placeholders. The
archive is not globally claimed complete, buildable or placeholder-free.
Compiled project objects, old caches and large historical audit dumps are not
release inputs. Historical exporter reads are offline provenance only; missing
historical elaborator metadata is not represented as fully restored.

[SOURCE_ISSUES.md](SOURCE_ISSUES.md) preserves manuscript qualifications;
[FORMALIZATION_ISSUES.md](FORMALIZATION_ISSUES.md) records Lean interface issues.
[THIRD_PARTY.md](THIRD_PARTY.md), [NOTICE](NOTICE) and the provider license files
preserve source attribution. The copied Apache license applies to the named
provider sources; this release assigns no blanket license to the Seifert work.
