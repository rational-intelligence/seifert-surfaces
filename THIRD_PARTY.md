# Third-party sources and license scope

Original source headers are preserved byte for byte. Existing licenses and
notices are retained; packaging grants no new project-wide license. In
particular, the canonical workspace's root Apache text is a DifferentialGeometry
provider notice, not a blanket grant for the Seifert formalization. Its copy is
[licenses/DifferentialGeometry-APACHE-2.0.txt](licenses/DifferentialGeometry-APACHE-2.0.txt).

| Component | Recorded upstream / revision | Preserved notice scope |
| --- | --- | --- |
| Lean / Mathlib | Lean 4.35.0-rc3; Mathlib `3f6737de4761ec7bf368491fe9faccc991ebd6ca` | Pinned external packages, with their upstream licenses; not vendored into the mathematical source tree. |
| DifferentialGeometry | `qinz1yang/differential-geometry`, `777299070a5529e96345e0033979706fd00c7e62` | [NOTICE](NOTICE), existing Apache text and [Weyl port modifications](licenses/WEYL_PORT_MODIFICATIONS.md). |
| Schoenflies | `alonamaloh/schoenflies-lean`; historical selected public provider `788efe97894474c032de6dfb1289d515f613d15a` | Apache-2.0; Álvaro Begué attribution and nested external license/modification notices. This release does not substitute the curve-complex release's provider revision. |
| TauCeti | `TauCetiProject/TauCeti`, `3358033ba2fd35f321356dceaf2372a0fd6c0bfd` | Joseph Tooby-Smith and Tau Ceti contributors; nested Apache license, source map and modifications. |
| CanonicalTopology, ClassificationOfSurfaces, HopfProblem | Exact source maps and attributions adjacent to retained historical provider sources | Ayush Khaitan and contributors, ClassificationOfSurfaces contributors, Steven Sivek, Kai Lam and nested HopfProblem attribution, as stated in [NOTICE](NOTICE). |
| Campanato, DeGiorgi, public corner, public Hopf and planar/longitude providers | Original headers and imported-provider notices | Named license copies in [licenses/](licenses/) and nested historical source directories; no inferred broader grant. |

The original Apache contribution notices under
`seifert-surfaces/historical/canonical/DifferentialGeometry/External/` retain
their `LICENSE`, `SOURCE_MAP.json` and `MODIFICATIONS.md` files where present.
The custody manifest records copied license/source bytes. Native provider
selection is documented in [CONTEXTS.json](docs/CONTEXTS.json); historical
acceptance paths in the result inventory locate the preserved workspace or
backup, not an additional dependency fetched by this release.

The supplied Apex theorem-B reference was an audited reference, not a production
dependency of the portable entry, and is not redistributed here. The manuscript
itself is identified by title, date and source hashes in the result inventory;
no manuscript license is inferred.
