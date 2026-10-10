# Source build status

`lake build MainTheorems` builds ten verified original results in one common environment. `tools/Verify.lean` audits fifteen roots, including one qualified support result. The shared surface foundation also passes source build and base-axiom gates. Native module names, private-name directives, universes and original statement binders are preserved.

| Entry | Fresh source build | Original credit represented |
| --- | --- | --- |
| `MainTheorems` | PASS | B, 2.2, full five-root 2.4 |
| `ConformalOriginals` | PASS | C.7, C.8, C.9 |
| Historical canonical and frozen packages | Not certified | Other 14 historically accepted originals |

The historical tree contains source documents, not runnable certified entries. It is excluded from Lake targets. Its absolute historical paths and object-loading commands are retained as provenance; the portable entry does not execute them. No project `.olean`, serialized proof-data archive or original workspace is required by the portable entry.

Concrete source-only boundaries:

- `SurfaceInvariants.lean` imports the same module in separate historical `cw_before` / `cw_paid` object environments. Those donor environments are omitted. This boundary reaches several canonical geometric/genus dependency chains, including 6.1, A.2/A.3/A.4/A.7 and C.6/C.11. Only historical acceptance is asserted for these chains.
- Full A.5 uses distinct primary1990 and producer1478 native environments and explicit compiler replay. Exact available source and manifest custody are preserved; several historical donor provider sources/data are not a complete clean source closure.
- Original 5.5 uses a sealed B.2 donor; original 5.7 uses a separately frozen producer context. Their documentary source modules contain unaccepted siblings. Rebuilding those roots requires the exact donors and cannot be replaced by a different provider with the same module name.
- B.1's `VM03ExactCaller_v464.lean` reads adjacent serialized module data. The 146 historical data objects are omitted; accepted-root source and receipt hashes remain.
- B.2 and the two B.3 providers remain separate. No coimport or source-normalized common environment is claimed; their held sibling proofs are retained as documentary obligations.
- 6.2's `Original62CompletionV510.lean` reads a historical `OriginalSection62.olean` to compare its full raw type. Its paid helper sources also use native replay mapping. Those frozen objects are omitted, so no source-only rebuild is certified.

No proof repair was attempted during packaging. Historical acceptance remains 20/46; only six originals have new source-rebuild certification. Exact root/module maps are in `CONTEXTS.json`, and all preserved source hashes are in `SOURCE_MANIFEST.json`.
