# Source audit: supplied Seifert-surfaces manuscript

Owner: F-Reviewer, source_audit. Assigned writable directory:
`/home/caoyichuan/test/seifert-surfaces/scratch/f-reviewer/source_audit`.
Master development, read-only to this agent:
`/home/caoyichuan/test/seifert-surfaces/target`.

Audited source: `/home/caoyichuan/test/seifert-surfaces.pdf`, 48 pages, dated
11 September 2026, author label Apex Intelligence; extraction:
`/home/caoyichuan/test/seifert-surfaces/references/seifert-surfaces.txt`.
References below use PDF page numbers and extraction line numbers. Pages 2 and 14
were visually checked against rendered PDF images; extraction alone loses bars
and other mathematical decorations.

This is a source-fidelity and dependency audit, not a Lean proof certificate.
No Lean statement was assigned for comparison, and no Lean files were edited.
Counterexample sketches below are **formal proof tasks**, not kernel-certified
results. The actual compilation, scan, axiom, guard, and read-back gates remain
required for all future Lean artifacts.

## Scope and manifest

The supplied paper contains **46 numbered assertions**: Theorems A–D and 42
other theorems, lemmas, propositions, and corollaries. It also has five numbered
definitions and ten numbered remarks. `source_manifest.json` inventories all 61
declarations, with pages, extraction intervals, statement summaries, and flags.
Definition A.1 and Definition C.2 are indispensable statement context even though
they are not assertions to prove.

The claimed result scope is: non-trivial knots (A), arbitrary non-empty connected
flag exchange complexes with well-ordered complexity (B), truncations (C), and
non-split linking-indecomposable links excluding the unknot (D). The scope does
**not** include arbitrary links, equivariant contractibility, arbitrary Haken
manifolds, or general `(E, γ, α)` complexes; pp. 2–3, lines 67–111. Descending-link
finiteness (F) is explicitly open, not an input to Theorem B. Appendix C is
explicitly unused by §§2–6 (p. 3, lines 105–111; p. 39, lines 1931–1940), but
belongs in an all-numbered-results formalization.

## SF-01: Theorem C states a different area truncation from its proof

Severity: source statement/proof mismatch; requires an explicit target decision.
Locations: p. 2, Theorem C, lines 63–66; p. 20, §6.2, lines 948–951.

The statement, visually verified on PDF p. 2, specifies the full subcomplex on
`{v | g(v) ≤ ℓ ∧ A(v) ≤ a₀}`. The proof instead uses
`{v | g(v) < ℓ} ∪ {v | g(v) = ℓ ∧ A(v) ≤ a₀}`.
These are different vertex sets: the proof's set includes every lower-genus
vertex, whatever its area. The proof applies heredity of downward subsets for
the **lexicographic** order `(g,A)`. A rectangular constraint on both coordinates
does not follow from lexicographic downwardness: a lower-genus vertex may have
larger area. No argument in §6.2 establishes the rectangular set is downward.

Next obligation: keep both predicates named and distinct; prove a theorem for
the intended predicate. Changing the source-facing predicate to the proof's
predicate is a source repair and must be recorded and reviewed, not treated as
a harmless Lean implementation choice. The genus-only clause has no such
statement/proof discrepancy.

## SF-02: Theorem C's area clause omits non-emptiness

Severity: candidate refutation of the printed unrestricted area clause, even
when ℓ is the minimal genus. Locations: p. 2, lines 63–66; p. 20, lines 948–951;
p. 3, Definition 2.1 footnote 2, lines 139–140; pp. 10–11, lines 469–503.

Theorem C says the second truncation is contractible for **every** `a₀ > 0`.
The proof itself says the lexicographic truncation is non-empty if
`ℓ > g(K)`, or if `ℓ = g(K)` and `a₀` is at least the least relative area among
vertices of minimal genus. This qualification is absent from the theorem.

Counterexample task using the source's own claims: the minimal-genus vertices
are non-empty (§4.1); their attained positive area values have a least member
`a* > 0` (Definition 4.7 and Lemma 4.8(ii),(iii)). Take `ℓ = g(K)` and
`a₀ = a*/2`. There are no lower-genus vertices and no minimal-genus vertex of
area at most `a₀`. Both proposed area truncations are then empty. Contractibility
requires a point; the source explicitly notes that the empty complex is not
contractible. A formal abstract counterexample can isolate this contradiction
without constructing all of knot topology first.

Next obligation: F-Generator can certify the abstract empty-sublevel obstruction;
Formalizer should expose non-emptiness in the repaired lexicographic result.
Do not silently add this hypothesis to a statement labelled as the unaltered
Theorem C. Isometric embedding by itself can still be valid for an empty domain.

## SF-03: Corollary 2.3's empty downward set is a convention fork

Severity: statement encoding risk, not an unconditional claim that the source
corollary is false. Locations: p. 4, lines 156–179; p. 5, lines 189–210.

There is no non-emptiness hypothesis on D in Corollary 2.3. The proof establishes
finite graph distances/geodesics between any two vertices in D. This is vacuous
for `D = ∅`. Under the convention that connectedness is pairwise reachability
(or topological preconnectedness), the empty-set case is harmless. Under a Lean
predicate incorporating non-emptiness, a connectedness conclusion for `D = ∅`
needs a hypothesis. The paper itself separately requires non-emptiness in
Definition 2.1 and explicitly conditions heredity on non-emptiness in Lemma 2.4.

Next obligation: acid-test the actual Lean connectivity definition. A transparent
faithful interface can state isometry and pairwise reachability for arbitrary D,
with nonempty connectedness only when `D.Nonempty`. A candidate refutation of
`Nonempty (Subtype D)` for all downward D uses a one-vertex exchange complex
and the empty downward set. Record the convention used; do not infer that
Corollary 2.3 supplies a vertex needed for contractibility.

## SF-04: Appendix A depends on the precise existence class (27)

Severity: acknowledged source debt affecting the main geometric chain.
Locations: p. 2, Remark 1.2, lines 83–88; p. 7, Theorem 3.2(i), lines 308–319;
p. 23, Definition A.1 and discussion, lines 1088–1118; p. 47, lines 2346–2367.

The source imports [6, Thm. 6.12] as attainment **within** the class of properly
embedded piecewise smooth surfaces isotopic rel boundary, interpreting the
undefined phrase in the cited theorem by its own Definition A.1. Equation (27)
is the assertion that the attained minimizer belongs to that precise class.
The source explicitly says this membership is not reached by the printed
argument in [6]; Appendix A proves regularity **given** that membership, not
existence in that class. Appendix C expressly does not close (27).

Next obligation: record fixed-boundary attainment plus Definition-A.1 membership
as an exact separate external theorem obligation. Do not claim Appendix A
discharges it. If retained as an external boundary, document that boundary and
its provenance before relying on it. If a complete self-contained formalization
is demanded, an additional existence proof is required. The external original
was not independently checked during this audit.

## SF-05: Appendix C's (L2) debt stays conditional

Severity: explicitly acknowledged analytic debt; affects Appendix C, not the
main §2–6 route. Locations: pp. 40–41, Definition C.2 and Proposition C.3,
lines 2016–2058; pp. 41–44, Remarks C.4/C.10 and Proposition C.9,
lines 2059–2071 and 2169–2216; pp. 46–47, Remark C.16, lines 2330–2358.

Definition C.2 includes three real conditions, not an arbitrary placeholder
predicate: area minimization with monotone onto boundary map (L1), harmonicity
and weak conformality for a metric **smooth up to the boundary** (L2), and
`C^(2,α)` boundary regularity for some `0 < α < 1` (L3). Results stated for a
Lemaire minimizer carry all three hypotheses.

Proposition C.3's existence is cited to [11, Thm. (1.7)]. The source says the
smooth representative required by (L2) is not reached by the printed argument.
The sentence in Remark C.4 that (L2) 'exceeds what is printed' and the later
claim that it is 'asserted' should be recorded as a provenance tension, not
resolved by silently inventing a stronger imported theorem.

Lemma C.7 supplies a metric from an **already smooth conformal structure on
the appropriate smooth surface**. It does not establish that a limiting moduli
point restricts to the original bordered subsurface. Proposition C.9 reduces
that compatibility to either (L2′) or (L2′′). Remark C.10 explicitly leaves both
unproved. Its suggested involution route additionally needs smooth convergence
of uniformizing metrics, preservation of the involution's topological type,
and genus-zero/one alternatives. Nothing in this audit certifies those inputs.

Next obligation: keep Proposition C.3 and the compatibility/existence debt
distinct from the conditional deductions C.6 and C.11–C.15. The wording 'let t
be ... of clause (L2)' in C.9 must not turn that reduction into the tautology
that the full already-assumed (L2) implies itself. Expose the preliminary
interior conformal structure, and add the actual (L2′)/(L2′′) compatibility
hypotheses to the reduction.

## SF-06: Appendix C does not prove a global embedding replacement

Severity: acknowledged source debt; alternative route remains unavailable.
Locations: p. 28, Remark A.8, lines 1336–1368; pp. 46–47, Remark C.16,
lines 2346–2367.

Local boundary immersion/transversality and separation of double points do not
give a global embedding of the minimizer in the proper isotopy class. The paper
lists the missing bounded variants of [3, §2] (relative homology, regular
neighborhood/tower, and Z2 intersection arguments from Lems. 2.2–2.5),
[3, Thm. 3.2], and the alterations in [3, §5]. It declines to treat them as
routine. [14, Thms. 1, 1′, 1′′] concern closed competing surfaces and do not
supply the fixed-boundary theorem either. [3, Existence Statement 7.3] is a
different, free-boundary assertion and is not the needed fixed-boundary input.

Next obligation: no theorem asserting that Appendix C closes (27), or proves
proper isotopic global embeddedness, is source-faithful. Keep those as explicit
unproved external/geometric obligations if that alternative route is pursued.

## SF-07: Theorem B needs the weak CW realization and a universal induction

Severity: large genuine formalization obligations; no source refutation found
in this audit. Locations: pp. 5–6, lines 211–256.

The inductive assertion is universal over **every** exchange complex of order
type at most α, not only initial subcomplexes of one fixed complex. At a
successor, both the old initial segment and the descending link have to receive
that inductive hypothesis. The latter has nonempty vertices for every
non-minimal top vertex, inherited exchange axioms, and order type at most α.
A proof only inducting on a fixed complex's initial segments misses this input.

The source does not say descending links are cones. It uses contractibility
of both the old segment and the link, the decomposition
`Y = A ∪ (v * L)` with intersection L, and two CW quotient homotopy equivalences.
At limits, it factors a compact sphere image through a **finite subcomplex**,
then a bounded initial segment, and invokes Whitehead. These are not valid
substitutes for a direct passage of arbitrary contractions through a union.

All realization statements concern the **weak topology**, explicitly distinct
from the metric topology for the infinite/non-locally-finite situation. The
source uses a CW realization, CW subcomplex inclusions, compact-image containment
in finite subcomplexes, cone contraction continuity, the product fact for a CW
space and the locally finite interval, quotient identification, and Whitehead.
Preserve the actual topology and establish these results or record each exact
outside-library boundary. A bare metric realization, graph connectedness alone,
finite vertices, finite descending links, or an arbitrary Prop standing for
'has CW topology' is not a faithful replacement.

Theorem B is not one of the four reportedly formalized Lean fragments (p. 3,
lines 114–121). This audit approves the **dependency map**, not a nonexistent
Lean proof or statement snapshot. A successful Lean topological induction
remains necessary to adjudicate the formal theorem.

## SF-08: No-closed-components condition is implicit in link spanning surfaces

Severity: definition completeness risk with a simple counterexample candidate.
Locations: p. 20, lines 956–957; p. 20–21, Lemma 6.1 proof, lines 975–990;
p. 8, lines 363–366.

The brief §6 wording calls a spanning surface properly embedded and orientable
with boundary the n longitudes. Those conditions alone do not exclude closed
components. The proof of Lemma 6.1 explicitly uses 'a spanning surface has no
closed component', and the knot comparison earlier makes the same assertion.
The intended Kakimizu concept therefore carries that condition. A structure
encoding only the brief boundary equation will be too weak.

Counterexample task for that weaker definition: add a disjoint small sphere in
a ball away from an existing spanning surface. The boundary equation survives,
but connectedness fails. This is a definition-acid-test candidate, not a
counterexample to the intended no-closed-components statement.

Next obligation: every component must carry boundary; use surface-framed
longitudes from (26) for links, not knot preferred longitude slopes. The
linking-indecomposable condition must retain the existential index and the
**sum** of oriented linking numbers to the opposite sublink; connectivity of
a graph of pairwise nonzero linking numbers is not automatically the same
condition when cancellation is possible.

## SF-09: Corner rounding changes the isotopy category

Severity: source definition/category conflict to resolve before a smooth Lean
statement. Locations: p. 8, ambient isotopy definition, lines 348–354;
p. 14, Lemma 5.4(3), lines 675–676; p. 23, lines 1094–1096.

Ambient isotopy in §4.1 is a smooth family of diffeomorphisms. Lemma 5.4(3)
carries a smooth rounded surface onto the original genuinely cornered surface.
A smooth diffeomorphism preserves smooth embedded-submanifold regularity;
its image cannot acquire the stated wedge corner. Appendix A separately uses
the piecewise smooth isotopy category. Thus the smoothing clause needs an
explicit topological/piecewise smooth ambient category, together with a bridge
back to smooth isotopy for the eventual smooth representatives. Do not encode
it as a smooth diffeomorphism between these two sets without addressing this
conflict. This is a candidate incompatibility requiring a formal category
argument, not a Lean-certified refutation issued by this audit.

PDF p. 14 was visually checked: Lemma 5.4(2) says the rounded surface lies in
the **closure** of U; extraction loses the overline. It does not say all of it
lies in the open U before pushing off. Keep this distinction in the scaffold.

The standalone lemma also promises a neat output that agrees with its input
away from the interior seam, without explicitly stating that the input is neat
near its unchanged boundary. Its intended applications have that property.
Check whether it is a standing input condition; otherwise retain this as an
additional source-scope repair, not a silently added hypothesis.

## SF-10: Reported 913-line Lean fragments are unrecovered, not proof certificates

Locations: p. 3, acknowledgements, lines 114–121.

Bounded content search over `.lean` files under `/home/caoyichuan/test` and
`/mnt/nvme1/caoyichuan/github/FL-Prover-v1`, excluding `.lake`, `.git`, and vendor
trees, found no pre-existing development with exchange-complex/tie-breaking/913
markers. Filename search found this run's newly created section scaffolds and
unrelated curve-complex exchange files, not the reported artifact. The source
itself provides no repository path, release, or pinned toolchain. Public title,
exchange-complex/Lean, and arXiv/GitHub searches did not recover the Lean files.
Absence from these bounded searches is not evidence they never existed.

A closely matching public revision was located:
[arXiv:2609.09224v2](https://arxiv.org/html/2609.09224v2), dated 12 September 2026.
Its Remark 6.11 says the source distribution lacks the earlier Lean sources
and a pinned toolchain, and declines a reproducible claim about line counts or
axiom dependencies. Its Theorem C uses the lexicographic set with a
non-emptiness qualifier. The arXiv abstract lists 69 pages; the supplied
48-page manuscript remains this audit's source. These public statements are
version comparison evidence, not an audit of the missing Lean development.

Next obligation: mark the old fragments as unavailable/unverified. Reconstruct
them or obtain immutable sources and toolchain, then run all deterministic
gates. Do not accept the acknowledgements' `no sorry/no axiom/no native_decide`
claim as a current compiler certificate.

## Minor editorial inconsistencies

On p. 3, lines 123–125 say nothing from §2 is quoted below except Definition
2.1, but §6 explicitly invokes Theorem B and Lemmas/Corollary 2.2–2.4. This
sentence cannot be read as the actual dependency list. On p. 20, lines 952–953,
the phrase 'that case is not claimed here' follows the minimal-Thurston-norm
comparison, whereas p. 2, lines 67–70 and the genus-only clause recover the
minimal-genus knot case. The intended exclusion appears to be the arbitrary
`(E,γ,α)` generalization, but the wording should be recorded as ambiguous.
Neither sentence changes the inventoried numbered statements.

## External assumptions and proof obligations

`source_manifest.json` includes a citation catalogue. Every entry is a
**candidate obligation**, not an accepted axiom. The only external source
opened in this audit was the public related arXiv revision. The mathematical
originals [1]–[21] were not independently checked. Source restatements of
(U), (E), and (Fin) are recorded with their exact manuscript intervals; their
original statements/hypotheses must still be checked before import.

The main route explicitly consumes universal least-area disjointness (U)(i),
fixed-boundary existence in the precise class of (E)(i)/(27), compactness and
finitely many isotopy classes (Fin), Kakimizu connectedness and its distance
comparison, isotopy extension, Seifert-surface existence, and elliptic/Hopf/
similarity/coordinate results used in Appendices A–B. Sliding-boundary
attainment and regularity are also asserted in (E)(ii); the source explains
that A.5/A.6 seek to derive the needed regularity from (E)(i) plus (Fin).

Appendix C additionally consumes Lemaire existence/regularity with its (L2)
qualification, sphere-theorem/asphericity input, and interior branch-point
exclusion. Its bounded global embedding obligations remain open. Comparison
citations [1, Lem. 9.13], [2, Prop. 5.15], [16], and [21] are not replacements
for the paper's own proofs. References [13] and [19] do not support any adopted
main-chain proof in the supplied text; [19] belongs to the unavailable
alternative embedding-to-isotopy route.

## Snapshot disposition

VERDICT: REJECT for blanket adoption/snapshot as an unconditional faithful
package. No assigned Lean declaration exists to approve; Theorem C's target
predicate and non-emptiness require explicit repairs, and the cited existence
boundaries must be represented honestly. Individual declarations can be
reviewed and snapshotted once their actual Lean statements and all transitive
definitions are supplied. Nothing here authorizes any target edit.

## FI-01: Supported rounding and arbitrary boundary parametrization

This is an error in our intermediate formalization, not an asserted manuscript error. The independent F-Reviewer rejected renewed acceptance of `disk_band_rounding_exists` at the original full snapshot `edf727c1501f345f11c73756dcecf722b85aa9cfead2a9b2fa26f25a42cabc1c`: the output fixes points away from geometric seams and preserves the literal boundary parameter while requiring smooth output; the input permits unrelated piecewise parameter breakpoints. The detailed speed-kink construction is an unproved diagnostic proposal, not a Lean-certified counterexample.

Evidence: [sealed review](scratch/f-reviewer/review_rounding_parameter_compatibility/REPORT.md), seal `7d8ce9088201c05bfeda29b67bfb1ee5797caaf5ddd472996567040e6015b5dd`. Repair owner `formalize_rounding_parameter_repair` constructs a compatible presentation and paid same-construction boundary trace. The final existence for every original knot/neighborhood and pointwise original knot boundary is retained. Historical snapshots remain unchanged; no rejected universal producer is counted as proved. The arbitrary supplied-rounding boundary trace has a separate missing-construction route, without a proved refutation.

## FI-02: Cylinder helper scope repair

F-Reviewer rejects C4/L2/C6/E2 auxiliary producer contracts: arbitrary covers lacked constructor-owned time-face rank; identity relabelling did not state spatial normalization; exact endpoint source maps lacked two-sided sector compatibility. This is a defect in our intermediate formalization, not a demonstrated manuscript error. Evidence: scratch/f-reviewer/review_metric_cylinder_helpers/CHECKPOINTS.md. Repair owner: scratch/blueprinter/plan_metric_cylinder_repair.

## FI-03: Signed-band center condition

F-Reviewer rejects diagram helper B5 exact-center crossing because permitted supplied resolution R may have incompatible corner geometry. Conditional P consumers remain held. This is a defect in our auxiliary interface, not a demonstrated manuscript error. Evidence: scratch/f-reviewer/review_longitude_diagram_helpers/report.md. Repair owner: scratch/formalizer/repair_diagram_B5.

## FI-04: Q3 chart source inferred in the ambient plane

Final source review rejects the affected v2 Q3 contract: an untyped set-builder caused `ActualDiskSectorChart.source_eq` to compare the ambient image of a subtype source with a full ambient ball, conflicting with the boundary construction. This is an auxiliary formalization defect, not a manuscript error. Evidence: scratch/f-reviewer/review_quotient_q34_final_flags/REPORT.md; immutable seal 161b6ad8c41ebefd2dc12bf7a6e49368f59624238f307f24906dcfb375509b9a. Explicit-carrier repair is assigned to repair_quotient_q3_source_scope;14 source declarations and95 operative records require re-review. The independent66 subset remains approved by the separately sealed supplement.

FI-02 follow-up: the exact-H rank review preserves all seven public existential endpoints, rejects universal exact-family C4/R3 authorization, and records the collapsing-slice construction as UNFORMALIZED_OBSTRUCTION_CANDIDATE. It does not prove a paper error or a Lean counterexample. Reverse spatial/endpoint normalization and a new endpoint-preserving forward route are assigned separately. The separate C2 PartialHomeomorph openness suspicion was withdrawn and independently cleared against the pinned kernel definition.

FI-03 follow-up: repaired17 declarations/six obligations are source-approved, preserving arbitrary supplied R, literal boundary beta and polygonLoop P endpoint. Their proofs remain under construction; approval is not an existence proof.

FI-04 repair checkpoint: the explicit subtype-preimage correction is APPROVE for all14 source declarations and106 operative records, with fresh14 literal reader clearance. Evidence: scratch/f-reviewer/review_q3_carrier_repair14/REPORT.md, seal d75b7349f215213f4cc16d72e340efcf68024669e7b52a86b7c74b6fc7b64e55. Root renewed lexical v2 and full operative v2 snapshots, preserving every v1/rejection artifact. Actual eight affected proof bodies are now assigned generate_q3_repaired14; repair approval is not proof completion.

FI-02 further source review: reverse metric repair v2 N1/N2/N3/N5 are rejected for lost initial compatibility, source-edge/off-graph regularity and actual edge-to-fan incidence. Fresh literal reading additionally flags a global proposition-equality antecedent in SelectedCylinderLocalProblems and elided constructor/context exports. Independent conditional rank/diagnostic68 has a separate complete-reader-supply route; no universal R3 or verified obstruction is claimed. Repair owner repair_metric_spatial98, evidence scratch/f-reviewer/review_metric_cylinder_repair98/report.md and scratch/statement-readback/readback_metric_cylinder_repair98/READBACK_SUMMARY.json. These are auxiliary formalization defects, not manuscript counterexamples.

FI-02 forward route: review_forward_endpoint_checkpoint rejects compulsory all-edge smoothness and universal static simultaneous terminal F/G cell construction; dropping the excess smooth_edges field alone does not establish compatible terminal cells. P4 containment/conditional selection remains a genuine construction debt. Repair owner repair_metric_forward_checkpoint; seven original public endpoints unchanged. Evidence scratch/f-reviewer/review_forward_endpoint_checkpoint/report.md, seal d5628dd205f1279943f688da536e0f92664a142999509cfcb230b47288abcc90.

FI-02 exact root75 adjudication: the independent68 supplement confirms that SelectedCylinderLocalProblems.mk used a global proposition-equality antecedent, rather than the particular selected chart's noninterior condition. That field's old approval is superseded by rejection; all30 spatial/image roots remain held. Root85 is a constructor-export rendering gap, not a proved obstruction. Evidence: scratch/f-reviewer/review_metric_independent68_supply/SOURCE_SCOPE_ADJUDICATION.md and FINAL_SEAL.json (120c6197598607cae8a1a58947b92bb02a3883f3dfbe37519f5218d266650bea). The68 separate conditional/diagnostic contracts are source-approved and fully frozen; their33 proof obligations do not assert unconditional R3 or an all-cover counterexample. The compiled spatial28 repair is sealed for fresh review, with fixed-initial/terminal-slice source regularity explicitly unresolved.

FI-02 fixed-slice follow-up (2026-10-05): F-Reviewer rejected spatial_normalization_from_original_inputs and image_cylinder_extension_of_paired_terminal_forms in the spatial28 checkpoint. Their source-smooth seams/collars on identity-fixed slices exceeded the original C1 source assumptions; smooth ambient edges do not establish that source regularity. The other26 contracts received conditional/literal approval only; package proof dispatch remains held. Evidence: scratch/f-reviewer/review_metric_spatial_checkpoint28/report.md, seal60a51314327d4872ac3aee6c3546c018ac859b903ecb9b1fca1fc51213806ec1. Repair owner repair_metric_fixed_slice_regularities has sealed an early C1 source-scope proposal, a3233fe811c6d1146ed65fd9ddc2109d9ef52fa6cd1af476aea8e391b9213544; review_fixed_slice_scope is auditing it. No manuscript refutation or universal rank obstruction is claimed.

## FI-05: Compact moving-frame support lost an inherited hypothesis

F-Reviewer rejected helper S6_disk_and_support because it accepts arbitrary supplied direction v while requiring compactness of the exact moving-frame rectangle image. Its original producer assumes smoothness of that same v; the intervening FrameShear record does not retain the needed continuity. Identity plane formulas alone cannot supply the missing moving-frame regularity. Evidence: scratch/f-reviewer/review_collar_remaining69/S6_REJECTION.md, final seald4d6cee4ec7191654b53f218210afbc13b8a9a4f73194b5af77bcb94bba81e3a. Formalizer repair_collar_S6 owns restoration of the exact inherited hypothesis and affected S-only caller contracts. All other released packages remain separate. This is a helper formalization defect, not a verified error in the manuscript; the exact support image and original guarded producer must be preserved.

## FI-06: Candidate endpoint-normalization mismatch under review

Formalizer formalize_compatible_rounding30 flags its G4/G5 draft endpoint equation: G3 retains transverse disk/band germs, whereas the proposed endpoint patch is mapped to a planar sector by a smooth ambient chart. The compatibility of those actual maps is unresolved and is not a kernel-certified obstruction or a manuscript-error verdict. Evidence: scratch/formalizer/formalize_compatible_rounding30/SOURCE_REVIEW_FINDING.md and seald34bfb8a69b466104eafc4fc326344be9c43d9ea52f9cb1f4ce9d68bbab3825f. F-Reviewer review_compatible_rounding88 owns exact source/caller adjudication; original public contracts, supplied boundary parameter and independent B/T1 checkpoint remain preserved. No affected proof is authorized before source approval.

## FI-07: Sampled secant parameter exceeded the source interval

F-Reviewer rejects ten inherited sampling contracts because secant_close quantifies over arbitrary real s, while the source's sampled segment parameter is s in Time=[0,1]. Exact names and dependent I1 sampling-route hold are recorded in scratch/f-reviewer/review_diagram96_Y51_final_scope/old96_final/VERDICTS.json, combined seal4ffdbf2fe6259b5549d6e730071841fd16f80a54a251431e3f147bf15520fc19. Formalizer repair_diagram_sampling_domain owns the exact internal domain repair with all original public endpoints preserved. Old snapshots and the prior approval/rejection history remain immutable; no proof search on the rejected ten is authorized. The other86 source contracts and the independent new51/Y3Y6 package were separately approved. This is a formalization-domain mismatch, not a manuscript counterexample.

FI-06 final source review: review_compatible_rounding88 rejects six declarations (G4 and its normalization record, G5 and its local-track record, G6, A2), approves the other82. Exact mixed endpoints, chart transport domains, covering/overlap conditions and arbitrary atlas signs require repair. Evidence sealbcc53a617b3c9b14f1d510623fa5a0d754ab22656509e678c0b2cd24828e131c. Owner repair_compatible_rounding6; no manuscript refutation inferred.

FI-07 repair checkpoint: explicit s : Time restored;15affected modules compile, unrelated86/new51/eightpublicheads exact. Sealccdd541c2c8e085ca828461aabd8dcc23968347197e55c6028b843fd411e8860 awaits freshsource review/guardrenewal.

## FI-08: Unused section hypothesis disappeared from orientation contracts

Final collar71review approved69 but rejected O3_literal_oriented_boundary and O4_exact_cut_constructor because Lean omitted unused section homega from compiled types. Actual original callers supply that orientation compatibility, which must be explicitly retained. This is a formalization defect, not a source-paper counterexample. Evidence scratch/f-reviewer/review_collar71_final_scope/SEAL.json2aba69f5a110b0013319ac331170b40481cbd11f3f87edfafd34b1638c058cfb. Owner repair_collar_O34; originalguardhistory retained and only affected proofs/assemblies held.


## FI-09: Sample-index phase is not numeric polygon phase

The independent151-root reader and final source/caller review reject SampledCommonTupleRounding and sampled_common_tuple_rounding after the Time-domain repair: SampledCyclicPolygon permits a cyclic indexing, but the rounding package silently uses numeric polygon phase zero. Three dependent callers require rebinding;146 other scopes are cleared. Source review seal173c477c4cb291a9bdac43035711390a27234542d6a7c974d07e1408e111f0b5. Formalizer repair_diagram_sampling_phase must return the actual numeric phase and its exact same-polygon equation, preserving universal hypotheses. This is a formalization defect, not a manuscript counterexample.

FI-08 final repair: exact original homega restored; fresh reader and final source/caller scopes APPROVE fe157172e7724c173e89d872b244d9a949e4ba99fcce4c6f52f292fda8d21e4f. Root renewed only O3/O4 lexical and fullv2 guards, preserving every v1. Existing Generator now owns all48 bodies; repair approval is not proof completion.

## FI-10: Literal disk-collar source-image scope under adjudication

Fresh quotient45 reader flags LiteralDiskCollar.source_relative_open_eq: the image appears to require negative-normal points although the supplied rectangle excludes them from the disk. Evidence scratch/statement-readback/readback_qchart_remaining45/MANIFEST.json and READBACK.md. F-Reviewer review_qchart_remaining37/addendum_01 owns source/caller/full-carrier adjudication. Independent P/H/C/O proofs continue; affected S/collar assemblies are held. This is a literal-reading flag, not a proved manuscript error or final source rejection.

FI-10 final adjudication: exact3 contracts REJECT and42 APPROVE, reviewer seal1312b8230492fbafe8d54a094e67589a0b724d0283023c213ca1c80294c12201. The equality elaborates as Set(Euc2) and loses the incident disk carrier. Formalizer repair_qchart_disk_source must explicitly bind q to the actual disk Carrier, retain both coordinate conditions and all otherfields/publicinputs. S5/A2 dependent proof routes held; independent work continues. No manuscript counterexample claimed.

FI-09 repair checkpoint: actualnumeric phase and same-polygon equation are explicit; universalproducer head and146other fullrecursive contracts preserved. Phase repair sealbcd681cb5434d996aeea3dc79d585d268d24bf614ea2fdc42999cc01d66a6320 and fresh5literal reader5d0616ef4a5e1f2ab61081ac0426978d9a4135d287f45d59fa4ccc2c117ba388 replay PASS. Finalsource/guardrenewal pending.

FI-09 final repair: source+fresh5literal APPROVE2e4e3e0053fc0057ce251dd2bd8f80cd797fffdc98aed5c881544bfc653595eb; root renewed5full/lexical scopes including45generated/194raw contracts preservingalloldversions. R5/J1/I1proofroute resumed; bodies remainunpaid.

FI-10 final repair: all3 exact repaired contracts APPROVE at review_qchart_disk_source3/SEAL.json4a3f537c109b43ddf79aec8a86367ef2c135fe6433f0fc1d4d040414a23e8c5c. Fresh2 literal scopes reconciled;16 opaque implementation wrappers preserve exact operative constraints and no supplement is required. Root renewed3 full snapshots and official guards, preserving all old versions and42 independent scopes. Four dependent proof bodies resumed. No manuscript error claimed.

Fixed-slice29 pending findings: review_fixed_slice29 withdrew an erroneous preliminary approval before root adoption. N6,N8,N9,N10,X1 are now reported as source-contract mismatches involving arbitrary histories and missing upstream certificates; final sealed review/readback reconciliation pending. No proof or guard release was made from preliminary approval.


## SF-03 disposition — 2026-10-08

Corollary 2.3 is fully represented under the previously approved connectivity convention: every downward set preserves the induced/ambient graph distance and is pairwise reachable (Preconnected); every ambient endpoint pair has a complexity-bounded shortest path; a nonempty downward set additionally satisfies Mathlib Connected. Empty sets provide no vertex. The four guarded existing proofs discharge this qualified scope; unconditional empty-inclusive Mathlib Connected is not claimed.

Current exact source review and evidence: `scratch/f-reviewer/review_section23_disposition_v463/REVIEW.md` and `EVIDENCE.json`. This is a disposition of existing proofs, not a new mathematical proof. Strict original-numbered accounting remains separate from this qualified convention coverage.


## SF-11（待审）：C.1(iv) 的任意连续映射与相对同伦边界约定

状态：2026-10-08 记录的源文疑点，尚未认定为原文错误，也未认可通过增加前提修复原命题。

位置：原文 C.1(iv)，提取文本 `references/seifert-surfaces.txt` 第 1974 行及其前文；原文称连续 pair map ψ 与 ρ ∘ ψ 在 [11, Def. (1.6)] 意义下相对同伦。

Formalizer 报告的疑点：当前对该参考定义的形式化要求同伦两端的边界映射单调且满射到指定曲线；任意连续 pair map 并不自动具有这个性质。需核对原文的隐含上下文、参考定义及现有 Lean 定义，区分原文缺少条件与形式化定义过强。

目前候选声明分别表达：对任意连续 pair map 存在逐点固定边界的连续同伦；在输入满足单调边界条件时，另外给出原生相对同伦。此分述仍待源文审查，不计为 C.1 原命题完成，也不把单调性作为未经说明的新假设。

影响：仅阻止 C.1 的相应声明获准证明；其他已审定原命题继续推进。审查由 `scratch/f-reviewer/review_original_C1_C12_v464` 负责。首报证据为 `scratch/formalizer/formalize_original_C1_C3_C12_C14_C15_v464/review/REVIEW_C1.md`。审查结论将追加在本条，所有原文问题继续集中于本文件。

### SF-11 审查结论 — 2026-10-08

F-Reviewer 已确认上述**全称范围与已采用的相对同伦定义不一致**，拒绝将当前候选计为未修改的原文 C.1。原文证明末尾“边界值保持不变且单调”只会保留已有的单调满射性质，不能为任意连续 pair map 产生该性质。审查以取值于经线一点的常值映射作定义层面的诊断；这不是新完成的 Lean 反例定理。该结论以此前审定的原生 [11] 定义为依据，未声称本轮独立核验了外部文献 [11]。

采纳的显式修正：对任意连续 pair map 给出逐点固定边界的连续同伦；当输入边界映射单调且满射到 λ 时，再给出 Lemaire 意义的相对同伦。其余 C.1 的度量完备性、齐性正则、同伦等价、Hessian 和面积不增结论保持原范围。审查接受此修正范围进入证明；原文字面的无条件相对同伦断言继续不计完成。不会通过暗中加强原命题前提或削弱已有相对同伦定义来宣称等价。

证据：`scratch/f-reviewer/review_original_C1_C12_v464/REVIEW_C1.md`（SHA-256 `381275f567d2073ce590f78519d01303adc7e55c839430b4c3cea89f88a87311`）；原文 `references/seifert-surfaces.txt` 第 1964–2013 行、边界约定第 2082–2087 行；原生定义 `target/C2Analytic.lean` 第 25–40 行。严格编号父任务 `paper_C_1` 保持 open，修正版本单独追踪。


### SF-09 补充：引理 5.4 的紧致输入与边界范围 — 2026-10-08

完整源文审查确认了独立陈述的范围缺口：PDF 第 14 页（提取文本按实际换行计第 639–694 行）明确给出紧致 Riemannian 环境，却未明确要求输入嵌入曲面紧致、proper，或在不改动的边界附近 neat；结论则要求紧致且 neat 的光滑输出。紧致环境本身不能保证任意嵌入曲面的像紧致。空接缝时，接缝邻域之外保持不变的条件覆盖整个输入，因而字面上的非紧致输入与紧致输出不相容；同样，保持位于环境内部的原边界无法产生所要求的 neat 边界。审查将这些记录为原文独立表述的范围不相容，未提供新的 Lean 反例定理。

处理：不向原始 `original_5_4` 暗加紧致性或边界前提；包含紧致输入及近边界 neatness 的版本明确作为单独修正版追踪，不计为无条件原命题完成。已有 SF-09 的光滑环境同痕与角点磨平类别问题继续保留。PDF 已核验结论为位于 `closure(U)`，不是 `U`，这一处无需改原文。

证据：`scratch/f-reviewer/review_original_section4_whole_v478/section5_v479/SOURCE_SCOPE_ADJUDICATION.md`（SHA-256 `752fd3082b411b1bbda7d7d8b9b2918970c5bc764053ee82381b3d359447dc42`）；完整审核 `scratch/f-reviewer/review_original_section4_whole_v478/section5_v479/REVIEW.md`（SHA-256 `e158c47dc54c1bcae9fa9e5e5e8033df1b51a417455527ffd890fd6ca1bd1bbc`）。

### SF-09 补充（V480-W1）：精确宽度剖面与源文正则性证明路线缺口 — 2026-10-08

对 B2–B5 宽度接口的完整审查确认了一个**形式化过约束，同时对应源文证明路线缺口**：当前 `SmallSliceGeometry` 同时要求任意源文允许的 C1 接缝宽度保留精确给定 `eta` 剖面并输出 C∞ 新剖面。局部常斜率诊断表明，非零常斜率的精确剖面若要求沿接缝 C∞，会迫使 `eta` 为 C∞；而源文 Lemma 5.4（PDF 14–15）只给出 C1 宽度并在最终曲面上给出光滑输出，Appendix B.1（PDF 29–30）书写精确剖面但没有补足任意 C1 `eta` 沿接缝高阶导数的论证。

这不是已实例化的紧致环境反例，也不是对原文结论的否定。修复边界是一次完整受影响闭包迁移：将未平滑的原始 `eta` 与最终 C∞ 切片解耦，或显式构造保留原始 `eta` 的支集、增益、面积、帽端、导数、侧别/同痕和全部传输条件的 C1→光滑桥接。B2/B3 三个不受影响头仍可独立推进；B4/B5 及 Section 5 六个直接消费者在迁移和复审前不计证明完成。

证据：`scratch/f-reviewer/review_original_B2_B5_v475/width_regularity_v480/REVIEW.md`（SHA-256 `1beaf61ef8c8557d017f45132d9fea3a8529e2aa98048a0b9e1e1c67fad6935e`）、`SOURCE_REGULARITY_BOUNDARY.md`（SHA-256 `ef2bda01483a95012c56d021711a55f241df8129b0373b24e999eb3dd798d993`）、`AFFECTED_CLOSURE.json`（SHA-256 `0f2e21979245c5779d78292ac3c73d2b1722b23a67cc1bef1a35e9659ff8debf`）。


## FI-11: Section 5 image-area atlas existence has an empty-ambient counterexample

状态：2026-10-09，Lean kernel 已确认；这是当前形式化接口缺陷，暂不认定为原论文错误。

受影响声明：`SeifertSurfaces.OriginalEndpoints.Section5.Obligations.image_area_atlas_exists`（`Section5OpenObligations.lean`）。当前 `ImageAreaAtlas F` 要求总映射 `map : ℕ → E2 → M`，因此任何 atlas 都给出 `map 0 0 : M`。但当前前提没有 `Nonempty M`；`SourceCornerSurface` 允许空 source 和空 seam family。

Lean 证据：`scratch/f-generator/generate_original_section5_approved26_v480/migration_v480/project/Section5EmptyAtlasCounterexampleV481.lean` 中的 `concrete_empty_ambient_counterexample` 构造 `M = Empty`、空度量和空 source，并证明不存在 `ImageAreaAtlas`。编译与公理审计通过，仅使用 `propext`、`Classical.choice`、`Quot.sound`。

处理：保持编号正文声明和原始快照不变；由 Formal Reviewer/Formalizer 一次性审查受影响闭包，选择允许空 chart index 的表示，或在下层接口显式处理空 ambient 分支。该问题已阻止当前 atlas-existence 证明计入完成。

证据文件：`scratch/f-generator/generate_original_section5_approved26_v480/migration_v480/CONFIRMED_SECTION5_FINDINGS_v481.md`。


### FI-11 修复进展（2026-10-09，v488）

已按审查通过的方案 A 修复表示：仅下层 `image_area_atlas_exists` 增加 `Nonempty M`，空集合的 `extendedImageArea` 明确取零；原始编号定理没有新增前提。七个受影响声明和九个空分支已完成源码审查、独立字面读回及精确复制后的声明保护检查，证明任务已恢复。`original_5_4` 的 SF-09 紧致性/neatness 范围问题继续保留，不能以本次空面积修复宣称该原始结论完成。

证据：`scratch/f-reviewer/review_original_section4_whole_v478/section5_empty_repair_v487/READY.json`；`scratch/statement-readback/readback_section5_empty_repair_v487/READY.json`（SHA-256 `478704e9d24f0f7666bdef97e97e1d5afae57aee42d78d046282100ca2c4a265`）；`logs/wave6_root/routes_v464/SECTION5_EMPTY_FINAL_GUARD_AUTH_v488.json`。字面读回中的 `ENNReal.toReal ⊤ = 0` 和非空分支不自动保证有效图册存在的说明已保留，图册存在性与面积不变性仍需实际证明。

### FI-11 证明接入进展（2026-10-09，v489）

九个空输入分支、通用图册面积不变性及修复后的 neat 面积桥接已完成证明，并于 `585ca55f644232facfb9218e202ddf5e1dcd6512` 接入主库。十一项声明保护、编译、占位符扫描和公理检查通过；接受的完整证明依赖不含 `sorryAx`，也不引用保留的 33 项未完成声明。原文编号前提保持不变；此处不宣称任意图册存在性或原文 5.4、5.5、5.7 已完成，SF-09 保留。

证据：`scratch/integrator/integrate_original_scalar_roots_v448/section5_native_area_v488/CANONICAL_SECTION5_AREA_EMPTY_WHOLE11_RECEIPT_v488.json`（SHA-256 `3ad83e3c8ce1fba49a11bb4aa39c6c43d2b6646e52c8a2c8b2f24ba51553a53b`）；独立验收 `scratch/regulator/audit_b1_whole_context_v480/section5_area_empty_whole11_v489/READY.json`（SHA-256 `d9c7f0e1e7730726ed915218ca70a9030725a47d07374997b9b8da7ec25c30de`）。


## FI-12: B3 新导入改变了原生距离使用的范数实例（已修复）

2026-10-09，确认属于形式化实现问题，不是原论文错误。B3 证明新增 Tensor/RSTensor 导入后，文字未改的 `metricEDist` 选中了新增全局切空间范数实例，替换了原来的度量 g 所诱导的范数。v482 在该定义处精确禁用新增实例、定义后恢复；全部 991 个原生声明和 450 个定义值逐字内核比对通过，保留原 v1 声明保护。旧失败证据保持不变，不把差异解释为无害的证明名称变化。证据：`scratch/f-generator/generate_B2_B5_whole_fresh_v481/release_b3_collar_v482/B3_COLLAR_WHOLE_ROOT_PACKET_v482.json`。

## FI-13: unknot 分支引用的面积下确界正性尚未证明

2026-10-09，实际原生上下文公理审计确认 `Section4.areaInfimum_positive` 依赖 `sorryAx`。此前任务交接中“already-native”未提供已完成证明的依据；原作者已在 `scratch/f-generator/generate_original_section3_main_whole_v479/CORRECTION_UNKNOT_AREA_V489.md` 撤回该完成暗示，旧交接文件及封存哈希保持不变。原生顶点唯一性不能代替该顶点面积下确界的严格正性。此项继续列为证明义务，不计 least-area 结论完成，也不认定为原论文错误。审计证据：`scratch/f-generator/generate_original_unknot_category_v489/logs/UnknotNativeAuditV489.build.log`。


## FI-14: A6 辅助合并接口保留任意整领圈，缺少受控邻域的构造依据

2026-10-09，完整源文审查拒绝当前 whole-C 辅助接口的适用范围；不是原论文反例。接口要求保持每个既有内部/指定出口领圈的全部 target，并由新圆盘覆盖整个选中工作域，但有限 incidence、sector 和精确并集条件没有保证这些任意大领圈的拓扑是原文构造中所选的受控邻域。六项 Lean 诊断已验证：在附加的大领圈覆盖紧致闭曲面的配置假设下，要求的单圆盘合并不可能；完整具体 NativeSmoothHandleGeometry 反例记录尚未构造。

处理：保留所有既有整领圈以及 MC1/MC2/C0；由 M 和每个后继阶段实际构造选中工作并集到选中闭 core 并集的强形变收缩数据，再由 C 证明光滑展开。该构造资料是下层 producer 的证明义务，不增加原文 A6/X0 的前提，也不把圆盘图或合并结果作为输入。受影响整包正在重建声明并将整体复审；旧快照及已封存的 _7 结果不改动。

证据：`scratch/f-reviewer/review_A6_MC_whole_extended_domain_v481/whole_C_collar_v490/REVIEW.md`（SHA-256 `d8414bbcd7eb3cbd692bb473d47859cc429de44fa4f970f452dd843350f5e3d8`）；`READY.json`（SHA-256 `c2d3d0baaa979e791d6573d789505c2e60dda9f36eb562417a168f70dc2768e5`）。


### FI-14 整包修订已通过审查（2026-10-09，v491）

保留全部内部、指定及受保护领圈，并把每个有限选中工作并集到相应闭 core 并集的强形变收缩资料纳入下层 producer 的构造义务。五个模块的完整 86 项声明已通过源码复审和独立字面读回；读回的选择间同伦不要求自然性、允许恒等邻域细化等范围说明均由审查者明确复核。13 项后继声明已建立 v3 保护，v1/v2 历史保留，M/C 证明工作已恢复。原始 A6/X0 没有增加前提；旧 `_7` 证明不自动迁入新环境，实际光滑展开和完整 Morse 构造仍须证明。

证据：`scratch/f-reviewer/review_A6_MC_whole_extended_domain_v481/regular_neighborhood_v491/RECONCILED_READY.json`（SHA-256 `6029e66b08690d9f03ad4f183bf485b77604063811574d51da1d0b22ba1c0ba0`）；`logs/wave6_root/routes_v464/A6_MC_REGULAR_GUARDS_v491.json`；完整原始声明与定义绑定 `.claude/state/statements/A6MCWhole_v491.raw_binding.json`（SHA-256 `b0a50e2ed212bf623f5a1dc3bb817c5c0fadafdbabc40f8452509e75f24c848a`）。


## FI-15: A0–A4 辅助声明的 iff 优先级错误（2026-10-09）

独立字面读回及 F-Reviewer 的编译器 AST 核对确认：`FiniteSurfaceComplex.coherent_orientation` 把 membership 与不同三角形的条件误置在 `↔` 左侧，`TopologicalSurfaceRegion.chart_boundary` 同样未把整个等价式限制在图的 source 内。这是新辅助接口的形式化错误，不是原论文错误。旧批准记录保留但已被有界复审拒绝；19 个候选证明尚未获准开始，也未创建声明保护。原 Formalizer 正在增量修复两处括号及受影响的完整声明闭包，现有原生弧领圈证明独立继续。

证据：`scratch/f-reviewer/review_section4_a0_a4_whole_v492/RECONCILIATION_READY.json`（SHA-256 `2d93375bf58d46fecb4cf44a330b68a35a85da7ad168fe980ebe4b3cda6ac25e`）；`scratch/statement-readback/readback_three_whole_packages_v491/section4_topology/READBACK.md`。


## FI-16: E 的切开圆盘接口错误要求暴露角点具有光滑半空间边界图（2026-10-09）

完整源文审查确认新辅助包 N7 的形式化要求过强：输出沿用原接缝并保持每一块的完整原域，但切开后允许出现两条不同切向射线组成的新边界角点，且不保证有保留的内部接缝落在该点。`native_disk_restriction_seam_and_smooth_charts` 却对这些点也要求带精确边界像等式的全秩 C∞ 半空间图。原块 C1 正则、边界两条射线光滑或拓扑圆盘识别不能直接满足这个更强的输出。

这是源文忠实度审查认定的辅助接口缺陷；尚无新 Lean 实例化反例，不认定原文 E/A6 错误。旧包整体拒绝，13 项新辅助证明尚未授权。Formalizer 正在同一 scratch 的 `corner_repair_v492` 一次性修复 N7 与受影响输出：明确角点类型，或把带真实光滑内部接缝、新域和父块因子分解的有限细分列为构造义务。不得向原始 E 增加光滑边界前提，也不得删除 `smooth_off_seam` 后声称仍得到原 `LocalSectorDisk`。已批准的独立拓扑构造继续推进。

证据：`scratch/f-reviewer/review_a6_p0_p2_whole_v491/E_global_disk_v491/REVIEW.md`（SHA-256 `d01e4f89daa51abd24b3ae79d6d95ae13c550367c121e6ec3ed1de7c111e4041`）；`READY.json`（SHA-256 `ded4d96148d99029ef989c3609a85649f380f2a7d91bf3a861a5aef515a7b4d1`）。独立字面读回 clean 仅说明表达式已读清，不能覆盖本项源文拒绝。

### FI-15 修复已完成审查并恢复整包证明（2026-10-09，v492）

两个 `↔` 的完整等价式已置于相应成员/不同对象条件内；全 53 项声明、5,417 条依赖和 165,629 个 AST 节点完成独立读回及源码复核。19 项辅助定理已创建新 v1 声明保护并通过检查；完整结构构造器与定义绑定一并封存，原始编号定理不变。19 项是证明义务数量，不是已完成结果。

证据：`scratch/f-reviewer/review_section4_a0_a4_whole_v492/repair_01/RECONCILED_READY.json`（SHA-256 `34b436c38c19d37a9b1ac0632cff7f6d3f6e0df7661465541da5578acee24171`）；`.claude/state/statements/Section4A0A4Whole_v492.raw_binding.json`（SHA-256 `979d458e297bd36b8a01e3fd6b6f97c85ab855db0ae7c9570ec759e0cfeeef6a`）。


### FI-16 修复继续：例外点集还需覆盖全部实际源顶点（2026-10-09，v493）

v492 整包复审确认：仅把有序圈列出的顶点纳入角点例外还不充分；当前调用数据允许圈弧内部穿过未标记的细分接缝顶点。新 N7 对这些点仍可能提出过强的光滑半空间图要求。已将完整有限例外集及其到 CornerExactLocalDiskPatch 的精确传递作为一次整包修复交给原 Formalizer；原始 A6 不增加前提，其余已审条款保留。此项仍是形式化接口缺陷，没有新 Lean 实例化反例，不认定原论文错误。

证据：scratch/f-reviewer/review_a6_p0_p2_whole_v491/E_corner_repair_v492/REVIEW.md，SHA-256 20d81aff012558795e7df9ad52a8813bd346930aca8dd5e3fd098397ee4a052b；READY.json SHA-256 099c0aec9ad124d63c0e703d1f70a246712f5c091e92c76966bffea9cc447e6e。独立读回 CLEAN 不覆盖本次源文审查拒绝。


### FI-16 完整角点修复已通过整包复审（2026-10-09，v494）

v493 把圈顶点与位于实际边界上的全部细分接缝顶点取并集、去重，并精确传递到圆盘补片及最终标签。完整 8 个新增和 11 个继承声明经源文复审、全新独立读回和读回标记复核后获准建立保护。权威表达式捕获为 140174 节点；139999 节点的 alpha-cache 版本不作为字面相等依据。此项批准不表示原始 E/A6 已证明。证据：scratch/f-reviewer/review_a6_p0_p2_whole_v491/E_reader_reconciliation_v494/READY.json，SHA256 84537dfb8fb6be853ef758b0b5c2ce4e7d810fe6a9400d7078b0bfb366723db6。

## FI-17: P2 剪切记录三个时间变量被推断为全部实数（2026-10-09）

编译器字段类型和源文复审确认 IntrinsicMatchedHalfstripShear 的 horizontal_strictMono、horizontal_surjective、spatial_block_lower_bound 把 s 推断成 ℝ，而原始同伦时间仅为 Time=[0,1]。这是辅助接口形式化错误，不是原论文错误。复审拒绝旧包，要求仅将三处明确为 (s : Time) 并在算式中强制转换为实数，其余 40 字段、6 个载体字段、5 个已付 P0/P1 证明体和原始 A6 接口保持不变。已交 Formalizer 整包修复；两项 P2 全局覆盖义务及 P4 尚未完成。证据：scratch/f-reviewer/review_a6_p0_p2_whole_v491/P2_time_binders_v494/READY.json，SHA256 0011407493da89996c6980b586df0258128bc7c4fe38084564e59bfeaa7a0f02。

## FI-18: B4/B5 端点速度定义不支持任意零速度见证的唯一性（2026-10-09）

Lean 诊断确认当前 IsMetricGeodesic 只约束闭时间段内的光滑性及内部 ODE，而初速度用端点处不受限的 mfderiv 定义。改变负时间延拓可以保留原生测地线条件而让记录的初速度为零，因此不能据此声称任意零记录速度见证的全局唯一性。这不反驳原始 B4/B5 或已指定的 N.exp_zero。源文审查批准保持原始目标不变：非零分支证明端点可微与全图 ODE 唯一性；实际光滑零速度流直接证明常值，再用 N.exp_zero。证据：scratch/f-reviewer/review_area_uniform_bound_whole_v491/B4B5_endpoint_velocity_v494/READY.json，SHA256 4d26199c9f411f2808c75123d4aa709ae7f0bd78e81be755cd041ce5ca2d7cb2。

## FI-19: 任意旧角点分解的有限共同光滑细分路线存在反例（2026-10-09）

新增 Lean 诊断通过编译、占位符和基础公理检查：对 y=0 与 y=x² 两个各自光滑的边界，有限个全秩原生角点块/棱柱不能同时从指定侧服从两套边界并覆盖尖点附近的中间曲线。该结果否定通用精确共同细分路线；并未否定原文 geometric_smooth_endpoint_bridge、任意源 hfixed 或 A6。后续整包构造需重新选择边界并证明实际映射的正则性、端面像保持和嵌入性。原目标未修改；已交整包 Blueprinter。证据：scratch/f-generator/generate_original_section4_whole_v479/WHOLE24_CREASE_ROUTE_REPORT_v494.md 及 receipts/WHOLE24_CREASE_ROUTE_RECEIPT_v494.json。


## FI-20: C 辅助运动输出未保证坐标闭球位于局部图的 source 内（2026-10-09）

独立字面读回指出 native_merge_simultaneous_corner_motion 的输出没有保证所选坐标闭球属于所选 partial chart 的 source。源文复审确认该接口不足以充当实际图补片证书；保留已有较弱运动支持结果，但后继声明须在输出中补全闭球包含关系，不增加原始 P/req 或 C/A6/X0 的前提。完整全局展开时钟的存在性仍作为一个实际待证明的整包构造；不得以任意预选端部种子的可延拓性替代原文要求。46 个新解析支持声明另获批准，尚需独立读回及保护，六个原始 C 根仍未完成。证据：scratch/f-reviewer/review_A6_MC_whole_extended_domain_v481/whole_frontier_v495/READY.json，SHA256 d0c9fd9d8221a8dd6bfe7b777e5872b1cff8d28d2f30497f17d058c357671acc；同目录 FORMALIZER_REQUEST.md。此项是辅助形式化输出缺失，不是原论文反例。

## FI-21: E 的参数精确性字段比较了不同类型的对象（2026-10-09）

证明构造暴露 CornerExactLocalDiskPatch.parameter_exact 的 HEq 左侧是 ContinuousMap 对象，右侧却是普通复合函数。源文复审确认这一辅助接口缺陷，要求仅将右侧改为打包的 ContinuousMap.comp，保留相同 W、源域、计数、patchParam、全部角点标签和其余 117 个字段。原始 E/A6 不增加前提；历史已排除的 NativeExactLocalDiskPatch 路线不随之改动。两个已付支持证明保留，完整 E 仍有奇偶性、圆盘、包络及变分构造义务。此项不是原论文错误。

已派 Formalizer 在独立 scratch 修复整个受影响声明闭包，再做精确复审、独立读回和保护更新。证据：scratch/f-reviewer/review_a6_p0_p2_whole_v491/E_parameter_HEq_v495/READY.json，SHA256 3e94dd03a45a61196e639c9057e27e92244858b648a26cdef2241f86dffbb1e6；REVIEW.md SHA256 535513f40ee2deeabbdd3e7b00c77222b49c76b5dabe53314dcb360b39db46d6。

### FI-17 修复已批准并恢复整包证明（2026-10-09，v495）

三个字段已明确使用 Time=[0,1]。完整 773 声明闭包、43 个剪切字段、6 个载体字段及生成构造器/递归器完成源文复审、独立读回和标记复核；五个已付证明体保持不变。Root 对 producer 执行合法 approve-change（文字头不变，完整记录含义已修复），其余五个头保留 v1，六项保护全部通过。新绑定为 .claude/state/statements/A6P0P2Whole_v491.time_repair_v495.raw_binding.json，SHA256 39452808862074dca193db75fbc427654472150cfc9518d847ae4c7615fbbd5b。两项 P2 全局覆盖、P4 和原始 A6 仍未完成。

### FI-13 证明已交付，最终验收仍待上游精确上下文修复（2026-10-09，v495）

未改变的无条件 areaInfimum_positive 已通过编译、占位符扫描、声明保护及基础三公理检查。封存证据 scratch/f-generator/generate_area_infimum_positive_whole_v490/READY_v495.json，SHA256 f2251c442bde2cb205539bf8fba93a52e083a9a13baa53b9643797aa675fa856。它使用的 foliation 证明环境正在修复一个拓扑实例差异与复制声明的分组元数据；原面积证明尚未最终接入验收，不能据此声称完整 4.7 或极小面积实现性完成。


## FI-22: 任意端帽附近的辅助圆柱正则性要求超出了分片光滑范围（2026-10-09）

已由完整源文审查确认：Section4WholeReplacementV496 的 RegularImageBlock、RepairStep 和 WholeReplacement 对任意 GeometricTrack，要求除精确端帽时刻外的每一点都有无接缝的光滑像圆柱模型，连任意有折痕端帽的所有穿孔时间邻域也包括在内。原文允许分片光滑的端帽和单侧局部模型；该中间接口因此添加了未经源文支持的正则性结论。此项是辅助形式化的范围错误，**不是原文定理的 Lean 反例**，原始两个 Section 4 目标及24条保护声明均保持不变。

修复责任：Formalizer 整包区分任意分片端帽的构造与具有原生光滑端点假设的 neat 构造，并将区别传递到局部修复、有限完成、复合及反向过程；保留任意原始 F 锚点、第二条轨道的完整 C1/秩条件、真实端帽/标签和同一最终见证。未经重新批准不为该10头候选建立保护或推进其证明。证据：[完整审查](scratch/f-reviewer/review_Section4_whole_replacement_v497/REPORT.md)、[审查收据](scratch/f-reviewer/review_Section4_whole_replacement_v497/READY_v497.json)。

## FI-23: P4 固定边界迹与任意独立参考时钟的有限 PL 要求不匹配（2026-10-09）

整包源文审查确认 native_fixed_polyhedral_replacement_exists 的量词过强：输出的固定边界迹已经确定了对应关系，但输入允许两个独立选择的参考边界参数，不能保证它们之间的对应是有限分片线性的。此项是辅助构造接口的形式化缺陷，不是原始 A6 的反例。全部11个头、记录字段、构造器和调用者已一并审查，1210项输入哈希吻合，原始 A6 与已付 P0/P1/P2 证明均未改变。

修复要求：从原有固定原生见证共同构造 RX、RY，将它们作为存在性输出；保留全部正则性、有限 PL、真实时间和固定迹字段，在两次整体替换中复用同一个实际 RC。不得向原始 A6 增加参考时钟兼容前提。旧候选整体拒绝，待新 Formalizer 整包修复后再审查、独立读回并建立保护。证据：[完整审查](scratch/f-reviewer/review_A6_P3P4_whole_v497/REVIEW.md)、[审查收据](scratch/f-reviewer/review_A6_P3P4_whole_v497/READY_V497.json)，收据 SHA256 `0246d4172158e299786bf807a0552b5858a89dad39a9c6136f31bce87329ddd5`。

### FI-13 最终验收完成（2026-10-09，v497）

原有无条件 areaInfimum_positive 已在提交 `9641955fab3794426dcb6b2ec2e63530705d3634` 完成主库接入和独立最终验收：22项有界检查、6项新编译验证通过，完整101487声明依赖仅含基础三公理，原 v1 声明不变。先前 foliation 上游精确上下文问题已针对本证明解决；完整4.7的实现性、极小性、嵌入性及稳定性仍是单独义务，不增加原文编号完成数。证据：[最终验收](scratch/regulator/audit_area_positive_whole_v497/READY.json)，SHA256 `3b9ff2c6e8d63f730b89bcf828e55b34a759a9edf75d6e7b3cabdc8708ed5750`。验证期间的临时探针路径事件保存在同目录 INCIDENT.md；数学源码及对象逐字不变。


### FI-23 修复和读回标记核对已完成（2026-10-09，v498）

RX/RY 已改为共同构造的存在性输出。全11个头及10850项 operative 声明完成源码审查、独立字面读回和9项标记核对；新的第一端点、stage 与 F 锚定轨道必须在调用者中一致使用，不可把输入的旧见证与替换见证强行识别。原始 A6 未增加前提，已付 P0/P1/P2 保留。Root 对所有11项建立 v1 保护并检查通过，整包证明恢复；这不是原始 A6 的完成。证据：[标记复核](scratch/f-reviewer/review_A6_P3P4_literal_flags_v498/READY_V498.json)，SHA256 `d985b2ca1802646247c11cee8ecd00d7fd7a886060dee1990432379690c46da9`；[完整绑定](.claude/state/statements/A6P3P4Whole_v498.raw_binding.json)，SHA256 `90cf977b487300b1f83b235922f22d8fd1e75636aee1d85f75d4b0171056a096`。


## FI-24: E 的完整端点扇错误地把所有物理边界芽限制在选定球内（2026-10-09，v498）

分类：辅助形式化范围缺陷；不是原始 Theorem 3.2(E)/A.6 的已构造反例或论文错误。

完整源文复审拒绝 v473 的 `RegularCutEndpointFanData`/`EndpointRefinedRelativeCutData` 作为原始 E/A6 整包交接。`fan_cover` 覆盖 R 中的完整开邻域，但 `side_germ` 的每个物理侧只能用 `RegularFixedRayGerm`，其 `original_label` 与 `clock_range` 把整个正径向区间限制在 B 的球内固定弧上。在指定边界横穿人工球面的位置，完整邻域同时具有球内与球外物理边界芽；后者没有合法标签。此前“无关物理顶点不需要标签”的说明没有覆盖这个实际交叉顶点。

Lean 已验证的 v497 诊断 `native_fan_contract_forces_fixed_edge_preimage_empty` 从原生旧 Q 得出 `γ ⁻¹' X.edge = ∅`，编译、占位符扫描及公理审计通过，只用 `propext`、`Classical.choice`、`Quot.sound`。这是旧输入记录的已证明限制，不是每个 Q 均不存在的结论，也没有完整具体原生 F/J/X/B 交叉反例。当前完整球覆盖 producer 只提供 B 的正则性/有限交点，未提供边界避开所有 edge 的构造；原始 E/A6 无此限制，不得利用诊断删去相对边界情形。

最小完整修订：保留完整扇邻域、同一表面/细分/原始参数；物理侧使用原始完整 Circle 的局部正则时钟，允许球外方向；仅被选为球内边界的芽才附原 B 固定弧的精确从属标签。此下层资料必须由原输入、同一个 C-prime、任意正面积预算的 T1 producer 构造；全部扇时钟、完整 link 与球内 cut/fixed network、角点圆盘/边界 seed、T2/T3 及原始 E caller 同包重绑。原始 E/A6 不增加前提，局部圆盘边界仍仅使用球内固定弧和原 cuts。保留已封存的 19 个声明保护和已完成几何结果，不自动迁移到修改定义后的环境。下一 owner 为 Formalizer，整包复审、独立字面读回及 Root 的合法 guard 转换后再继续证明。

源文：`references/seifert-surfaces.txt`，Theorem 3.2(i) 308–319，Definition A.1 1088–1118，Theorem A.6 1288–1323；同名 PDF 印刷页 7、23、27。SF-04 的精确存在类 (27) 源文债务另行保留。

证据：`scratch/f-reviewer/review_A6_E_physical_fan_scope_v498/REVIEW.md`、`REPAIR_SPEC.md`、`READY.json`；输入 `scratch/f-generator/generate_A6_relative_cut_compatibility_v469/parameter_area_stage_v476/repaired_whole_v496/READY_V497.json`，SHA-256 `189fb6b93d0483bd1b79033df361881eb91c4fa6667eb90880cdd0a814378ecd`。本审查未编辑源代码、原声明、保护、ledger 或共享 memory。



## FI-25: 原始 D 所需的多分量解析接口尚未覆盖（2026-10-09，v501）

分类：证明过程中确认的形式化覆盖缺口，不是原文 D 的反例。原始 D 的 n 分量目标与已有保护头保持不变。

整包 D 证明负责人核对现有 `BoundaryFoliation`、`OriginalA7ScaffoldV463` 和 Section 4 源几何接口后报告：`LongitudeFoliation` 使用单分量 `SeifertSurface`，并要求单个环面覆盖整个边界；这些接口目前不能直接提供任意 n 分量链环所需的 U/E/R1/Fin。已完成的多环面边界、总链接数和条件下降归约不构成这些解析 producer 的证明，也不构成原始 D 或 Kakimizu 连通性的完成。

已派同一整包 Formalizer 补齐真实标号多环面边界、longitude/metric/minimizer/complexity 及其原始调用者，保留原文 non-split、linking-indecomposable 与逐分量不可压缩条件；不得给原始 D 增加这些 producer 的假设，也不得把任意 spanning 输入限定为连通表面。具体新接口仍须完成源文审查、独立读回和声明保护；现有 knot 结果不自动升级为 link 结果。

证据：[D 整包报告](scratch/f-generator/generate_original_D_link_exchange_whole_v500/REPORT.md)、[实际候选验证](scratch/f-generator/generate_original_D_link_exchange_whole_v500/CANDIDATE_GATES_V500.json)。原文位置：`references/seifert-surfaces.txt` 第77–78行及1010–1076行。修订 owner：`formalize_original_D_link_analytic_whole_v501`；原始 D 的循环覆盖、参考表面及实际下降证明继续由独立整包 generator 推进。


### FI-24 整包修复已批准，原始证明继续（2026-10-09，v502）

完整物理 Circle 的局部时钟与球内固定弧标签已分开。74 模块的 257 项外层声明和 2404 项 operative 定义完成源文审查及完整独立读回，三个字面标记已由审查者核对。Root 对 12 个变更历史头合法更新为 v2，7 个历史头保持不变，16 个新增头建立 v1；旧保护和已封存证明证据保留。新的整包 E 证明已交给独立 scratch 的 Sol 继续。

这仅解决辅助接口的范围缺陷；原始 E/A6、169 个证明空缺、固定与滑动竞争类之间的构造桥梁及 SF-04 仍未完成。证据：[完整标记复核](scratch/f-reviewer/review_A6_E_complete_literal_flags_v502/READY.json)，SHA256 `6d717d695bf1b12d5c538f223ebb1bf34cbf304438842398476e3d7ebde50fbd`；[整包保护绑定](.claude/state/statements/A6EPhysicalWhole_v502.raw_binding.json)。未发现新的论文反例。


### FI-24 native export custody reconciliation (confirmed, v504)

Confirmed binding incident, not a new mathematical source defect or paper counterexample: the approved physical-scope code capture re-elaborated the complete caller under diagnostic module `WholePhysicalDirectCaptureV498`, then labelled its local declarations as `A6WholeOriginalECallerV498`. The actual approved compiled caller object's generated binder names differ literally. Fresh import-only export confirms exactly 228 inherited signature discrepancies, including five protected heads; all other expression fields and complete source headers remain unchanged. Both old and native raw signatures must be retained.

The faithful repair is additive corrected native-object export and parent-binding reconciliation, preceded by independent complete code-only native read-back. Preserve the previous 257 outer/259 explicit/2,404 operative binding, all guards (including task06's byte-identical v2/v3 history), original source/object pins and mismatch evidence. No alpha normalization, guard reset, theorem/proof edit, infrastructure rewrite or automatic candidate credit is permitted. Original E/A6, SF-04, simultaneous final processing and fixed-to-sliding recovery remain unpaid.

Evidence: `scratch/f-reviewer/review_A6_E_native_binding_whole_v503/READY.json`, `REVIEW.md`, `PROTECTED5_EXACT_RECONCILIATION.json`, `CODE_ONLY_RESOURCES.json`, and `logs/ALL228_LITERAL_DIFFERENCE_DIAGNOSIS.json`. Next owner: statement-readback on code-only resources, then Root additive binding adoption, then fresh-context whole E F-Generator. Recorded by Root from the sealed source review; additive native read-back remains pending.


## FI-26 (confirmed): opening boundary rays double-reverse the terminal direction

Classification: confirmed auxiliary formalization sign mismatch; not a paper
error, complete original-presentation counterexample, or completed Section3
proof. Date: 2026-10-09. Root adopted this entry as FI-26 from the sealed reviewer report; the reviewer made no shared edits.

Definition A.1 requires distinct rays of the two edges at a corner and includes
smooth surfaces and compatible triangulation (`references/seifert-surfaces.txt`,
1088–1096, printed p. 23). In `SupportedCompatibleGeometry.lean` 3636–3673,
`stageBoundaryTangent` uses raw chart +1, inward at both endpoints of Time.
`OpeningTrack.distinct_boundary_rays` additionally negates the final-endpoint
vector. It therefore tests a different ray pair and excludes harmless smooth
straight subdivisions. Mathlib `Instances/Icc.lean` 52–65 explicitly distinguishes
the intrinsic oriented interval tangent 1 from raw chart +1.

V506 compiler diagnostics certify only conditional native-record impossibility
under adjacent literal affine disk-cell formulas; no complete regular original
diagram counterexample was constructed. The chosen original compatibility
producer preserves source trace and isotopy but supplies no bypass certificate.
No original theorem has been refuted, narrowed or newly paid.

Minimal repair: Formalizer keeps the existing raw tangent convention and
removes the extra negation from the ray field in its own scratch, delivering the
complete dependent opening/rounding/C1/source-geometry caller package. No
additional original hypothesis, no no-subdivision restriction and no change of
physical boundary or source isotopy. Whole source review, independent complete
code-only readback and lawful guard update are required before proof work.
Preserve all frozen old evidence and 87 support roots; rerun affected gates in
the repaired context. Original heads stay 2 paid / 18 open; MainD connectedness
is separately owned.

Evidence: `scratch/f-reviewer/review_Section3_opening_ray_sign_whole_v505/REVIEW.md`,
`REPAIR_SPEC.md`, `READY.json`; input
`scratch/f-generator/generate_original_section3_main_whole_v479/READY_WHOLE_OWNER_HANDOFF_V506.json`,
SHA256 `d187e7dd46ae413198a5b92df79d67c39f9aa797fb0a999b5ca1d02f71079e0f`.

Root record v505: copied from the sealed source review above. This is a confirmed formalization mismatch; no complete original theorem counterexample or revised snapshot is claimed.


## FI-28 — strict native identity receipt used the wrong comparator (resolved, v507)

2026-10-10. Classification: confirmed verification-receipt mismatch, not a mathematical source error. The Section3 v506 adapter audit used `original.type == target.type`, invoking `Expr.eqv`, while its receipt claimed strict `Expr.equal`. The reviewer rejected only that identity receipt; the whole source approval and completed 115-root literal readback stayed valid. No original result was accepted on this rejected receipt.

An additive compiled v507 audit invokes `Expr.equal` directly and separately checks exact level parameters for all 158 adapter/runtime pairs. The final bounded review approves all 158 strict comparisons, the complete 260-contract mapping and retention of all 24 old guards. All 158 theorem slots remain unpaid; 102 other contracts are native custody, not theorem proofs. The prior rejected artifacts are retained. Evidence: `scratch/f-reviewer/review_Section3_opening_ray_repaired_whole_v505/ADAPTER_FINAL_READY.json` (rejection); `ADAPTER_STRICT_V507_FINAL_READY.json` SHA256 `f9216e4ace8d68d785e5f8ea739891ce57c084a8158431af51f6f59d1792c955` (additive approval). The review binds actual READY bytes despite a stale circular manifest self-reference; that stale field is not accepted as a pin.

### E W-relative bridge review (v507)

The bounded source review found no justified statement repair. `boundary_image` refers to the boundary of the two-dimensional chart, not ambient physical boundary. The whole-E retained-edge and true-boundary half-chart constructions remain proof obligations in the unchanged approved physical context. This is not a paper counterexample. Evidence: `scratch/f-reviewer/review_A6_E_whole_W_relative_bridge_v507/READY.json`, SHA256 `745759cbf2a920ba798d165ab465fd970bcf7d9198c0cf49596ce860de83cb79`.

## FI-29 — 分片曲面接缝弧的端点边界条件缺少反向关联（2026-10-10，v510）

分类：已确认的源文与形式化定义覆盖差异，不是论文错误，也不是桥接定理的反例。Definition A.1 的 LF1090 将接缝与曲面边界的交集指定为接缝弧端点；当前原生 `SeamGraph` 只要求弧在边界上的原像包含于 `{0,1}`，没有要求两个端点都落在边界上。V510 独立读回后的源文复核因此撤回“完整 A.1 类别已逐字实现”的联合接纳；较宽类别上的已编译面积等式本身不由此判假。

下一步为正文消费者的整包忠实表示/范围修订：保留现有较宽类别、原生定义、已付证明和全部保护，显式给出原文类别到现有接口的映射及完整消费者适用范围；若必须改动保护声明，先交完整审查。`image_area_atlas_exists` 保留有界批准；`image_area_piecewise_bridge` 的原文完整类别接纳暂缓。不得自动迁移为正文结果完成信用。读回关于 SectorChart target 开性的英文误述与未列明的辅助目录读取另行核实，均不记为论文缺陷。

证据：[最终源文复核](scratch/f-reviewer/review_section5_joint_consumers_v509/final_v510/REVIEW.md)、[精确问题记录](scratch/f-reviewer/review_section5_joint_consumers_v509/final_v510/SOURCE_ISSUES.json)。455 项输入校验匹配，原保护未修改；原先 generated14/sorry4 有界处置与 unrestricted literal FAIL 均保留。Owner：`formalize_body_piecewise_endpoint_scope_v511`。

## FI-27 — kernel-checked obstruction to a generic auxiliary refinement recipe

2026-10-09. Whole-U v507 supplies a checked Euclidean quadratic-shear overlap: two individually smooth regular rectangles intersect in a cusp. Its limiting tip prevents a finite closed full-rank regular-piece cover subordinate to that intersection, even when covering the entire interior. Evidence: scratch/f-generator/generate_original_U_whole_v500/v507/READY.json (SHA256 28fb29efb2bcbe2a40697424cc55d37d8e8d2e7778c7df89a3a7b01538fbde50), REPORT.md and the eight new anonymous kernel/base-axiom receipts.

Scope: this confirms failure of the generic exact old-cell-subordinate refinement route under its explicit tested conditions. It is not a counterexample to original U or a claim that the paper is false; bounded F-Reviewer v508 rejects only the unconditional selected-core/finite exact old-cell-subordinate full-rank refinement implication. The local example has explicit closed-image, unique-differentiation and rank conditions; no full original-U hypothesis instance or category counterexample is supplied. The manuscript and protected interfaces do not require simultaneous subordination to old witnesses. No protected U statement repair is required by this evidence; both obligations and all nontransverse/shared-boundary cases remain. Review: scratch/f-reviewer/review_U_finite_refinement_obstruction_whole_v508/REPORT.md (READY SHA256 8915e13a3e0372eb73059404dd47a06595fc243ab674aa7bc0de58894893eefa). The original two statements and guards remain unchanged. Next route must handle tangent seams using source-faithful witnesses; independent strict total-area exchange proof work continues.


### FI-29 v511：最小专门化路线已获批准

源文复核批准显式补足端点条件的包装，并确认已有较宽类别的原生面积等式可以直接用于该包装；数值面积调用不需要先证明新的闭接缝表示或三角剖分存在性。任意原生表示与原文完整竞争者／同伦类别的等价仍未证明，不能由数值公式推出。14 个脚手架头仍是待证义务，其中表示生产者是可选路线，不作为复用已有面积公式的前置条件。证据：[v511 审查](scratch/f-reviewer/review_body_piecewise_endpoint_scope_v511/REVIEW.md)。


## FI-30 — 两条辅助推理路线的编译反例（2026-10-10）

这是证明路线问题，不是原文反例。Section3 V508 的 Lean 诊断证明：初态和终态满秩，加终态横截性，不能推出直线竖直插值的全时满秩；中间时刻可以降秩。证据：[完整交接](scratch/f-generator/generate_original_section3_main_whole_v479/preparation_v508/HANDOFF_V508.md) 与其中 `VerticalOpeningRankRouteDiagnosticV508.lean`。正文原始 OpeningTrack 存在性仍未否定，需要实际全时嵌入和秩控制构造。

U V514 另证明其精确多项式拼接偏移在原点有绝对值折痕，不能直接作为光滑环境微分同胚族；它仍提供拓扑同胚，而局部分片光滑 taper 保留。证据：[V514 报告](scratch/f-generator/generate_original_U_whole_v500/v514/REPORT.md) 中 `exact_global_taper_offset_has_genuine_crease_at_origin`。这不否定原始 U 或 FHS 交换结论；待补实际分片竞争曲面及全局拼接。


### FI-29 v512：已有面积结果完成有界接纳

最终审查接纳原有 atlas 存在性与较宽原生类别的数值面积等式两个辅助结果，提交 `94831c23062a12c38ffe656becd7b3ea9a1e88d4`。无需重新证明这些公式或先完成可选表示生产者；完整原文竞争者／同伦类别等价仍是独立义务。证据：`scratch/regulator/audit_section5_atlas_area_final_v511/REPORT.md`。此项更新不增加原文编号成果完成数。


### FI-29 v515：网格／同痕生产者的范围处置

有界源文复核批准六个较宽原生网格／同痕辅助声明继续保持原保护并证明，不需因端点关联差异整体重建表示。原文调用仍须补一套与实际每阶段曲面映射绑定的 A.1 成员关系、精确关系和必要的相对边界传输；只加端点包装不足以证明完整竞争者／同痕类别等价。圆周细分边仍是辅助网格单元，不作为新的原文接缝弧。证据：`scratch/f-reviewer/review_section4_mesh_category_v515/REVIEW.md`。整包生产者已恢复，新原文调用声明由 `formalize_section4_source_callers_whole_v516` 负责；无原文完成信用。


## FI-31 — 第 3 节直线开口辅助目标超出了原文的存在性构造范围（2026-10-10）

F-Reviewer v511 已确认一处**形式化范围差异**：原文第 3 节先选择相对度量与经线叶状结构，后续只需从原始结/外部数据构造 `Nonempty (Section3Main.SourceGeometry E)`；原文没有要求对每个任意给定的 `CompatibleDiskBandPresentation C`、正 `delta`、支撑覆盖 `U` 和分解 `Q`，都产生逐点固定所有圆盘、按同一个直线物理公式移动带、并在全部闭附件端点保持终态横截的 `OpeningTrack`。这些是既有辅助证明路线额外施加的要求，不能标作原文必须满足的全称构造。

处理：保留已保护的全称辅助声明及旧证据，不重置 guard，也不认定它为假。另行形式化从原始输入**同时选择**表示和开口/圆滑化数据的完整构造，保留选定边界、两条 `LiteralSourceTrace`、图示同痕及实际同一家族的全部正则性/嵌入/边界方程；最终 `SourceGeometry` 和正文 A/C20 的输入与结论不变。新声明须经完整复审、独立字面回读和保护后再证明。若保留直线运动，物理侧别、有限多边形端点扇和全时刻碰撞控制仍是待证构造，不能变成新增的原文假设。

限制：V510 的 Lean 检查只证明一个光滑局部带相对于**无限半平面**的直线开口障碍；它没有实例化完整原生表示、有限圆盘、全局带输运和 U/Q。故不是原文反例，也没有证明所有原生输入无法推出所需侧别。该几何非蕴含问题仍为未决路线风险。

证据：`scratch/f-reviewer/review_section3_straight_sheet_scope_v511/REVIEW.md`（SHA256 `c043cb2e7644bf429b31379422253ad4f6b9cc86d85d7aad166be44f8000db9d`）及 `ROUTE.md`；源文实际换行第 258–298、308–321、397–398、1087–1096 行。修复候选由 `scratch/formalizer/formalize_section3_joint_geometry_whole_v512` 负责；本条不增加原文证明完成数。


### FI-31 后续核对：Section3 整包存在性声明保留批准（v516）

独立字面读回确认：最终 SourceGeometry 是独立存在的见证，图曲面与球面见证仅通过亏格相等关联；SelectedAmbientCorrection 未声称等于所给 corridor 历史。源文审查者在核对最终读回后保留 APPROVE：这两条额外历史同一性不是原文存在性结论的要求，不能将缺失它们标为原文错误，也不能在后续证明中借用它们。无需强加新的构造历史等式或重做整包声明。13 个新存在性声明保持原始输入和正文 A/C 的类型；当前优先证明 A 所需的几何存在性，证明仍未完成。证据：scratch/f-reviewer/review_section3_joint_geometry_whole_v515/READBACK_CORRELATION_FINAL_V516.md 与 READY_V516.json；scratch/statement-readback/readback_section3_joint_geometry_whole_v515/READY.json。
