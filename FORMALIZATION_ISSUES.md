# F-Reviewer smoothness audit

VERDICT: REJECT

Statement snapshot allowed: NO for the current source-facing declarations listed below. Existing approvals/guards for their old definition closure must not authorize proof or adoption. This report leaves all protected snapshots, prior sealed review artifacts and Lean sources unchanged.

Owner/scratch: /home/caoyichuan/test/seifert-surfaces/scratch/f-reviewer/review_smoothness. Audited at 2026-10-04T17:21:42.629961+00:00. Exact source: /home/caoyichuan/test/seifert-surfaces/references/seifert-surfaces.txt, Appendix B.1, lines 1376–1384 (printed pp. 28–29); excerpt in source_excerpt_B1.txt. This is a FORMALIZATION mismatch, not a source-paper error.

## Exact mismatch and required repair

Mathlib in the installed v4.35.0-rc3 baseline uses `ℕ∞ω = WithTop ℕ∞` for differentiability orders. Its actual notation definitions in FTaylorSeries.lean:115–119 give `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` for infinitely differentiable functions, and `ω = (⊤ : WithTop ℕ∞)` for analytic functions. Bare `⊤` in the order parameter is the latter outer top. ContDiff/Defs.lean:1066–1071 explicitly has an analytic-series branch at that index; :1195–1197 states contDiff_omega_iff_analyticOnNhd. This is actual definition inspection, not a guess from notation.

The source selects an odd χ in C∞, constant one near 1, whose primitive meets |t| to infinite order at the two seams. It does not require real analyticity. The current fields `Section5.Analysis.RoundingProfile.smooth` and `AppendixB.RoundingCutoff.smooth` require `ContDiff ℝ ⊤`. `AppendixB.roundingProfile_smooth` also explicitly concludes that stronger analytic predicate.

Required Formalizer repair: use the scoped C∞ order `∞` for these THREE occurrences (and add `open scoped ContDiff` in the respective modules so the intended inner-top notation resolves). Preserve all other cutoff/profile fields, seam conditions, formulas, domains and estimates. No weaker finite differentiability replacement, removal of seam matching, profile assumption, axiom, or proof-by-empty-input is an acceptable repair. Repair in a Formalizer-owned scratch, request F-Reviewer approval of the revised complete closure, then have the Orchestrator run guard approve-change before proof owners resume affected statements.

## Compiler evidence, without reviewer proof writing

I copied the generator's supplied StatementBlocker.lean BYTE-FOR-BYTE into my owned project and ran the three deterministic gates. Compilation PASS (0 errors, 0 warnings); scan PASS (0 placeholders); axiom audit PASS (only propext, Classical.choice, Quot.sound). The copied theorem `approved_profile_fields_impossible` uses only a real profile, `ContDiff ℝ ⊤`, and agreement with |t| for |t|≥1. Its kernel-checked conclusion is False. The supplied proof obtains agreement with identity near 2, applies Mathlib's analytic identity principle on the connected real line, and contradicts the required agreement at −2. It imports Mathlib only and no scaffold existence theorem or sorryAx.

Thus the current Section5 RoundingProfile existence target is obstructed by the compiler-verified diagnostic. This is not a proof effort on the source claim, and I authored no Lean proof or statement change. The same regularity-index mismatch rejects the AppendixB cutoff/primitive closure on fidelity grounds; this report does not claim to have authored a separate cutoff inconsistency theorem.

## Per-declaration rejection and definition closure

The current source-facing semantics of 34 explicit declarations depend on the wrong regularity bundle: 11 Section5 declarations and 23 AppendixB declarations. Their typed expressions/formulas remain useful after closure repair. Some implications over the current inputs can be vacuous; compiler success there would not verify the intended C∞ source support. The table rejects their CURRENT SOURCE-FACING APPROVAL, not the independent integral/arithmetic formulas in isolation.

| Exact declaration | Verdict | Mismatch |
| --- | --- | --- |
| `SeifertSurfaces.Section5.Analysis.RoundingProfile` | REJECT | Definition acid test FAIL: smooth field uses outer top of WithTop ℕ∞, i.e. analytic regularity, where B.1 requires C∞. |
| `SeifertSurfaces.Section5.Analysis.rounding_profile_exists` | REJECT | Existence conclusion requires the mismatched RoundingProfile. The unchanged generator diagnostic kernel-proves False from just its current analytic and seam-matching fields. |
| `SeifertSurfaces.Section5.Analysis.profileGain` | REJECT | Depends on the mismatched RoundingProfile definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.Section5.Analysis.angleGain` | REJECT | Depends on the mismatched RoundingProfile definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.Section5.Analysis.profile_gain_positive` | REJECT | Depends on the mismatched RoundingProfile definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.Section5.Analysis.profile_gain_continuous` | REJECT | Depends on the mismatched RoundingProfile definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.Section5.Analysis.profile_gain_monotone` | REJECT | Depends on the mismatched RoundingProfile definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.Section5.Analysis.angle_gain_positive` | REJECT | Depends on the mismatched RoundingProfile definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.Section5.Analysis.angle_gain_continuous` | REJECT | Depends on the mismatched RoundingProfile definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.Section5.Analysis.angle_gain_monotone` | REJECT | Depends on the mismatched RoundingProfile definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.Section5.Analysis.profile_gain_dominates_twice_angle_gain` | REJECT | Depends on the mismatched RoundingProfile definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.RoundingCutoff` | REJECT | Definition acid test FAIL: smooth field uses outer top of WithTop ℕ∞, i.e. analytic regularity, where B.1 requires C∞. |
| `SeifertSurfaces.AppendixB.roundingProfile` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.roundingProfile_hasDerivAt` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.roundingProfile_smooth` | REJECT | Both input cutoff closure and explicit ContDiff ℝ ⊤ output demand analytic regularity instead of the source C∞ primitive. |
| `SeifertSurfaces.AppendixB.roundingProfile_even` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.roundingProfile_majorizes_abs` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.roundingProfile_bounds` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.roundingProfile_matches_abs_near_seams` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.roundingCutoff_abs_le_one` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.profileGain` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.profileGain_pos` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.profileGain_continuous` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.profileGain_monotoneOn` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.profileGain_zero` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.angleGain` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.angleGain_properties` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.angleGain_is_half_minimum` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.normalized_profileGain_limits` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.longitudinalDerivative` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.varyingWidth_profile_derivative` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.longitudinalDerivative_sq_le` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.newSliceArea` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |
| `SeifertSurfaces.AppendixB.euclidean_slice_gain` | REJECT | Depends on the mismatched RoundingCutoff definition. Current source-facing scope is REJECT until that complete closure is repaired; retain the independent formulas/conclusions for re-review. |

Complete current source bodies/fields are copied in source_snapshots/. source_manifest.json pins them and the actual Mathlib notation/regularity definitions with full SHA-256. affected_declarations.json supplies exact file, fully qualified declaration, line, hash, scope, mismatch and repair route. The closure retains every field of RoundingProfile/RoundingCutoff, the constructed integral definitions and the associated real derivative/integral support; replacing only theorem header guards without rechecking those fields would be insufficient.

## Workspace-wide notation audit and unaffected salvage

workspace_notation_audit.json records every regularity/top/infinity line and full hash of all 55 active formalizer Lean source files scanned, excluding dependency .lake directories. The only outer-top regularity occurrences are the THREE rejected uses above. The other top occurrence, AppendixASupport.T⊔B=⊤, is lattice top for a submodule-spanning equation, unrelated to differentiability. No blanket replacement of ⊤ is authorized.

Section4EmbeddingCore correctly uses `∞` in both manifold assumptions and IsSmoothEmbedding; its earlier sealed review remains unchanged and unaffected. Appendix A contains no outer-top smoothness index. Appendix C and seifert_foundations use `∞` for intended C∞ manifold/embedding/diffeomorphism/metric regularity and numeric 1 or 2 for finite regularity. These retain their existing review scopes; this notation audit is not a new full fidelity approval of the geometric declarations.

The following declarations in the two mixed modules do not reference the rejected rounding types in their statement/definition closures and may continue under their existing approvals and guards. This is independence from this defect, not automatic proof acceptance:

**/home/caoyichuan/test/seifert-surfaces/scratch/formalizer/section5/Section5Analysis.lean**

`SeifertSurfaces.Section5.Analysis.twoSidedAngle`, `SeifertSurfaces.Section5.Analysis.two_sided_angle_bounds`, `SeifertSurfaces.Section5.Analysis.complementary_sectors_have_same_angle`, `SeifertSurfaces.Section5.Analysis.wedge_slope_bounds`, `SeifertSurfaces.Section5.Analysis.profile_longitudinal_derivative_bound`, `SeifertSurfaces.Section5.Analysis.roundingDensity`, `SeifertSurfaces.Section5.Analysis.roundingWidthCeiling`, `SeifertSurfaces.Section5.Analysis.roundingDerivativeCeiling`, `SeifertSurfaces.Section5.Analysis.rounding_ceilings_positive`, `SeifertSurfaces.Section5.Analysis.admissible_rounding_bounds_control_errors`, `SeifertSurfaces.Section5.Analysis.rounding_density_lower_bound`, `SeifertSurfaces.Section5.Analysis.restricted_rounding_integral_lower_bound`, `SeifertSurfaces.Section5.Analysis.integrated_rounding_density_bound`, `SeifertSurfaces.Section5.Analysis.exists_small_push_off_parameter`, `SeifertSurfaces.Section5.Analysis.choose_push_off_preserving_gain`, `SeifertSurfaces.Section5.Analysis.exists_common_push_off_parameter`, `SeifertSurfaces.Section5.Analysis.finite_order_gradient_bound_excludes_punctured_critical_points`, `SeifertSurfaces.Section5.Analysis.compact_closed_isolated_subset_finite`

**/home/caoyichuan/test/seifert-surfaces/scratch/formalizer/appendixB/project/AppendixBAnalysis.lean**

`SeifertSurfaces.AppendixB.frontier_agreement_prevents_open_inclusion`, `SeifertSurfaces.AppendixB.slope_mem_interval`, `SeifertSurfaces.AppendixB.sqrt_add_upper_bound`, `SeifertSurfaces.AppendixB.oldSliceArea`, `SeifertSurfaces.AppendixB.oldSliceArea_remainder`, `SeifertSurfaces.AppendixB.slice_gain_from_error_caps`, `SeifertSurfaces.AppendixB.width_derivative_error_cap`, `SeifertSurfaces.AppendixB.uniform_slice_caps`, `SeifertSurfaces.AppendixB.gain_on_measurable_subset`, `SeifertSurfaces.AppendixB.exp_sub_one_le_mul_exp`, `SeifertSurfaces.AppendixB.uniform_exponential_pushOff_bound`, `SeifertSurfaces.AppendixB.uniform_jacobian_from_log_derivative`, `SeifertSurfaces.AppendixB.small_radius_coercivity`, `SeifertSurfaces.AppendixB.finite_order_lower_bound`, `SeifertSurfaces.AppendixB.product_gradient_lower_bound`, `SeifertSurfaces.AppendixB.RadialC2Family`, `SeifertSurfaces.AppendixB.radial_derivative_deviation`, `SeifertSurfaces.AppendixB.uniform_radial_sign_on_neighborhood`, `SeifertSurfaces.AppendixB.finite_zeros_not_identically_zero`, `SeifertSurfaces.AppendixB.positive_sign_excludes_opposite_level`, `SeifertSurfaces.AppendixB.collapsed_length_bound`, `SeifertSurfaces.AppendixB.uniform_angle_near_compact`, `SeifertSurfaces.AppendixB.uniform_positive_on_compact`, `SeifertSurfaces.AppendixB.uniform_positive_lowerSemicontinuous_on_compact`, `SeifertSurfaces.AppendixB.distanceRamp`, `SeifertSurfaces.AppendixB.collarDistanceRamp`, `SeifertSurfaces.AppendixB.widthRamp`, `SeifertSurfaces.AppendixB.distanceRamp_lipschitz`, `SeifertSurfaces.AppendixB.collarDistanceRamp_lipschitz`, `SeifertSurfaces.AppendixB.widthRamp_lipschitz`, `SeifertSurfaces.AppendixB.widthRamp_values`, `SeifertSurfaces.AppendixB.fixed_width_and_gain_positive`, `SeifertSurfaces.AppendixB.small_error_excludes_disc_gain`, `SeifertSurfaces.AppendixB.final_area_gap`

## Checklist and next owner

For the rejected bundles/consumers: Definition Acid Test FAIL; Object Fidelity FAIL (analytic rather than C∞ cutoff/profile); Typeclass/order-parameter Fidelity FAIL; Generality FAIL (source smooth data restricted to a stronger class); Anti-Laziness FAIL if the empty input is used to claim source support. Directionality, explicit numerical constants, finite families and declaration kinds otherwise remain as previously reviewed; no axiom/opaque boundary is introduced here. The supplied diagnostic's compile/sorry/axiom gates pass, but compilation of a scaffold with sorry would not cure the semantic mismatch.

Next owner: Formalizer for the three regularity repairs and any typed downstream adapters. F-Reviewer re-reviews exact repaired bytes; Orchestrator refreshes affected guards and notifies affected proof owners. Unaffected support proofs can proceed under their existing task scopes. No user permission is needed for this explicit fidelity repair route. A memory candidate is stored under this assigned scratch for Orchestrator aggregation.

## Full source/definition hashes

- /home/caoyichuan/test/seifert-surfaces/references/seifert-surfaces.txt: `3558fb893638e96f989508467386127869f8e8734cf1874795a6c2f1537d4009`
- /home/caoyichuan/test/seifert-surfaces/scratch/f-generator/gen_s5_analysis/project/StatementBlocker.lean: `3e293d30f5183b96978cf6de96b54edd8721a9ad3a17f53859e21251a0a0de67`
- /home/caoyichuan/test/seifert-surfaces/scratch/formalizer/section5/Section5Analysis.lean: `0c251f51ea4d1401631b33e7efd0f3fbef7a332a2fa6cb65131968fea97c33ed`
- /home/caoyichuan/test/seifert-surfaces/scratch/formalizer/appendixB/project/AppendixBAnalysis.lean: `ad710766098e231907c24ff35e28f9689373684a0a6e956c24af4eddaae1ff51`
- /home/caoyichuan/test/curve-complex-formalization/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean: `7e71ea678a68945db40db3ec3fed8db6ef4c1a3815b916911d55dfaa61822ea2`
- /home/caoyichuan/test/curve-complex-formalization/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean: `c3af8893907c6b9abf4976de60d1d6f92e2bff05be41d7a95a93c398347d1a4d`
- /home/caoyichuan/test/curve-complex-formalization/.lake/packages/mathlib/Mathlib/Analysis/Analytic/Uniqueness.lean: `58009b2989e1f31a7fd9582698bb2e6a5f1dada2f10beb7f5d2cc3453ff66c8c`
- /home/caoyichuan/test/curve-complex-formalization/.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Defs.lean: `4de1c020b537855e1230b51dd679cf6dd4a309fbd8ef38391cb7d7defe7fc886`


## Wave 4 repair and scope receipts

These are formalization findings, not newly asserted paper errors.

- The earlier C-infinity/analytic index defect was repaired and independently approved. Exact repaired Section5Analysis and AppendixBAnalysis proofs are now integrated; old rejected source/seal history remains intact.
- Generic ambient incompressibility/disk equivalences omitted the source exterior/two-sidedness context. The Seifert foundation repair is approved with complete readback; the genus/compression repair uses actual SmoothExterior and LinkSpanningSurface and is approved in scratch/f-reviewer/review_compression_repair/REVIEW.md. Its new head still needs independent readback. Original rejected 133-declaration receipt remains preserved.
- Metric/minimizer representation had 23 rejected contracts: reflex sectors, compatible geometric isotopy maps and unrestricted Fin scope. scratch/formalizer/repair_metric_minimizer/report.md records repaired contracts and three complete-type rendering repairs. Fresh review_metric_repair is active; no old approval authorizes these new definitions.
- Exact full compiler types supplement lexical guards where letI or named arguments truncate extraction. Whitehead master admission stores all 213 exact kernel types in .claude/state/whitehead_bridge_dag_admission.json. Historical tie DAG text remains immutable and has an explicitly linked fulltype sibling.
- A star reader was exposed to editorial intent and refused. The original refusal is preserved; a fresh sanitized code-only packet, independent reader and review_star_readback/adoption_clearance.json discharge the issue. Naming/strength warnings were approved only at the literal support scope.
- Wave 3 Regulator found same-line attributed declarations omitted by lexical indexing; ten affected reused theorems received direct clean kernel axiom audits. A minimal tooling repair is assigned separately. Counts use the audited full declaration inventory.

References are immutable specialist artifacts under scratch; these status notes do not replace their semantic findings or compiler gates.


### R1b retained after the first metric repair

Fresh review_metric_repair rejected full source adoption: 21 source-facing contracts still depend on a C1 injective sector-to-fixed-halfspace parametrization that excludes reflex source-boundary corners. Standalone (0, 2π) sector sets did not resolve that operative category interaction. This is a source-representation finding, not a kernel-certified counterexample to the paper. The Formalizer now owns repair_metric_sector_reference. All 54 explicitly independent contracts are approved only at their recorded support scopes; exact metric, area, topology and minimizer producers remain proof obligations. See scratch/f-reviewer/review_metric_repair/report.md and PROOF_PACKAGES.json.

### Literal derivative and naming warnings

The collar helper local_min_second_deriv_nonneg states a nonnegative totalized second derivative and does not assert derivative existence. review_collar_helpers/readback_adjudication.json approves this exact numerical scope; its actual consumer supplies C2. No stronger regularity theorem is inferred from the helper name. All 26 helpers are reviewed, with the 18 source support heads and 32 operative declarations preserved.

### Wave 6: selected-core history missing from universal R8

Bounded source review rejects the current helper interface, not the manuscript: Q.connector_avoids does not transfer to an arbitrary supplied C.planarConnector, although R8 retains that exact C by HEq while requiring full endpoint collar separation. All99 Q/C/N/F fields were audited. No Lean counterexample was supplied and no theorem-false claim is made. The public exact-A producer and full endpoint widths remain protected. Formalizer owns an explicit upstream selected-core construction certificate and affected downstream witness repair; its producer remains proof debt from original inputs, never a new public hypothesis. Independent clean15 is preserved.

Evidence: scratch/f-reviewer/review_resolution_R8_context/SEAL.json, SHA da62214f8f1bcb58fd666c4c82466fdd4e833ffe07e4b3401b738b60cdfb3ab3; root50payload replay logs/wave6_root/R8_source_review_replay.json PASS. Repair dispatch .claude/state/dispatch/resolution31_after_R8_review.md.

## Fixed history T4: same-germ compact shrinking

F-Reviewer rejected T4 only after inspecting arbitrary retained germ maps: their current data do not carry local inverse/radial-end control needed for strict compact truncations of those same maps. This is a formalization boundary, not a proved counterexample to the full target or a manuscript-error claim. The other29 approvals remain unchanged. Exact final reviewer seal: scratch/f-reviewer/review_fixed_terminal_T4_scope/FINAL_SEAL.json, SHA22004ff7d91a69c414b6585447b048bf0eaadc4477cf6b8a9b9c7364784921c8; root56payload integrity PASS. Root suspended fixedhistory30_e0cb3f44e8b750da and routed repair_fixed_terminal_germs to Formalizer. Preferred minimal repair adds a helper-only actual-germ control certificate constructed jointly by T3, retaining the original public records/inputs and same maps; changed Prepared/T3/T4/X1/X2 closure requires fresh source/readback/guard review. Original snapshots and failed diagnostic remain immutable. Existing construction-history negative constraints cover the lesson; no duplicate long-term card needed.

## Resolution H3: explicitly shorten the supplied escape germs

F-Reviewer rejected the fresh universal H3 intake after auditing all inherited fields: arbitrary supplied full escape germs have no mutual-separation condition, but its connector embedding fixes both full clock intervals. This is a source-fidelity rejection, not a kernel-proved counterexample or manuscript error. Exact rejection packet scratch/f-reviewer/review_resolution_constructive31/H3_REPAIR_SEAL.json SHAbb9594d132c002883a48acce222837d0a380334df2f8f1fb8a4fcfc277a8843e was root4payload-replayed. Root dispatched formalize_resolution_H3_shortening: add a new producer returning same-direction shorter positive germs Gprime and an actual connector B on those same germs. All33 prior heads/20records/public producers remain unchanged, oldH3 stays rejected. ConditionalH4/H5 remain eligible after final scope/reader release; actual construction descendants await the new producer. Existing retained-construction compatibility constraints cover the lesson.

## Metric C4: boundary-target normal form

F-Reviewer rejects C4 only: its full corner-target IsSmoothEmbedding requires an unsupported compatible-chart normal form. No Lean contradiction or manuscript error is claimed. Seal scratch/f-reviewer/review_metric_prism_C4_scope/FINAL_SEAL.json SHAa4707f40847d668e3350e1639ebbacbd5c683b2b9af6b7d607517ab2f532ac50, root68payload PASS. Exact task metricgeometry47_3d8fc83d867e5828 is held. Formalizer owns minimal whole-closed-domain embedding/smoothness/everywhere-rank bundle with full smooth embedding after the fixed boundary-forgetting ambient readout. Literal maps, C3 derivative, atlas compatibility and arbitrary-D recognition stay required.39 future changed roots need fresh source/readback/guards; other21 current source scopes and clean17 remain tied to old exact contexts. Diameter full embedding is unchanged.

## Fixed N4: compatible fan must be selected upstream

F-Reviewer rejects IF1/N4 arbitrary supplied-fan source scope only; exact inherited fixed-seam implication remains unresolved, not refuted. IF2 joint-selected whole-chart centres/prisms and IF3 same-history nine-field certificate scopes are approved but their producers remain unpaid. Seal scratch/f-reviewer/review_fixed_history_interfaces3/SEAL.json SHAb39f44ae4df1659851468ff37fac379654546e4008160c2952cac4d3de498850, root82payload PASS. Exact task fixedhistory30_7b82f54ec5f57d21 is held; formalize_fixed_selected_fan produces an actual upstream selected-compatible fan from unchanged original inputs and repairs internalN4/R0 call binding. Existing records should stay unchanged; no postulated EdgeCollarNormalForms or final cylinder hypothesis. Independent T4/Prepared repair has separate ownership. Full new operative closure/source/reader approval is required before any guard revision. Existing actual-construction memory constraints cover this lesson.

## Wave6 repair clearance update, 2026-10-05 22:42 UTC

These entries preserve the preceding rejections as historical findings; they do not assert manuscript errors. T4 exact repaired actual-germ/Prepared context has fresh full source and literal approval, including the formerly missing changed recursor: reviewer addendum seal93d3eac0c44fee51163b23fc2bde500570acab55f1f6c4df94aec001c418c867, Root53payloadPASS. Six source guards/15complete contracts registered in T4_repaired_obligations.json, eight new contracts, two changed generated contracts and five renewed existing contexts; all old snapshots retained. T3/T4 and X1/X2 proof owners are active; source approval itself proves no body.

Metric C4 repaired four-map whole-domain regularity/ambient-embedding scope has fresh82-root literal and source approval: sealcced50568edc04e61c40a4638e44b73654bddbb51b71035fcea986a037c9997b, Root257PASS. Root registered42source/82full/4863recursive contracts plus3893typed proof slots; C4/D1/DiagnosticGeometry revision history explicitly recorded, old78pins preserved. Old21 proofs remain tied to old contexts until current independent revalidation; C4proof has a separate Astra owner.

Selected-fan new4source roots received conditional source APPROVE (checkpoint8ce23c7aab0db4fe7f5174cfecbc65a9e388b1aeaae74ca01c703d8dd342b23c). A first reader exposed unrelated memory and refused; no draft accepted. Full23root/4568recursive sanitized code export e320433f5d82574f78a8e772b612764cc8276712a7c3a71f8acf95636278e745 is now under a fresh independent reader. Oldarbitrary-fan N4 rejection remains; no newproofpermission yet.


## Wave6: same-family seam D04/D05/D09 source-scope repair

Reviewer final seal 1c869d849a58a4abf643a0c00a2d091e41b1471301767c7964a20eac131b98de (Root614 payload replay PASS) rejects three proposed auxiliary interfaces. D04 omitted the source-permitted one-sided temporal correction while requiring unchanged two-sided regular collars. D05 lost inherited endpoint smoothness/rank needed for the exact endpoint join. D09 encoded only those restricted operations. Six dependent helper contexts are held pending repair; eight independent helpers retain source and fresh literal approval and Root guards. The original Y2 inputs and103 inherited fields remain protected. This is a formalization-source mismatch, not an established error in the manuscript or a compiler-proved counterexample.

Exact finding: scratch/f-reviewer/review_diagram_same_family_seams17/D04_D05_D09_SOURCE_FINDING.md. Repair owner: scratch/formalizer/repair_diagram_same_family_seams9.


## Section3 V511: jointly chosen geometry versus universal straight opening

F-Reviewer rejects identifying the arbitrary-C/U/Q straight, disk-fixed OpeningTrack helper as required by the original source. The paper and original caller require an existential choice of geometry. This is a confirmed source-scope excess in the auxiliary route; the universal helper's truth is unresolved, V510 has no native finite-disk counterexample, and no manuscript falsity is asserted. Existing protected statements and original mainA/C20 remain unchanged.

The existing whole Formalizer task must return a joint original-input construction choosing the presentation/opening/rounding witnesses, preserving both literal traces, diagram-isotopy identity, all-stage embeddings, boundary clocks and final SourceGeometry. Its new construction certificate is an unpaid output, never an extra original premise. Any changed route needs bundled review/readback and a narrowly approved guard transition; this rejection authorizes no current transition.

Evidence: `scratch/f-reviewer/review_section3_straight_sheet_scope_v511/REVIEW.md` and `ROUTE.md`; READY SHA256 `ff0aa7d1faa76cd0c9d5d903bf05a3a0b8433b0cd15adb32fdb95963d6ab73d2`. Root checked all five pinned artifacts in `logs/wave6_root/checkpoint_v514/RECEIPT_PIN_CHECK.json`. Existing construction-history negative constraints cover this issue; no duplicate memory card needed.


### FI-31 后续核对：Section3 整包存在性声明保留批准（v516）

独立字面读回确认：最终 SourceGeometry 是独立存在的见证，图曲面与球面见证仅通过亏格相等关联；SelectedAmbientCorrection 未声称等于所给 corridor 历史。源文审查者在核对最终读回后保留 APPROVE：这两条额外历史同一性不是原文存在性结论的要求，不能将缺失它们标为原文错误，也不能在后续证明中借用它们。无需强加新的构造历史等式或重做整包声明。13 个新存在性声明保持原始输入和正文 A/C 的类型；当前优先证明 A 所需的几何存在性，证明仍未完成。证据：scratch/f-reviewer/review_section3_joint_geometry_whole_v515/READBACK_CORRELATION_FINAL_V516.md 与 READY_V516.json；scratch/statement-readback/readback_section3_joint_geometry_whole_v515/READY.json。
