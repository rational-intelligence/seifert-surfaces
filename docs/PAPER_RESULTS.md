# Paper results: partial formalization

**20 of 46 original assertions are verified; 26 remain open.** Theorem B is
complete. Theorems A, C and D remain open. All 20 historically accepted originals
also compile from source together through the single `MainTheorems` entry:
**B, 2.2, 2.4, 5.5, 5.7, 6.1, 6.2, A.2, A.3, A.4, A.5, A.7, B.1, B.2, B.3,
C.6, C.7, C.8, C.9 and C.11**. This is an assertion count, not an effort percentage.

[VERIFIED_RESULTS.json](VERIFIED_RESULTS.json) preserves the exact all-46
inventory, original declarations, source qualifications and historical review
provenance. [VERIFIED_RESULTS.md](VERIFIED_RESULTS.md) gives a compact accepted
head index. [VERIFICATION.json](VERIFICATION.json) records the receiving source
gates. [HISTORICAL_ACCEPTANCE.json](HISTORICAL_ACCEPTANCE.json) preserves compact
native acceptance summaries: its old workspace paths are archival locators,
not runtime inputs. Historical acceptance and current source verification apply
to their respective exact states; neither certifies the entire archive.

| Source | Conclusion and exact declaration | Release source | Verification |
| --- | --- | --- | --- |
| Theorem A | Non-trivial knot K in S3: the weak realization of IS(K) is contractible.<br>No accepted complete original endpoint. | — | Open |
| Theorem C | For integers ell >= g(K), genus truncation IS_ell is isometric in IS(K) and contractible; printed area clause uses g<=ell AND A<=a0 for every a0>0.<br>No accepted complete original endpoint. | — | Open |
| Theorem D | Non-split linking-indecomposable link, excluding the unknot: IS(L) is contractible.<br>No accepted complete original endpoint. | — | Open |
| Theorem B | Every exchange complex is contractible; realization carries the weak CW topology.<br>`SeifertSurfaces.exchange_complex_contractible` | [TheoremB.lean](../seifert-surfaces/unified/Section2/TheoremB.lean) | Fresh common source + historical acceptance |
| Lemma 2.2 | An exchange structure can be refined to an injective complexity that well-orders the vertices; no vertex finiteness assumed.<br>`SeifertSurfaces.exists_injective_exchange_complexity` | [TieBreaking.lean](../seifert-surfaces/unified/Section2/TieBreaking.lean) | Fresh common source + historical acceptance |
| Corollary 2.3 | Every downward vertex subset is isometric and connected; any p,q have a geodesic bounded by max of endpoint complexities. Empty-D connectivity convention must be specified.<br>No accepted complete original endpoint. | — | Open |
| Lemma 2.4 | Nonempty downward full subcomplexes and nonempty descending links inherit exchange structure; descending links are nonempty for nonleast vertices.<br>`SeifertSurfaces.nonempty_full_downset_exchange_complex`<br>`SeifertSurfaces.nonempty_full_descending_link_exchange_complex`<br>`SeifertSurfaces.nonempty_strict_sublevel_exchange_graph`<br>`SeifertSurfaces.descending_link_nonempty_of_not_least`<br>`SeifertSurfaces.full_subcomplex_is_flag` | [FlagExchangeComplex.lean](../seifert-surfaces/unified/Section2/FlagExchangeComplex.lean)<br>[FlagComplex.lean](../seifert-surfaces/unified/Section2/FlagComplex.lean)<br>[Heredity.lean](../seifert-surfaces/unified/Section2/Heredity.lean) | Fresh common source + historical acceptance |
| Theorem 3.1 | U(i): minimizers from disjoint-representable classes are disjoint or coincide; U(ii): finite pairwise nonisotopic disjoint input classes have disjoint minimizing images.<br>No accepted complete original endpoint. | — | Open |
| Theorem 3.2 | E(i): fixed-boundary piecewise-smooth isotopy-class infimum attained within that class; E(ii): sliding-boundary infimum attained by stable minimal smooth proper embedded surface.<br>No accepted complete original endpoint. | — | Open |
| Theorem 3.3 | Fin: area-bounded stable-minimal embedding space of a fixed compact connected surface is C1-compact and a disjoint union of finitely many clopen mutually-isotopic subsets.<br>No accepted complete original endpoint. | — | Open |
| Lemma 4.2 | Incompressible neatly embedded link spanning surface with longitudinal boundary is boundary-incompressible.<br>No accepted complete original endpoint. | — | Open |
| Lemma 4.3 | Minimizers chosen independently in distinct adjacent classes are disjoint; IS and genus truncations are flag; common neighbor minimizer is disjoint from both endpoint minimizers.<br>No accepted complete original endpoint. | — | Open |
| Lemma 4.4 | Oriented normal exchange preserves total Euler characteristic; compression retaining knot boundary strictly lowers genus and terminates in an incompressible Seifert surface.<br>No accepted complete original endpoint. | — | Open |
| Lemma 4.5 | In irreducible orientable M, compress connected neat P with nonempty boundary away from disjoint incompressible Q while preserving the prescribed intermediate/final isotopy classes.<br>No accepted complete original endpoint. | — | Open |
| Corollary 4.6 | In the knot complex, every incompressible compression descendant of P disjoint from Q has class equal or adjacent to [Q].<br>No accepted complete original endpoint. | — | Open |
| Lemma 4.8 | Fixed-genus bounded-area vertex sets are finite; each area fiber set is closed/discrete with order type <= omega; W well-ordered of type <= omega^2; vertices countable.<br>No accepted complete original endpoint. | — | Open |
| Lemma 4.9 | Connected Seifert inputs S,S+,S- with S disjoint from both, transverse meeting endpoints with disjoint boundaries and no disc patch give two outputs with disjointness, universal fixed-class neighbor robustness, Euler accounting and discarded closed components of chi<=0.<br>No accepted complete original endpoint. | — | Open |
| Theorem 5.1 | For x adjacent to u,w at distance two, exist two output vertices BEFORE every z; output adjacency to x,u,w, robustness for all common closed-neighborhood vertices z, genus sum <= input sum, and strict area-sum decrease at genus equality.<br>No accepted complete original endpoint. | — | Open |
| Proposition 5.2 | Two-intervals in IS(K) have apices; some apex strictly lowers maximum endpoint complexity; genus-bounded endpoints have a genus-bounded apex; IS(K) is an exchange complex.<br>No accepted complete original endpoint. | — | Open |
| Lemma 5.4 | Pointwise corner rounding: positive geometric widths/derivative bounds, supported smoothing with same boundary, CLOSED-side containment and collar, ambient isotopy, nonnegative slicewise integral area gain, preservation of complementary regions. All five clauses retained.<br>No accepted complete original endpoint. | — | Open |
| Lemma 5.5 | After rounding, sufficiently small positive push-off into open U keeps foliation-leaf boundary and isotopy class, with area increase <= C sigma.<br>`SeifertSurfaces.OriginalEndpoints.original_5_5` | [OriginalSection5Whole.lean](../seifert-surfaces/unified/OriginalSection5Whole.lean) | Fresh common source + historical acceptance |
| Lemma 5.6 | If near-minimal transverse isotopic perturbation A of minimizer A0 and minimizer B have a disc patch, two closed intersection curves, possibly equal, have combined rounding gain <= area error e.<br>No accepted complete original endpoint. | — | Open |
| Proposition 5.7 | Tangencies of distinct distance-two minimizers: isolated interior finite-order sign-changing critical points with gradient estimate; common-boundary collar has no interior critical points and finitely many boundary critical points; finite tangency set in both configurations.<br>`SeifertSurfaces.OriginalEndpoints.original_5_7` | [OriginalSection5Whole.lean](../seifert-surfaces/unified/OriginalSection5Whole.lean) | Fresh common source + historical acceptance |
| Lemma 6.1 | Linking-indecomposable link: every intended spanning surface has no closed component, is connected and has exactly n boundary curves; frontier outputs inherit it.<br>`SeifertSurfaces.OriginalEndpoints.original_6_1` | [OriginalSection61.lean](../seifert-surfaces/unified/OriginalSection61.lean) | Fresh common source + historical acceptance |
| Lemma 6.2 | Essential separating compression leaves exactly one boundary-bearing component, carrying all n curves and lower genus; nonseparating compression also lowers genus; iteration terminates.<br>`SeifertSurfaces.OriginalEndpoints.original_6_2` | [Original62CompletionV510.lean](../seifert-surfaces/unified/Original62CompletionV510.lean) | Fresh common source + historical acceptance |
| Lemma A.2 | Attained fixed-boundary minimizer is stationary under all compactly interior-supported smooth vector fields; pieces are minimal and adjacent sheets have opposite conormals.<br>`SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.A2_original` | [OriginalA2ScaffoldV464.lean](../seifert-surfaces/unified/OriginalA2ScaffoldV464.lean) | Fresh common source + historical acceptance |
| Lemma A.3 | Two otherwise disjoint smooth minimal sheets sharing boundary arc and opposite conormals glue to a smooth minimal surface near each interior arc point.<br>`SeifertSurfaces.OriginalEndpoints.A3_original` | [OriginalA3Final.lean](../seifert-surfaces/unified/OriginalA3Final.lean) | Fresh common source + historical acceptance |
| Lemma A.4 | Minimal C1 graph in convex collar with positive interior distance and interior-sphere-condition projection domain has tangent plane different from ambient boundary tangent plane.<br>`SeifertSurfaces.OriginalEndpoints.A4_original` | [OriginalA4.lean](../seifert-surfaces/unified/OriginalA4.lean) | Fresh common source + historical acceptance |
| Proposition A.5 | Given an attained minimizer within the Definition-A.1 class, it is globally smooth embedded minimal, stable, smooth up to boundary with exact boundary intersection.<br>`SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.A5_original` | [OriginalA5ScaffoldV464.lean](../seifert-surfaces/unified/OriginalA5ScaffoldV464.lean) | Fresh common source + historical acceptance |
| Theorem A.6 | Piecewise-smooth incompressible isotopy class with sliding longitudinal boundary attains its area infimum at smooth proper stable minimal embedding with exact boundary intersection.<br>No accepted complete original endpoint. | — | Open |
| Lemma A.7 | Every minimizer as in A.6 is transverse to ambient boundary and hence neat.<br>`SeifertSurfaces.OriginalEndpoints.A7.A7_original` | [OriginalA7ScaffoldV463.lean](../seifert-surfaces/unified/OriginalA7ScaffoldV463.lean) | Fresh common source + historical acceptance |
| Lemma B.1 | Common-boundary graph difference has nonzero boundary normal derivative somewhere; choose sign, closed boundary arc and positive a0,r1 with signed f>=a0*r/2>0 there.<br>`SeifertSurfaces.OriginalEndpoints.B1_original` | [OriginalB1_v468.lean](../seifert-surfaces/unified/OriginalB1_v468.lean) | Fresh common source + historical acceptance |
| Lemma B.2 | For all sufficiently small perturbations in T2, every closed intersection component has a uniform positive diameter.<br>`SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480.B2_original_push_off` | [OriginalB2B5V480.lean](../seifert-surfaces/unified/OriginalB2B5V480.lean) | Fresh common source + historical acceptance |
| Lemma B.3 | T2 perturbation intersections avoid fixed boundary strip, collar loops are not null-homotopic, and every closed component has a uniform positive length away from boundary and tangency neighborhoods.<br>`SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480.B3_original_interior`<br>`SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480.B3_original_collar` | [OriginalB2B5V480.lean](../seifert-surfaces/unified/OriginalB2B5V480.lean)<br>[OriginalB2B5V480.lean](../seifert-surfaces/unified/OriginalB2B5V480.lean) | Fresh common source + historical acceptance |
| Corollary B.4 | T2 bounds independent of perturbation parameter: uniform length outside tangency balls, two-sided angle lower bound on specified region away from boundary, and positive geometric rounding-width/derivative bounds.<br>No accepted complete original endpoint. | — | Open |
| Lemma B.5 | T1 perturbations have uniform positive diameter and exterior length, two-sided angle bounds, and geometric rounding bounds outside nested tangency neighborhoods.<br>No accepted complete original endpoint. | — | Open |
| Lemma C.1 | Boundaryless outward extension is complete/homogeneously regular; M inclusion is homotopy equivalence and pi2 vanishes; Hess r nonpositive with exact radial equality; retraction is 1-Lipschitz, non-area-increasing, relative-homotopy-preserving.<br>No accepted complete original endpoint. | — | Open |
| Proposition C.3 | Cited existence of a full Lemaire minimizer in the inclusion relative homotopy class with area <= every piecewise-smooth properly isotopic fixed-boundary competitor.<br>No accepted complete original endpoint. | — | Open |
| Lemma C.6 | Given full Lemaire minimizer, Laplacian of collar coordinate equals Hessian trace <=0 with radial equality case; C2,alpha and smooth uniformly elliptic operator.<br>`SeifertSurfaces.AppendixC.OriginalEndpoints.original_C6` | [OriginalC6C11.lean](../seifert-surfaces/unified/OriginalC6C11.lean) | Fresh common source + historical acceptance |
| Lemma C.7 | Smooth conformal class field on smooth surface has global smooth representing metric; restriction to a compact smooth subsurface gives boundary-smooth representative.<br>`SeifertSurfaces.AppendixC.Original.paper_C7` | [OriginalC7.lean](../seifert-surfaces/unified/OriginalC7.lean) | Fresh common source + historical acceptance |
| Lemma C.8 | Anti-holomorphic involution at a fixed point has invariant holomorphic chart in which it is conjugation; fixed set is locally real-analytic separating arc.<br>`SeifertSurfaces.AppendixC.Original.paper_C8` | [OriginalC8.lean](../seifert-surfaces/unified/OriginalC8.lean) | Fresh common source + historical acceptance |
| Proposition C.9 | Either subsurface-preserving diffeomorphism compatibility L2-prime or suitable doubled anti-conformal-involution compatibility L2-double-prime yields boundary-smooth representative; latter gives analytic boundary.<br>`SeifertSurfaces.AppendixC.Original.paper_C9` | [OriginalC9Final3.lean](../seifert-surfaces/unified/OriginalC9Final3.lean) | Fresh common source + historical acceptance |
| Proposition C.11 | Every full Lemaire minimizer stays in M by the barrier argument.<br>`SeifertSurfaces.AppendixC.OriginalEndpoints.original_C11` | [OriginalC6C11.lean](../seifert-surfaces/unified/OriginalC6C11.lean) | Fresh common source + historical acceptance |
| Proposition C.12 | Full Lemaire minimizer: interior positive collar distance; positive inward normal derivative; boundary rank two/transversality/nonzero tangential derivative; boundary homeomorphism and nearby immersion; global immersion also uses interior branch exclusion.<br>No accepted complete original endpoint. | — | Open |
| Corollary C.14 | Full minimizer is globally injective for image points in a fixed near-boundary collar; its double point set is compact and uniformly interior.<br>No accepted complete original endpoint. | — | Open |
| Corollary C.15 | Universal-cover translates meeting near old boundary are the same image; distinct translates and intermediate-cover images intersect only uniformly away from old boundary.<br>No accepted complete original endpoint. | — | Open |

One original may require several declaration heads: Lemma 2.4 has five and B.3
has two. The public audit covers exactly 25 original heads plus the qualified
`SeifertSurfaces.nonempty_complexity_downset_connected` support head. All are
available through the common entry; no support head adds numbered credit.

A.2/A.5 assume an attained minimizer in the Definition-A.1 class; A.7 assumes the
supplied A.6 minimizer. C.6/C.11 assume a full Lemaire minimizer. C.9 retains the
source’s L2′/L2″ compatibility alternatives. None establishes the still-open
existence or headline results.

Corollary 2.3 remains open in the strict count. The retained source supplies
distance/reachability statements and connectedness for nonempty downsets.
The empty-downset convention is explicit; this qualified support creates no
additional original credit.

The archived originals retain their historical provider provenance. The current
unified sources select reviewed owners and restore previously checked closed
terms where needed. Exact bounded identities and replay receipts preserve the
operative geometric data; raw historical mismatches remain separately recorded.
[BUILD_STATUS.md](BUILD_STATUS.md) explains their scope. No generic normalization
of expressions, provider metadata or hypotheses is authorized.

B.1’s divergent reader finding and source-review reconciliation remain in the
historical inventory. C.7’s compact-subsurface reconciliation is preserved.
Packaging does not relabel those reviews. [SOURCE_ISSUES.md](../SOURCE_ISSUES.md)
and [FORMALIZATION_ISSUES.md](../FORMALIZATION_ISSUES.md) distinguish manuscript
findings from Lean interface issues; they do not establish that Theorem A is false.
