import Section5GraphAssemblyV480
import OriginalSection4Whole
import Section5ExchangeBranchesV481
import Section5AnalyticConsumerLinksV481
import B3LocalInteriorDonorBridgeV481
import B3FullCollarDonorBridgeV488
import Section5CollarOrientationV481

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators ENNReal

namespace SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.GenusLinking SeifertSurfaces.Complexity
open SeifertSurfaces.OriginalEndpoints.Section4
open SeifertSurfaces.OriginalEndpoints.Section5

/-! The six complete original Section 5 roots. No E, U, Fin, exchange-pair,
rounding-provider, compactness, nodal-order or transverse-family result is a
new hypothesis. Source defects of 5.4 are retained explicitly for review.
Affected area consumers are statement scaffolds. Existing unrelated proof
bodies are pinned context; this packet derives no proofs. -/

/-- Theorem 5.1, original (a)--(d), with fixed vertices preceding every z.
The native IS distance, genus and full geometric class area infimum are used.
No simultaneous disjointness of the five representatives is imposed. -/
theorem original_5_1 {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (H : Section4.SourceGeometry E)
    (hK : KnotIsNontrivial K) (x u w : Vertices E)
    (hxu : graphDistance E x u = 1) (hxw : graphDistance E x w = 1)
    (huw : graphDistance E u w = 2) :
    ∃ up down : Vertices E,
      (EqualOrAdjacent E up x ∧ EqualOrAdjacent E up u ∧ EqualOrAdjacent E up w) ∧
      (EqualOrAdjacent E down x ∧ EqualOrAdjacent E down u ∧ EqualOrAdjacent E down w) ∧
      (∀ z : Vertices E, EqualOrAdjacent E z u → EqualOrAdjacent E z w →
        EqualOrAdjacent E z up ∧ EqualOrAdjacent E z down) ∧
      vertexGenus E up + vertexGenus E down ≤ vertexGenus E u + vertexGenus E w ∧
      (vertexGenus E up + vertexGenus E down = vertexGenus E u + vertexGenus E w →
        areaInfimum E H up + areaInfimum E H down < areaInfimum E H u + areaInfimum E H w) := by
  obtain ⟨S, A, B, hS, hA, hB, hSmin, hAmin, hBmin, hdisj, _⟩ :=
    Section5.Obligations.independently_chosen_minimizers E H hK x u w hxu hxw huw
  have hSA : graphDistance E (SurfaceVertex E S) (SurfaceVertex E A) = 1 := by
    simpa only [hS, hA] using hxu
  have hSB : graphDistance E (SurfaceVertex E S) (SurfaceVertex E B) = 1 := by
    simpa only [hS, hB] using hxw
  have hAB : graphDistance E (SurfaceVertex E A) (SurfaceVertex E B) = 2 := by
    simpa only [hA, hB] using huw
  rcases Section5.Obligations.three_configurations_exhaust E H A B hAmin hBmin with hT0 | hT1 | hT2
  · obtain ⟨up, down, _, hpair⟩ := Section5.Obligations.transverse_original_exchange
      E H hK S A B hSmin hAmin hBmin hSA hSB hAB hT0
    have hpair' := (Section5.Obligations.exchange_pair_native_graph_bridge E H _ _ _ up down).mp hpair
    exact ⟨up, down, by simpa only [hS, hA, hB] using hpair'⟩
  · obtain ⟨up, down, hpair⟩ := Section5.WholeAssemblyV480.t1_native_exchange_pair
      E H hK S A B hSmin hAmin hBmin hSA hSB hAB hdisj hT1
    have hpair' := (Section5.Obligations.exchange_pair_native_graph_bridge E H _ _ _ up down).mp hpair
    exact ⟨up, down, by simpa only [hS, hA, hB] using hpair'⟩
  · obtain ⟨up, down, hpair⟩ := Section5.WholeAssemblyV480.t2_native_exchange_pair
      E H hK S A B hSmin hAmin hBmin hSA hSB hAB hdisj hT2
    have hpair' := (Section5.Obligations.exchange_pair_native_graph_bridge E H _ _ _ up down).mp hpair
    exact ⟨up, down, by simpa only [hS, hA, hB] using hpair'⟩

/-- Proposition 5.2: existence, both outputs from any common neighbour,
one descended apex for every genus bound, and the whole exchange-complex
conclusion with the actual nonempty connected flag complex and attained order. -/
theorem original_5_2 {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (H : Section4.SourceGeometry E)
    (hK : KnotIsNontrivial K) :
    (∀ u w : Vertices E, graphDistance E u w = 2 →
    (∃ x : Vertices E, Apex E u w x) ∧
    (∀ x : Vertices E, x ∈ commonNeighbors E u w →
      ∀ up down : Vertices E, ExchangePair E H x u w up down →
        Apex E u w up ∧ Apex E u w down) ∧
    (∃ x : Vertices E, Apex E u w x ∧
      Section4.complexity E H x < max (Section4.complexity E H u) (Section4.complexity E H w) ∧
      ∀ ell : ℤ, (vertexGenus E u : ℤ) ≤ ell → (vertexGenus E w : ℤ) ≤ ell →
        (vertexGenus E x : ℤ) ≤ ell)) ∧
    ExchangeComplex E H := by
  have hconnected : (oneSkeleton.{0} E).Connected := by
    sorry
  obtain ⟨hwell, _⟩ := (original_4_8 E H hK).2.2.1
  apply Section5.WholeAssemblyV480.whole_proposition52 E H hconnected
    (original_4_3 E H).2.1 hwell
  intro x u w hxu hxw huw
  exact original_5_1 E H hK x u w hxu hxw huw

/-- Lemma 5.4, standalone C² seam input, all clauses and width quantifiers.
The literal original smooth ambient-isotopy reading is encoded and flagged
SF-09; a topological variant is separately named in the definitions, never
silently substituted. Input boundary neatness is deliberately not added.
Positive finite lower radii are tested against extended local reach and
boundary distance; this retains the empty-boundary (+∞) case. -/
theorem original_5_4 (M : Type) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M]
    (g : SmoothMetric M) (F : SourceCornerSurface g) :
    ∃ C : RoundingBounds F, ∀ eta : M → ℝ,
      WidthAdmissible g F.seams C.etaMax C.kappa eta →
        Nonempty (OriginalRoundedSurface F C eta) := by
  sorry

/-- Lemma 5.5: constants depend on the once-chosen rounded surface and
metric before σ, one whole family, leaf boundaries, contained in open U,
isotopy to the original and between every two outputs, and actual area cost.
The input collar puts time zero in closure U and positive times in U. -/
theorem original_5_5 {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (H : Section4.SourceGeometry E)
    (F : GeneralNeatImage E.Carrier) (U : Set E.Carrier) (hU : IsOpen U)
    (collar : GeneralOneSidedCollar F U)
    (hboundary : ∃ label : Circle, F.boundary = H.foliation.leaf label) :
    ∃ sigma0 C : ℝ, 0 < sigma0 ∧
      ∃ pushed : ℝ → GeneralNeatImage E.Carrier,
        (∀ sigma : ℝ, 0 < sigma → sigma ≤ sigma0 →
          (pushed sigma).image ⊆ U ∧
          (∃ label : Circle, (pushed sigma).boundary = H.foliation.leaf label) ∧
          SmoothAmbientIsotopy.Rel F.image (pushed sigma).image ∧
          imageArea H.metric (pushed sigma).image - imageArea H.metric F.image ≤ C * sigma) ∧
        (∀ sigma sigma' : ℝ, 0 < sigma → sigma ≤ sigma0 →
          0 < sigma' → sigma' ≤ sigma0 →
          SmoothAmbientIsotopy.Rel (pushed sigma).image (pushed sigma').image) := by
  classical
  have horientation : Nonempty (SmoothVolumeOrientation (𝓡∂ 2) F.surface) :=
    Section5.WholeAssemblyV480.general_one_sided_collar_orientation F collar
  let orientation := Classical.choice horientation
  let source : CompactOrientedSurface.{0} := { carrier := F.surface, orientation := orientation }
  let f : NeatEmbedding source E.Carrier := {
    toFun := F.map
    smoothEmbedding := F.smooth
    boundary_preimage := F.proper
    boundary_transverse := F.transverse }
  let C0 : AppendixBOriginalV479.OneSidedCollar f U := {
    epsilon := collar.epsilon
    epsilon_pos := collar.positive
    map := collar.map
    initial := collar.initial
    smooth := collar.smooth
    embedding := collar.embedded
    into_region := collar.open_side
    closed_side := collar.closed_side
    boundary_strata := collar.boundary_strata
    immersion := collar.immersion }
  have hfleaf : H.foliation.BoundaryIn f.toFun := hboundary
  obtain ⟨sigma0, C, hsigma, pushed, hpush, hsame⟩ :=
    Section5.ConsumerLinks.B2_push_off_native_consumer E H f U hU C0 hfleaf
  let surfaces : ℝ → GeneralNeatImage E.Carrier := fun sigma => {
    surface := { carrier := source }
    map := (pushed sigma).toFun
    smooth := (pushed sigma).smoothEmbedding
    proper := (pushed sigma).boundary_preimage
    transverse := (pushed sigma).boundary_transverse }
  refine ⟨sigma0, C, hsigma, surfaces, ?_, ?_⟩
  · intro sigma hp hle
    obtain ⟨hU', hb, hi, ha⟩ := hpush sigma hp hle
    refine ⟨hU', hb, hi, ?_⟩
    have hbefore : imageArea H.metric F.image = area H.metric f.toFun :=
      Section5.Obligations.image_area_neat_bridge H.metric f
    have hafter : imageArea H.metric (surfaces sigma).image =
        area H.metric (pushed sigma).toFun :=
      Section5.Obligations.image_area_neat_bridge H.metric (pushed sigma)
    rw [hbefore, hafter]
    exact ha
  · exact fun sigma sigma' hp hle hp' hle' => hsame sigma sigma' hp hle hp' hle'


/-- Lemma 5.6, with an actual normal isotopy, genuine minimizers of two
distinct classes, a literal disc component of the cut-open complement, and
gain defined as the arclength integral with the same θ and width for either
opposite-sector pair. The two returned curves may coincide. -/
theorem original_5_6 {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (H : Section4.SourceGeometry E) (hK : KnotIsNontrivial K)
    (A0 B : IncompressibleSpanningSurface.{0} E)
    (hA0 : IsRelativeAreaMinimizer H.metric H.foliation A0)
    (hB : IsRelativeAreaMinimizer H.metric H.foliation B)
    (hdistinct : SurfaceVertex E A0 ≠ SurfaceVertex E B)
    (A : NeatEmbedding A0.1.surface E.Carrier) (hA : A.Incompressible)
    (hnormal : Nonempty (ReparametrizedNormalIsotopy A0.1.surface E.Carrier A0.1.embedding A))
    (hleaf : H.foliation.BoundaryIn A.toFun)
    (herror : 0 ≤ area H.metric A.toFun - area H.metric A0.1.embedding.toFun)
    (htransverse : AppendixBOriginalV479.Transverse A B.1.embedding)
    (hboundary : Disjoint (A.toFun '' A0.1.surface.boundary) (SurfaceBoundary E B))
    (hdisc : AppendixBOriginalV479.HasDiscPatch A (A.image ∩ B.1.image) ∨
      AppendixBOriginalV479.HasDiscPatch B.1.embedding (A.image ∩ B.1.image))
    : ∃ C : PairRoundingControl H.metric A B.1.embedding,
      ∀ eta : E.Carrier → ℝ,
      WidthAdmissible H.metric C.seams C.etaMax C.kappa eta →
      ∃ a b : AppendixBOriginalV479.ClosedIntersectionComponent (A.image ∩ B.1.image),
        pairGain C eta a + pairGain C eta b ≤
          area H.metric A.toFun - area H.metric A0.1.embedding.toFun := by
  sorry

/-- Proposition 5.7: whole original pair, no local elliptic estimate or
collar-regularity premise. Interior signed nodal estimates, collar production
for a common leaf, its single r0, all critical points, and global finiteness
are conclusions. Arbitrarily supplied exact collar graphs are also covered. -/
theorem original_5_7 {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (H : Section4.SourceGeometry E) (hK : KnotIsNontrivial K)
    (A B : IncompressibleSpanningSurface.{0} E)
    (hA : IsRelativeAreaMinimizer H.metric H.foliation A)
    (hB : IsRelativeAreaMinimizer H.metric H.foliation B)
    (hdistance : graphDistance E (SurfaceVertex E A) (SurfaceVertex E B) = 2)
    (hmeet : (A.1.image ∩ B.1.image).Nonempty) :
    InteriorTangencyResult E A B ∧
    (SurfaceBoundary E A = SurfaceBoundary E B →
      ∃ D : B1OriginalData H.metric H.foliation, D.A = A ∧ D.B = B ∧ CollarTangencyResult E D) ∧
    (∀ D : B1OriginalData H.metric H.foliation,
      D.A = A → D.B = B → CollarTangencyResult E D) ∧
    (AppendixBOriginalV479.interiorTangencies A.1.embedding B.1.embedding).Finite := by
  obtain ⟨P, hPA, hPB⟩ := Section5.ConsumerLinks.original_pair_to_B3 E H hK A B hA hB hdistance
  have hcollar : ∀ D : B1OriginalData H.metric H.foliation, CollarTangencyResult E D :=
    fun D => (Section5.WholeAssemblyV480.b3_native_full_collar_result D).1
  refine ⟨?_, ?_, fun D _ _ => hcollar D, ?_⟩
  · have hinterior := Section5.WholeAssemblyV480.b3_native_interior_result P
    rw [hPA, hPB] at hinterior
    exact hinterior
  · intro hboundary
    obtain ⟨D, hDA, hDB⟩ := Section5.Obligations.minimizer_common_leaf_graph
      E H hK A B hA hB hdistance hboundary
    exact ⟨D, hDA, hDB, hcollar D⟩
  · by_cases hboundary : SurfaceBoundary E A = SurfaceBoundary E B
    · obtain ⟨D,hDA,hDB⟩ := Section5.Obligations.minimizer_common_leaf_graph
        E H hK A B hA hB hdistance hboundary
      have hfinite := (Section5.WholeAssemblyV480.b3_native_full_collar_result D).2
      rw [hDA,hDB] at hfinite
      exact hfinite
    · have hne : SurfaceBoundary E P.A ≠ SurfaceBoundary E P.B := by
        simpa only [hPA,hPB] using hboundary
      have hfinite := Section5.WholeAssemblyV480.b3_native_distinct_boundary_finite P hne
      rw [hPA,hPB] at hfinite
      exact hfinite

end SeifertSurfaces.OriginalEndpoints
