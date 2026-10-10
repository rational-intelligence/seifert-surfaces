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
