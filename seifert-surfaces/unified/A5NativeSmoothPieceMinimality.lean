import A5SmoothRegularImageLift
import A5NativePieceGraphRegularity
import A5NativeSphereCoordinateRank
import OriginalA4GeometryBridges

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- Actual piece minimality transfers to any smooth regular parametrization
of the same native interior image. The source-coordinate lift is constructed
from the native embedding; its smoothness is a conclusion of regularity. -/
theorem native_smooth_image_minimal_on_piece_interior
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (h : AmbientMetric ThreeSphere) (e : OpenPartialHomeomorph S E2)
    (U : Set E2) (hU : IsOpen U) (hUe : U ⊆ e.target)
    (hf : ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 3) ∞ (F.map ∘ e.symm) U)
    (hrank : ∀ x ∈ U, Function.Injective
      (mfderiv 𝓘(ℝ, E2) (𝓡∂ 3) (F.map ∘ e.symm) x))
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (hminimal : IsMinimalPatch h
      (E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      (interior ((F.domain i).chart j).map.target))
    (hpiece : ∀ y ∈ U, e.symm y ∈ F.parametrization i ''
      ((F.domain i).interior ∩ ((F.domain i).chart j).map.source))
    (c : SmoothAmbientChart ThreeSphere)
    (hchart : MapsTo (E.toSphere ∘ F.map ∘ e.symm) U c.chart.source) :
    IsMinimalParametrizationOn (actualChartTensor h c)
      (c.chart ∘ E.toSphere ∘ F.map ∘ e.symm) U := by
  classical
  let b := ((F.domain i).chart j).map
  let Φ := E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j
  let Ω := interior b.target ∩ Φ ⁻¹' c.chart.source
  have hΩ : IsOpen Ω :=
    hminimal.1.continuousOn.isOpen_inter_preimage isOpen_interior c.chart.open_source
  have hex (y : E2) (hy : y ∈ U) : ∃ z ∈ interior b.target,
      sectorCoordinateMap (F.map ∘ F.parametrization i) j z = F.map (e.symm y) := by
    obtain ⟨v, hv, hvy⟩ := hpiece y hy
    refine ⟨b v, ?_, ?_⟩
    · rw [← AreaCertificates.sector_chart_piece_interior]
      exact ⟨v, hv, rfl⟩
    · change F.map (F.parametrization i (b.symm (b v))) = _
      rw [b.left_inv hv.2, hvy]
  let q (y : E2) := if hy : y ∈ U then (hex y hy).choose else 0
  have hq (y : E2) (hy : y ∈ U) : q y ∈ interior b.target ∧
      sectorCoordinateMap (F.map ∘ F.parametrization i) j (q y) = F.map (e.symm y) := by
    simpa only [q, dite_eq_left hy] using (hex y hy).choose_spec
  have hqΩ : MapsTo q U Ω := by
    intro y hy
    refine ⟨(hq y hy).1, ?_⟩
    change E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q y)) ∈ c.chart.source
    rw [(hq y hy).2]
    exact hchart hy
  have hqcont : ContinuousOn q U :=
    continuous_coordinate_lift_of_embedded_image b (F.map ∘ F.parametrization i)
      (F.piece_topological_embedding i) U (F.map ∘ e.symm) q
      (F.map.continuous.comp_continuousOn (e.symm.continuousOn.mono hUe))
      (fun y hy => interior_subset (hq y hy).1) (fun y hy => (hq y hy).2)
  obtain ⟨hgs, hsymm, hpos⟩ :=
    SeifertSurfaces.OriginalEndpoints.A4GeometryBridges.actual_chart_tensor_metric_properties h c
  let g : CoordinateMetric c.chart.target := ⟨actualChartTensor h c, hgs, hsymm, hpos⟩
  obtain ⟨hfs, hfr⟩ := native_sphere_coordinate_smooth_rank E (F.map ∘ e.symm) U hU hf hrank c hchart
  apply coordinate_minimality_of_continuous_image_lift c.chart.target c.chart.open_target g
    U Ω hU hΩ (c.chart ∘ E.toSphere ∘ F.map ∘ e.symm) (c.chart ∘ Φ) q
    hfs (hminimal.2.2 c) (fun z hz => c.chart.map_source hz.2) hfr
    (native_minimal_patch_coordinate_rank Φ (interior b.target) Ω hΩ hminimal c subset_rfl)
    hqcont hqΩ
  intro y hy
  change c.chart (E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q y))) =
    c.chart (E.toSphere (F.map (e.symm y)))
  rw [(hq y hy).2]

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
