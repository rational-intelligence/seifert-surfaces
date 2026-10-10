import A5NativeImageChartPlane
import A5NativeSphereCoordinateRank
import A5SmoothImageGraphRegularity

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- Smooth native image charts automatically regularize any C¹ transverse
projection parametrization of the same image. The inverse chart lift and
its differentiability are derived, without a smooth auxiliary source map. -/
theorem native_projection_smooth_of_image_chart_cover
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (e : OpenPartialHomeomorph S E2) (c : SmoothAmbientChart ThreeSphere)
    (P : E3 →L[ℝ] E2)
    (he : ∀ x ∈ e.source, e x = P (c.chart (E.toSphere (F.map x))))
    (hmaps : MapsTo (E.toSphere ∘ F.map) e.source c.chart.source)
    (U : Set E2) (hU : IsOpen U) (hUe : U ⊆ e.target)
    (hC1 : ContDiffOn ℝ 1 (c.chart ∘ E.toSphere ∘ F.map ∘ e.symm) U)
    (hboundary : ∀ y ∈ U, e.symm y ∉ S.boundary)
    (hcover : ∀ y ∈ U, ∃ C : SmoothImageChart S F.map, e.symm y ∈ C.chart.source) :
    ContDiffOn ℝ ∞ (c.chart ∘ E.toSphere ∘ F.map ∘ e.symm) U := by
  intro y hy
  obtain ⟨C, hCy⟩ := hcover y hy
  obtain ⟨d, hyd, _, hdsmooth, hdrank⟩ := native_image_chart_plane_parametrization S F.map
    C (e.symm y) hCy (hboundary y hy)
  let V := U ∩ e.symm ⁻¹' d.source
  have hV : IsOpen V := (e.symm.continuousOn.mono hUe).isOpen_inter_preimage hU d.open_source
  have hyV : y ∈ V := ⟨hy, hyd⟩
  let Ω := d.target ∩ d.symm ⁻¹' e.source
  have hΩ : IsOpen Ω := d.isOpen_inter_preimage_symm e.open_source
  let Φ := c.chart ∘ E.toSphere ∘ F.map ∘ d.symm
  obtain ⟨hΦ, hΦrank⟩ := native_sphere_coordinate_smooth_rank E (F.map ∘ d.symm)
    Ω hΩ (hdsmooth.mono inter_subset_left) (fun z hz => hdrank z hz.1) c
    (fun z hz => hmaps hz.2)
  let κ := d ∘ e.symm
  have hκ : ContinuousOn κ V := d.continuousOn.comp
    (e.symm.continuousOn.mono (fun z hz => hUe hz.1)) (fun z hz => hz.2)
  have hκΩ : MapsTo κ V Ω := by
    intro z hz
    refine ⟨d.map_source hz.2, ?_⟩
    change d.symm (d (e.symm z)) ∈ e.source
    rw [d.left_inv hz.2]
    exact e.map_target (hUe hz.1)
  have heq : ∀ z ∈ V, Φ (κ z) = c.chart (E.toSphere (F.map (e.symm z))) := by
    intro z hz
    change c.chart (E.toSphere (F.map (d.symm (d (e.symm z))))) = _
    rw [d.left_inv hz.2]
  have hsection : ∀ z ∈ V, P (c.chart (E.toSphere (F.map (e.symm z)))) = z := by
    intro z hz
    rw [← he _ (e.map_target (hUe hz.1)), e.right_inv (hUe hz.1)]
  have hs := smooth_projection_section_of_smooth_embedded_image
    (c.chart ∘ E.toSphere ∘ F.map ∘ e.symm) Φ κ P V Ω hV hΩ
    (hC1.mono inter_subset_left) hΦ hΦrank hκ hκΩ heq hsection
  exact (hs.contDiffAt (hV.mem_nhds hyV)).contDiffWithinAt

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
