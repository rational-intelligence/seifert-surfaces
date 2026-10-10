import A5NativeSmoothImageTangents
import A5NativeChartTangents
import A5InteriorInvarianceOfDomain

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe u

/-- A transverse projection is a local homeomorphism at any point of a
smooth native image chart. Transversality is checked on just one actual
incident closed-sector chart and then transported to the smooth image. -/
theorem native_smooth_image_projection_local_homeomorph
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (x : S) (hxboundary : x ∉ S.boundary)
    (C : SmoothImageChart S F.map) (hxC : x ∈ C.chart.source)
    (c : SmoothAmbientChart ThreeSphere) (hc : E.toSphere (F.map x) ∈ c.chart.source)
    (P : E3 →L[ℝ] E2)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : E2)
    (hy : y ∈ ((F.domain i).chart j).map.target)
    (hyx : F.parametrization i (((F.domain i).chart j).map.symm y) = x)
    (hP : Function.Bijective (P.comp (fderivWithin ℝ
      (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      ((F.domain i).chart j).map.target y))) :
    IsLocalHomeomorphOn (P ∘ c.chart ∘ E.toSphere ∘ F.map) {x} := by
  obtain ⟨d, hxd, _, hs, hr⟩ := native_image_chart_plane_parametrization S F.map C x hxC hxboundary
  let Ω := d.target ∩ (E.toSphere ∘ F.map ∘ d.symm) ⁻¹' c.chart.source
  have hΩ : IsOpen Ω :=
    ((continuous_subtype_val.comp F.map.continuous).comp_continuousOn d.symm.continuousOn).isOpen_inter_preimage
      d.open_target c.chart.open_source
  have hxΩ : d x ∈ Ω := by
    refine ⟨d.map_source hxd, ?_⟩
    change E.toSphere (F.map (d.symm (d x))) ∈ c.chart.source
    rwa [d.left_inv hxd]
  let Φ := c.chart ∘ E.toSphere ∘ F.map ∘ d.symm
  obtain ⟨hΦ, hΦrank⟩ := native_sphere_coordinate_smooth_rank E (F.map ∘ d.symm) Ω hΩ
    (hs.mono inter_subset_left) (fun z hz => hr z hz.1) c (fun z hz => hz.2)
  have heq := native_sector_tangent_matches_smooth_plane_chart E F d hs hr i j y hy
    (by rw [hyx]; exact hxd) c (by change E.toSphere (F.map (F.parametrization i _)) ∈ _; rw [hyx]; exact hc)
  rw [hyx] at heq
  have hPD : Function.Bijective (P.comp (fderiv ℝ Φ (d x))) :=
    projection_bijective_of_equal_tangent_ranges _ _ P heq (hΦrank _ hxΩ) hP
  let Q := P ∘ Φ
  have hQ : ContDiffAt ℝ ∞ Q (d x) :=
    P.contDiff.contDiffAt.comp _ (hΦ.contDiffAt (hΩ.mem_nhds hxΩ))
  let L := ContinuousLinearEquiv.ofBijective (P.comp (fderiv ℝ Φ (d x)))
    (LinearMap.ker_eq_bot.mpr hPD.1) (LinearMap.range_eq_top.mpr hPD.2)
  have hQD : HasFDerivAt Q (L : E2 →L[ℝ] E2) (d x) :=
    P.hasFDerivAt.comp _ ((hΦ.contDiffAt (hΩ.mem_nhds hxΩ)).differentiableAt (by simp)).hasFDerivAt
  let e := hQ.toOpenPartialHomeomorph Q hQD (by simp)
  have hxde : d x ∈ e.source := hQ.mem_toOpenPartialHomeomorph_source hQD (by simp)
  apply IsLocalHomeomorphOn.mk
  intro z hz
  rcases mem_singleton_iff.mp hz with rfl
  refine ⟨d.trans e, ⟨hxd, hxde⟩, ?_⟩
  intro z hz
  change P (c.chart (E.toSphere (F.map z))) = P (c.chart (E.toSphere (F.map (d.symm (d z)))))
  rw [d.left_inv hz.1]

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
