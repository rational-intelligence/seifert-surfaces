import A5RelativeImageTangent

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe u

/-- Every incident native closed-sector parametrization has the tangent
plane of a smooth image chart. This includes corners and reflex sectors;
no differentiability into the original source surface is needed. -/
theorem native_sector_tangent_matches_smooth_plane_chart
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (d : OpenPartialHomeomorph S E2)
    (hs : ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 3) ∞ (F.map ∘ d.symm) d.target)
    (hr : ∀ v ∈ d.target, Function.Injective
      (mfderiv 𝓘(ℝ, E2) (𝓡∂ 3) (F.map ∘ d.symm) v))
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : E2)
    (hy : y ∈ ((F.domain i).chart j).map.target)
    (hdy : F.parametrization i (((F.domain i).chart j).map.symm y) ∈ d.source)
    (c : SmoothAmbientChart ThreeSphere)
    (hc : E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j y) ∈ c.chart.source) :
    (fderivWithin ℝ (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      ((F.domain i).chart j).map.target y).toLinearMap.range =
    (fderiv ℝ (c.chart ∘ E.toSphere ∘ F.map ∘ d.symm)
      (d (F.parametrization i (((F.domain i).chart j).map.symm y)))).toLinearMap.range := by
  let b := ((F.domain i).chart j).map
  let p := F.parametrization i ∘ b.symm
  let x := p y
  have hxD : x ∈ d.source := hdy
  let q := d ∘ p
  let Φ := c.chart ∘ E.toSphere ∘ F.map ∘ d.symm
  let Ω := d.target ∩ (E.toSphere ∘ F.map ∘ d.symm) ⁻¹' c.chart.source
  have hΩ : IsOpen Ω :=
    ((continuous_subtype_val.comp F.map.continuous).comp_continuousOn d.symm.continuousOn).isOpen_inter_preimage
      d.open_target c.chart.open_source
  have hxΩ : q y ∈ Ω := by
    refine ⟨d.map_source hdy, ?_⟩
    change E.toSphere (F.map (d.symm (d x))) ∈ c.chart.source
    rw [d.left_inv hxD]
    exact hc
  obtain ⟨hΦ, hΦrank⟩ := native_sphere_coordinate_smooth_rank E (F.map ∘ d.symm) Ω hΩ
    (hs.mono inter_subset_left) (fun v hv => hr v hv.1) c (fun v hv => hv.2)
  have hΦd : HasFDerivAt Φ (fderiv ℝ Φ (q y)) (q y) :=
    ((hΦ.contDiffAt (hΩ.mem_nhds hxΩ)).differentiableAt (by simp)).hasFDerivAt
  have hp : ContinuousWithinAt p b.target y :=
    (F.parametrization i).continuous.continuousAt.comp_continuousWithinAt (b.symm.continuousOn y hy)
  have hq : ContinuousWithinAt q b.target y :=
    (show ContinuousAt d (p y) from d.continuousAt hxD).comp_continuousWithinAt hp
  let g := c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j
  obtain ⟨hg, hgr⟩ := native_piece_chart_C1_rank_at E F i j y hy c hc
  have heq : (Φ ∘ q) =ᶠ[𝓝[b.target] y] g := by
    filter_upwards [hp (d.open_source.mem_nhds hxD)] with z hz
    change c.chart (E.toSphere (F.map (d.symm (d (p z))))) = c.chart (E.toSphere (F.map (p z)))
    rw [d.left_inv hz]
  have hpoint : Φ (q y) = g y := by
    change c.chart (E.toSphere (F.map (d.symm (d x)))) = c.chart (E.toSphere (F.map x))
    rw [d.left_inv hxD]
  have huniq : UniqueDiffWithinAt ℝ b.target y := by
    have hu := ((F.domain i).chart j).model.uniqueDiffOn_domain
    rw [← ((F.domain i).chart j).target_eq] at hu
    exact hu y hy
  exact relative_tangent_range_of_continuous_image_lift g Φ q b.target y hy huniq
    (fderivWithin ℝ g b.target y) (fderiv ℝ Φ (q y))
    (hg.differentiableWithinAt (by norm_num)).hasFDerivWithinAt hgr hΦd
    (hΦrank _ hxΩ) hq heq hpoint

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
