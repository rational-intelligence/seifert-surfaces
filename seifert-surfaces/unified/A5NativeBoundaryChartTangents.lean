import A5HalfspaceChartTangents
import A5NativeSmoothImageTangents

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u

/-- Every incident closed native sector has the tangent plane of a genuine
smooth image chart, including at its flat boundary. -/
theorem native_sector_tangent_matches_smooth_halfspace_chart
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (C : SmoothImageChart S F.map)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ ((F.domain i).chart j).map.target)
    (hdy : F.parametrization i (((F.domain i).chart j).map.symm y) ∈ C.chart.source)
    (c : SmoothAmbientChart ThreeSphere)
    (hc : E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j y) ∈ c.chart.source) :
    (fderivWithin ℝ (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      ((F.domain i).chart j).map.target y).toLinearMap.range =
    (fderivWithin ℝ (c.chart ∘ E.toSphere ∘ F.map ∘ C.chart.symm ∘ (𝓡∂ 2).symm)
      (range (𝓡∂ 2)) ((𝓡∂ 2) (C.chart
        (F.parametrization i (((F.domain i).chart j).map.symm y))))).toLinearMap.range := by
  let b := ((F.domain i).chart j).map
  let p := F.parametrization i ∘ b.symm
  let x := p y
  have hxC : x ∈ C.chart.source := hdy
  let q := C.chart ∘ p
  let f := c.chart ∘ E.toSphere ∘ F.map ∘ C.chart.symm
  let V := C.chart.target ∩ (E.toSphere ∘ F.map ∘ C.chart.symm) ⁻¹' c.chart.source
  have hinc : Manifold.IsImmersion (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := by
    let : ChartedSpace (EuclideanHalfSpace 3) T.Carrier := E.charted
    let : IsManifold (𝓡∂ 3) ∞ T.Carrier := E.smooth
    exact E.inclusion.isImmersion
  have hsphere : ContMDiffOn (𝓡∂ 2) (𝓡 3) ∞
      (E.toSphere ∘ F.map ∘ C.chart.symm) C.chart.target :=
    hinc.contMDiff.comp_contMDiffOn C.cInfinity
  have hV : IsOpen V := hsphere.continuousOn.isOpen_inter_preimage C.target_open c.chart.open_source
  have hxV : q y ∈ V := by
    refine ⟨C.chart.map_source hdy,?_⟩
    change E.toSphere (F.map (C.chart.symm (C.chart x))) ∈ c.chart.source
    rw [C.chart.left_inv hxC]
    exact hc
  have hfs : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,Euc 3) ∞ f V :=
    c.smooth.comp (hsphere.mono inter_subset_left) (fun z hz => hz.2)
  have hfi : Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 3) f (q y)) := by
    have hmd := (C.cInfinity.contMDiffAt (C.target_open.mem_nhds hxV.1)).mdifferentiableAt (by simp)
    have hsd := (hsphere.contMDiffAt (C.target_open.mem_nhds hxV.1)).mdifferentiableAt (by simp)
    have hcd : c.chart.MDifferentiable (𝓡 3) 𝓘(ℝ,Euc 3) :=
      ⟨c.smooth.mdifferentiableOn (by simp),c.inverse_smooth.mdifferentiableOn (by simp)⟩
    have hci := C.differential_injective (q y) hxV.1
    rw [mfderivWithin_of_mem_nhds (C.target_open.mem_nhds hxV.1)] at hci
    change Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 3)
      (c.chart ∘ E.toSphere ∘ (F.map ∘ C.chart.symm)) (q y))
    rw [mfderiv_comp _ (hcd.mdifferentiableAt hxV.2) hsd,
      mfderiv_comp _ (hinc.contMDiff.mdifferentiable (by simp) _) hmd]
    exact (hcd.mfderiv_injective hxV.2).comp
      ((hinc.mfderiv_injective (by simp) _).comp hci)
  have hp : ContinuousWithinAt p b.target y :=
    (F.parametrization i).continuous.continuousAt.comp_continuousWithinAt (b.symm.continuousOn y hy)
  have hcc : ContinuousAt C.chart (p y) :=
    C.chart.continuousOn.continuousAt (C.source_open.mem_nhds hxC)
  have hq : ContinuousWithinAt q b.target y := hcc.comp_continuousWithinAt hp
  let g := c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j
  obtain ⟨hg,hgi⟩ := native_piece_chart_C1_rank_at E F i j y hy c hc
  have he : f ∘ q =ᶠ[𝓝[b.target] y] g := by
    filter_upwards [hp (C.source_open.mem_nhds hdy)] with z hz
    change c.chart (E.toSphere (F.map (C.chart.symm (C.chart (p z))))) =
      c.chart (E.toSphere (F.map (p z)))
    rw [C.chart.left_inv hz]
  have hep : f (q y) = g y := by
    change c.chart (E.toSphere (F.map (C.chart.symm (C.chart x)))) = c.chart (E.toSphere (F.map x))
    rw [C.chart.left_inv hxC]
  have hu : UniqueDiffWithinAt ℝ b.target y := by
    have hh := ((F.domain i).chart j).model.uniqueDiffOn_domain
    rw [← ((F.domain i).chart j).target_eq] at hh
    exact hh y hy
  exact relative_tangent_range_of_halfspace_image_lift g f q b.target y hy hu
    (fderivWithin ℝ g b.target y) (hg.differentiableWithinAt (by norm_num)).hasFDerivWithinAt
    hgi V hV hfs hxV hfi hq he hep

/-- Native tangent agreement follows from a single smooth image chart even
at a boundary point; arbitrary rough source parametrizations add no premise. -/
theorem native_incident_tangents_eq_of_smooth_image_chart
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (C : SmoothImageChart S F.map)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (k : Fin F.pieceCount) (l : Fin (F.domain k).count) (z w : Euc 2)
    (hz : z ∈ ((F.domain i).chart j).map.target)
    (hw : w ∈ ((F.domain k).chart l).map.target)
    (heq : F.parametrization i (((F.domain i).chart j).map.symm z) =
      F.parametrization k (((F.domain k).chart l).map.symm w))
    (hxC : F.parametrization i (((F.domain i).chart j).map.symm z) ∈ C.chart.source)
    (c : SmoothAmbientChart ThreeSphere)
    (hc : E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j z) ∈ c.chart.source) :
    (fderivWithin ℝ (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      ((F.domain i).chart j).map.target z).toLinearMap.range =
    (fderivWithin ℝ (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization k) l)
      ((F.domain k).chart l).map.target w).toLinearMap.range := by
  have h1 := native_sector_tangent_matches_smooth_halfspace_chart E F C i j z hz hxC c hc
  have hkc : E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization k) l w) ∈ c.chart.source := by
    change E.toSphere (F.map (F.parametrization k _)) ∈ _
    rw [← heq]
    exact hc
  have h2 := native_sector_tangent_matches_smooth_halfspace_chart E F C k l w hw (heq ▸ hxC) c hkc
  rw [← heq] at h2
  exact h1.trans h2.symm

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
