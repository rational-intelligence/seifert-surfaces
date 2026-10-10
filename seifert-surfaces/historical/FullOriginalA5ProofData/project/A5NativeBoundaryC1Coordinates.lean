import A5OriginalBoundaryC1ContractV474
import A5NativeBoundaryChartTangents

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u

/-- The approved C1 image-chart contract gives regular C1 coordinates in
an actual smooth ambient chart. Both the map and its derivative are those
of the native original surface, on the exact restricted target. -/
theorem native_boundary_C1_image_coordinate_patch
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (C : BoundaryC1ImageChart S E.Carrier F.map)
    (x : S) (hx : x ∈ C.chart.source)
    (c : SmoothAmbientChart ThreeSphere)
    (hc : E.toSphere (F.map x) ∈ c.chart.source) :
    ∃ V : Set (EuclideanHalfSpace 2), IsOpen V ∧ C.chart x ∈ V ∧
      V ⊆ C.chart.target ∧
      MapsTo (E.toSphere ∘ F.map ∘ C.chart.symm) V c.chart.source ∧
      ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,Euc 3) 1
        (c.chart ∘ E.toSphere ∘ F.map ∘ C.chart.symm) V ∧
      ∀ y ∈ V, Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 3)
        (c.chart ∘ E.toSphere ∘ F.map ∘ C.chart.symm) y) := by
  let V := C.chart.target ∩ (E.toSphere ∘ F.map ∘ C.chart.symm) ⁻¹' c.chart.source
  have hinc : Manifold.IsImmersion (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := by
    let : ChartedSpace (EuclideanHalfSpace 3) T.Carrier := E.charted
    let : IsManifold (𝓡∂ 3) ∞ T.Carrier := E.smooth
    exact E.inclusion.isImmersion
  have hsphere : ContMDiffOn (𝓡∂ 2) (𝓡 3) 1
      (E.toSphere ∘ F.map ∘ C.chart.symm) C.chart.target :=
    (hinc.contMDiff.of_le (by simp)).comp_contMDiffOn C.cOne
  have hV : IsOpen V := hsphere.continuousOn.isOpen_inter_preimage C.target_open c.chart.open_source
  have hxV : C.chart x ∈ V := by
    refine ⟨C.chart.map_source hx,?_⟩
    change E.toSphere (F.map (C.chart.symm (C.chart x))) ∈ c.chart.source
    rwa [C.chart.left_inv hx]
  have hfs : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,Euc 3) 1
      (c.chart ∘ E.toSphere ∘ F.map ∘ C.chart.symm) V :=
    (c.smooth.of_le (by simp)).comp (hsphere.mono inter_subset_left) (fun z hz => hz.2)
  refine ⟨V,hV,hxV,inter_subset_left,fun _ hz => hz.2,hfs,?_⟩
  intro y hy
  have hmd := (C.cOne.contMDiffAt (C.target_open.mem_nhds hy.1)).mdifferentiableAt (by norm_num)
  have hsd := (hsphere.contMDiffAt (C.target_open.mem_nhds hy.1)).mdifferentiableAt (by norm_num)
  have hcd : c.chart.MDifferentiable (𝓡 3) 𝓘(ℝ,Euc 3) :=
    ⟨c.smooth.mdifferentiableOn (by simp),c.inverse_smooth.mdifferentiableOn (by simp)⟩
  have hci := C.differential_injective y hy.1
  rw [mfderivWithin_of_mem_nhds (C.target_open.mem_nhds hy.1)] at hci
  change Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 3)
    (c.chart ∘ E.toSphere ∘ (F.map ∘ C.chart.symm)) y)
  rw [mfderiv_comp _ (hcd.mdifferentiableAt hy.2) hsd,
    mfderiv_comp _ (hinc.contMDiff.mdifferentiable (by simp) _) hmd]
  exact (hcd.mfderiv_injective hy.2).comp
    ((hinc.mfderiv_injective (by simp) _).comp hci)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
