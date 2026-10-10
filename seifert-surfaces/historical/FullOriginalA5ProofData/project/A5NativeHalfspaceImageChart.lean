import A5NativeAmbientLift

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u

/-- Smooth regular coordinates on an actual half-space source give the
literal native image chart into the exterior. No smoothness of the auxiliary
source coordinate homeomorphism is assumed. -/
theorem native_halfspace_image_chart_of_coordinate_parametrization
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (e : PartialHomeomorph S (EuclideanHalfSpace 2))
    (hes : IsOpen e.source) (het : IsOpen e.target)
    (hb : e '' (S.boundary ∩ e.source) =
      ((𝓡∂ 2).boundary (EuclideanHalfSpace 2)) ∩ e.target)
    (c : SmoothAmbientChart ThreeSphere)
    (hchart : MapsTo (E.toSphere ∘ F.map ∘ e.symm) e.target c.chart.source)
    (hsmooth : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,Euc 3) ∞
      (c.chart ∘ E.toSphere ∘ F.map ∘ e.symm) e.target)
    (hrank : ∀ y ∈ e.target, Function.Injective
      (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 3) (c.chart ∘ E.toSphere ∘ F.map ∘ e.symm) y)) :
    ∃ C : SmoothImageChart S F.map, C.chart = e := by
  let f := F.map ∘ e.symm
  have hinc : Manifold.IsImmersion (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := by
    let : ChartedSpace (EuclideanHalfSpace 3) T.Carrier := E.charted
    let : IsManifold (𝓡∂ 3) ∞ T.Carrier := E.smooth
    exact E.inclusion.isImmersion
  have hsphere : ContMDiffOn (𝓡∂ 2) (𝓡 3) ∞ (E.toSphere ∘ f) e.target := by
    have h := c.inverse_smooth.comp hsmooth (fun y hy => c.chart.map_source (hchart hy))
    apply h.congr
    intro y hy
    exact (c.chart.left_inv (hchart hy)).symm
  have hf : ContMDiffOn (𝓡∂ 2) (𝓡∂ 3) ∞ f e.target := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply (ContMDiffAt.iff_comp_isImmersionAt (hinc.isImmersionAt (f y))).mpr
    exact ⟨F.map.continuous.continuousAt.comp
        (e.symm.continuousOn.continuousAt (het.mem_nhds hy)),
      hsphere.contMDiffAt (het.mem_nhds hy)⟩
  refine ⟨⟨e,hes,het,hf,?_,hb⟩,rfl⟩
  intro y hy
  have hfd := (hf.contMDiffAt (het.mem_nhds hy)).mdifferentiableAt (by simp)
  have hsd := (hsphere.contMDiffAt (het.mem_nhds hy)).mdifferentiableAt (by simp)
  have hcd := (c.smooth.contMDiffAt
    (c.chart.open_source.mem_nhds (hchart hy))).mdifferentiableAt (by simp)
  have hi := hrank y hy
  change Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 3) (c.chart ∘ E.toSphere ∘ f) y) at hi
  rw [mfderiv_comp y hcd hsd,
    mfderiv_comp y (hinc.contMDiff.mdifferentiable (by simp) _) hfd] at hi
  rw [mfderivWithin_of_mem_nhds (het.mem_nhds hy)]
  exact Function.Injective.of_comp (Function.Injective.of_comp hi)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
