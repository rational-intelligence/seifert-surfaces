import A5ManifoldHalfspaceCancellation

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u v w

/-- A continuous lift into the actual smooth source of a proper embedding
inherits C1 or smooth regularity from its ambient image, including at the
boundary and for arbitrary source corner models. -/
theorem proper_smooth_embedding_lift_contMDiffAt
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    {H₁ : Type*} [TopologicalSpace H₁] (I : ModelWithCorners ℝ E₁ H₁)
    {X : Type u} [TopologicalSpace X] [ChartedSpace H₁ X]
    {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    {S : CompactOrientedSurface.{w}} (f : ProperSmoothEmbedding S M)
    (q : X → S) (x : X) (hq : ContinuousAt q x)
    (n : ℕ∞ω) (hn : n ≤ ∞) (himage : ContMDiffAt I (𝓡∂ 3) n (f.toFun ∘ q) x) :
    ContMDiffAt I (𝓡∂ 2) n q x := by
  let c := chartAt (EuclideanHalfSpace 2) (q x)
  let k := c ∘ q
  let g := f.toFun ∘ c.symm
  have hqx : q x ∈ c.source := mem_chart_source _ _
  have hkx : k x ∈ c.target := c.map_source hqx
  have hkc : ContinuousAt k x := (c.continuousAt hqx).comp hq
  have hg : ContMDiffOn (𝓡∂ 2) (𝓡∂ 3) ∞ g c.target :=
    f.smooth.comp_contMDiffOn contMDiffOn_chart_symm
  have hcd : c.MDifferentiable (𝓡∂ 2) (𝓡∂ 2) :=
    ⟨(contMDiffOn_chart (n := ∞)).mdifferentiableOn (by simp),
      (contMDiffOn_chart_symm (n := ∞)).mdifferentiableOn (by simp)⟩
  have hgk : Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) g (k x)) := by
    rw [mfderiv_comp (k x) (f.smooth.mdifferentiable (by simp) _) (hcd.mdifferentiableAt_symm hkx)]
    exact (f.differential_injective _).comp (hcd.symm.mfderiv_injective hkx)
  have he : g ∘ k =ᶠ[𝓝 x] f.toFun ∘ q := by
    filter_upwards [hq.preimage_mem_nhds (c.open_source.mem_nhds hqx)] with y hy
    change f.toFun (c.symm (c (q y))) = f.toFun (q y)
    rw [c.left_inv hy]
  have hks := contMDiffAt_lift_through_regular_halfspace_map I g c.target c.open_target hg k x
    hkc hkx hgk n hn (himage.congr_of_eventuallyEq he)
  have hqi : q =ᶠ[𝓝 x] c.symm ∘ k := by
    filter_upwards [hq.preimage_mem_nhds (c.open_source.mem_nhds hqx)] with y hy
    exact (c.left_inv hy).symm
  have hci : ContMDiffAt (𝓡∂ 2) (𝓡∂ 2) n c.symm (k x) :=
    (contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds hkx)).of_le hn
  exact (hci.comp x hks).congr_of_eventuallyEq hqi

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
