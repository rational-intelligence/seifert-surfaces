import A7NativeBoundaryCovectorV464
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u v w
variable {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]
  {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
  {N : Type w} [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ,E3) ∞ N]

theorem collar_differential_forces_native_transversality
    {f : S → M} (hf : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ f)
    {i : M → N} (hi : ContMDiff (𝓡∂ 3) 𝓘(ℝ,E3) ∞ i)
    (h : AmbientMetric N) (R : Set N) (C : WarpedBoundaryCollar h R)
    (himage : ∀ y, i y ∈ R)
    (hboundary : ∀ y, i y ∈ frontier R ↔ y ∈ (𝓡∂ 3).boundary M)
    (x : S) (hfxb : f x ∈ (𝓡∂ 3).boundary M)
    (hpx : i (f x) ∈ C.coordinates.chart.source)
    (hdr : (mfderiv 𝓘(ℝ,E3) 𝓘(ℝ) C.radial (i (f x))).comp
      (LinearMap.range (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) (i ∘ f) x).toLinearMap).subtypeL ≠ 0) :
    ∃ v : TangentSpace (𝓡∂ 2) x,
      inwardCoordinate (f x) (mfderiv (𝓡∂ 2) (𝓡∂ 3) f x v) ≠ 0 := by
  by_contra hn
  have hz : ∀ v : TangentSpace (𝓡∂ 2) x,
      inwardCoordinate (f x) (mfderiv (𝓡∂ 2) (𝓡∂ 3) f x v) = 0 := by
    simpa only [not_exists,not_not] using hn
  let q : M → ℝ := C.radial ∘ i
  have hrad : MDifferentiableAt 𝓘(ℝ,E3) 𝓘(ℝ) C.radial (i (f x)) :=
    ((C.radial_smooth _ hpx).contMDiffAt (C.coordinates.chart.open_source.mem_nhds hpx)).mdifferentiableAt (by simp)
  have hq : MDifferentiableAt (𝓡∂ 3) 𝓘(ℝ) q (f x) :=
    hrad.comp (f x) (hi.mdifferentiableAt (by simp))
  have hqx : q (f x) = 0 :=
    (C.boundary_identification _ hpx).1 ((hboundary _).2 hfxb)
  have hmin : ∀ᶠ y in 𝓝 (f x), 0 ≤ q y := by
    have hs : ∀ᶠ y in 𝓝 (f x), i y ∈ C.coordinates.chart.source :=
      hi.continuous.continuousAt.preimage_mem_nhds (C.coordinates.chart.open_source.mem_nhds hpx)
    filter_upwards [hs] with y hy
    exact (C.region_identification _ hy).1 (himage y)
  apply hdr
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨w,hw⟩ := v.property
  change mfderiv 𝓘(ℝ,E3) 𝓘(ℝ) C.radial (i (f x)) v.val = 0
  rw [←hw]
  have hc : mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) (i ∘ f) x =
      (mfderiv (𝓡∂ 3) 𝓘(ℝ,E3) i (f x)).comp (mfderiv (𝓡∂ 2) (𝓡∂ 3) f x) :=
    mfderiv_comp x (hi.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))
  rw [hc]
  have hqchain : mfderiv (𝓡∂ 3) 𝓘(ℝ) q (f x) =
      (mfderiv 𝓘(ℝ,E3) 𝓘(ℝ) C.radial (i (f x))).comp
        (mfderiv (𝓡∂ 3) 𝓘(ℝ,E3) i (f x)) :=
    mfderiv_comp (f x) hrad (hi.mdifferentiableAt (by simp))
  have hzero := boundary_minimum_covector hq hfxb hqx hmin
    (mfderiv (𝓡∂ 2) (𝓡∂ 3) f x w) (hz w)
  rw [hqchain] at hzero
  exact hzero

end SeifertSurfaces.OriginalEndpoints.A7Support
