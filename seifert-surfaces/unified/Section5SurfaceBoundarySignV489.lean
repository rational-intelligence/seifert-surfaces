import Section5SurfaceCoordinateDataV489
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
open SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates
universe u v
variable {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]
  {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (𝓡∂ 2) ∞ M]

theorem surface_coordinate_extension_boundary_zero {f : S → M}
    (hf : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ f)
    (hboundary : ∀ y, y ∈ (𝓡∂ 2).boundary S → f y ∈ (𝓡∂ 2).boundary M)
    (x : S) {g : E2 → E2}
    (hge : g =ᶠ[𝓝[range (𝓡∂ 2)] (extChartAt (𝓡∂ 2) x x)]
      ((extChartAt (𝓡∂ 2) (f x)) ∘ f ∘ (extChartAt (𝓡∂ 2) x).symm)) :
    ∀ᶠ z : E2 in 𝓝 (extChartAt (𝓡∂ 2) x x), z 0 = 0 → g z 0 = 0 := by
  let e := extChartAt (𝓡∂ 2) x
  let a := e x
  let d := chartAt (EuclideanHalfSpace 2) (f x)
  have heT : Tendsto e.symm (𝓝[range (𝓡∂ 2)] a) (𝓝 x) := by
    have ht := (contMDiffWithinAt_extChartAt_symm_range (I := 𝓡∂ 2) (n := ∞) x
      (mem_extChartAt_target x)).continuousWithinAt.tendsto
    have he : e.symm a = x := e.left_inv (mem_extChartAt_source x)
    change Tendsto e.symm (𝓝[range (𝓡∂ 2)] a) (𝓝 (e.symm a)) at ht
    rwa [he] at ht
  have hdf : ∀ᶠ z in 𝓝[range (𝓡∂ 2)] a, f (e.symm z) ∈ d.source :=
    (hf.continuous.continuousAt.tendsto.comp heT).eventually
      (d.open_source.mem_nhds (mem_chart_source _ _))
  have hct : ∀ᶠ z in 𝓝[range (𝓡∂ 2)] a, z ∈ e.target := extChartAt_target_mem_nhdsWithin x
  filter_upwards [eventually_nhdsWithin_iff.1 hge,eventually_nhdsWithin_iff.1 hdf,
    eventually_nhdsWithin_iff.1 hct] with z hgez hdz hcz
  intro hz0
  have hr : z ∈ range (𝓡∂ 2) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ z 0
    rw [hz0]
  have hzt := hcz hr
  have hys : e.symm z ∈ (chartAt (EuclideanHalfSpace 2) x).source := by
    have hs := e.map_target hzt
    simpa only [e,extChartAt_source] using hs
  have hyb : e.symm z ∈ (𝓡∂ 2).boundary S := by
    apply (chart_boundary_coordinate_iff x (e.symm z) hys).2
    change e (e.symm z) 0 = 0
    rw [e.right_inv hzt,hz0]
  have hfy := (chart_boundary_coordinate_iff (f x) (f (e.symm z)) (hdz hr)).1
    (hboundary _ hyb)
  have hge' := hgez hr
  change g z = (extChartAt (𝓡∂ 2) (f x)) (f (e.symm z)) at hge'
  rw [hge']
  exact hfy

theorem surface_coordinate_extension_boundary_sign {f : S → M}
    (hf : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ f)
    (hboundary : ∀ y, y ∈ (𝓡∂ 2).boundary S → f y ∈ (𝓡∂ 2).boundary M)
    (x : S) (hx : x ∈ (𝓡∂ 2).boundary S) {g : E2 → E2}
    (hg : ContDiff ℝ ∞ g)
    (hge : g =ᶠ[𝓝[range (𝓡∂ 2)] (extChartAt (𝓡∂ 2) x x)]
      ((extChartAt (𝓡∂ 2) (f x)) ∘ f ∘ (extChartAt (𝓡∂ 2) x).symm))
    (hd : HasFDerivAt g (surfaceCoordinateDifferential f x) (extChartAt (𝓡∂ 2) x x))
    {c : ℝ} (hc : 0 < c)
    (hrow : ∀ z : E2, surfaceCoordinateDifferential f x z 0 = c * z 0) :
    ∀ᶠ z : E2 in 𝓝 (extChartAt (𝓡∂ 2) x x), 0 ≤ g z 0 ↔ 0 ≤ z 0 := by
  have ha : (extChartAt (𝓡∂ 2) x x) 0 = 0 :=
    (chart_boundary_coordinate_iff x x (mem_chart_source _ _)).1 hx
  let p : E2 →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hD : p.comp (surfaceCoordinateDifferential f x) =
      c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) := by
    apply ContinuousLinearMap.ext
    intro z
    exact hrow z
  have hdq : HasFDerivAt (fun z : E2 => g z 0)
      (c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2))
      (extChartAt (𝓡∂ 2) x x) := by
    convert (by simpa only [hD] using
      p.hasFDerivAt.comp (extChartAt (𝓡∂ 2) x x) hd) using 1 <;> rfl
  apply halfspace_sign_of_strict_derivative ha hc
    ((p.contDiff.comp hg).contDiffAt.hasStrictFDerivAt' hdq (by simp))
  exact surface_coordinate_extension_boundary_zero hf hboundary x hge

end SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
