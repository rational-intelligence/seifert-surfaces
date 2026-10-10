import Section5CylinderProjectionRankV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
noncomputable section
universe u
variable {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]

theorem surface_open_derivative_ne_zero (U : TopologicalSpace.Opens S)
    (x : U) {r : S → ℝ} (hr : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ) r x.val)
    (hn : mfderiv (𝓡∂ 2) 𝓘(ℝ) r x.val ≠ 0) :
    mfderiv (𝓡∂ 2) 𝓘(ℝ) (r ∘ Subtype.val : U → ℝ) x ≠ 0 := by
  obtain ⟨inc,hinc,hincs,_⟩ := surface_open_inclusion U ⟨x⟩
  have hsurj : Surjective (mfderiv (𝓡∂ 2) (𝓡∂ 2) (Subtype.val : U → S) x) := by
    let hh := (inc.isLocalDiffeomorphAt (𝓡∂ 2) (𝓡∂ 2) ∞ (hincs ▸ mem_univ x)).mfderivToContinuousLinearEquiv (by simp)
    have hi : Surjective (mfderiv (𝓡∂ 2) (𝓡∂ 2) inc x) := by
      simpa only [hh,IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv] using! hh.surjective
    have he : (inc : U → S) = Subtype.val := funext hinc
    rwa [he] at hi
  intro hz
  apply hn
  rw [mfderiv_comp x hr (contMDiff_subtype_val.mdifferentiableAt (n:=∞) (by simp))] at hz
  ext v
  obtain ⟨w,hw⟩ := hsurj v
  have hh := congrArg (fun d => d w) hz
  change mfderiv (𝓡∂ 2) 𝓘(ℝ) r x.val
    (mfderiv (𝓡∂ 2) (𝓡∂ 2) (Subtype.val : U → S) x w) = 0 at hh
  rwa [hw] at hh

#print axioms surface_open_derivative_ne_zero
end
end SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
