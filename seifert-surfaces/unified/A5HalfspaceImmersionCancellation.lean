import A5BoundaryTransitionV466

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- A continuous lift through a smooth regular half-space immersion has
the regularity of its image, on an arbitrary relative source set. This
includes closed corner pieces and prisms and does not require neatness. -/
theorem halfspace_immersion_cancel_on_relative_source
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (g : Euc 2 → Euc 3) (q : X → Euc 2) (A : Set X) (x : X) (hx : x ∈ A)
    (U : Set (Euc 2)) (hU : IsOpen U) (hqx : q x ∈ U)
    (hqrange : q x ∈ range (𝓡∂ 2))
    (hg : ContDiffOn ℝ ∞ g (U ∩ range (𝓡∂ 2)))
    (hinj : Function.Injective (fderivWithin ℝ g (range (𝓡∂ 2)) (q x)))
    (hq : ContinuousWithinAt q A x)
    (hqmap : ∀ᶠ y in 𝓝[A] x, q y ∈ range (𝓡∂ 2))
    (n : ℕ∞ω) (hn : n ≤ ∞) (himage : ContDiffWithinAt ℝ n (g ∘ q) A x) :
    ContDiffWithinAt ℝ n q A x := by
  obtain ⟨G, hG, hGg⟩ :=
    SeifertSurfaces.OriginalEndpoints.A7Support.exists_contDiff_extension_halfspace_local hU hg hqx
  have hud := (𝓡∂ 2).uniqueDiffOn (q x) hqrange
  have hGeq : fderiv ℝ G (q x) = fderivWithin ℝ g (range (𝓡∂ 2)) (q x) := by
    rw [← fderivWithin_eq_fderiv hud (hG.differentiable (by simp) _)]
    exact hGg.fderivWithin_eq_of_mem hqrange
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (show Function.Injective (fderiv ℝ G (q x)) by rwa [hGeq])
  have hLD : HasFDerivAt (L ∘ G)
      (ContinuousLinearEquiv.refl ℝ (Euc 2) : Euc 2 →L[ℝ] Euc 2) (q x) := by
    have hd := L.hasFDerivAt.comp (q x) (hG.differentiable (by simp) _).hasFDerivAt
    have he : L.comp (fderiv ℝ G (q x)) =
        (ContinuousLinearEquiv.refl ℝ (Euc 2) : Euc 2 →L[ℝ] Euc 2) := by
      apply ContinuousLinearMap.ext
      intro v
      exact hL v
    simpa only [he] using hd
  have hLG : ContDiffAt ℝ ∞ (L ∘ G) (q x) := L.contDiff.contDiffAt.comp _ hG.contDiffAt
  have hqt : Tendsto q (𝓝[A] x) (𝓝[range (𝓡∂ 2)] (q x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq, hqmap⟩
  have hGqgq : G ∘ q =ᶠ[𝓝[A] x] g ∘ q := hGg.comp_tendsto hqt
  have hLGq : ContDiffWithinAt ℝ n (L ∘ G ∘ q) A x :=
    L.contDiff.contDiffAt.comp_contDiffWithinAt x
      (himage.congr_of_eventuallyEq_of_mem hGqgq hx)
  have hinv := hLG.to_localInverse hLD (by simp)
  have hleft := (hLG.hasStrictFDerivAt' hLD (by simp)).eventually_left_inverse
  have heq : ((hLG.localInverse hLD (by simp)) ∘ (L ∘ G ∘ q)) =ᶠ[𝓝[A] x] q :=
    hq.eventually hleft
  exact (((hinv.of_le hn).comp_contDiffWithinAt x hLGq)).congr_of_eventuallyEq_of_mem heq.symm hx

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
