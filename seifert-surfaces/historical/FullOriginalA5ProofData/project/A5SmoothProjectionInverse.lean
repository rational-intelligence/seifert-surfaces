import A5NativeMinimalGraph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

set_option autoImplicit false
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates

/-- A continuous inverse section of a smooth transverse projection is
automatically smooth with invertible derivative on the actual open region. -/
theorem smooth_regular_continuous_inverse_section
    (Q κ : E2 → E2) (Ω U : Set E2) (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hQregular : ∀ y ∈ Ω, Function.Bijective (fderiv ℝ Q y))
    (hκ : ContinuousOn κ U) (hκimage : MapsTo κ U Ω)
    (hsection : ∀ x ∈ U, Q (κ x) = x) :
    ContDiffOn ℝ ∞ κ U ∧ ∀ x ∈ U, Function.Bijective (fderiv ℝ κ x) := by
  have hκsmooth (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ κ x := by
    have hq := hQ.contDiffAt (hΩ.mem_nhds (hκimage hx))
    let A : E2 ≃L[ℝ] E2 := ContinuousLinearEquiv.ofBijective (fderiv ℝ Q (κ x))
      (LinearMap.ker_eq_bot.mpr (hQregular _ (hκimage hx)).1)
      (LinearMap.range_eq_top.mpr (hQregular _ (hκimage hx)).2)
    have hd : HasFDerivAt Q (A : E2 →L[ℝ] E2) (κ x) :=
      (hq.differentiableAt (by simp)).hasFDerivAt
    let e := hq.toOpenPartialHomeomorph Q hd (by simp)
    have he : κ x ∈ e.source := hq.mem_toOpenPartialHomeomorph_source hd (by simp)
    have hnear : κ ⁻¹' e.source ∈ 𝓝 x :=
      (hκ.continuousAt (hU.mem_nhds hx)).preimage_mem_nhds (e.open_source.mem_nhds he)
    have heq : κ =ᶠ[𝓝 x] e.symm := by
      filter_upwards [hU.mem_nhds hx, hnear] with y hy hey
      have hleft := e.left_inv hey
      change e.symm (Q (κ y)) = κ y at hleft
      rw [hsection y hy] at hleft
      exact hleft.symm
    have hinv : ContDiffAt ℝ ∞ e.symm x := by
      rw [← hsection x hx]
      exact hq.to_localInverse hd (by simp)
    exact hinv.congr_of_eventuallyEq heq
  refine ⟨fun x hx => (hκsmooth x hx).contDiffWithinAt, ?_⟩
  intro x hx
  have heq : Q ∘ κ =ᶠ[𝓝 x] id := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hsection y hy
  have hchain : (fderiv ℝ Q (κ x)).comp (fderiv ℝ κ x) =
      ContinuousLinearMap.id ℝ E2 := by
    rw [← fderiv_comp x
      ((hQ.contDiffAt (hΩ.mem_nhds (hκimage hx))).differentiableAt (by simp))
      ((hκsmooth x hx).differentiableAt (by simp)), heq.fderiv_eq, fderiv_id]
  have hinj : Function.Injective (fderiv ℝ κ x) := by
    intro v w hvw
    have hv := congrArg (fun L : E2 →L[ℝ] E2 => L v) hchain
    have hw := congrArg (fun L : E2 →L[ℝ] E2 => L w) hchain
    exact hv.symm.trans ((congrArg (fderiv ℝ Q (κ x)) hvw).trans hw)
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
