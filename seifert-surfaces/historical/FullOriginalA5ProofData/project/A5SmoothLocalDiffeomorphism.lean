import A5SmoothProjectionInverse

set_option autoImplicit false
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates

/-- A local inverse with smoothness and invertible derivatives at every
point of its actual source and target, produced by shrinking the inverse
function theorem neighborhood inside the original smooth domain. -/
theorem smooth_local_diffeomorphism_of_regular_map
    (Q : E2 → E2) (U : Set E2) (hU : IsOpen U)
    (hQ : ContDiffOn ℝ ∞ Q U) (x : E2) (hx : x ∈ U)
    (hrank : Function.Bijective (fderiv ℝ Q x)) :
    ∃ e : OpenPartialHomeomorph E2 E2,
      (e : E2 → E2) = Q ∧ x ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ (e : E2 → E2) e.source ∧
      ContDiffOn ℝ ∞ (e.symm : E2 → E2) e.target ∧
      (∀ z ∈ e.source, Function.Bijective (fderiv ℝ (e : E2 → E2) z)) ∧
      ∀ z ∈ e.target, Function.Bijective (fderiv ℝ (e.symm : E2 → E2) z) := by
  let A : E2 ≃L[ℝ] E2 := ContinuousLinearEquiv.ofBijective (fderiv ℝ Q x)
    (LinearMap.ker_eq_bot.mpr hrank.1) (LinearMap.range_eq_top.mpr hrank.2)
  have hqx := hQ.contDiffAt (hU.mem_nhds hx)
  have hd : HasFDerivAt Q (A : E2 →L[ℝ] E2) x :=
    (hqx.differentiableAt (by simp)).hasFDerivAt
  let e₀ := hqx.toOpenPartialHomeomorph Q hd (by simp)
  let V := U ∩ {y | (fderiv ℝ Q y).IsInvertible}
  have hV : IsOpen V :=
    (hQ.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage hU
      ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hxV : x ∈ V := ⟨hx, A, rfl⟩
  let e := e₀.restrOpen V hV
  have hex : x ∈ e.source :=
    ⟨hqx.mem_toOpenPartialHomeomorph_source hd (by simp), hxV⟩
  have heU : e.source ⊆ U := fun y hy => hy.2.1
  have heQ : (e : E2 → E2) = Q := rfl
  have heC : ContDiffOn ℝ ∞ (e : E2 → E2) e.source := hQ.mono heU
  have heR (z : E2) (hz : z ∈ e.source) :
      Function.Bijective (fderiv ℝ (e : E2 → E2) z) := by
    obtain ⟨B, hB⟩ := hz.2.2
    change Function.Bijective (fderiv ℝ Q z)
    rw [← hB]
    exact B.bijective
  obtain ⟨hi, hir⟩ := smooth_regular_continuous_inverse_section (e : E2 → E2)
    e.symm e.source e.target e.open_source e.open_target heC heR
    e.symm.continuousOn e.symm.mapsTo (fun z hz => e.right_inv hz)
  exact ⟨e, heQ, hex, heU, heC, hi, heR, hir⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
