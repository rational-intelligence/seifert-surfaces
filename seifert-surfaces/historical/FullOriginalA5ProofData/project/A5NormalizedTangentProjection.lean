import A5CommonProjection

set_option autoImplicit false
open Set
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations

/-- A regular two-dimensional tangent in ambient dimension three has an
actual separating projection-height pair normalized to its source jet. -/
theorem rank_two_normalized_projection_with_height
    (D : Euc 2 →L[ℝ] Euc 3) (hD : Function.Injective D) :
    ∃ P : Euc 3 →L[ℝ] Euc 2, ∃ height : Euc 3 →L[ℝ] ℝ,
      Function.Injective (fun z => (P z,height z)) ∧
      ∀ v : Euc 2, P (D v) = v := by
  obtain ⟨P₀,height,hsep,hP₀⟩ := finite_rank_two_common_projection_with_height
    (fun _ : Unit => D) (fun _ => hD)
  let A : Euc 2 ≃L[ℝ] Euc 2 := ContinuousLinearEquiv.ofBijective (P₀.comp D)
    (LinearMap.ker_eq_bot.mpr (hP₀ ()).1) (LinearMap.range_eq_top.mpr (hP₀ ()).2)
  let P := A.symm.toContinuousLinearMap.comp P₀
  refine ⟨P,height,?_,fun v => A.symm_apply_apply v⟩
  intro x y hxy
  apply hsep
  apply Prod.ext
  · have hh := congrArg (fun p : Euc 2 × ℝ => A p.1) hxy
    simpa only [P,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using hh
  · have hh : height x = height y := congrArg (fun p : Euc 2 × ℝ => p.2) hxy
    exact hh

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
