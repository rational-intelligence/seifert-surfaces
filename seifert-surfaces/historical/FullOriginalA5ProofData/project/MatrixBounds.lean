import ProviderBridgeData

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff Matrix
namespace SeifertSurfaces.QuasilinearProviderBridge.Helpers
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

lemma matrixAction_norm_le_of_entries (A : Matrix (Fin 3) (Fin 3) ℝ)
    (E : ℝ) (hE : 0 ≤ E) (hA : ∀ i j, |A i j| ≤ E) (ξ : E3) :
    ‖matrixAction A ξ‖ ≤ 3 * E * ‖ξ‖ := by
  have he (i j : Fin 3) : A i j ^ 2 ≤ E ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hE).mpr (hA i j)
  have hrow (i : Fin 3) : (matrixAction A ξ i) ^ 2 ≤ 3 * E ^ 2 * ‖ξ‖ ^ 2 := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
      (fun j => A i j) (fun j => ξ j)
    have he' : (∑ j : Fin 3, A i j ^ 2) ≤ 3 * E ^ 2 := by
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => he i j)
    have hc' : (matrixAction A ξ i) ^ 2 ≤ (∑ j : Fin 3, A i j ^ 2) * ‖ξ‖ ^ 2 := by
      simpa only [matrixAction, WithLp.ofLp_toLp, PiLp.toLp_apply, Matrix.mulVec,
        dotProduct, EuclideanSpace.real_norm_sq_eq, Real.norm_eq_abs, sq_abs] using hc
    exact hc'.trans (mul_le_mul_of_nonneg_right he' (sq_nonneg ‖ξ‖))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 3 * E * ‖ξ‖)).mp
  calc
    ‖matrixAction A ξ‖ ^ 2 = ∑ i : Fin 3, (matrixAction A ξ i) ^ 2 :=
      EuclideanSpace.real_norm_sq_eq _
    _ ≤ ∑ _i : Fin 3, 3 * E ^ 2 * ‖ξ‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = (3 * E * ‖ξ‖) ^ 2 := by simp; ring

lemma matrixAction_smul (c : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) (ξ : E3) :
    matrixAction (c • A) ξ = c • matrixAction A ξ := by
  ext i
  simp [matrixAction, Matrix.smul_mulVec]

lemma norm_sq_planarPart (ξ : E3) : ‖ξ‖ ^ 2 = ‖planarPart ξ‖ ^ 2 + (ξ 2) ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, planarPart]
  ring

end SeifertSurfaces.QuasilinearProviderBridge.Helpers
