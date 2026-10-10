import NativeBoundaryHolderOperations
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

/-- A closed convex native set has an actual nonexpansive retraction. -/
theorem native_closed_convex_lipschitz_retraction
    (K : Set E2) (hK : IsClosed K) (hc : Convex ℝ K) (hne : K.Nonempty) :
    ∃ P : E2 → E2, (∀ x, P x ∈ K) ∧ EqOn P id K ∧ LipschitzWith 1 P := by
  have hex := exists_norm_eq_iInf_of_complete_convex hne hK.isComplete hc
  choose P hP hmin using hex
  have hchar (x : E2) : ∀ y ∈ K, inner ℝ (x - P x) (y - P x) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hc (hP x)).mp (hmin x)
  refine ⟨P, hP, ?_, ?_⟩
  · intro x hx
    have hh := hchar x x hx
    rw [real_inner_self_eq_norm_sq] at hh
    have hz : ‖x - P x‖ = 0 := by nlinarith [norm_nonneg (x - P x)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hx := hchar x (P y) (hP y)
    have hy := hchar y (P x) (hP x)
    have hq : ‖P x - P y‖ ^ 2 ≤ inner ℝ (x - y) (P x - P y) := by
      rw [show P y - P x = -(P x - P y) by abel, inner_neg_right, inner_sub_left] at hx
      rw [inner_sub_left] at hy
      rw [inner_sub_left]
      have he : inner ℝ (P x) (P x - P y) - inner ℝ (P y) (P x - P y) = ‖P x - P y‖ ^ 2 := by
        rw [← inner_sub_left, real_inner_self_eq_norm_sq]
      linarith
    have hcs := real_inner_le_norm (x - y) (P x - P y)
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    by_cases hz : ‖P x - P y‖ = 0
    · rw [hz]; positivity
    · have hp : 0 < ‖P x - P y‖ := (norm_nonneg _).lt_of_ne' hz
      nlinarith

/-- Holder coefficients on a closed convex cap extend by the SAME values
at the retracted point, preserving all pointwise ellipticity and bounds. -/
theorem native_holder_matrix_extension
    (K : Set E2) (hK : IsClosed K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (a : E2 → Matrix (Fin 2) (Fin 2) ℝ) (H α : ℝ≥0) (κ M : ℝ)
    (hholder : ∀ i j, HolderOnWith H α (fun x => a x i j) K)
    (hbound : ∀ x ∈ K, ∀ ξ : E2,
      κ * ‖ξ‖ ^ 2 ≤ inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (a x) ξ) ξ ∧
        ∀ i j, |a x i j| ≤ M) :
    ∃ A : E2 → Matrix (Fin 2) (Fin 2) ℝ, EqOn A a K ∧
      (∀ i j, HolderWith H α (fun x => A x i j)) ∧
      (∀ x : E2, ∀ ξ : E2,
        κ * ‖ξ‖ ^ 2 ≤ inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (A x) ξ) ξ ∧
          ∀ i j, |A x i j| ≤ M) := by
  obtain ⟨P, hP, heq, hL⟩ := native_closed_convex_lipschitz_retraction K hK hc hne
  refine ⟨fun x => a (P x), ?_, ?_, ?_⟩
  · intro x hx
    change a (P x) = a x
    rw [heq hx, id_eq]
  · intro i j
    have hh := (hholder i j).comp_holderWith hL.holderWith hP
    convert hh using 1 <;> simp [Function.comp_def]
  · intro x ξ
    exact hbound (P x) (hP x) ξ

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
