import FrozenLoadBounded

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder

set_option maxHeartbeats 3000000

lemma frozenForm_eq_inner (A : Mat) (Ω : Set V) (p q : H01Space Ω) :
    frozenForm A Ω (p, q) = inner ℝ
      ((matrixActionLinear A).compLp (pairGradientLinear Ω p))
      (pairGradientLinear Ω q) := by
  unfold frozenForm
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(matrixActionLinear A).coeFn_compLp (pairGradientLinear Ω p)] with x hx
  rw [hx]
  rfl

lemma frozenForm_bounded (A : Mat) (Ω : Set V) :
    IsBoundedBilinearMap ℝ (frozenForm A Ω) := by
  let P := pairGradientLinear Ω
  let M := ((matrixActionLinear A).compLpL 2 (volume.restrict Ω)).comp P
  refine { add_left := ?_, smul_left := ?_, add_right := ?_, smul_right := ?_, bound := ?_ }
  · intro p₁ p₂ q
    simp only [frozenForm_eq_inner]
    change inner ℝ (M (p₁ + p₂)) (P q) = inner ℝ (M p₁) (P q) + inner ℝ (M p₂) (P q)
    rw [map_add, inner_add_left]
  · intro c p q
    simp only [frozenForm_eq_inner]
    change inner ℝ (M (c • p)) (P q) = c • inner ℝ (M p) (P q)
    rw [map_smul, real_inner_smul_left]
    rfl
  · intro p q₁ q₂
    simp only [frozenForm_eq_inner]
    change inner ℝ (M p) (P (q₁ + q₂)) = inner ℝ (M p) (P q₁) + inner ℝ (M p) (P q₂)
    rw [map_add, inner_add_right]
  · intro c p q
    simp only [frozenForm_eq_inner]
    change inner ℝ (M p) (P (c • q)) = c • inner ℝ (M p) (P q)
    rw [map_smul, inner_smul_right]
    rfl
  · refine ⟨1 + ‖M‖ * ‖P‖, by positivity, ?_⟩
    intro p q
    rw [frozenForm_eq_inner]
    change ‖inner ℝ (M p) (P q)‖ ≤ (1 + ‖M‖ * ‖P‖) * ‖p‖ * ‖q‖
    calc
      _ ≤ ‖M p‖ * ‖P q‖ := norm_inner_le_norm _ _
      _ ≤ (‖M‖ * ‖p‖) * (‖P‖ * ‖q‖) := mul_le_mul (M.le_opNorm _) (P.le_opNorm _)
        (norm_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith [norm_nonneg p, norm_nonneg q]

end SeifertSurfaces.WeakSchauder
