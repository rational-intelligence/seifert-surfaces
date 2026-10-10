import NativeMetricSectionProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

def seamMetricOrthogonalOutward (B : Euc 2 →L[ℝ] Euc 2 →L[ℝ] ℝ) (e m : Euc 2) : Euc 2 :=
  (B m e / B e e) • e - m

def seamMetricUnitOutward (B : Euc 2 →L[ℝ] Euc 2 →L[ℝ] ℝ) (e m : Euc 2) : Euc 2 :=
  let n := seamMetricOrthogonalOutward B e m
  (Real.sqrt (B n n))⁻¹ • n

/-- Metric Gram--Schmidt on the actual inward straight-sector frame gives
a unique-sign unit source vector orthogonal to its boundary tangent. -/
theorem seam_metric_unit_outward_properties
    (B : Euc 2 →L[ℝ] Euc 2 →L[ℝ] ℝ) (e m : Euc 2)
    (hpos : ∀ v : Euc 2, v ≠ 0 → 0 < B v v)
    (he : ‖e‖ = 1) (hm : ‖m‖ = 1) (hem : inner ℝ e m = 0) :
    B (seamMetricUnitOutward B e m) (seamMetricUnitOutward B e m) = 1 ∧
      B (seamMetricUnitOutward B e m) e = 0 ∧
      inner ℝ m (seamMetricUnitOutward B e m) < 0 := by
  let n := seamMetricOrthogonalOutward B e m
  have hme : inner ℝ m e = 0 := by rw [real_inner_comm, hem]
  have hninner : inner ℝ m n = -1 := by
    dsimp [n, seamMetricOrthogonalOutward]
    rw [inner_sub_right, inner_smul_right, hme, mul_zero,
      real_inner_self_eq_norm_sq, hm, one_pow]
    norm_num
  have hn : n ≠ 0 := by
    intro h
    rw [h, inner_zero_right] at hninner
    norm_num at hninner
  have hen : e ≠ 0 := by intro hz; simpa [hz] using he
  have hepos := hpos e hen
  have hnpos := hpos n hn
  have hne : B n e = 0 := by
    dsimp [n, seamMetricOrthogonalOutward]
    simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ hepos.ne')
  let d := Real.sqrt (B n n)
  have hd : 0 < d := Real.sqrt_pos.mpr hnpos
  have hd2 : d ^ 2 = B n n := Real.sq_sqrt hnpos.le
  change B (d⁻¹ • n) (d⁻¹ • n) = 1 ∧ B (d⁻¹ • n) e = 0 ∧ inner ℝ m (d⁻¹ • n) < 0
  refine ⟨?_, ?_, ?_⟩
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [← hd2]
    field_simp [hd.ne']
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hne, mul_zero]
  · rw [inner_smul_right, hninner]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hd) (by norm_num)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
