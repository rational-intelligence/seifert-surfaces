import ActualPlanarWholeEmbeddingExtensionV759
import ActualDiskFixedPlanarIsotopyV757

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology Metric
open CompressionActualPlanarWholeDiskExtensionV756
noncomputable section
namespace CompressionActualRelativeRadialSqueezeV765

/-- Continuous radial compression fixes every point of the whole unit disk. -/
def squeeze (a : ℝ) (x : Plane) : Plane :=
  (a + (1-a)/(max 1 ‖x‖)) • x

lemma squeeze_joint_continuous : Continuous (fun p : ℝ × Plane => squeeze p.1 p.2) := by
  have hm : Continuous (fun p : ℝ × Plane => max (1:ℝ) ‖p.2‖) :=
    continuous_const.max continuous_snd.norm
  have hne (p : ℝ × Plane) : max (1:ℝ) ‖p.2‖ ≠ 0 :=
    ne_of_gt ((show (0:ℝ)<1 by norm_num).trans_le (le_max_left _ _))
  have hc : Continuous (fun p : ℝ × Plane => p.1 + (1-p.1)/(max 1 ‖p.2‖)) :=
    continuous_fst.add ((continuous_const.sub continuous_fst).div hm hne)
  exact hc.smul continuous_snd

lemma squeeze_fixed (a : ℝ) (x : Plane) (hx : ‖x‖ ≤ 1) : squeeze a x = x := by
  simp only [squeeze,max_eq_left hx,div_one]
  convert one_smul ℝ x using 2
  ring

lemma squeeze_norm_outer (a : ℝ) (ha : 0 < a) (x : Plane) (hx : 1 ≤ ‖x‖) :
    ‖squeeze a x‖ = 1+a*(‖x‖-1) := by
  have hn : 0 < ‖x‖ := lt_of_lt_of_le (by norm_num) hx
  have hc : 0 < a + (1-a)/‖x‖ := by
    apply (mul_pos_iff_of_pos_right hn).mp
    have he : (a+(1-a)/‖x‖)*‖x‖ = 1+a*(‖x‖-1) := by
      field_simp
      ring
    rw [he]
    have hp : 0 ≤ a*(‖x‖-1) := mul_nonneg ha.le (sub_nonneg.mpr hx)
    linarith
  simp only [squeeze,max_eq_right hx,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  field_simp
  ring

lemma squeeze_injective (a : ℝ) (ha : 0 < a) : Function.Injective (squeeze a) := by
  intro x y he
  have hn : ‖x‖ = ‖y‖ := by
    have hh := congrArg norm he
    by_cases hx : ‖x‖ ≤ 1 <;> by_cases hy : ‖y‖ ≤ 1
    · simpa only [squeeze_fixed a x hx,squeeze_fixed a y hy] using hh
    · rw [squeeze_fixed a x hx,squeeze_norm_outer a ha y (le_of_not_ge hy)] at hh
      nlinarith [lt_of_not_ge hy]
    · rw [squeeze_norm_outer a ha x (le_of_not_ge hx),squeeze_fixed a y hy] at hh
      nlinarith [lt_of_not_ge hx]
    · rw [squeeze_norm_outer a ha x (le_of_not_ge hx),
        squeeze_norm_outer a ha y (le_of_not_ge hy)] at hh
      nlinarith
  have hc : a + (1-a)/(max 1 ‖x‖) ≠ 0 := by
    by_cases hx : ‖x‖ ≤ 1
    · rw [max_eq_left hx,div_one]
      linarith
    · rw [max_eq_right (le_of_not_ge hx)]
      have hr : 0 < ‖x‖ := lt_trans (by norm_num) (lt_of_not_ge hx)
      intro h
      have hm := congrArg (fun z : ℝ => z*‖x‖) h
      simp only [zero_mul] at hm
      have hmul : (a + (1-a)/‖x‖)*‖x‖ = 1+a*(‖x‖-1) := by
        field_simp
        ring
      rw [hmul] at hm
      nlinarith [mul_pos ha (sub_pos.mpr (lt_of_not_ge hx))]
  dsimp only [squeeze] at he
  rw [← hn] at he
  have hh := congrArg (fun z : Plane => (a + (1-a)/(max 1 ‖x‖))⁻¹ • z) he
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hh

lemma squeeze_norm_le (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (x : Plane) :
    ‖squeeze a x‖ ≤ ‖x‖ := by
  by_cases hx : ‖x‖ ≤ 1
  · rw [squeeze_fixed a x hx]
  · rw [squeeze_norm_outer a ha x (le_of_not_ge hx)]
    nlinarith [lt_of_not_ge hx]

lemma squeeze_one (x : Plane) : squeeze 1 x = x := by simp [squeeze]

end CompressionActualRelativeRadialSqueezeV765
