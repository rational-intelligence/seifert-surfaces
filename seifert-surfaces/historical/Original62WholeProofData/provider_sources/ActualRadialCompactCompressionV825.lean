import ActualCompactlySupportedContinuousBijectionV823

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology Metric
open CompressionActualCompactlySupportedContinuousBijectionV823
noncomputable section
namespace CompressionActualRadialCompactCompressionV825
abbrev Plane := Schoenflies.Plane

def coefficient (r s a u : ℝ) : ℝ :=
  a + (1-a) * min 1 (max 0 ((u-r)/(s-r)))

def radial (r s a : ℝ) (x : Plane) : Plane := coefficient r s a ‖x‖ • x

lemma coefficient_continuous (r s : ℝ) :
    Continuous (fun p : ℝ × ℝ => coefficient r s p.1 p.2) := by
  unfold coefficient
  fun_prop

lemma coefficient_bounds (r s a u : ℝ) (_ha : 0 < a) (ha1 : a ≤ 1) :
    a ≤ coefficient r s a u ∧ coefficient r s a u ≤ 1 := by
  have hn : 0 ≤ min 1 (max 0 ((u-r)/(s-r))) := le_min (by norm_num) (le_max_left _ _)
  have h1 : min 1 (max 0 ((u-r)/(s-r))) ≤ 1 := min_le_left _ _
  dsimp [coefficient]
  constructor <;> nlinarith

lemma coefficient_inner (r s a u : ℝ) (hrs : r < s) (hu : u ≤ r) :
    coefficient r s a u = a := by
  have hn : (u-r)/(s-r) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  simp [coefficient,max_eq_left hn]

lemma coefficient_outer (r s a u : ℝ) (hrs : r < s) (hu : s ≤ u) :
    coefficient r s a u = 1 := by
  have hn : 1 ≤ (u-r)/(s-r) := (le_div_iff₀ (by linarith)).mpr (by linarith)
  rw [coefficient,max_eq_right (by linarith),min_eq_left hn]
  ring

lemma coefficient_monotone (r s a : ℝ) (hrs : r < s) (ha1 : a ≤ 1) :
    Monotone (coefficient r s a) := by
  intro u v huv
  dsimp [coefficient]
  gcongr

lemma radial_joint_continuous (r s : ℝ) : Continuous (fun p : ℝ × Plane => radial r s p.1 p.2) :=
  (coefficient_continuous r s |>.comp (continuous_fst.prodMk continuous_snd.norm)).smul continuous_snd

lemma radial_norm (r s a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (x : Plane) :
    ‖radial r s a x‖ = coefficient r s a ‖x‖ * ‖x‖ := by
  rw [radial,norm_smul,Real.norm_eq_abs,abs_of_pos (ha.trans_le (coefficient_bounds r s a ‖x‖ ha ha1).1)]

lemma radius_strictMono (r s a : ℝ) (hrs : r < s) (ha : 0 < a) (ha1 : a ≤ 1) :
    StrictMonoOn (fun u => coefficient r s a u * u) (Ici 0) := by
  intro u hu v hv huv
  have hc := coefficient_monotone r s a hrs ha1 huv.le
  have hp : 0 < coefficient r s a v := ha.trans_le (coefficient_bounds r s a v ha ha1).1
  exact (mul_le_mul_of_nonneg_right hc hu).trans_lt (mul_lt_mul_of_pos_left huv hp)

lemma radial_injective (r s a : ℝ) (hrs : r < s) (ha : 0 < a) (ha1 : a ≤ 1) :
    Function.Injective (radial r s a) := by
  intro x y he
  have hn : ‖x‖ = ‖y‖ := (radius_strictMono r s a hrs ha ha1).injOn
    (norm_nonneg x) (norm_nonneg y) (by simpa only [radial_norm r s a ha ha1] using congrArg norm he)
  have hc : coefficient r s a ‖x‖ ≠ 0 := ne_of_gt (ha.trans_le (coefficient_bounds r s a ‖x‖ ha ha1).1)
  dsimp [radial] at he
  rw [← hn] at he
  have hh := congrArg (fun z : Plane => (coefficient r s a ‖x‖)⁻¹ • z) he
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hh

lemma radial_fixed_outer (r s a : ℝ) (hrs : r < s) (x : Plane) (hx : s ≤ ‖x‖) :
    radial r s a x = x := by rw [radial,coefficient_outer r s a ‖x‖ hrs hx,one_smul]

lemma radial_surjective (r s a : ℝ) (hr : 0 < r) (hrs : r < s) (ha : 0 < a) (ha1 : a ≤ 1) :
    Function.Surjective (radial r s a) := by
  intro y
  by_cases hy : y = 0
  · exact ⟨0,by simp [radial,hy]⟩
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let m : ℝ := max s ‖y‖
  have hm : 0 ≤ m := (norm_nonneg y).trans (le_max_right _ _)
  have hcont : Continuous (fun u : ℝ => coefficient r s a u * u) :=
    ((coefficient_continuous r s).comp (continuous_const.prodMk continuous_id)).mul continuous_id
  have hends : ‖y‖ ∈ Icc (coefficient r s a 0 * 0) (coefficient r s a m * m) := by
    rw [mul_zero,coefficient_outer r s a m hrs (le_max_left _ _),one_mul]
    exact ⟨hn.le,le_max_right _ _⟩
  obtain ⟨u,hu,he⟩ := intermediate_value_Icc hm hcont.continuousOn hends
  change coefficient r s a u * u = ‖y‖ at he
  let x : Plane := (u/‖y‖) • y
  have hxn : ‖x‖ = u := by
    dsimp [x]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hu.1 hn.le)]
    exact div_mul_cancel₀ u hn.ne'
  refine ⟨x,?_⟩
  rw [radial,hxn]
  change coefficient r s a u • ((u/‖y‖) • y) = y
  rw [smul_smul]
  have hc : coefficient r s a u * (u/‖y‖) = 1 := by
    rw [← mul_div_assoc,he,div_self hn.ne']
  rw [hc,one_smul]

def compression (r s a : ℝ) (hr : 0 < r) (hrs : r < s) (ha : 0 < a) (ha1 : a ≤ 1) : Plane ≃ₜ Plane :=
  homeomorph_of_fixed_outside_compact (radial r s a)
    ((radial_joint_continuous r s).comp (continuous_const.prodMk continuous_id))
    ⟨radial_injective r s a hrs ha ha1,radial_surjective r s a hr hrs ha ha1⟩
    (closedBall 0 s) (isCompact_closedBall _ _) (by
      intro x hx
      exact radial_fixed_outer r s a hrs x (le_of_not_ge (fun h => hx (mem_closedBall_zero_iff.mpr h))))

#print axioms radial_injective
#print axioms radial_surjective
#print axioms compression
end CompressionActualRadialCompactCompressionV825
