import CurveComplexGenusTwo.Topology.ActualFareyClassification.PositiveGaugeRadialHomeomorph
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Set Topology Filter Metric

/-- A bounded nonnegative continuous direction-width gives an actual global
radial expansion. Width may vanish at the fixed endpoint directions. -/
theorem bounded_direction_width_radial_homeomorph
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : E→ℝ) (hw : Continuous w) (C : ℝ) (_hC : 0≤C)
    (hb : ∀ x, 0≤w x ∧ w x≤C) :
    ∃ H : E ≃ₜ E,
      (∀ x, H x=(1+w (‖x‖⁻¹ • x)) • x) ∧
      (∀ x, H.symm x=(1+w (‖x‖⁻¹ • x))⁻¹ • x) := by
  let n : E→E := fun x => ‖x‖⁻¹ • x
  let c : E→ℝ := fun x => 1+w (n x)
  have hc (x : E) : 0<c x := by dsimp [c]; linarith [(hb (n x)).1]
  have hnscale (r : ℝ) (hr : 0<r) (x : E) : n (r • x)=n x := by
    dsimp [n]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_inv_rev,smul_smul]
    congr 1
    rw [mul_assoc,inv_mul_cancel₀ hr.ne',mul_one]
  let f : E→E := fun x => c x • x
  let k : E→E := fun x => (c x)⁻¹ • x
  have hcf (x : E) : c (f x)=c x := by dsimp only [c,f]; rw [hnscale _ (hc x)]
  have hck (x : E) : c (k x)=c x := by dsimp only [c,k]; rw [hnscale _ (inv_pos.mpr (hc x))]
  have hkf (x : E) : k (f x)=x := by
    change (c (f x))⁻¹ • (c x • x)=x
    rw [hcf,smul_smul,inv_mul_cancel₀ (hc x).ne',one_smul]
  have hfk (x : E) : f (k x)=x := by
    change c (k x) • ((c x)⁻¹ • x)=x
    rw [hck,smul_smul,mul_inv_cancel₀ (hc x).ne',one_smul]
  have norm_zero_cont (q : E→E) (hq0 : q 0=0) (B : ℝ)
      (hq : ∀ x, ‖q x‖≤B*‖x‖) : ContinuousAt q 0 := by
    rw [ContinuousAt,hq0]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun x => norm_nonneg (q x)) hq
    simpa using tendsto_const_nhds.mul (continuous_norm.continuousAt : Tendsto (fun x : E => ‖x‖) (nhds 0) (nhds ‖(0:E)‖))
  have hcn (x : E) (hx : x≠0) : ContinuousAt c x := by
    exact continuousAt_const.add (hw.continuousAt.comp
      ((continuous_norm.continuousAt.inv₀ (norm_pos_iff.mpr hx).ne').smul continuousAt_id))
  have hfc : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x=0
    · subst x
      apply norm_zero_cont f (by simp [f]) (1+C)
      intro x
      dsimp [f]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hc x)]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      dsimp [c]
      linarith [(hb (n x)).2]
    · exact (hcn x hx).smul continuousAt_id
  have hkc : Continuous k := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x=0
    · subst x
      apply norm_zero_cont k (by simp [k]) 1
      intro x
      dsimp [k]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hc x))]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (inv_le_one₀ (hc x)).mpr (by dsimp [c]; linarith [(hb (n x)).1])
    · exact ((hcn x hx).inv₀ (hc x).ne').smul continuousAt_id
  let H : E ≃ₜ E := {
    toFun := f
    invFun := k
    left_inv := hkf
    right_inv := hfk
    continuous_toFun := hfc
    continuous_invFun := hkc }
  exact ⟨H,fun _ => rfl,fun _ => rfl⟩

#print axioms bounded_direction_width_radial_homeomorph
