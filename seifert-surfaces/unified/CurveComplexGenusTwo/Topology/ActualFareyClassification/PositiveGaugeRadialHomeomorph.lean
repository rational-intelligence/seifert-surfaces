import CurveComplexGenusTwo.Topology.ActualFareyClassification.MidpointSquareBoundary
import Mathlib.Analysis.Convex.GaugeRescale

open Set Topology Filter

/-- Radial rescaling for an actual continuous positive homogeneous gauge.
Convexity is unnecessary, so this applies to the square with attached ports. -/
theorem positive_homogeneous_gauge_radial_homeomorph
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E→ℝ) (hg : Continuous g)
    (hom : ∀ (r : ℝ) (x : E), 0≤r → g (r • x)=r*g x)
    (c d : ℝ) (hc : 0<c) (_hd : 0<d)
    (hb : ∀ x, c*‖x‖≤g x ∧ g x≤d*‖x‖) :
    ∃ H : E ≃ₜ E, (∀ x, H x=(‖x‖/g x) • x) ∧
      (∀ x, g (H x)=‖x‖) ∧
      H '' {x : E | ‖x‖≤1}={x : E | g x≤1} := by
  have hg0 : g 0=0 := by
    have hh := hb 0
    simp only [norm_zero,mul_zero] at hh
    exact le_antisymm hh.2 hh.1
  have hpos (x : E) (hx : x≠0) : 0<g x := (mul_pos hc (norm_pos_iff.mpr hx)).trans_le (hb x).1
  let f : E→E := fun x => (‖x‖/g x) • x
  let k : E→E := fun x => (g x/‖x‖) • x
  have hf0 : f 0=0 := by simp [f]
  have hk0 : k 0=0 := by simp [k]
  have hgf (x : E) : g (f x)=‖x‖ := by
    by_cases hx : x=0
    · simp [hx,hf0,hg0]
    · dsimp [f]
      rw [hom _ _ (div_nonneg (norm_nonneg _) (hpos x hx).le),div_mul_cancel₀ _ (hpos x hx).ne']
  have hnk (x : E) : ‖k x‖=g x := by
    by_cases hx : x=0
    · simp [hx,hk0,hg0]
    · dsimp [k]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos (hpos x hx) (norm_pos_iff.mpr hx)),
        div_mul_cancel₀ _ (norm_pos_iff.mpr hx).ne']
  have hkf (x : E) : k (f x)=x := by
    by_cases hx : x=0
    · simp [hx,hf0,hk0]
    · have hp := hpos x hx
      have hn := norm_pos_iff.mpr hx
      dsimp [k]
      rw [hgf]
      dsimp [f]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hn hp),smul_smul]
      have he : ‖x‖ / (‖x‖ / g x * ‖x‖) * (‖x‖ / g x)=1 := by field_simp
      rw [he,one_smul]
  have hfk (x : E) : f (k x)=x := by
    by_cases hx : x=0
    · simp [hx,hf0,hk0]
    · have hp := hpos x hx
      have hn := norm_pos_iff.mpr hx
      dsimp [f]
      rw [hnk]
      dsimp [k]
      rw [hom _ _ (div_pos hp hn).le,smul_smul]
      have he : g x / (g x / ‖x‖ * g x) * (g x / ‖x‖)=1 := by field_simp
      rw [he,one_smul]
  have hnf (x : E) : ‖f x‖≤(1/c)*‖x‖ := by
    by_cases hx : x=0
    · simp [hx,hf0]
    · have hp := hpos x hx
      have hn := norm_pos_iff.mpr hx
      dsimp [f]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hn hp)]
      apply mul_le_mul_of_nonneg_right _ hn.le
      apply (div_le_div_iff₀ hp hc).mpr
      nlinarith [(hb x).1]
  have continuous_zero_bound (q : E→E) (hq0 : q 0=0) (C : ℝ)
      (hq : ∀ x, ‖q x‖≤C*‖x‖) : ContinuousAt q 0 := by
    rw [ContinuousAt,hq0]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun x => norm_nonneg (q x)) hq
    simpa using tendsto_const_nhds.mul (continuous_norm.continuousAt : Filter.Tendsto (fun x : E => ‖x‖) (nhds 0) (nhds ‖(0:E)‖))
  have hfc : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x=0
    · subst x; exact continuous_zero_bound f hf0 (1/c) hnf
    · exact (continuous_norm.continuousAt.div hg.continuousAt (hpos x hx).ne').smul continuousAt_id
  have hkc : Continuous k := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x=0
    · subst x
      exact continuous_zero_bound k hk0 d (fun x => by rw [hnk]; exact (hb x).2)
    · exact (hg.continuousAt.div continuous_norm.continuousAt (norm_pos_iff.mpr hx).ne').smul continuousAt_id
  let H : E ≃ₜ E := {
    toFun := f
    invFun := k
    left_inv := hkf
    right_inv := hfk
    continuous_toFun := hfc
    continuous_invFun := hkc }
  refine ⟨H,fun _ => rfl,hgf,?_⟩
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩; exact (hgf x).trans_le hx
  · intro hy
    refine ⟨k y,?_,hfk y⟩
    change ‖k y‖≤1
    rwa [hnk]

#print axioms positive_homogeneous_gauge_radial_homeomorph
