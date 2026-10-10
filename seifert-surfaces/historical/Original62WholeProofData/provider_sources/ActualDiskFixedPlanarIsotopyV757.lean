import SchoenfliesNativeCoimportProbeV754

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology Filter
open SeifertSurfaces.Foundations
noncomputable section
namespace CompressionActualDiskFixedPlanarIsotopyV757

abbrev Plane := Schoenflies.Plane

/-- Dilation moves the support outward. The family is literally stationary near
    time zero on every bounded set, and keeps the entire unit disk fixed. -/
theorem disk_fixed_homeomorph_isotopy (h : Plane ≃ₜ Plane)
    (hfix : ∀ x : Plane, ‖x‖ ≤ 1 → h x = x) :
    ∃ K : Time → Plane ≃ₜ Plane,
      Continuous (fun p : Time × Plane => K p.1 p.2) ∧
      (∀ x,K 0 x = x) ∧ (∀ x,K 1 x = h x) ∧
      (∀ t x,‖x‖ ≤ 1 → K t x = x) := by
  classical
  let K (t : Time) : Plane ≃ₜ Plane :=
    if ht : (t : ℝ) = 0 then Homeomorph.refl Plane
    else (Homeomorph.smulOfNeZero (t : ℝ) ht).trans
      (h.trans (Homeomorph.smulOfNeZero (t : ℝ) ht).symm)
  have hformula (t : Time) (ht : (t : ℝ) ≠ 0) (x : Plane) :
      K t x = (t : ℝ)⁻¹ • h ((t : ℝ) • x) := by
    simp only [K,dite_eq_right ht,Homeomorph.trans_apply,Homeomorph.smulOfNeZero_apply,
      Homeomorph.smulOfNeZero_symm_apply]
  have hsmall (t : Time) (x : Plane) (hx : (t : ℝ) * ‖x‖ ≤ 1) : K t x = x := by
    by_cases ht : (t : ℝ) = 0
    · dsimp only [K]
      rw [dite_eq_left ht]
      rfl
    · rw [hformula t ht x,hfix]
      · exact inv_smul_smul₀ ht x
      · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg t.property.1]
        exact hx
  have hcont : Continuous (fun p : Time × Plane => K p.1 p.2) := by
    rw [continuous_iff_continuousAt]
    intro p
    by_cases ht : (p.1 : ℝ) = 0
    · have hN : {q : Time × Plane | (q.1 : ℝ) * ‖q.2‖ < 1} ∈ 𝓝 p :=
        (isOpen_lt (continuous_fst.subtype_val.mul continuous_snd.norm)
          continuous_const).mem_nhds (by simp [ht])
      apply continuous_snd.continuousAt.congr_of_eventuallyEq
      filter_upwards [hN] with q hq
      exact hsmall q.1 q.2 hq.le
    · have hN : {q : Time × Plane | (q.1 : ℝ) ≠ 0} ∈ 𝓝 p :=
        (isOpen_ne.preimage continuous_fst.subtype_val).mem_nhds ht
      have hc : ContinuousAt
          (fun q : Time × Plane => (q.1 : ℝ)⁻¹ • h ((q.1 : ℝ) • q.2)) p :=
        (continuous_fst.subtype_val.continuousAt.inv₀ ht).smul
          (h.continuous.continuousAt.comp
            (continuous_fst.subtype_val.smul continuous_snd).continuousAt)
      apply hc.congr_of_eventuallyEq
      filter_upwards [hN] with q hq
      exact hformula q.1 hq q.2
  refine ⟨K,hcont,?_,?_,?_⟩
  · intro x
    simp [K]
  · intro x
    rw [hformula 1 (by norm_num)]
    simp
  · intro t x hx
    exact hsmall t x ((mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg x)).trans
      (by simpa using hx))

end CompressionActualDiskFixedPlanarIsotopyV757
