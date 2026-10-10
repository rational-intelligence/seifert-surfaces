import ActualDiskFixedSupportedPlanarIsotopyV827

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology Metric
open SeifertSurfaces.Foundations
open CompressionActualCompactlySupportedContinuousBijectionV823
open CompressionActualRadialCompactCompressionV825
noncomputable section
namespace CompressionActualTaperedNormalBlockIsotopyV837

/-- Extend an actual supported planar isotopy in the normal coordinate,
    with a continuous taper that preserves the whole zero slice exactly. -/
theorem tapered_normal_block_isotopy (K : Time → Plane ≃ₜ Plane)
    (hK : Continuous (fun p : Time × Plane => K p.1 p.2))
    (hK0 : ∀ x,K 0 x = x) (W : Set Plane) (hW : IsOpen W)
    (hWc : IsCompact (closure W)) (hoff : ∀ t x,x ∉ W → K t x = x)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : Time → (Plane × ℝ) ≃ₜ (Plane × ℝ),
      Continuous (fun p : Time × (Plane × ℝ) => L p.1 p.2) ∧
      (∀ p,L 0 p = p) ∧
      (∀ t x,L t (x,0) = (K t x,0)) ∧
      (∀ t p,(L t p).2 = p.2) ∧
      (∀ t p,p ∉ W ×ˢ Ioo (-δ) δ → L t p = p) ∧
      IsOpen (W ×ˢ Ioo (-δ) δ) ∧ IsCompact (closure (W ×ˢ Ioo (-δ) δ)) ∧
      (∀ t x,(∀ s,K s x = x) → ∀ z,L t (x,z) = (x,z)) := by
  classical
  let height (z : ℝ) : ℝ := max 0 (1-min 1 (|z|/δ))
  have hheight (z : ℝ) : 0 ≤ height z ∧ height z ≤ 1 := by
    have hn : 0 ≤ min 1 (|z|/δ) := le_min (by norm_num) (div_nonneg (abs_nonneg z) hδ.le)
    have h1 := min_le_left (1:ℝ) (|z|/δ)
    dsimp [height]
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (by linarith)
  let time (t : Time) (z : ℝ) : Time := ⟨t.val*height z,
    mul_nonneg t.property.1 (hheight z).1,
    (mul_le_mul_of_nonneg_left (hheight z).2 t.property.1).trans (by simpa using t.property.2)⟩
  have htime : Continuous (fun p : Time × ℝ => time p.1 p.2) := by
    apply Continuous.subtype_mk
    unfold height
    fun_prop
  have htime0 (z : ℝ) : time 0 z = 0 := Subtype.ext (by simp [time])
  have htimez (t : Time) : time t 0 = t := Subtype.ext (by simp [time,height])
  have htimeoff (t : Time) (z : ℝ) (hz : z ∉ Ioo (-δ) δ) : time t z = 0 := by
    have hab : δ ≤ |z| := by
      apply le_of_not_gt
      intro h
      exact hz (abs_lt.mp h)
    have hd : 1 ≤ |z|/δ := (le_div_iff₀ hδ).mpr (by simpa using hab)
    exact Subtype.ext (by simp [time,height,min_eq_left hd])
  have hKi : Continuous (fun p : Time × Plane => (K p.1).symm p.2) :=
    continuous_family_inverse K hK (closure W) hWc
      (fun t x hx => hoff t x (fun hw => hx (subset_closure hw)))
  let L (t : Time) : (Plane × ℝ) ≃ₜ (Plane × ℝ) := {
    toFun := fun p => (K (time t p.2) p.1,p.2)
    invFun := fun p => ((K (time t p.2)).symm p.1,p.2)
    left_inv := by intro p; exact Prod.ext ((K _).symm_apply_apply p.1) rfl
    right_inv := by intro p; exact Prod.ext ((K _).apply_symm_apply p.1) rfl
    continuous_toFun := ((hK.comp
      ((htime.comp (continuous_const.prodMk continuous_snd)).prodMk continuous_fst))).prodMk continuous_snd
    continuous_invFun := ((hKi.comp
      ((htime.comp (continuous_const.prodMk continuous_snd)).prodMk continuous_fst))).prodMk continuous_snd }
  have hLc : Continuous (fun p : Time × (Plane × ℝ) => L p.1 p.2) :=
    (hK.comp ((htime.comp (continuous_fst.prodMk continuous_snd.snd)).prodMk continuous_snd.fst)).prodMk
      continuous_snd.snd
  refine ⟨L,hLc,?_,?_,fun _ _ => rfl,?_,hW.prod isOpen_Ioo,?_,?_⟩
  · intro p
    change (K (time 0 p.2) p.1,p.2) = p
    rw [htime0,hK0]
  · intro t x
    change (K (time t 0) x,0) = (K t x,0)
    rw [htimez]
  · intro t p hp
    change (K (time t p.2) p.1,p.2) = p
    by_cases hx : p.1 ∈ W
    · rw [htimeoff _ _ (fun hz => hp ⟨hx,hz⟩),hK0]
    · rw [hoff _ _ hx]
  · rw [closure_prod_eq]
    exact hWc.prod (isCompact_Icc.of_isClosed_subset isClosed_closure
      (closure_minimal Ioo_subset_Icc_self isClosed_Icc))
  · intro t x hx z
    exact Prod.ext (hx _) rfl

#print axioms tapered_normal_block_isotopy
end CompressionActualTaperedNormalBlockIsotopyV837
