import ActualTaperedNormalBlockIsotopyV837

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology Metric
open SeifertSurfaces.Foundations
open CompressionActualRadialCompactCompressionV825
noncomputable section
namespace CompressionActualVariableNormalFamilyStraighteningV895

/-- The same parameter family that defines a variable cap collar gives
    its exact normal-dependent straightening. Every point is matched,
    the normal coordinate is retained, and the support is constructed. -/
theorem variable_normal_family_straightening
    (K : Time → Plane ≃ₜ Plane)
    (hK : Continuous (fun p : Time × Plane => K p.1 p.2))
    (hKi : Continuous (fun p : Time × Plane => (K p.1).symm p.2))
    (hK1 : ∀ x,K 1 x = x)
    (W : Set Plane) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hoff : ∀ t x,x ∉ W → K t x = x)
    (ρ : ℝ) (hρ : 0 < ρ)
    (φ : ℝ → Time) (hφ : Continuous φ) (hφ0 : φ 0 = 1)
    (hφoff : ∀ n,n ∉ Ioo (-ρ) ρ → φ n = 0) :
    ∃ L : Time → (Plane × ℝ) ≃ₜ (Plane × ℝ),
      Continuous (fun p : Time × (Plane × ℝ) => L p.1 p.2) ∧
      Continuous (fun p : Time × (Plane × ℝ) => (L p.1).symm p.2) ∧
      (∀ p,L 0 p = p) ∧ (∀ t p,(L t p).2 = p.2) ∧
      (∀ t p,p ∉ W ×ˢ Ioo (-ρ) ρ → L t p = p) ∧
      IsOpen (W ×ˢ Ioo (-ρ) ρ) ∧ IsCompact (closure (W ×ˢ Ioo (-ρ) ρ)) ∧
      (∀ x,L 1 (x,0) = (K 0 x,0)) ∧
      ∀ n x,L 1 (K (φ n) x,n) = (K 0 x,n) := by
  let phase (t : Time) (n : ℝ) : Time := ⟨(1-t.val)*(φ n).val,
    mul_nonneg (sub_nonneg.mpr t.property.2) (φ n).property.1,
    (mul_le_mul_of_nonneg_left (φ n).property.2 (sub_nonneg.mpr t.property.2)).trans
      (by simpa using sub_le_self (1:ℝ) t.property.1)⟩
  have hphase : Continuous (fun p : Time × ℝ => phase p.1 p.2) := by
    apply Continuous.subtype_mk
    exact (continuous_const.sub continuous_fst.subtype_val).mul (hφ.subtype_val.comp continuous_snd)
  have hp0 (n : ℝ) : phase 0 n = φ n := Subtype.ext (by simp [phase])
  have hp1 (n : ℝ) : phase 1 n = 0 := Subtype.ext (by simp [phase])
  have hpoff (t : Time) (n : ℝ) (hn : n ∉ Ioo (-ρ) ρ) : phase t n = 0 :=
    Subtype.ext (by simp [phase,hφoff n hn])
  let L (t : Time) : (Plane × ℝ) ≃ₜ (Plane × ℝ) := {
    toFun := fun p => (K (phase t p.2) ((K (φ p.2)).symm p.1),p.2)
    invFun := fun p => (K (φ p.2) ((K (phase t p.2)).symm p.1),p.2)
    left_inv := by
      intro p
      apply Prod.ext
      · change K (φ p.2) ((K (phase t p.2)).symm
          (K (phase t p.2) ((K (φ p.2)).symm p.1))) = p.1
        rw [(K _).symm_apply_apply,(K _).apply_symm_apply]
      · rfl
    right_inv := by
      intro p
      apply Prod.ext
      · change K (phase t p.2) ((K (φ p.2)).symm
          (K (φ p.2) ((K (phase t p.2)).symm p.1))) = p.1
        rw [(K _).symm_apply_apply,(K _).apply_symm_apply]
      · rfl
    continuous_toFun := (hK.comp
      ((hphase.comp (continuous_const.prodMk continuous_snd)).prodMk
        (hKi.comp ((hφ.comp continuous_snd).prodMk continuous_fst)))).prodMk continuous_snd
    continuous_invFun := (hK.comp
      ((hφ.comp continuous_snd).prodMk
        (hKi.comp ((hphase.comp (continuous_const.prodMk continuous_snd)).prodMk continuous_fst)))).prodMk continuous_snd }
  have hLc : Continuous (fun p : Time × (Plane × ℝ) => L p.1 p.2) :=
    (hK.comp ((hphase.comp (continuous_fst.prodMk continuous_snd.snd)).prodMk
      (hKi.comp ((hφ.comp continuous_snd.snd).prodMk continuous_snd.fst)))).prodMk continuous_snd.snd
  have hLci : Continuous (fun p : Time × (Plane × ℝ) => (L p.1).symm p.2) :=
    (hK.comp ((hφ.comp continuous_snd.snd).prodMk
      (hKi.comp ((hphase.comp (continuous_fst.prodMk continuous_snd.snd)).prodMk continuous_snd.fst)))).prodMk continuous_snd.snd
  refine ⟨L,hLc,hLci,?_,fun _ _ => rfl,?_,hW.prod isOpen_Ioo,?_,?_,?_⟩
  · intro p
    change (K (phase 0 p.2) ((K (φ p.2)).symm p.1),p.2) = p
    rw [hp0,(K _).apply_symm_apply]
  · intro t p hp
    change (K (phase t p.2) ((K (φ p.2)).symm p.1),p.2) = p
    by_cases hx : p.1 ∈ W
    · rw [hφoff _ (fun hn => hp ⟨hx,hn⟩),hpoff _ _ (fun hn => hp ⟨hx,hn⟩),(K 0).apply_symm_apply]
    · have hi : (K (φ p.2)).symm p.1 = p.1 := (K (φ p.2)).injective
        (by rw [(K _).apply_symm_apply,hoff _ _ hx])
      rw [hi,hoff _ _ hx]
  · rw [closure_prod_eq]
    exact hWc.prod (isCompact_Icc.of_isClosed_subset isClosed_closure
      (closure_minimal Ioo_subset_Icc_self isClosed_Icc))
  · intro x
    change (K (phase 1 0) ((K (φ 0)).symm x),0) = (K 0 x,0)
    have hi : (K 1).symm x = x := (K 1).injective (by rw [(K 1).apply_symm_apply,hK1])
    rw [hp1,hφ0,hi]
  · intro n x
    change (K (phase 1 n) ((K (φ n)).symm (K (φ n) x)),n) = (K 0 x,n)
    rw [(K _).symm_apply_apply,hp1]

#print axioms variable_normal_family_straightening
end CompressionActualVariableNormalFamilyStraighteningV895
