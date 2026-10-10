import CurveComplexGenusTwo.Filtration.CleanSubset

namespace CurveGenusTwo.Filtration

universe u v

variable {V : Type u} {B : Type v} [DecidableEq V]

section Chains

variable [LinearOrder V]

omit [LinearOrder V] in
private theorem face_valid (K : FiniteComplex V) (n : ℤ)
    (σ : SimplexAt K n) {v : V} (hv : v ∈ σ.1) :
    σ.1.erase v ∈ K ∧
      ((n - 1 = -1 ∧ σ.1.erase v = ∅) ∨
        (0 ≤ n - 1 ∧ ((σ.1.erase v).card : ℤ) = (n - 1) + 1)) := by
  classical
  have hmem : σ.1.erase v ∈ K := K.down_closed (Finset.erase_subset v σ.1) σ.2.1
  refine ⟨hmem, ?_⟩
  rcases σ.2.2 with hneg | hpos
  · exact False.elim (by simp [hneg.2] at hv)
  · have hcard : (σ.1.erase v).card + 1 = σ.1.card := by
      simpa using Finset.card_erase_add_one hv
    by_cases hn : n = 0
    · left
      constructor
      · omega
      · have hσcard : σ.1.card = 1 := by omega
        exact Finset.card_eq_zero.mp (by omega)
    · right
      constructor <;> omega

private def faceAt (K : FiniteComplex V) (n : ℤ)
    (σ : SimplexAt K n) (v : σ.1) : SimplexAt K (n - 1) :=
  ⟨σ.1.erase v.1, face_valid K n σ v.2⟩

private theorem faceBoundary_eq (K : FiniteComplex V) (n : ℤ)
    (σ : SimplexAt K n) :
    faceBoundary K n σ = ∑ v ∈ σ.1.attach,
      (-1 : ℤ) ^ (σ.1.filter (· < v.1)).card •
        FreeAbelianGroup.of (faceAt K n σ v) := by
  classical
  rw [faceBoundary]
  conv_lhs => rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro v hv
  have hvalid := face_valid K n σ v.2
  have hproof : (⟨σ.1.erase v.1, hvalid⟩ : SimplexAt K (n - 1)) =
      faceAt K n σ v := Subtype.ext rfl
  exact (dite_eq_left hvalid).trans (congrArg
    (fun x : SimplexAt K (n - 1) =>
      (-1 : ℤ) ^ (σ.1.filter (· < v.1)).card • FreeAbelianGroup.of x) hproof)

private theorem boundary_minus_one_zero (K : FiniteComplex V) :
    boundary K (-1) = 0 := by
  apply FreeAbelianGroup.lift_ext
  intro σ
  have hσ : σ.1 = ∅ := by
    rcases σ.2.2 with h | h
    · exact h.2
    · omega
  simp [boundary, faceBoundary, hσ]

private theorem sign_swap_ordered (s : Finset V) {v w : V}
    (hv : v ∈ s) (_hw : w ∈ s) (hvw : v < w) :
    (-1 : ℤ) ^ (s.filter (· < v)).card *
        (-1 : ℤ) ^ ((s.erase v).filter (· < w)).card =
      -((-1 : ℤ) ^ (s.filter (· < w)).card *
        (-1 : ℤ) ^ ((s.erase w).filter (· < v)).card) := by
  classical
  have hvf : v ∈ s.filter (· < w) := Finset.mem_filter.mpr ⟨hv, hvw⟩
  have hwf : w ∉ s.filter (· < v) := by simp [not_lt.mpr (le_of_lt hvw)]
  have ha : ((s.erase v).filter (· < w)).card + 1 =
      (s.filter (· < w)).card := by
    rw [Finset.filter_erase]
    exact Finset.card_erase_add_one hvf
  have hb : ((s.erase w).filter (· < v)).card =
      (s.filter (· < v)).card := by
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem hwf]
  have he : (s.filter (· < v)).card + ((s.erase v).filter (· < w)).card + 1 =
      (s.filter (· < w)).card + ((s.erase w).filter (· < v)).card := by omega
  rw [← pow_add, ← pow_add]
  rw [← he]
  simp [pow_succ]

private theorem sign_swap (s : Finset V) {v w : V}
    (hv : v ∈ s) (hw : w ∈ s) (hne : v ≠ w) :
    (-1 : ℤ) ^ (s.filter (· < v)).card *
        (-1 : ℤ) ^ ((s.erase v).filter (· < w)).card =
      -((-1 : ℤ) ^ (s.filter (· < w)).card *
        (-1 : ℤ) ^ ((s.erase w).filter (· < v)).card) := by
  by_cases hvw : v < w
  · exact sign_swap_ordered s hv hw hvw
  · have hwv : w < v := lt_of_le_of_ne (le_of_not_gt hvw) hne.symm
    simpa only [neg_neg] using congrArg Neg.neg (sign_swap_ordered s hw hv hwv).symm

private theorem alternating_double_sum_zero {G : Type*} [AddCommGroup G] [Module ℤ G]
    (s : Finset V) (f : Finset V → G) :
    (∑ v ∈ s, ∑ w ∈ s.erase v,
      ((-1 : ℤ) ^ (s.filter (· < v)).card *
        (-1 : ℤ) ^ ((s.erase v).filter (· < w)).card) •
          f ((s.erase v).erase w)) = 0 := by
  classical
  let F : V × V → G := fun p =>
    ((-1 : ℤ) ^ (s.filter (· < p.1)).card *
      (-1 : ℤ) ^ ((s.erase p.1).filter (· < p.2)).card) •
        f ((s.erase p.1).erase p.2)
  have hzero : ∑ p ∈ s.offDiag, F p = 0 := by
    apply Finset.sum_involution (fun p _ => (p.2, p.1))
    · intro p hp
      have h := Finset.mem_offDiag.mp hp
      have hs := sign_swap s h.1 h.2.1 h.2.2
      dsimp [F]
      rw [Finset.erase_right_comm]
      rw [hs]
      simp
    · intro p hp hnonzero hswap
      exact (Finset.mem_offDiag.mp hp).2.2 (congrArg Prod.fst hswap).symm
    · intro p hp
      exact Finset.mem_offDiag.mpr
        ⟨(Finset.mem_offDiag.mp hp).2.1,
          (Finset.mem_offDiag.mp hp).1,
          (Finset.mem_offDiag.mp hp).2.2.symm⟩
    · intro p hp
      cases p
      rfl
  have hprod : (∑ p ∈ s.offDiag, F p) =
      ∑ v ∈ s, ∑ w ∈ s.erase v, F (v, w) :=
    Finset.sum_finset_product s.offDiag s (fun v => s.erase v) (by
      intro p
      simp only [Finset.mem_offDiag, Finset.mem_erase]
      tauto)
  rw [hprod] at hzero
  exact hzero

omit [LinearOrder V] in
private theorem double_valid (K : FiniteComplex V) (n : ℤ)
    (σ : SimplexAt K n) {v w : V} (hv : v ∈ σ.1)
    (hw : w ∈ σ.1.erase v) :
    (σ.1.erase v).erase w ∈ K ∧
      ((n - 1 - 1 = -1 ∧ (σ.1.erase v).erase w = ∅) ∨
        (0 ≤ n - 1 - 1 ∧ (((σ.1.erase v).erase w).card : ℤ) = (n - 1 - 1) + 1)) := by
  let v' : σ.1 := ⟨v, hv⟩
  let w' : (faceAt K n σ v').1 := ⟨w, hw⟩
  have h := face_valid K (n - 1) (faceAt K n σ v') w'.2
  simpa only [faceAt] using h

private noncomputable def doubleRaw (K : FiniteComplex V) (n : ℤ)
    (t : Finset V) : chains K (n - 1 - 1) := by
  classical
  exact if h : t ∈ K ∧
      ((n - 1 - 1 = -1 ∧ t = ∅) ∨
        (0 ≤ n - 1 - 1 ∧ (t.card : ℤ) = (n - 1 - 1) + 1)) then
    FreeAbelianGroup.of (⟨t, h⟩ : SimplexAt K (n - 1 - 1))
  else 0

omit [LinearOrder V] in
private theorem doubleRaw_eq (K : FiniteComplex V) (n : ℤ)
    (σ : SimplexAt K n) {v w : V} (hv : v ∈ σ.1)
    (hw : w ∈ σ.1.erase v) :
    doubleRaw K n ((σ.1.erase v).erase w) =
      FreeAbelianGroup.of
        (faceAt K (n - 1) (faceAt K n σ ⟨v, hv⟩) ⟨w, hw⟩) := by
  have hvalid := double_valid K n σ hv hw
  have hproof : (⟨(σ.1.erase v).erase w, hvalid⟩ : SimplexAt K (n - 1 - 1)) =
      faceAt K (n - 1) (faceAt K n σ ⟨v, hv⟩) ⟨w, hw⟩ := Subtype.ext rfl
  exact (dite_eq_left hvalid).trans (congrArg FreeAbelianGroup.of hproof)

private theorem boundary_of (K : FiniteComplex V) (n : ℤ)
    (σ : SimplexAt K n) :
    boundary K n (FreeAbelianGroup.of σ) = faceBoundary K n σ := by
  simp [boundary]

theorem boundary_boundary (K : FiniteComplex V) (n : ℤ) :
    (boundary K (n - 1)).comp (boundary K n) = 0 := by
  classical
  apply FreeAbelianGroup.lift_ext
  intro σ
  by_cases hn : n ≤ 0
  · have : n = 0 ∨ n < 0 := by omega
    rcases this with rfl | hn
    · change boundary K (-1) (boundary K 0 (FreeAbelianGroup.of σ)) = 0
      rw [boundary_minus_one_zero]
      simp
    · have hσ : σ.1 = ∅ := by
        rcases σ.2.2 with h | h
        · exact h.2
        · omega
      simp [boundary, faceBoundary, hσ]
  · change boundary K (n - 1) (boundary K n (FreeAbelianGroup.of σ)) = 0
    rw [boundary_of, faceBoundary_eq]
    simp_rw [map_sum, map_zsmul, boundary_of, faceBoundary_eq]
    calc
      _ = ∑ v ∈ σ.1.attach, ∑ w ∈ (faceAt K n σ v).1.attach,
            ((-1 : ℤ) ^ (σ.1.filter (· < v.1)).card *
              (-1 : ℤ) ^ ((σ.1.erase v.1).filter (· < w.1)).card) •
              doubleRaw K n ((σ.1.erase v.1).erase w.1) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro w hw
        rw [smul_smul, doubleRaw_eq K n σ v.2 w.2]
        rfl
      _ = ∑ v ∈ σ.1, ∑ w ∈ σ.1.erase v,
            ((-1 : ℤ) ^ (σ.1.filter (· < v)).card *
              (-1 : ℤ) ^ ((σ.1.erase v).filter (· < w)).card) •
              doubleRaw K n ((σ.1.erase v).erase w) := by
        change (∑ v ∈ σ.1.attach, ∑ w ∈ (σ.1.erase v.1).attach,
            ((-1 : ℤ) ^ (σ.1.filter (· < v.1)).card *
              (-1 : ℤ) ^ ((σ.1.erase v.1).filter (· < w.1)).card) •
              doubleRaw K n ((σ.1.erase v.1).erase w.1)) = _
        rw [show (∑ v ∈ σ.1.attach, ∑ w ∈ (σ.1.erase v.1).attach,
            ((-1 : ℤ) ^ (σ.1.filter (· < v.1)).card *
              (-1 : ℤ) ^ ((σ.1.erase v.1).filter (· < w.1)).card) •
              doubleRaw K n ((σ.1.erase v.1).erase w.1)) =
            ∑ v ∈ σ.1, ∑ w ∈ (σ.1.erase v).attach,
              ((-1 : ℤ) ^ (σ.1.filter (· < v)).card *
                (-1 : ℤ) ^ ((σ.1.erase v).filter (· < w.1)).card) •
                doubleRaw K n ((σ.1.erase v).erase w.1) from
          Finset.sum_attach σ.1 (fun v : V =>
            ∑ w ∈ (σ.1.erase v).attach,
              ((-1 : ℤ) ^ (σ.1.filter (· < v)).card *
                (-1 : ℤ) ^ ((σ.1.erase v).filter (· < w.1)).card) •
                doubleRaw K n ((σ.1.erase v).erase w.1))]
        apply Finset.sum_congr rfl
        intro v hv
        exact Finset.sum_attach (σ.1.erase v) (fun w : V =>
          ((-1 : ℤ) ^ (σ.1.filter (· < v)).card *
            (-1 : ℤ) ^ ((σ.1.erase v).filter (· < w)).card) •
            doubleRaw K n ((σ.1.erase v).erase w))
      _ = 0 := alternating_double_sum_zero σ.1 (doubleRaw K n)

end Chains

end CurveGenusTwo.Filtration
