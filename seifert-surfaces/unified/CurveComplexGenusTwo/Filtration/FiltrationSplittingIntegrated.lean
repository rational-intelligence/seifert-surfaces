import CurveComplexGenusTwo.Filtration.FiltrationRelativeNaturality

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

private theorem cast_apply_boundary (L : FiniteComplex V) (k : ℤ)
    {j : ℤ} (h : k - 1 = j) (τ : SimplexAt L k) :
    (cast (congrArg (fun m : ℤ => chains L k →+ chains L m) h)
      (boundary L k)) (FreeAbelianGroup.of τ) =
    cast (congrArg (chains L) h) (faceBoundary L k τ) := by
  cases h
  simp [boundary]

private theorem cast_chains_sum (L : FiniteComplex V) {i j : ℤ}
    (h : i = j) {α : Type*} (s : Finset α) (f : α → chains L i) :
    (cast (congrArg (chains L) h) (∑ x ∈ s, f x)) =
      ∑ x ∈ s, cast (congrArg (chains L) h) (f x) := by
  cases h
  rfl

private theorem cast_chains_zsmul (L : FiniteComplex V) {i j : ℤ}
    (h : i = j) (z : ℤ) (x : chains L i) :
    cast (congrArg (chains L) h) (z • x) =
      z • cast (congrArg (chains L) h) x := by
  cases h
  rfl

private theorem cast_chains_of (L : FiniteComplex V) {i j : ℤ}
    (h : i = j) (τ : SimplexAt L i) :
    cast (congrArg (chains L) h) (FreeAbelianGroup.of τ) =
      FreeAbelianGroup.of (cast (congrArg (SimplexAt L) h) τ) := by
  cases h
  rfl

private theorem cast_simplex_val (L : FiniteComplex V) {i j : ℤ}
    (h : i = j) (τ : SimplexAt L i) :
    (cast (congrArg (SimplexAt L) h) τ).1 = τ.1 := by
  cases h
  rfl

private theorem shiftedBoundary_apply (L : FiniteComplex V) (p : ℕ)
    (n : ℤ) (τ : SimplexAt L (n - p)) :
    (by
      have hn : n - (p : ℤ) - 1 = (n - 1) - p := by omega
      rw [← hn]
      exact boundary L (n - p) :
      chains L (n - p) →+ chains L ((n - 1) - p))
      (FreeAbelianGroup.of τ) =
    Eq.mp (congrArg (chains L) (show n - (p : ℤ) - 1 = (n - 1) - p by omega))
      (faceBoundary L (n - p) τ) := by
  have hn : n - (p : ℤ) - 1 = (n - 1) - p := by omega
  change
    (cast (congrArg (fun j : ℤ =>
      chains L (n - p) →+ chains L j) hn)
      (boundary L (n - p))) (FreeAbelianGroup.of τ) =
    cast (congrArg (chains L) hn) (faceBoundary L (n - p) τ)
  exact cast_apply_boundary L (n - p) hn τ

private theorem shiftedBoundary_face_sum (L : FiniteComplex V) (p : ℕ)
    (n : ℤ) (τ : SimplexAt L (n - p)) :
    (by
      have hn : n - (p : ℤ) - 1 = (n - 1) - p := by omega
      rw [← hn]
      exact boundary L (n - p) :
      chains L (n - p) →+ chains L ((n - 1) - p))
      (FreeAbelianGroup.of τ) =
    ∑ v ∈ τ.1.attach,
      (-1 : ℤ) ^ (τ.1.filter (· < v.1)).card •
        cast (congrArg (chains L)
          (show n - (p : ℤ) - 1 = (n - 1) - p by omega))
          (FreeAbelianGroup.of (faceAt L (n - p) τ v)) := by
  rw [shiftedBoundary_apply, faceBoundary_eq]
  have hn : n - (p : ℤ) - 1 = (n - 1) - p := by omega
  change cast (congrArg (chains L) hn)
      (∑ v ∈ τ.1.attach,
        (-1 : ℤ) ^ (τ.1.filter (· < v.1)).card •
          FreeAbelianGroup.of (faceAt L (n - p) τ v)) = _
  rw [cast_chains_sum L hn]
  apply Finset.sum_congr rfl
  intro v hv
  exact cast_chains_zsmul L (show n - (p : ℤ) - 1 = (n - 1) - p by omega)
    _ _

noncomputable def relativeBoundaries (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) (n : ℤ) : AddSubgroup (relativeChains K a p n) :=
  by
    have hn : n + 1 - 1 = n := by omega
    exact Eq.mp (congrArg (fun m : ℤ => AddSubgroup (relativeChains K a p m)) hn)
      (relativeBoundary K a p (n + 1)).range

/-- The homology of `C̃(Y_p,Y_{p-1})`, in its exact bad-support basis. -/
noncomputable abbrev relativeHomology (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) (n : ℤ) : Type u :=
  (relativeCycles K a p n) ⧸
    ((relativeBoundaries K a p n).comap (relativeCycles K a p n).subtype)

private theorem split_degree_iff (s t : Finset V) (p : ℕ) (n : ℤ)
    (hd : Disjoint s t) (hs : s.card = p) :
    ((n = -1 ∧ s ∪ t = ∅) ∨
      (0 ≤ n ∧ ((s ∪ t).card : ℤ) = n + 1)) ↔
    ((n - p = -1 ∧ t = ∅) ∨
      (0 ≤ n - p ∧ (t.card : ℤ) = n - p + 1)) := by
  have hc : (s ∪ t).card = s.card + t.card := Finset.card_union_of_disjoint hd
  have hc' : ((s ∪ t).card : ℤ) = (p : ℤ) + t.card := by
    exact_mod_cast (hs ▸ hc)
  constructor
  · intro h
    rcases h with ⟨hn, he⟩ | ⟨hn, he⟩
    · have hse : s = ∅ := Finset.subset_empty.mp (he ▸ Finset.subset_union_left)
      have hte : t = ∅ := Finset.subset_empty.mp (he ▸ Finset.subset_union_right)
      left
      constructor
      · simp [hse] at hs
        omega
      · exact hte
    · by_cases ht : t = ∅
      · left
        constructor
        · have hcard : (s.card : ℤ) = n + 1 := by simpa [ht] using he
          have hsc : (s.card : ℤ) = p := by exact_mod_cast hs
          omega
        · exact ht
      · right
        have htpos : 0 < t.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ht)
        constructor <;> omega
  · intro h
    rcases h with ⟨hn, ht⟩ | ⟨hn, ht⟩
    · by_cases hp : p = 0
      · left
        have he : s = ∅ := Finset.card_eq_zero.mp (by omega)
        simp [he, ht] at *
        omega
      · right
        have hcard : ((s ∪ t).card : ℤ) = p := by
          simp only [ht, Finset.union_empty]
          exact_mod_cast hs
        constructor <;> omega
    · right
      constructor <;> omega

private noncomputable def relativeSplitBasis (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) (n : ℤ) :
    RelativeSimplexAt K a p n ≃
      Σ S : strata K a p, SimplexAt (restrictedLink K a S) (n - p) where
  toFun σ := by
    classical
    let T := badVertices a σ.1.1
    have hT := bad_support_in_strata K a σ.1.2.1 p σ.2
    let S : strata K a p := ⟨T, hT.1, σ.2, hT.2⟩
    let τ := σ.1.1 \ T
    have hsub : T ⊆ σ.1.1 := Finset.filter_subset _ _
    have hdisj : Disjoint T τ := Finset.disjoint_sdiff
    have hunion : T ∪ τ = σ.1.1 := Finset.union_sdiff_of_subset hsub
    have hτ : τ ∈ restrictedLink K a S := by
      change Disjoint T τ ∧ T ∪ τ ∈ K ∧ badVertices a (T ∪ τ) = T
      exact ⟨hdisj, hunion.symm ▸ σ.1.2.1, by simpa [hunion, T]⟩
    have hdegree :
        ((n - p = -1 ∧ τ = ∅) ∨
          (0 ≤ n - p ∧ (τ.card : ℤ) = n - p + 1)) := by
      apply (split_degree_iff T τ p n hdisj σ.2).mp
      simpa only [hunion] using σ.1.2.2
    exact ⟨S, ⟨τ, hτ, hdegree⟩⟩
  invFun z := by
    classical
    let σ := z.1.1 ∪ z.2.1
    have hlink := z.2.2.1
    have hmem : σ ∈ K := hlink.2.1
    have hbad : badVertices a σ = z.1.1 := hlink.2.2
    have hdegree :
        ((n = -1 ∧ σ = ∅) ∨
          (0 ≤ n ∧ (σ.card : ℤ) = n + 1)) :=
      (split_degree_iff z.1.1 z.2.1 p n hlink.1 z.1.2.2.1).mpr z.2.2.2
    exact ⟨⟨σ, hmem, hdegree⟩, by simp [hbad, z.1.2.2.1]⟩
  left_inv σ := by
    classical
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    exact Finset.union_sdiff_of_subset (Finset.filter_subset _ _)
  right_inv z := by
    classical
    apply Sigma.ext
    · apply Subtype.ext
      exact z.2.2.1.2.2
    · refine (Subtype.heq_iff_coe_heq rfl ?_).2 ?_
      · apply heq_of_eq
        funext x
        congr 1
        congr 1
        congr 1
        apply Subtype.ext
        exact z.2.2.1.2.2
      · apply heq_of_eq
        dsimp
        rw [z.2.2.1.2.2]
        exact Finset.union_sdiff_cancel_left z.2.2.1.1

private def splitSign (s t : Finset V) : ℤ :=
  (-1 : ℤ) ^ (∑ v ∈ t, (s.filter (v < ·)).card)

private theorem splitSign_sq (s t : Finset V) : splitSign s t * splitSign s t = 1 := by
  simp [splitSign, ← pow_add, ← two_mul]

private theorem splitSign_erase (s t : Finset V) {v : V} (hv : v ∈ t) :
    splitSign s t =
      splitSign s (t.erase v) * (-1 : ℤ) ^ (s.filter (v < ·)).card := by
  unfold splitSign
  rw [← pow_add, Finset.sum_erase_add t (fun w => (s.filter (w < ·)).card) hv]

private theorem splitSign_sign_erase (s t : Finset V)
    (hd : Disjoint s t) {v : V} (hv : v ∈ t) :
    splitSign s t * (-1 : ℤ) ^ (t.filter (· < v)).card =
      (-1 : ℤ) ^ s.card *
        (-1 : ℤ) ^ ((s ∪ t).filter (· < v)).card *
          splitSign s (t.erase v) := by
  classical
  have hpartition : (s.filter (· < v)).card + (s.filter (v < ·)).card = s.card := by
    have hvnot : v ∉ s := by
      intro hvs
      exact (Finset.disjoint_left.mp hd hvs) hv
    have hfilter : s.filter (v < ·) = s.filter (fun w => ¬ w < v) := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · intro h
        exact ⟨h.1, not_lt.mpr (le_of_lt h.2)⟩
      · intro h
        have hne : w ≠ v := by
          intro heq
          subst w
          exact hvnot h.1
        exact ⟨h.1, lt_of_le_of_ne (le_of_not_gt h.2) hne.symm⟩
    rw [hfilter]
    exact Finset.card_filter_add_card_filter_not _
  have hfilterUnion : ((s ∪ t).filter (· < v)).card =
      (s.filter (· < v)).card + (t.filter (· < v)).card := by
    rw [Finset.filter_union, Finset.card_union_of_disjoint]
    exact hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [splitSign_erase s t hv]
  rw [show (-1 : ℤ) ^ s.card =
      (-1 : ℤ) ^ (s.filter (· < v)).card *
        (-1 : ℤ) ^ (s.filter (v < ·)).card by
      rw [← pow_add, hpartition]]
  rw [hfilterUnion]
  have hpow (k : ℕ) : (-1 : ℤ) ^ (2 * k) = 1 := by
    calc
      (-1 : ℤ) ^ (2 * k) = ((-1 : ℤ) ^ 2) ^ k := pow_mul _ _ _
      _ = 1 := by norm_num
  calc
    splitSign s (t.erase v) * (-1 : ℤ) ^ (s.filter (v < ·)).card *
        (-1 : ℤ) ^ (t.filter (· < v)).card =
      splitSign s (t.erase v) *
        (-1 : ℤ) ^ ((s.filter (v < ·)).card + (t.filter (· < v)).card) := by
          rw [pow_add]
          ring
    _ = splitSign s (t.erase v) *
        (-1 : ℤ) ^ ((s.filter (· < v)).card +
          (s.filter (v < ·)).card +
          ((s.filter (· < v)).card + (t.filter (· < v)).card)) := by
          rw [show (s.filter (· < v)).card + (s.filter (v < ·)).card +
              ((s.filter (· < v)).card + (t.filter (· < v)).card) =
              (s.filter (v < ·)).card + (t.filter (· < v)).card +
                2 * (s.filter (· < v)).card by omega]
          conv_rhs => rw [pow_add, hpow, mul_one]
    _ = _ := by rw [pow_add, pow_add, pow_add]; ring

private theorem splitSign_coeff (s t : Finset V) (p : ℕ)
    (hd : Disjoint s t) (hp : s.card = p) {v : V} (hv : v ∈ t) :
    (-1 : ℤ) ^ ((s ∪ t).filter (· < v)).card * splitSign s (t.erase v) =
      splitSign s t * ((-1 : ℤ) ^ p * (-1 : ℤ) ^ (t.filter (· < v)).card) := by
  have hs := splitSign_sign_erase s t hd hv
  rw [hp] at hs
  have hcc : (-1 : ℤ) ^ p * (-1 : ℤ) ^ p = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    (-1 : ℤ) ^ ((s ∪ t).filter (· < v)).card * splitSign s (t.erase v) =
        ((-1 : ℤ) ^ p * (-1 : ℤ) ^ p) *
          ((-1 : ℤ) ^ ((s ∪ t).filter (· < v)).card *
            splitSign s (t.erase v)) := by rw [hcc, one_mul]
    _ = (-1 : ℤ) ^ p *
          (splitSign s t * (-1 : ℤ) ^ (t.filter (· < v)).card) := by
            rw [hs]
            ring
    _ = _ := by ring

private theorem relative_face_iff_good (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) (n : ℤ) (σ : RelativeSimplexAt K a p n)
    {v : V} (hv : v ∈ σ.1.1) :
    (badVertices a (σ.1.1.erase v)).card = p ↔
      v ∉ badVertices a σ.1.1 := by
  constructor
  · intro heq hbad
    have hlt := erase_bad_lowers_count K a σ.1.2.1 hbad
    have hp := σ.2
    omega
  · intro hgood
    rw [erase_good_preserves_bad_support K a σ.1.2.1 hv hgood]
    exact σ.2

private theorem bad_support_erase_good (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) (n : ℤ) (σ : RelativeSimplexAt K a p n)
    {v : V} (hv : v ∈ σ.1.1) (hgood : v ∉ badVertices a σ.1.1) :
    badVertices a (σ.1.1.erase v) = badVertices a σ.1.1 :=
  erase_good_preserves_bad_support K a σ.1.2.1 hv hgood

private noncomputable def relativeGoodFaceAt (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) (n : ℤ) (σ : RelativeSimplexAt K a p n)
    (v : {v : V // v ∈ σ.1.1 \ badVertices a σ.1.1}) :
    RelativeSimplexAt K a p (n - 1) :=
  ⟨⟨σ.1.1.erase v.1, face_valid K n σ.1
      (Finset.mem_sdiff.mp v.2).1⟩,
    (relative_face_iff_good K a p n σ (Finset.mem_sdiff.mp v.2).1).mpr
      (Finset.mem_sdiff.mp v.2).2⟩

private theorem relativeFaceBoundary_good_eq (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ)
    (σ : RelativeSimplexAt K a p n) :
    relativeFaceBoundary K a p n σ =
      ∑ v ∈ (σ.1.1 \ badVertices a σ.1.1).attach,
        (-1 : ℤ) ^ (σ.1.1.filter (· < v.1)).card •
          FreeAbelianGroup.of (relativeGoodFaceAt K a p n σ v) := by
  classical
  unfold relativeFaceBoundary
  let f : V → relativeChains K a p (n - 1) := fun v =>
    if h : (σ.1.1.erase v ∈ K ∧
      ((n - 1 = -1 ∧ σ.1.1.erase v = ∅) ∨
        (0 ≤ n - 1 ∧ ((σ.1.1.erase v).card : ℤ) = (n - 1) + 1))) ∧
        (badVertices a (σ.1.1.erase v)).card = p then
      (-1 : ℤ) ^ (σ.1.1.filter (· < v)).card •
        FreeAbelianGroup.of
          (⟨⟨σ.1.1.erase v, h.1⟩, h.2⟩ : RelativeSimplexAt K a p (n - 1))
    else 0
  change (∑ v ∈ σ.1.1, f v) = _
  have hsum : (∑ v ∈ σ.1.1, f v) =
      ∑ v ∈ σ.1.1 \ badVertices a σ.1.1, f v := by
    symm
    apply Finset.sum_subset (Finset.sdiff_subset)
    intro v hv hvnot
    have hbad : v ∈ badVertices a σ.1.1 := by
      by_contra hgood
      exact hvnot (Finset.mem_sdiff.mpr ⟨hv, hgood⟩)
    have hne : (badVertices a (σ.1.1.erase v)).card ≠ p := by
      have hlt := erase_bad_lowers_count K a σ.1.2.1 hbad
      have hp := σ.2
      omega
    simp [f, hne]
  rw [hsum]
  conv_lhs => rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro v hv
  have hvalid := face_valid K n σ.1 (Finset.mem_sdiff.mp v.2).1
  have hp := (relative_face_iff_good K a p n σ (Finset.mem_sdiff.mp v.2).1).mpr
    (Finset.mem_sdiff.mp v.2).2
  have h : (σ.1.1.erase v.1 ∈ K ∧
      ((n - 1 = -1 ∧ σ.1.1.erase v.1 = ∅) ∨
        (0 ≤ n - 1 ∧ ((σ.1.1.erase v.1).card : ℤ) = (n - 1) + 1))) ∧
        (badVertices a (σ.1.1.erase v.1)).card = p := ⟨hvalid, hp⟩
  have hproof :
      (⟨⟨σ.1.1.erase v.1, hvalid⟩, hp⟩ :
        RelativeSimplexAt K a p (n - 1)) =
      relativeGoodFaceAt K a p n σ v :=
    Subtype.ext (Subtype.ext rfl)
  exact (dite_eq_left h).trans (congrArg
    (fun x : RelativeSimplexAt K a p (n - 1) =>
      (-1 : ℤ) ^ (σ.1.1.filter (· < v.1)).card • FreeAbelianGroup.of x) hproof)

private theorem relativeSplitBasis_good_face (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ)
    (σ : RelativeSimplexAt K a p n)
    (v : {v : V // v ∈ σ.1.1 \ badVertices a σ.1.1}) :
    (relativeSplitBasis K a p (n - 1))
      (relativeGoodFaceAt K a p n σ v) =
    ⟨(relativeSplitBasis K a p n σ).1,
      (by
        let z := relativeSplitBasis K a p n σ
        let w : z.2.1 := ⟨v.1, v.2⟩
        have hn : n - (p : ℤ) - 1 = (n - 1) - p := by omega
        have hf := face_valid (restrictedLink K a z.1) (n - p) z.2 w.2
        exact ⟨z.2.1.erase v.1, hf.1, by simpa only [hn] using hf.2⟩)⟩ := by
  classical
  apply Sigma.ext
  · apply Subtype.ext
    exact bad_support_erase_good K a p n σ
      (Finset.mem_sdiff.mp v.2).1 (Finset.mem_sdiff.mp v.2).2
  · refine (Subtype.heq_iff_coe_heq rfl ?_).2 ?_
    · apply heq_of_eq
      funext x
      congr 1
      congr 1
      congr 1
      apply Subtype.ext
      exact bad_support_erase_good K a p n σ
        (Finset.mem_sdiff.mp v.2).1 (Finset.mem_sdiff.mp v.2).2
    · apply heq_of_eq
      dsimp [relativeSplitBasis, relativeGoodFaceAt]
      ext x
      change x ∈ (σ.1.1.erase v.1 \ badVertices a (σ.1.1.erase v.1)) ↔
        x ∈ (σ.1.1 \ badVertices a σ.1.1).erase v.1
      rw [bad_support_erase_good K a p n σ
        (Finset.mem_sdiff.mp v.2).1 (Finset.mem_sdiff.mp v.2).2]
      simp only [Finset.mem_sdiff, Finset.mem_erase]
      tauto

private noncomputable def relativeSplitForward (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    relativeChains K a p n →+
      DirectSum (strata K a p)
        (fun S => chains (restrictedLink K a S) (n - p)) := by
  classical
  exact FreeAbelianGroup.lift fun σ =>
    let z := relativeSplitBasis K a p n σ
    splitSign z.1.1 z.2.1 •
      DirectSum.of (fun S : strata K a p =>
        chains (restrictedLink K a S) (n - p)) z.1 (FreeAbelianGroup.of z.2)

private noncomputable def relativeSplitBackward (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    DirectSum (strata K a p)
      (fun S => chains (restrictedLink K a S) (n - p)) →+
        relativeChains K a p n := by
  classical
  exact DirectSum.toAddMonoid fun S =>
    FreeAbelianGroup.lift fun τ =>
      splitSign S.1 τ.1 •
        FreeAbelianGroup.of ((relativeSplitBasis K a p n).symm ⟨S, τ⟩)

private noncomputable def relativeSplitEquiv (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    relativeChains K a p n ≃+
      DirectSum (strata K a p)
        (fun S => chains (restrictedLink K a S) (n - p)) := by
  classical
  let f := relativeSplitForward K a p n
  let g := relativeSplitBackward K a p n
  refine {
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    map_add' := f.map_add }
  · intro c
    induction c using FreeAbelianGroup.induction_on with
    | zero => simp [f, g]
    | add x y hx hy => simp [map_add, hx, hy]
    | neg x hx => simp [map_neg, hx]
    | of σ =>
      let z := relativeSplitBasis K a p n σ
      change g (f (FreeAbelianGroup.of σ)) = FreeAbelianGroup.of σ
      simp only [f, relativeSplitForward, FreeAbelianGroup.lift_apply_of,
        g, relativeSplitBackward, map_zsmul, DirectSum.toAddMonoid_of,
        FreeAbelianGroup.lift_apply_of]
      rw [smul_smul, splitSign_sq, one_smul]
      exact congrArg FreeAbelianGroup.of ((relativeSplitBasis K a p n).symm_apply_apply σ)
  · intro c
    induction c using DirectSum.induction_on with
    | zero => simp [f, g]
    | add x y hx hy => simp [map_add, hx, hy]
    | of S x =>
      induction x using FreeAbelianGroup.induction_on with
      | zero => simp [f, g]
      | add x y hx hy => simp [map_add, hx, hy]
      | neg x hx => simp [map_neg, hx]
      | of τ =>
        change f (g (DirectSum.of _ S (FreeAbelianGroup.of τ))) =
          DirectSum.of _ S (FreeAbelianGroup.of τ)
        simp only [g, relativeSplitBackward, DirectSum.toAddMonoid_of,
          FreeAbelianGroup.lift_apply_of, f, relativeSplitForward, map_zsmul,
          FreeAbelianGroup.lift_apply_of]
        rw [smul_smul]
        have hz : (relativeSplitBasis K a p n)
            ((relativeSplitBasis K a p n).symm ⟨S, τ⟩) =
            (⟨S, τ⟩ :
              Σ S : strata K a p, SimplexAt (restrictedLink K a S) (n - p)) :=
          (relativeSplitBasis K a p n).apply_symm_apply ⟨S, τ⟩
        rw [hz]
        rw [splitSign_sq, one_smul]

theorem relativeChains_split (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) :
    ∃ e : (n : ℤ) → relativeChains K a p n ≃+
      DirectSum (strata K a p)
        (fun S => chains (restrictedLink K a S) (n - p)),
      ∀ n : ℤ, ∀ c : relativeChains K a p n,
        e (n - 1) (relativeBoundary K a p n c) =
          DirectSum.map (fun S : strata K a p =>
            ((-1 : ℤ) ^ p) •
              (by
                have hn : n - (p : ℤ) - 1 = (n - 1) - p := by omega
                rw [← hn]
                exact boundary (restrictedLink K a S) (n - p) :
                chains (restrictedLink K a S) (n - p) →+
                  chains (restrictedLink K a S) ((n - 1) - p)))
            (e n c) := by
  classical
  refine ⟨relativeSplitEquiv K a p, ?_⟩
  intro n c
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | neg x hx => simp [map_neg, hx]
  | of σ =>
    have hn : n - (p : ℤ) - 1 = (n - 1) - p := by omega
    change relativeSplitForward K a p (n - 1)
      (relativeBoundary K a p n (FreeAbelianGroup.of σ)) =
        DirectSum.map _ (relativeSplitForward K a p n (FreeAbelianGroup.of σ))
    simp only [relativeBoundary, FreeAbelianGroup.lift_apply_of,
      relativeSplitForward, map_zsmul]
    rw [relativeFaceBoundary_good_eq]
    simp only [map_sum, map_zsmul, FreeAbelianGroup.lift_apply_of]
    simp_rw [relativeSplitBasis_good_face K a p n σ]
    simp only [DirectSum.map_of]
    simp only [AddMonoidHom.smul_apply]
    rw [shiftedBoundary_face_sum
      (L := restrictedLink K a ((relativeSplitBasis K a p n σ).1))
      p n ((relativeSplitBasis K a p n σ).2)]
    let L := restrictedLink K a ((relativeSplitBasis K a p n σ).1)
    generalize hz : relativeSplitBasis K a p n σ = z at *
    simp only [Finset.smul_sum, map_sum, map_zsmul, smul_smul]
    subst z
    apply Finset.sum_congr rfl
    intro v hv
    rw [relativeSplitBasis_good_face K a p n σ v]
    rw [cast_chains_of
      (restrictedLink K a ((relativeSplitBasis K a p n σ).1))
      hn
      (faceAt (restrictedLink K a ((relativeSplitBasis K a p n σ).1))
        (n - p) (relativeSplitBasis K a p n σ).2 v)]
    congr 1
    · have hcoeff := splitSign_coeff
        (relativeSplitBasis K a p n σ).1.1
        (relativeSplitBasis K a p n σ).2.1 p
        (relativeSplitBasis K a p n σ).2.2.1.1
        (relativeSplitBasis K a p n σ).1.2.2.1 v.2
      have hunion :
          (relativeSplitBasis K a p n σ).1.1 ∪
            (relativeSplitBasis K a p n σ).2.1 = σ.1.1 := by
        change badVertices a σ.1.1 ∪
          (σ.1.1 \ badVertices a σ.1.1) = σ.1.1
        exact Finset.union_sdiff_of_subset (Finset.filter_subset _ _)
      rw [hunion] at hcoeff
      simpa only [relativeSplitBasis_good_face] using hcoeff
    · congr 1
      congr 1
      apply Subtype.ext
      simpa only [faceAt] using
        (cast_simplex_val
          (restrictedLink K a ((relativeSplitBasis K a p n σ).1)) hn
          (faceAt (restrictedLink K a ((relativeSplitBasis K a p n σ).1))
            (n - p) (relativeSplitBasis K a p n σ).2 v)).symm

end Chains

end CurveGenusTwo.Filtration
