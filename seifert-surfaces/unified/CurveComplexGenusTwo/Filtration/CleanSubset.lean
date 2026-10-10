import CurveComplexGenusTwo.Filtration.Combinatorics

namespace CurveGenusTwo.Filtration

universe u v

variable {V : Type u} {B : Type v} [DecidableEq V]

theorem restricted_link_remainder_unique
    (K : FiniteComplex V) (a : ArcLabels V B)
    {σ : Finset V} (hσ : σ ∈ K) (p : ℕ)
    (hp : (badVertices a σ).card = p)
    (S S' : strata K a p) (τ τ' : Finset V)
    (hτ : τ ∈ restrictedLink K a S) (hτ' : τ' ∈ restrictedLink K a S')
    (h : σ = S.1 ∪ τ) (h' : σ = S'.1 ∪ τ') :
    S = S' ∧ τ = τ' := by
  have hS : S.1 = badVertices a σ := by simpa [h] using hτ.2.2.symm
  have hS' : S'.1 = badVertices a σ := by simpa [h'] using hτ'.2.2.symm
  have hSS' : S = S' := Subtype.ext (hS.trans hS'.symm)
  subst S'
  refine ⟨rfl, ?_⟩
  have hd : Disjoint S.1 τ := hτ.1
  have hd' : Disjoint S.1 τ' := hτ'.1
  apply Finset.Subset.antisymm
  · intro x hx
    have hxσ : x ∈ σ := h ▸ Finset.mem_union_right _ hx
    rw [h'] at hxσ
    rcases Finset.mem_union.mp hxσ with hxS | hxτ'
    · exact False.elim ((Finset.disjoint_left.mp hd) hxS hx)
    · exact hxτ'
  · intro x hx
    have hxσ : x ∈ σ := h' ▸ Finset.mem_union_right _ hx
    rw [h] at hxσ
    rcases Finset.mem_union.mp hxσ with hxS | hxτ
    · exact False.elim ((Finset.disjoint_left.mp hd') hxS hx)
    · exact hxτ

theorem filtration_mono (K : FiniteComplex V) (a : ArcLabels V B)
    {p p' : ℤ} (h : p ≤ p') :
    (filtration K a p).simplices ⊆ (filtration K a p').simplices := by
  intro σ hσ
  exact ⟨hσ.1, le_trans hσ.2 h⟩

section Chains

variable [LinearOrder V]

def SimplexAt (K : FiniteComplex V) (n : ℤ) : Type u :=
  {σ : Finset V // σ ∈ K ∧
    ((n = -1 ∧ σ = ∅) ∨ (0 ≤ n ∧ (σ.card : ℤ) = n + 1))}

abbrev chains (K : FiniteComplex V) (n : ℤ) : Type u := FreeAbelianGroup (SimplexAt K n)

noncomputable def chainInclusion (K L : FiniteComplex V)
    (h : K.simplices ⊆ L.simplices) (n : ℤ) : chains K n →+ chains L n :=
  FreeAbelianGroup.lift fun σ =>
    FreeAbelianGroup.of
      (⟨σ.1, h σ.2.1, σ.2.2⟩ : SimplexAt L n)

noncomputable def faceBoundary (K : FiniteComplex V) (n : ℤ)
    (σ : SimplexAt K n) : chains K (n - 1) := by
  classical
  exact ∑ v ∈ σ.1,
    if h : (σ.1.erase v ∈ K ∧
      (((n - 1) = -1 ∧ σ.1.erase v = ∅) ∨
        (0 ≤ n - 1 ∧ ((σ.1.erase v).card : ℤ) = (n - 1) + 1))) then
      (-1 : ℤ) ^ (σ.1.filter (· < v)).card •
        FreeAbelianGroup.of (⟨σ.1.erase v, h⟩ : SimplexAt K (n - 1))
    else 0

noncomputable def boundary (K : FiniteComplex V) (n : ℤ) :
    chains K n →+ chains K (n - 1) :=
  FreeAbelianGroup.lift (faceBoundary K n)

noncomputable def cycles (K : FiniteComplex V) (n : ℤ) :
    AddSubgroup (chains K n) := (boundary K n).ker

noncomputable def boundaries (K : FiniteComplex V) (n : ℤ) :
    AddSubgroup (chains K n) := by
  have hn : n + 1 - 1 = n := by omega
  exact Eq.mp (congrArg (fun m : ℤ => AddSubgroup (chains K m)) hn)
    (boundary K (n + 1)).range

noncomputable abbrev reducedHomology (K : FiniteComplex V) (n : ℤ) : Type u :=
  (cycles K n) ⧸ ((boundaries K n).comap (cycles K n).subtype)

theorem void_chains_subsingleton (n : ℤ) :
    Subsingleton (chains (void V) n) := by
  have : IsEmpty (SimplexAt (void V) n) := ⟨fun σ => σ.2.1⟩
  infer_instance

theorem emptyOnly_minus_one_chains :
    Nonempty (chains (emptyOnly V) (-1) ≃+ ℤ) := by
  letI : Unique (SimplexAt (emptyOnly V) (-1)) := {
    default := ⟨∅, by
      constructor
      · change (∅ : Finset V) ∈ ({∅} : Set (Finset V))
        simp
      · exact Or.inl ⟨rfl, rfl⟩⟩
    uniq := by
      intro σ
      apply Subtype.ext
      have hmem := σ.2.1
      change σ.1 ∈ ({∅} : Set (Finset V)) at hmem
      simpa using hmem
  }
  exact ⟨(FreeAbelianGroup.equivFinsupp _).trans (Finsupp.uniqueAddEquiv default)⟩

theorem void_reducedHomology_subsingleton (n : ℤ) :
    Subsingleton (reducedHomology (void V) n) := by
  letI := void_chains_subsingleton (V := V) n
  refine ⟨fun x y => ?_⟩
  induction x using Quotient.inductionOn with
  | _ x =>
    induction y using Quotient.inductionOn with
    | _ y => congr 1; exact Subsingleton.elim x y

private theorem boundary_minus_one_zero (K : FiniteComplex V) :
    boundary K (-1) = 0 := by
  apply FreeAbelianGroup.lift_ext
  intro σ
  have hσ : σ.1 = ∅ := by
    rcases σ.2.2 with h | h
    · exact h.2
    · omega
  simp [boundary, faceBoundary, hσ]

theorem emptyOnly_minus_one_homology :
    Nonempty (reducedHomology (emptyOnly V) (-1) ≃+ ℤ) := by
  have hc : cycles (emptyOnly V) (-1) = ⊤ := by
    simp [cycles, boundary_minus_one_zero]
  have hEmpty : IsEmpty (SimplexAt (emptyOnly V) 0) := ⟨by
      intro σ
      have hσ : σ.1 = ∅ := σ.2.1
      rcases σ.2.2 with h | h
      · omega
      · have hc : (σ.1.card : ℤ) = 0 := by simp [hσ]
        omega⟩
  have hzero : Subsingleton (chains (emptyOnly V) 0) := by
    infer_instance
  have hb : boundaries (emptyOnly V) (-1) = ⊥ := by
    have hmap : boundary (emptyOnly V) 0 = 0 := by
      ext x
      exact isEmptyElim x
    simp [boundaries, hmap]
  obtain ⟨e⟩ := emptyOnly_minus_one_chains (V := V)
  change Nonempty (((cycles (emptyOnly V) (-1)) ⧸
    ((boundaries (emptyOnly V) (-1)).comap
      (cycles (emptyOnly V) (-1)).subtype)) ≃+ ℤ)
  rw [hc, hb]
  have hker : (⊤ : AddSubgroup (chains (emptyOnly V) (-1))).subtype.ker = ⊥ := by
    ext x
    simp
  change Nonempty (((⊤ : AddSubgroup (chains (emptyOnly V) (-1))) ⧸
    (⊤ : AddSubgroup (chains (emptyOnly V) (-1))).subtype.ker) ≃+ ℤ)
  rw [hker]
  simpa using
    (show Nonempty (((⊤ : AddSubgroup (chains (emptyOnly V) (-1))) ⧸ ⊥) ≃+ ℤ) from
      ⟨(QuotientAddGroup.quotientBot).trans (AddSubgroup.topEquiv.trans e)⟩)

theorem emptyOnly_other_homology (n : ℤ) (hn : n ≠ -1) :
    Subsingleton (reducedHomology (emptyOnly V) n) := by
  have hEmpty : IsEmpty (SimplexAt (emptyOnly V) n) := ⟨by
    intro σ
    have hσ : σ.1 = ∅ := σ.2.1
    rcases σ.2.2 with h | h
    · exact hn h.1
    · have hc : (σ.1.card : ℤ) = 0 := by simp [hσ]
      omega⟩
  have hchain : Subsingleton (chains (emptyOnly V) n) := inferInstance
  refine ⟨fun x y => ?_⟩
  induction x using Quotient.inductionOn with
  | _ x =>
    induction y using Quotient.inductionOn with
    | _ y => congr 1; exact Subsingleton.elim x y

def RelativeSimplexAt (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) (n : ℤ) : Type u :=
  {σ : SimplexAt K n // (badVertices a σ.1).card = p}

abbrev relativeChains (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) (n : ℤ) : Type u := FreeAbelianGroup (RelativeSimplexAt K a p n)

theorem relativeChains_above_twelve (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12)
    {p : ℕ} (hp : 12 < p) (n : ℤ) :
    Subsingleton (relativeChains K a p n) := by
  classical
  have : IsEmpty (RelativeSimplexAt K a p n) := ⟨by
    intro σ
    have hsub : badVertices a σ.1.1 ⊆ σ.1.1 := Finset.filter_subset _ _
    have hle := (Finset.card_le_card hsub).trans (hcard σ.1.1 σ.1.2.1)
    have hp' := σ.2
    omega⟩
  infer_instance

end Chains

end CurveGenusTwo.Filtration
