import Mathlib

/-!
Section 8 and the homology assembly of Section 11 of
`references/curve-complex-genus-two.pdf`. All theorem bodies are obligations.
-/

namespace CurveGenusTwo.Filtration

universe u v

/-- An abstract complex of finite vertex sets. The empty set need not be a simplex. -/
structure FiniteComplex (V : Type u) where
  simplices : Set (Finset V)
  down_closed : ∀ ⦃σ τ : Finset V⦄, τ ⊆ σ → σ ∈ simplices → τ ∈ simplices

instance {V : Type u} : Membership (Finset V) (FiniteComplex V) := ⟨fun K σ => σ ∈ K.simplices⟩

@[ext] theorem FiniteComplex.ext {V : Type u} {K L : FiniteComplex V}
    (h : K.simplices = L.simplices) : K = L := by
  cases K; cases L; simp_all

/-- Convention 8.1: the void complex has no simplex, including the empty simplex. -/
def void (V : Type u) : FiniteComplex V where
  simplices := ∅
  down_closed := by simp

/-- Convention 8.1: the empty-only complex contains exactly the empty simplex. -/
def emptyOnly (V : Type u) : FiniteComplex V where
  simplices := {∅}
  down_closed := by
    intro σ τ hsub hσ
    simp only [Set.mem_singleton_iff] at hσ ⊢
    subst σ
    exact Finset.subset_empty.mp hsub

structure ArcLabels (V : Type u) (B : Type v) where
  isLoop : V → Prop
  endpointPair : V → Finset B
  nonloop_endpoint_card : ∀ v, ¬ isLoop v → (endpointPair v).card = 2

variable {V : Type u} {B : Type v} [DecidableEq V]

/-- Definition 8.2: every loop is bad, and each member of a repeated endpoint pair is bad. -/
noncomputable def badVertices (a : ArcLabels V B) (σ : Finset V) : Finset V := by
  classical
  exact σ.filter fun v => a.isLoop v ∨
    ∃ w ∈ σ, w ≠ v ∧ ¬ a.isLoop v ∧ ¬ a.isLoop w ∧
      a.endpointPair w = a.endpointPair v

theorem badVertices_mono (a : ArcLabels V B) {τ σ : Finset V} (h : τ ⊆ σ) :
    badVertices a τ ⊆ badVertices a σ := by
  classical
  intro v hv
  simp only [badVertices, Finset.mem_filter] at hv ⊢
  refine ⟨h hv.1, ?_⟩
  rcases hv.2 with hl | ⟨w, hw, hne, hvl, hwl, heq⟩
  · exact Or.inl hl
  · exact Or.inr ⟨w, h hw, hne, hvl, hwl, heq⟩

theorem badVertices_empty (a : ArcLabels V B) : badVertices a ∅ = ∅ := by
  simp [badVertices]

/-- Definition 8.4, with `p = -1` permitted. -/
def filtration (K : FiniteComplex V) (a : ArcLabels V B) (p : ℤ) :
    FiniteComplex V where
  simplices := {σ | σ ∈ K ∧ (badVertices a σ).card ≤ p}
  down_closed := by
    intro σ τ hsub hσ
    exact ⟨K.down_closed hsub hσ.1,
      le_trans (by exact_mod_cast Finset.card_le_card (badVertices_mono a hsub)) hσ.2⟩

/-- Definition 8.4: the full bad support is the stratum simplex. -/
def strata (K : FiniteComplex V) (a : ArcLabels V B) (p : ℕ) : Type u :=
  {S : Finset V // S ∈ K ∧ S.card = p ∧ badVertices a S = S}

/-- Definition 8.4: simplices in the link of `S` with no new bad vertices. -/
def restrictedLinkSet (K : FiniteComplex V) (a : ArcLabels V B)
    (S : Finset V) : Set (Finset V) :=
  {τ | Disjoint S τ ∧ S ∪ τ ∈ K ∧ badVertices a (S ∪ τ) = S}

theorem restrictedLinkSet_down (K : FiniteComplex V) (a : ArcLabels V B)
    (S : Finset V) (hS : badVertices a S = S) ⦃τ υ : Finset V⦄
    (hυ : υ ⊆ τ) (hτ : τ ∈ restrictedLinkSet K a S) :
    υ ∈ restrictedLinkSet K a S := by
  rcases hτ with ⟨hdisj, hmem, hbad⟩
  have hunion : S ∪ υ ⊆ S ∪ τ :=
    Finset.union_subset Finset.subset_union_left (hυ.trans Finset.subset_union_right)
  have hlow : S ⊆ badVertices a (S ∪ υ) := by
    have hm := badVertices_mono a (Finset.subset_union_left : S ⊆ S ∪ υ)
    simpa only [hS] using hm
  have hhigh : badVertices a (S ∪ υ) ⊆ S := by
    have hm := badVertices_mono a hunion
    simpa only [hbad] using hm
  exact ⟨hdisj.mono_right hυ, K.down_closed hunion hmem,
    Finset.Subset.antisymm hhigh hlow⟩

def restrictedLink (K : FiniteComplex V) (a : ArcLabels V B)
    (S : strata K a p) : FiniteComplex V where
  simplices := restrictedLinkSet K a S.1
  down_closed := restrictedLinkSet_down K a S.1 S.2.2.2

theorem filtration_neg_one_eq_void (K : FiniteComplex V) (a : ArcLabels V B) :
    filtration K a (-1) = void V := by
  apply FiniteComplex.ext
  ext σ
  simp only [filtration, void, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  omega

theorem empty_mem_filtration_zero (K : FiniteComplex V) (a : ArcLabels V B)
    (h : (∅ : Finset V) ∈ K) : (∅ : Finset V) ∈ filtration K a 0 := by
  exact ⟨h, by simp [badVertices_empty]⟩

theorem strata_zero_unique (K : FiniteComplex V) (a : ArcLabels V B)
    (h : (∅ : Finset V) ∈ K) : ∃! S : strata K a 0, S.1 = ∅ := by
  refine ⟨⟨∅, h, by simp, badVertices_empty a⟩, rfl, ?_⟩
  intro S hS
  exact Subtype.ext hS

/-- `X` is the simplex complex with no bad vertices, before its geometric identification. -/
def goodSubcomplex (K : FiniteComplex V) (a : ArcLabels V B) : FiniteComplex V :=
  filtration K a 0

theorem filtration_zero_eq_good (K : FiniteComplex V) (a : ArcLabels V B) :
    filtration K a 0 = goodSubcomplex K a := rfl

theorem restrictedLink_zero_eq_good (K : FiniteComplex V) (a : ArcLabels V B)
    (h : (∅ : Finset V) ∈ K) (S : strata K a 0) :
    restrictedLink K a S = goodSubcomplex K a := by
  have hS : S.1 = ∅ := Finset.card_eq_zero.mp S.2.2.1
  apply FiniteComplex.ext
  ext τ
  simp only [restrictedLink, restrictedLinkSet, goodSubcomplex, filtration,
    Set.mem_setOf_eq]
  rw [hS]
  simp [Finset.card_eq_zero]

theorem filtration_top (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12) :
    filtration K a 12 = K := by
  apply FiniteComplex.ext
  ext σ
  constructor
  · exact And.left
  · intro hσ
    exact ⟨hσ, by
      classical
      have hsub : badVertices a σ ⊆ σ := Finset.filter_subset _ _
      have := Finset.card_le_card hsub
      exact_mod_cast this.trans (hcard σ hσ)⟩

theorem strata_above_twelve_empty (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12) {p : ℕ} (hp : 12 < p) :
    IsEmpty (strata K a p) := by
  refine ⟨fun S => ?_⟩
  have := hcard S.1 S.2.1
  have := S.2.2.1
  omega

theorem bad_support_in_strata (K : FiniteComplex V) (a : ArcLabels V B)
    {σ : Finset V} (hσ : σ ∈ K) (p : ℕ)
    (hp : (badVertices a σ).card = p) :
    badVertices a σ ∈ K ∧ badVertices a (badVertices a σ) = badVertices a σ := by
  classical
  constructor
  · exact K.down_closed (Finset.filter_subset _ _) hσ
  · apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro v hv
    simp only [badVertices, Finset.mem_filter] at hv ⊢
    refine ⟨hv, ?_⟩
    rcases hv.2 with hl | ⟨w, hw, hne, hvl, hwl, heq⟩
    · exact Or.inl hl
    · right
      have hwbad : w ∈ badVertices a σ := by
        simp only [badVertices, Finset.mem_filter]
        exact ⟨hw, Or.inr ⟨v, hv.1, Ne.symm hne, hwl, hvl, heq.symm⟩⟩
      exact ⟨w, by simpa only [badVertices, Finset.mem_filter] using hwbad,
        hne, hvl, hwl, heq⟩

theorem unique_bad_support_split (K : FiniteComplex V) (a : ArcLabels V B)
    {σ : Finset V} (hσ : σ ∈ K) (p : ℕ)
    (hp : (badVertices a σ).card = p) :
    ∃! S : strata K a p,
      ∃ τ : Finset V, τ ∈ restrictedLink K a S ∧ σ = S.1 ∪ τ := by
  classical
  let T := badVertices a σ
  have hT := bad_support_in_strata K a hσ p hp
  have hsub : T ⊆ σ := Finset.filter_subset _ _
  refine ⟨⟨T, hT.1, hp, hT.2⟩, ?_, ?_⟩
  · refine ⟨σ \ T, ?_, (Finset.union_sdiff_of_subset hsub).symm⟩
    change (σ \ T) ∈ restrictedLinkSet K a T
    exact ⟨Finset.disjoint_sdiff, by simpa [Finset.union_sdiff_of_subset hsub] using hσ,
      by simp [Finset.union_sdiff_of_subset hsub, T]⟩
  · intro S ⟨τ, hτ, hsplit⟩
    apply Subtype.ext
    have hbad : badVertices a σ = S.1 := by
      rw [hsplit]
      exact hτ.2.2
    exact hbad.symm

theorem erase_good_preserves_bad_support (K : FiniteComplex V) (a : ArcLabels V B)
    {σ : Finset V} (hσ : σ ∈ K) {u : V} (hu : u ∈ σ)
    (hgood : u ∉ badVertices a σ) :
    badVertices a (σ.erase u) = badVertices a σ := by
  classical
  apply Finset.Subset.antisymm
  · exact badVertices_mono a (Finset.erase_subset u σ)
  · intro v hv
    have hv' := hv
    simp only [badVertices, Finset.mem_filter] at hv' ⊢
    have hvne : v ≠ u := by
      intro heq
      subst v
      exact hgood hv
    refine ⟨Finset.mem_erase.mpr ⟨hvne, hv'.1⟩, ?_⟩
    rcases hv'.2 with hl | ⟨w, hw, hwne, hvl, hwl, heq⟩
    · exact Or.inl hl
    · right
      have hwne_u : w ≠ u := by
        intro heqwu
        subst w
        apply hgood
        simp only [badVertices, Finset.mem_filter]
        exact ⟨hu, Or.inr ⟨v, hv'.1, hwne.symm, hwl, hvl, heq.symm⟩⟩
      exact ⟨w, Finset.mem_erase.mpr ⟨hwne_u, hw⟩, hwne, hvl, hwl, heq⟩

theorem erase_bad_lowers_count (K : FiniteComplex V) (a : ArcLabels V B)
    {σ : Finset V} (hσ : σ ∈ K) {v : V} (hv : v ∈ badVertices a σ) :
    (badVertices a (σ.erase v)).card < (badVertices a σ).card := by
  classical
  apply Finset.card_lt_card
  have hsub : badVertices a (σ.erase v) ⊆ badVertices a σ :=
    badVertices_mono a (Finset.erase_subset v σ)
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro heq
  have : v ∈ badVertices a (σ.erase v) := heq.symm ▸ hv
  have hmem : v ∈ σ.erase v := (Finset.filter_subset _ _) this
  simp at hmem

end CurveGenusTwo.Filtration
