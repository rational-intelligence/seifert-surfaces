import CurveComplexGenusTwo.Foundations.RealizationCW

set_option maxHeartbeats 1000000

namespace CurveComplex

open Set

variable {V : Type*} [DecidableEq V]

/-- The realized full subcomplex on vertices satisfying `P`. -/
def fullSupportLocus (K : AbstractSimplicialComplex V) (P : V → Prop) :
    Set (RealizationPoint K) :=
  {x | ∀ w, ¬ P w → x.weight w = 0}

theorem isClosed_fullSupportLocus
    (K : AbstractSimplicialComplex V) (P : V → Prop) :
    IsClosed (fullSupportLocus K P) := by
  classical
  let D (w : V) : Set (RealizationPoint K) :=
    if P w then Set.univ else {x | x.weight w = 0}
  have hD (w : V) : IsClosed (D w) := by
    by_cases hw : P w
    · simp [D, hw]
    · simpa [D, hw] using
        (isClosed_eq (continuous_weight K w) continuous_const)
  have heq : fullSupportLocus K P = ⋂ w, D w := by
    ext x
    simp only [fullSupportLocus, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hx w
      by_cases hw : P w
      · simp [D, hw]
      · simpa [D, hw] using hx w hw
    · intro hx w hw
      simpa [D, hw] using hx w
  rw [heq]
  exact isClosed_iInter hD

/-- Nonempty finite faces all of whose vertices satisfy `P`. -/
def FullFaceIndex (K : AbstractSimplicialComplex V) (P : V → Prop) :=
  {σ : Finset V // σ ∈ K.faces ∧ ∀ w ∈ σ, P w}

noncomputable def fullFaceInclusion
    (K : AbstractSimplicialComplex V) (P : V → Prop)
    (σ : FullFaceIndex K P) :
    FiniteSimplex σ.1 → fullSupportLocus K P := by
  intro p
  refine ⟨faceInclusion K σ.1 σ.2.1 p, ?_⟩
  intro w hw
  by_cases hmem : w ∈ σ.1
  · exact False.elim (hw (σ.2.2 w hmem))
  · exact faceInclusion_weight_of_not_mem K σ.1 σ.2.1 p w hmem

theorem fullFaceInclusion_continuous
    (K : AbstractSimplicialComplex V) (P : V → Prop)
    (σ : FullFaceIndex K P) :
    Continuous (fullFaceInclusion K P σ) := by
  apply Continuous.subtype_mk
  exact continuous_faceInclusion K σ.1 σ.2.1

theorem isClosed_fullSupportLocus_iff_ambientFaces
    (K : AbstractSimplicialComplex V) (P : V → Prop)
    (S : Set (fullSupportLocus K P)) :
    IsClosed S ↔
      ∀ (σ : Finset V) (hσ : σ ∈ K.faces),
        IsClosed ((faceInclusion K σ hσ) ⁻¹' (Subtype.val '' S)) := by
  have hfull := isClosed_fullSupportLocus K P
  constructor
  · intro hS σ hσ
    exact (hfull.isClosedMap_subtype_val S hS).preimage
      (continuous_faceInclusion K σ hσ)
  · intro hfaces
    have hclosed : IsClosed (Subtype.val '' S : Set (RealizationPoint K)) := by
      rw [← isOpen_compl_iff]
      change ∀ (σ : Finset V) (hσ : σ ∈ K.faces),
        IsOpen ((faceInclusion K σ hσ) ⁻¹' (Subtype.val '' S)ᶜ)
      intro σ hσ
      rw [Set.preimage_compl]
      exact (hfaces σ hσ).isOpen_compl
    have heq : S = Subtype.val ⁻¹' (Subtype.val '' S) := by
      ext x
      simp
    rw [heq]
    exact hclosed.preimage continuous_subtype_val

private theorem fullSupportPoint_supported_on_filteredFace
    (K : AbstractSimplicialComplex V) (P : V → Prop) [DecidablePred P]
    (σ : Finset V) (x : fullSupportLocus K P)
    (hσ : ∀ w ∉ σ, x.1.weight w = 0) :
    ∀ w ∉ σ.filter P, x.1.weight w = 0 := by
  classical
  intro w hw
  by_cases hmem : w ∈ σ
  · have hnP : ¬ P w := by
      intro hP
      exact hw (Finset.mem_filter.mpr ⟨hmem, hP⟩)
    exact x.property w hnP
  · exact hσ w hmem

theorem isClosed_fullSupportLocus_iff_fullFaces
    (K : AbstractSimplicialComplex V) (P : V → Prop)
    (S : Set (fullSupportLocus K P)) :
    IsClosed S ↔
      ∀ σ : FullFaceIndex K P,
        IsClosed ((fullFaceInclusion K P σ) ⁻¹' S) := by
  classical
  constructor
  · intro hS σ
    exact hS.preimage (fullFaceInclusion_continuous K P σ)
  · intro hfaces
    apply (isClosed_fullSupportLocus_iff_ambientFaces K P S).2
    intro σ hσ
    let τ := σ.filter P
    by_cases hne : τ.Nonempty
    · have hτsubset : τ ⊆ σ := by
        exact Finset.filter_subset _ _
      have hτ : τ ∈ K.faces := (K.isRelLowerSet_faces hσ).2 hτsubset hne
      have hP : ∀ w ∈ τ, P w := by
        intro w hw
        exact (Finset.mem_filter.mp hw).2
      let i : FullFaceIndex K P := ⟨τ, hτ, hP⟩
      let f := fullFaceInclusion K P i
      have hC : IsClosed (Subtype.val '' (f '' (f ⁻¹' S)) :
          Set (RealizationPoint K)) := by
        have hp : IsCompact (f ⁻¹' S) := (hfaces i).isCompact
        have hc : Continuous (fun p : FiniteSimplex τ =>
            (f p : RealizationPoint K)) :=
          continuous_subtype_val.comp (fullFaceInclusion_continuous K P i)
        have hi : IsCompact ((fun p : FiniteSimplex τ =>
            (f p : RealizationPoint K)) '' (f ⁻¹' S)) := hp.image hc
        simpa only [Set.image_image, Function.comp_def] using hi.isClosed
      have heq : ((faceInclusion K σ hσ) ⁻¹' (Subtype.val '' S)) =
          ((faceInclusion K σ hσ) ⁻¹' (Subtype.val '' (f '' (f ⁻¹' S)))) := by
        ext p
        constructor
        · rintro ⟨x, hxS, hxp⟩
          have hxσ : ∀ w ∉ σ, x.1.weight w = 0 := by
            intro w hw
            rw [hxp]
            exact faceInclusion_weight_of_not_mem K σ hσ p w hw
          have hxτ := fullSupportPoint_supported_on_filteredFace K P σ x hxσ
          have hxr : x.1 ∈ Set.range (faceInclusion K τ hτ) := by
            rw [← faceCarrier_eq_range_faceInclusion K τ hτ]
            exact hxτ
          rcases hxr with ⟨q, hq⟩
          have hfq : f q = x := Subtype.ext hq
          refine ⟨x, ⟨q, ?_, hfq⟩, hxp⟩
          show f q ∈ S
          rw [hfq]
          exact hxS
        · rintro ⟨x, ⟨q, hqS, hqx⟩, hxp⟩
          exact ⟨x, hqx ▸ hqS, hxp⟩
      rw [heq]
      exact hC.preimage (continuous_faceInclusion K σ hσ)
    · have hτempty : τ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hempty : ((faceInclusion K σ hσ) ⁻¹' (Subtype.val '' S)) = ∅ := by
        ext p
        constructor
        · rintro ⟨x, hxS, hxp⟩
          have hxσ : ∀ w ∉ σ, x.1.weight w = 0 := by
            intro w hw
            rw [hxp]
            exact faceInclusion_weight_of_not_mem K σ hσ p w hw
          have hxτ := fullSupportPoint_supported_on_filteredFace K P σ x hxσ
          have hz : ∀ w : V, x.1.weight w = 0 := by
            intro w
            exact hxτ w (by simp [τ, hτempty])
          obtain ⟨ρ, _, _, hsum⟩ := x.1.liesInFace
          have hzsum : ∑ w ∈ ρ, x.1.weight w = 0 := by
            apply Finset.sum_eq_zero
            intro w _
            exact hz w
          rw [hzsum] at hsum
          norm_num at hsum
        · simp
      rw [hempty]
      exact isClosed_empty

/-- The coproduct of actual finite faces of a full subcomplex induces its
weak subspace topology. -/
noncomputable def fullFaceCoverMap
    (K : AbstractSimplicialComplex V) (P : V → Prop) :
    (Σ σ : FullFaceIndex K P, FiniteSimplex σ.1) →
      fullSupportLocus K P :=
  fun p => fullFaceInclusion K P p.1 p.2

theorem fullFaceCoverMap_isQuotientMap
    (K : AbstractSimplicialComplex V) (P : V → Prop) :
    Topology.IsQuotientMap (fullFaceCoverMap K P) := by
  apply Topology.isQuotientMap_iff_isClosed.mpr
  constructor
  · intro x
    let σ := supportFinset K x.1
    have hσ : σ ∈ K.faces := supportFinset_mem_faces K x.1
    have hP : ∀ w ∈ σ, P w := by
      intro w hw
      by_contra hn
      exact (mem_supportFinset_iff K x.1 w).1 hw (x.property w hn)
    have hxrange : x.1 ∈ Set.range (faceInclusion K σ hσ) := by
      rw [← faceCarrier_eq_range_faceInclusion K σ hσ]
      exact (mem_faceCarrier_iff_support_subset K σ x.1).2 Subset.rfl
    rcases hxrange with ⟨p, hp⟩
    refine ⟨⟨⟨σ, hσ, hP⟩, p⟩, ?_⟩
    exact Subtype.ext hp
  · intro S
    constructor
    · intro hS
      exact hS.preimage (continuous_sigma_iff.mpr (fun σ =>
        fullFaceInclusion_continuous K P σ))
    · intro hpre
      apply (isClosed_fullSupportLocus_iff_fullFaces K P S).2
      intro σ
      exact (isClosed_sigma_iff.mp hpre σ)

end CurveComplex
