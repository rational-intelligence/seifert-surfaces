import CurveComplexGenusTwo.Topology.StarCompatibleFace
import CurveComplexGenusTwo.Topology.StarConeChart

set_option linter.style.haveILetI false

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
private theorem finite_link_point_ext
    (K : AbstractSimplicialComplex V) {x y : RealizationPoint K}
    (h : x.weight = y.weight) : x = y := by
  cases x with
  | mk wx hx px =>
    cases y with
    | mk wy hy py =>
      cases h
      rfl

omit [DecidableEq V] in
theorem finiteSimplex_compact (σ : Finset V) :
    CompactSpace (FiniteSimplex σ) := by
  classical
  let s : Set (σ → ℝ) := {x | (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1}
  have hs : IsClosed s := by
    have heq : s =
        (⋂ v : σ, {x : σ → ℝ | 0 ≤ x v}) ∩
          {x : σ → ℝ | ∑ v, x v = 1} := by
      ext x
      simp [s]
    rw [heq]
    have hsumcont : Continuous (fun x : σ → ℝ => ∑ v, x v) :=
      continuous_finsetSum _ (fun v _ => continuous_apply v)
    exact (isClosed_iInter (fun v : σ =>
      isClosed_le continuous_const (continuous_apply v))).inter
      (isClosed_eq hsumcont continuous_const)
  have hbounded : s ⊆ Set.Icc (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) := by
    intro x hx
    rcases hx with ⟨hxnonneg, hxsum⟩
    constructor
    · exact hxnonneg
    · intro v
      calc
        x v ≤ ∑ w, x w := Finset.single_le_sum (fun w _ => hxnonneg w)
          (Finset.mem_univ v)
        _ = 1 := hxsum
  have hc : IsCompact s := IsCompact.of_isClosed_subset isCompact_Icc hs hbounded
  exact isCompact_iff_compactSpace.mp hc

omit [DecidableEq V] in
/-- Every finite face has compact image in the weak realization. -/
theorem isCompact_range_faceInclusion
    (K : AbstractSimplicialComplex V) (σ : Finset V)
    (hσ : σ ∈ K.faces) :
    IsCompact (Set.range (faceInclusion K σ hσ)) := by
  letI := finiteSimplex_compact σ
  have hcont : Continuous (faceInclusion K σ hσ) := by
    rw [continuous_def]
    intro U hU
    exact hU σ hσ
  have himg := isCompact_univ.image hcont
  convert himg using 1
  ext x
  simp

/-- A finite face of the separating link maps continuously into the actual
realized link subspace. -/
noncomputable def finiteLinkFaceMap
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u})
    (τ : Finset V) (hτ : τ ∈ K.faces)
    (hlink : LinkFace intersect v τ) :
    FiniteSimplex τ → RealizedSeparatingLink K intersect separating v := by
  intro p
  let x := faceInclusion K τ hτ p
  refine ⟨x, ?_⟩
  change x ∈ ClosedStarLocus K intersect v ∩
    NonseparatingWeightLocus K separating
  constructor
  · refine ⟨τ, hτ, hlink.2, ?_⟩
    intro w hw
    simp [x, faceInclusion, hw]
  · intro w hw
    by_cases hwt : w ∈ τ
    · exact False.elim
        ((separating_link_in_nonseparating intersect separating hsep
          v v.property τ hlink).2 w hwt hw)
    · simp [x, faceInclusion, hwt]

theorem finiteLinkFaceMap_continuous
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u})
    (τ : Finset V) (hτ : τ ∈ K.faces)
    (hlink : LinkFace intersect v τ) :
    Continuous (finiteLinkFaceMap K intersect separating hsep v τ hτ hlink) := by
  apply Continuous.subtype_mk
  rw [continuous_def]
  intro U hU
  exact hU τ hτ

theorem finiteLinkFaceMap_range_compact
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u})
    (τ : Finset V) (hτ : τ ∈ K.faces)
    (hlink : LinkFace intersect v τ) :
    IsCompact (Set.range
      (finiteLinkFaceMap K intersect separating hsep v τ hτ hlink)) := by
  letI := finiteSimplex_compact τ
  have himg := isCompact_univ.image
    (finiteLinkFaceMap_continuous K intersect separating hsep v τ hτ hlink)
  rw [show Set.range (finiteLinkFaceMap K intersect separating hsep v τ hτ hlink) =
      finiteLinkFaceMap K intersect separating hsep v τ hτ hlink '' Set.univ by
        ext y
        simp]
  simpa using himg

/-- The compact image is exactly the link points supported on the given face. -/
theorem finiteLinkFaceMap_range_eq_support
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u})
    (τ : Finset V) (hτ : τ ∈ K.faces)
    (hlink : LinkFace intersect v τ) :
    Set.range (finiteLinkFaceMap K intersect separating hsep v τ hτ hlink) =
      {x : RealizedSeparatingLink K intersect separating v |
        ∀ w ∉ τ, x.1.weight w = 0} := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩ w hw
    simp [finiteLinkFaceMap, faceInclusion, hw]
  · intro hx
    obtain ⟨ρ, _, hρzero, hρsum⟩ := x.1.liesInFace
    have hτu : ∑ w ∈ τ, x.1.weight w =
        ∑ w ∈ τ ∪ ρ, x.1.weight w := by
      apply Finset.sum_subset_zero_on_sdiff
      · exact Finset.subset_union_left
      · intro w hw
        exact hx w (Finset.mem_sdiff.mp hw).2
      · intro w hw
        rfl
    have hρu : ∑ w ∈ ρ, x.1.weight w =
        ∑ w ∈ τ ∪ ρ, x.1.weight w := by
      apply Finset.sum_subset_zero_on_sdiff
      · exact Finset.subset_union_right
      · intro w hw
        exact hρzero w (Finset.mem_sdiff.mp hw).2
      · intro w hw
        rfl
    have hsum : ∑ w ∈ τ, x.1.weight w = 1 := by
      calc
        _ = ∑ w ∈ τ ∪ ρ, x.1.weight w := hτu
        _ = ∑ w ∈ ρ, x.1.weight w := hρu.symm
        _ = 1 := hρsum
    let p : FiniteSimplex τ :=
      ⟨fun w => x.1.weight w, (fun w => x.1.nonneg w), by
        simpa only [Finset.sum_attach, Finset.univ_eq_attach] using hsum⟩
    refine ⟨p, ?_⟩
    apply Subtype.ext
    apply finite_link_point_ext K
    funext w
    by_cases hw : w ∈ τ
    · simp [finiteLinkFaceMap, faceInclusion, p, hw]
    · simp [finiteLinkFaceMap, faceInclusion, p, hw, hx w hw]

end CurveComplexGenusTwo.Topology
