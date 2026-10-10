import CurveComplexGenusTwo.Topology.FiniteLinkCompact

set_option linter.style.haveILetI false

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- The full subcomplex on nonseparating vertices is closed in the actual
weak realization. -/
theorem isClosed_nonseparatingWeightLocus
    (K : AbstractSimplicialComplex V) (separating : V → Prop) :
    IsClosed (NonseparatingWeightLocus K separating) := by
  classical
  let D (v : V) : Set (RealizationPoint K) :=
    if separating v then {x | x.weight v = 0} else Set.univ
  have hD (v : V) : IsClosed (D v) := by
    by_cases hv : separating v
    · simpa [D, hv, Set.preimage] using
        (isClosed_singleton.preimage (realization_weight_continuous K v))
    · simp [D, hv]
  have heq : NonseparatingWeightLocus K separating = ⋂ v, D v := by
    ext x
    simp only [NonseparatingWeightLocus, Set.mem_ofPred_eq,
      Set.mem_iInter]
    constructor
    · intro hx v
      by_cases hv : separating v
      · simpa [D, hv] using hx v hv
      · simp [D, hv]
    · intro hx v hv
      simpa [D, hv] using hx v
  rw [heq]
  exact isClosed_iInter hD

/-- The realized separating link is a closed subset of the weak realization
under the full curve-face characterization of the ambient complex. -/
theorem isClosed_realizedSeparatingLink
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop) (v : {u : V // separating u})
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hfull : ∀ σ : Finset V, σ.Nonempty →
      CurveFace intersect 1 σ → σ ∈ K.faces) :
    IsClosed (RealizedSeparatingLink K intersect separating v) := by
  exact (isClosed_closedStarLocus K intersect v hcurve hfull).inter
    (isClosed_nonseparatingWeightLocus K separating)

/-- Closedness in a realized star is tested on every ambient finite face. -/
theorem isClosed_closedStarLocus_iff_faces
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V)
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hfull : ∀ σ : Finset V, σ.Nonempty →
      CurveFace intersect 1 σ → σ ∈ K.faces)
    (S : Set (ClosedStarLocus K intersect v)) :
    IsClosed S ↔
      ∀ (σ : Finset V) (hσ : σ ∈ K.faces),
        IsClosed ((faceInclusion K σ hσ) ⁻¹'
          (Subtype.val '' S)) := by
  have hstar := isClosed_closedStarLocus K intersect v hcurve hfull
  constructor
  · intro hS σ hσ
    exact (hstar.isClosedMap_subtype_val S hS).preimage
      (by rw [continuous_def]; intro U hU; exact hU σ hσ)
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

/-- A closed subset of the realized link is detected on every ambient finite
face. This uses the actual weak realization topology and its closed subspace
topology, so it does not assume a CW structure. -/
theorem isClosed_realizedSeparatingLink_iff_faces
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop) (v : {u : V // separating u})
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hfull : ∀ σ : Finset V, σ.Nonempty →
      CurveFace intersect 1 σ → σ ∈ K.faces)
    (S : Set (RealizedSeparatingLink K intersect separating v)) :
    IsClosed S ↔
      ∀ (σ : Finset V) (hσ : σ ∈ K.faces),
        IsClosed ((faceInclusion K σ hσ) ⁻¹'
          (Subtype.val '' S)) := by
  have hlink := isClosed_realizedSeparatingLink K intersect separating v
    hcurve hfull
  constructor
  · intro hS σ hσ
    exact (hlink.isClosedMap_subtype_val S hS).preimage
      (by rw [continuous_def]; intro U hU; exact hU σ hσ)
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

/-- The part of an ambient face that can support a point of the realized link. -/
def ambientLinkPart (intersect : V → V → ℕ)
    (v : V) (σ : Finset V) : Finset V :=
  (compatiblePart intersect v σ).erase v

theorem ambientLinkPart_face
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (σ : Finset V) (hσ : σ ∈ K.faces)
    (hne : (ambientLinkPart intersect v σ).Nonempty) :
    ambientLinkPart intersect v σ ∈ K.faces := by
  apply (K.isRelLowerSet_faces hσ).2 _ hne
  exact (Finset.erase_subset _ _).trans
    (compatiblePart_subset intersect v σ)

theorem ambientLinkPart_linkFace
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (σ : Finset V) (hσ : σ ∈ K.faces)
    (hcurve : ∀ ρ : Finset V, ρ ∈ K.faces → CurveFace intersect 1 ρ) :
    LinkFace intersect v (ambientLinkPart intersect v σ) := by
  constructor
  · simp [ambientLinkPart]
  · have hs := compatiblePart_closedStarFace K intersect v σ hσ hcurve
    simpa [ambientLinkPart, ClosedStarFace, Finset.insert_erase] using hs

theorem realizedLink_support_ambientLinkPart
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop) (v : {u : V // separating u})
    (σ : Finset V) (x : RealizedSeparatingLink K intersect separating v)
    (hσ : ∀ w ∉ σ, x.1.weight w = 0) :
    ∀ w ∉ ambientLinkPart intersect v σ, x.1.weight w = 0 := by
  intro w hw
  by_cases hwv : w = (v : V)
  · subst w
    exact x.property.2 v v.property
  · have hcomp := closedStar_support_compatiblePart K intersect v σ x.1
      x.property.1 hσ
    apply hcomp
    intro hmem
    exact hw (Finset.mem_erase.mpr ⟨hwv, hmem⟩)

omit [DecidableEq V] in
private theorem realizedPoint_not_supported_empty
    (K : AbstractSimplicialComplex V) (x : RealizationPoint K)
    (hzero : ∀ w : V, x.weight w = 0) : False := by
  obtain ⟨ρ, _, _, hsum⟩ := x.liesInFace
  have hsumzero : ∑ w ∈ ρ, x.weight w = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    exact hzero w
  rw [hsumzero] at hsum
  norm_num at hsum

/-- The actual realized link has the weak topology of its finite link faces.
Equivalently, their inclusions form a quotient cover. -/
theorem isClosed_realizedSeparatingLink_iff_linkFaces
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u})
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hfull : ∀ σ : Finset V, σ.Nonempty →
      CurveFace intersect 1 σ → σ ∈ K.faces)
    (S : Set (RealizedSeparatingLink K intersect separating v)) :
    IsClosed S ↔
      ∀ (τ : Finset V) (hτ : τ ∈ K.faces)
        (hlink : LinkFace intersect v τ),
        IsClosed ((finiteLinkFaceMap K intersect separating hsep v τ hτ hlink) ⁻¹' S) := by
  constructor
  · intro hS τ hτ hlink
    exact hS.preimage
      (finiteLinkFaceMap_continuous K intersect separating hsep v τ hτ hlink)
  · intro hfaces
    haveI : T2Space (RealizationPoint K) := by
      constructor
      intro p q hpq
      have h : ∃ w : V, p.weight w ≠ q.weight w := by
        by_contra hn
        push Not at hn
        apply hpq
        cases p with
        | mk pw pn pl =>
          cases q with
          | mk qw qn ql =>
            have heq : pw = qw := funext hn
            cases heq
            rfl
      obtain ⟨w, hw⟩ := h
      exact separated_by_continuous (realization_weight_continuous K w) hw
    apply (isClosed_realizedSeparatingLink_iff_faces K intersect separating v
      hcurve hfull S).2
    intro σ hσ
    let τ := ambientLinkPart intersect v σ
    by_cases hne : τ.Nonempty
    · have hτ : τ ∈ K.faces := ambientLinkPart_face K intersect v σ hσ hne
      have hlink : LinkFace intersect v τ :=
        ambientLinkPart_linkFace K intersect v σ hσ hcurve
      let f := finiteLinkFaceMap K intersect separating hsep v τ hτ hlink
      have hC : IsClosed (Subtype.val '' (f '' (f ⁻¹' S)) :
          Set (RealizationPoint K)) := by
        letI := finiteSimplex_compact τ
        have hp : IsCompact (f ⁻¹' S) := (hfaces τ hτ hlink).isCompact
        have hc : Continuous (fun p : FiniteSimplex τ => (f p : RealizationPoint K)) :=
          continuous_subtype_val.comp
            (finiteLinkFaceMap_continuous K intersect separating hsep v τ hτ hlink)
        have hi : IsCompact ((fun p : FiniteSimplex τ =>
            (f p : RealizationPoint K)) '' (f ⁻¹' S)) := hp.image hc
        have heq : ((fun p : FiniteSimplex τ =>
            (f p : RealizationPoint K)) '' (f ⁻¹' S)) =
            Subtype.val '' (f '' (f ⁻¹' S)) := by
          ext x
          simp [Set.image_image]
        rw [heq] at hi
        exact hi.isClosed
      have heq : ((faceInclusion K σ hσ) ⁻¹' (Subtype.val '' S)) =
          ((faceInclusion K σ hσ) ⁻¹' (Subtype.val '' (f '' (f ⁻¹' S)))) := by
        ext p
        constructor
        · rintro ⟨x, hxS, hxp⟩
          have hxσ : ∀ w ∉ σ, x.1.weight w = 0 := by
            intro w hw
            rw [hxp]
            simp [faceInclusion, hw]
          have hxτ := realizedLink_support_ambientLinkPart K intersect
            separating v σ x hxσ
          have hxr : x ∈ Set.range f := by
            rw [finiteLinkFaceMap_range_eq_support K intersect separating
              hsep v τ hτ hlink]
            exact hxτ
          rcases hxr with ⟨q, hq⟩
          refine ⟨x, ⟨q, ?_, hq⟩, hxp⟩
          change f q ∈ S
          rw [hq]
          exact hxS
        · rintro ⟨x, ⟨q, hqS, hqx⟩, hxp⟩
          exact ⟨x, hqx ▸ hqS, hxp⟩
      rw [heq]
      exact hC.preimage
        (by rw [continuous_def]; intro U hU; exact hU σ hσ)
    · have hτempty : τ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hempty : ((faceInclusion K σ hσ) ⁻¹' (Subtype.val '' S)) = ∅ := by
        ext p
        constructor
        · rintro ⟨x, hxS, hxp⟩
          have hxσ : ∀ w ∉ σ, x.1.weight w = 0 := by
            intro w hw
            rw [hxp]
            simp [faceInclusion, hw]
          have hxτ := realizedLink_support_ambientLinkPart K intersect
            separating v σ x hxσ
          have hz : ∀ w : V, x.1.weight w = 0 := by
            intro w
            exact hxτ w (by simp [τ, hτempty])
          exact (realizedPoint_not_supported_empty K x.1 hz).elim
        · simp
      rw [hempty]
      exact isClosed_empty

/-- Nonempty finite faces of `K` lying in the link of `v`. -/
def FiniteLinkFaceIndex (K : AbstractSimplicialComplex V)
    (intersect : V → V → ℕ) (v : V) :=
  {τ : Finset V // τ ∈ K.faces ∧ LinkFace intersect v τ}

/-- The canonical map from the coproduct of finite link simplices. -/
noncomputable def realizedLinkFaceCoverMap
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u}) :
    (Σ τ : FiniteLinkFaceIndex K intersect v, FiniteSimplex τ.1) →
      RealizedSeparatingLink K intersect separating v :=
  fun p => finiteLinkFaceMap K intersect separating hsep v
    p.1.1 p.1.2.1 p.1.2.2 p.2

/-- The realized link is a quotient of the coproduct of its actual finite
link faces. This is the weak topology needed to check continuity facewise. -/
theorem realizedLinkFaceCoverMap_isQuotientMap
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u})
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hfull : ∀ σ : Finset V, σ.Nonempty →
      CurveFace intersect 1 σ → σ ∈ K.faces) :
    Topology.IsQuotientMap
      (realizedLinkFaceCoverMap K intersect separating hsep v) := by
  apply Topology.isQuotientMap_iff_isClosed.mpr
  constructor
  · intro x
    obtain ⟨σ, hσ, hσzero, _⟩ := x.1.liesInFace
    let τ := ambientLinkPart intersect v σ
    have hxτ := realizedLink_support_ambientLinkPart K intersect
      separating v σ x hσzero
    have hne : τ.Nonempty := by
      by_contra hn
      have hempty : τ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      have hzero : ∀ w : V, x.1.weight w = 0 := by
        intro w
        exact hxτ w (by simp [τ, hempty])
      exact realizedPoint_not_supported_empty K x.1 hzero
    have hτ : τ ∈ K.faces := ambientLinkPart_face K intersect v σ hσ hne
    have hlink : LinkFace intersect v τ :=
      ambientLinkPart_linkFace K intersect v σ hσ hcurve
    have hxr : x ∈ Set.range
        (finiteLinkFaceMap K intersect separating hsep v τ hτ hlink) := by
      rw [finiteLinkFaceMap_range_eq_support K intersect separating
        hsep v τ hτ hlink]
      exact hxτ
    rcases hxr with ⟨p, hp⟩
    exact ⟨⟨⟨τ, hτ, hlink⟩, p⟩, hp⟩
  · intro S
    rw [isClosed_realizedSeparatingLink_iff_linkFaces K intersect separating
      hsep v hcurve hfull S]
    rw [isClosed_sigma_iff]
    constructor
    · intro h τ
      exact h τ.1 τ.2.1 τ.2.2
    · intro h τ hτ hlink
      exact h ⟨τ, hτ, hlink⟩

/-- Continuity from the realized link can be checked independently on every
finite link simplex. -/
theorem continuous_iff_continuous_on_linkFaces
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u})
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hfull : ∀ σ : Finset V, σ.Nonempty →
      CurveFace intersect 1 σ → σ ∈ K.faces)
    {Y : Type*} [TopologicalSpace Y]
    (f : RealizedSeparatingLink K intersect separating v → Y) :
    Continuous f ↔
      ∀ (τ : Finset V) (hτ : τ ∈ K.faces)
        (hlink : LinkFace intersect v τ),
        Continuous (f ∘ finiteLinkFaceMap K intersect separating
          hsep v τ hτ hlink) := by
  constructor
  · intro hf τ hτ hlink
    exact hf.comp
      (finiteLinkFaceMap_continuous K intersect separating hsep v τ hτ hlink)
  · intro hfaces
    apply (realizedLinkFaceCoverMap_isQuotientMap K intersect separating
      hsep v hcurve hfull).continuous_iff.mpr
    apply continuous_sigma
    intro τ
    exact hfaces τ.1 τ.2.1 τ.2.2

end CurveComplexGenusTwo.Topology
