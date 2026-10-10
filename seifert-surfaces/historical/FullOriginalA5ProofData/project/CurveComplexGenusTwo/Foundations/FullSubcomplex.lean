import CurveComplexGenusTwo.Foundations.FullSubcomplexWeakTopology

namespace CurveComplex

variable {V : Type*} [DecidableEq V]

/-- The full subcomplex on a predicate has exactly the selected vertices. -/
noncomputable def fullSubcomplex (K : AbstractSimplicialComplex V)
    (P : V → Prop) : AbstractSimplicialComplex {v : V // P v} := by
  classical
  refine {
    faces := {σ | σ.image Subtype.val ∈ K.faces}
    isRelLowerSet_faces := ?_
    singleton_mem := ?_ }
  · intro σ hσ
    constructor
    · exact Finset.image_nonempty.mp (K.isRelLowerSet_faces hσ).1
    · intro τ hsub hne
      exact (K.isRelLowerSet_faces hσ).2
        ((Finset.image_mono Subtype.val) hsub) (Finset.image_nonempty.mpr hne)
  · intro v
    simpa using K.singleton_mem v.1

theorem mem_fullSubcomplex_iff (K : AbstractSimplicialComplex V)
    (P : V → Prop) (σ : Finset {v : V // P v}) :
    σ ∈ (fullSubcomplex K P).faces ↔
      σ.image Subtype.val ∈ K.faces := Iff.rfl

noncomputable def fullToAmbient (K : AbstractSimplicialComplex V)
    (P : V → Prop) :
    RealizationPoint (fullSubcomplex K P) → RealizationPoint K := by
  classical
  intro x
  refine ⟨(fun v => if hv : P v then x.weight ⟨v, hv⟩ else 0), ?_, ?_⟩
  · intro v
    split_ifs with hv
    · exact x.nonneg _
    · exact le_refl _
  · obtain ⟨σ, hσ, hz, hs⟩ := x.liesInFace
    refine ⟨σ.image Subtype.val, hσ, ?_, ?_⟩
    · intro v hv
      by_cases hp : P v
      · simp only [dite_eq_left hp]
        apply hz
        intro hm
        exact hv (Finset.mem_image.mpr ⟨⟨v, hp⟩, hm, rfl⟩)
      · simp [hp]
    · rw [Finset.sum_image (Subtype.val_injective.injOn)]
      calc
        (∑ v ∈ σ, if hv : P v.1 then x.weight ⟨v.1, hv⟩ else 0) =
            ∑ v ∈ σ, x.weight v := by
              apply Finset.sum_congr rfl
              intro v hv
              simp [v.property]
        _ = 1 := hs

theorem fullToAmbient_weight_of_property
    (K : AbstractSimplicialComplex V) (P : V → Prop)
    (x : RealizationPoint (fullSubcomplex K P)) (v : V)
    (hv : P v) :
    (fullToAmbient K P x).weight v = x.weight ⟨v, hv⟩ := by
  simp [fullToAmbient, hv]

theorem fullToAmbient_weight_of_not_property
    (K : AbstractSimplicialComplex V) (P : V → Prop)
    (x : RealizationPoint (fullSubcomplex K P)) (v : V)
    (hv : ¬ P v) :
    (fullToAmbient K P x).weight v = 0 := by
  simp [fullToAmbient, hv]

theorem fullToAmbient_mem_supported
    (K : AbstractSimplicialComplex V) (P : V → Prop)
    (x : RealizationPoint (fullSubcomplex K P)) :
    fullToAmbient K P x ∈ fullSupportLocus K P := by
  intro v hv
  exact fullToAmbient_weight_of_not_property K P x v hv

theorem fullToAmbient_injective
    (K : AbstractSimplicialComplex V) (P : V → Prop) :
    Function.Injective (fullToAmbient K P) := by
  intro x y hxy
  apply RealizationPoint.ext
  funext v
  have h := congrArg (fun z : RealizationPoint K => z.weight v.1) hxy
  simpa only [fullToAmbient_weight_of_property K P x v.1 v.2,
    fullToAmbient_weight_of_property K P y v.1 v.2] using h

omit [DecidableEq V] in
private theorem sum_supportFinset (K : AbstractSimplicialComplex V)
    (x : RealizationPoint K) :
    ∑ v ∈ supportFinset K x, x.weight v = 1 := by
  classical
  let ρ : Finset V := Classical.choose x.liesInFace
  have hρ := Classical.choose_spec x.liesInFace
  have hsub : supportFinset K x ⊆ ρ := by
    intro v hv
    exact (Finset.mem_filter.mp hv).1
  have heq : (∑ v ∈ supportFinset K x, x.weight v) =
      ∑ v ∈ ρ, x.weight v := by
    apply Finset.sum_subset hsub
    intro v hvρ hvs
    by_contra hn
    exact hvs ((mem_supportFinset_iff K x v).mpr hn)
  rw [heq]
  exact hρ.2.2

noncomputable def supportedToFull (K : AbstractSimplicialComplex V)
    (P : V → Prop) :
    fullSupportLocus K P → RealizationPoint (fullSubcomplex K P) := by
  classical
  intro x
  let σ := supportFinset K x.1
  have hP : ∀ v ∈ σ, P v := by
    intro v hv
    by_contra hp
    exact ((mem_supportFinset_iff K x.1 v).mp hv) (x.2 v hp)
  let τ := σ.subtype P
  have himage : τ.image Subtype.val = σ := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
      exact Finset.mem_subtype.mp hw
    · intro hv
      exact Finset.mem_image.mpr
        ⟨⟨v, hP v hv⟩, Finset.mem_subtype.mpr hv, rfl⟩
  refine ⟨fun v => x.1.weight v.1, fun v => x.1.nonneg v.1, ?_⟩
  refine ⟨τ, ?_, ?_, ?_⟩
  · change τ.image Subtype.val ∈ K.faces
    rw [himage]
    exact supportFinset_mem_faces K x.1
  · intro v hv
    apply Classical.not_not.mp
    intro hn
    exact hv ((Finset.mem_subtype).mpr
      ((mem_supportFinset_iff K x.1 v.1).mpr hn))
  · have hsum := sum_supportFinset K x.1
    change (∑ v ∈ σ, x.1.weight v) = 1 at hsum
    rw [← himage] at hsum
    rw [Finset.sum_image (Subtype.val_injective.injOn)] at hsum
    exact hsum

theorem fullToAmbient_supportedToFull
    (K : AbstractSimplicialComplex V) (P : V → Prop)
    (x : fullSupportLocus K P) :
    fullToAmbient K P (supportedToFull K P x) = x.1 := by
  apply RealizationPoint.ext
  funext v
  by_cases hp : P v
  · simp [fullToAmbient_weight_of_property, supportedToFull, hp]
  · rw [fullToAmbient_weight_of_not_property K P _ v hp]
    exact (x.2 v hp).symm

theorem supportedToFull_fullToAmbient
    (K : AbstractSimplicialComplex V) (P : V → Prop)
    (x : RealizationPoint (fullSubcomplex K P)) :
    supportedToFull K P ⟨fullToAmbient K P x,
      fullToAmbient_mem_supported K P x⟩ = x := by
  apply fullToAmbient_injective K P
  exact fullToAmbient_supportedToFull K P _

private noncomputable def fullFaceEquiv (P : V → Prop)
    (σ : Finset {v : V // P v}) :
    (σ.image Subtype.val) ≃ σ := by
  classical
  refine {
    toFun := fun w =>
      ⟨Classical.choose (Finset.mem_image.mp w.2),
        (Classical.choose_spec (Finset.mem_image.mp w.2)).1⟩
    invFun := fun v => ⟨v.1.1,
      Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro w
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.mem_image.mp w.2)).2
  · intro v
    apply Subtype.ext
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.mem_image.mp
      (Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩))).2

private noncomputable def fullSimplexMap (P : V → Prop)
    (σ : Finset {v : V // P v}) :
    FiniteSimplex σ → FiniteSimplex (σ.image Subtype.val) := by
  intro x
  let e := fullFaceEquiv P σ
  refine ⟨fun w => x.val (e w), (fun w => x.property.1 (e w)), ?_⟩
  exact (Fintype.sum_equiv e
    (fun w => x.val (e w)) x.val (fun _ => rfl)).trans x.property.2

private theorem fullSimplexMap_continuous (P : V → Prop)
    (σ : Finset {v : V // P v}) :
    Continuous (fullSimplexMap P σ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro w
  exact (continuous_apply (fullFaceEquiv P σ w)).comp continuous_subtype_val

private theorem fullToAmbient_face
    (K : AbstractSimplicialComplex V) (P : V → Prop)
    (σ : Finset {v : V // P v})
    (hσ : σ ∈ (fullSubcomplex K P).faces)
    (x : FiniteSimplex σ) :
    fullToAmbient K P (faceInclusion (fullSubcomplex K P) σ hσ x) =
      faceInclusion K (σ.image Subtype.val) hσ (fullSimplexMap P σ x) := by
  apply RealizationPoint.ext
  funext v
  by_cases hm : v ∈ σ.image Subtype.val
  · rcases Finset.mem_image.mp hm with ⟨w, hw, heq⟩
    have hp : P v := heq ▸ w.property
    have hvm : (⟨v, hp⟩ : Subtype P) ∈ σ := by
      simpa [← heq] using hw
    rw [fullToAmbient_weight_of_property K P _ v hp]
    rw [faceInclusion_weight_of_mem K _ hσ _ v hm]
    rw [faceInclusion_weight_of_mem (fullSubcomplex K P) σ hσ x
      ⟨v, hp⟩ hvm]
    have he : (⟨⟨v, hp⟩, hvm⟩ : σ) =
        fullFaceEquiv P σ ⟨v, hm⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      exact (Classical.choose_spec (Finset.mem_image.mp hm)).2.symm
    exact congrArg x.val he
  · rw [faceInclusion_weight_of_not_mem K _ hσ _ v hm]
    by_cases hp : P v
    · rw [fullToAmbient_weight_of_property K P _ v hp]
      apply faceInclusion_weight_of_not_mem
      intro hv
      exact hm (Finset.mem_image.mpr ⟨⟨v, hp⟩, hv, rfl⟩)
    · exact fullToAmbient_weight_of_not_property K P _ v hp

theorem fullToAmbient_continuous
    (K : AbstractSimplicialComplex V) (P : V → Prop) :
    Continuous (fullToAmbient K P) := by
  rw [continuous_def]
  intro U hU σ hσ
  have heq : fullToAmbient K P ∘
      faceInclusion (fullSubcomplex K P) σ hσ =
      faceInclusion K (σ.image Subtype.val) hσ ∘
        fullSimplexMap P σ := by
    funext x
    exact fullToAmbient_face K P σ hσ x
  change IsOpen ((fullToAmbient K P ∘
    faceInclusion (fullSubcomplex K P) σ hσ) ⁻¹' U)
  rw [heq]
  exact (hU _ hσ).preimage (fullSimplexMap_continuous P σ)

private noncomputable def subtypeFaceEquiv
    (K : AbstractSimplicialComplex V) (P : V → Prop)
    [DecidablePred P]
    (i : FullFaceIndex K P) :
    (i.1.subtype P) ≃ i.1 := by
  classical
  refine {
    toFun := fun w => ⟨w.1.1, Finset.mem_subtype.mp w.2⟩
    invFun := fun v => ⟨⟨v.1, i.2.2 v.1 v.2⟩,
      Finset.mem_subtype.mpr v.2⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro w
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro v
    apply Subtype.ext
    rfl

private noncomputable def subtypeSimplexMap
    (K : AbstractSimplicialComplex V) (P : V → Prop)
    [DecidablePred P]
    (i : FullFaceIndex K P) :
    FiniteSimplex i.1 → FiniteSimplex (i.1.subtype P) := by
  intro x
  let e := subtypeFaceEquiv K P i
  refine ⟨fun w => x.val (e w), (fun w => x.property.1 (e w)), ?_⟩
  exact (Fintype.sum_equiv e
    (fun w => x.val (e w)) x.val (fun _ => rfl)).trans x.property.2

omit [DecidableEq V] in
private theorem subtypeSimplexMap_continuous
    (K : AbstractSimplicialComplex V) (P : V → Prop)
    [DecidablePred P]
    (i : FullFaceIndex K P) :
    Continuous (subtypeSimplexMap K P i) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro w
  exact (continuous_apply (subtypeFaceEquiv K P i w)).comp continuous_subtype_val

private theorem subtypeFace_mem_full
    (K : AbstractSimplicialComplex V) (P : V → Prop)
    [DecidablePred P]
    (i : FullFaceIndex K P) :
    i.1.subtype P ∈ (fullSubcomplex K P).faces := by
  classical
  change (i.1.subtype P).image Subtype.val ∈ K.faces
  have h : (i.1.subtype P).image Subtype.val = i.1 := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
      exact Finset.mem_subtype.mp hw
    · intro hv
      exact Finset.mem_image.mpr
        ⟨⟨v, i.2.2 v hv⟩, Finset.mem_subtype.mpr hv, rfl⟩
  rw [h]
  exact i.2.1

private theorem supportedToFull_fullFaceInclusion
    (K : AbstractSimplicialComplex V) (P : V → Prop)
    [DecidablePred P]
    (i : FullFaceIndex K P) (x : FiniteSimplex i.1) :
    supportedToFull K P (fullFaceInclusion K P i x) =
      faceInclusion (fullSubcomplex K P) (i.1.subtype P)
        (subtypeFace_mem_full K P i) (subtypeSimplexMap K P i x) := by
  apply RealizationPoint.ext
  funext w
  by_cases hw : w.1 ∈ i.1
  · have hwm : w ∈ i.1.subtype P := Finset.mem_subtype.mpr hw
    rw [faceInclusion_weight_of_mem _ _ _ _ w hwm]
    change (faceInclusion K i.1 i.2.1 x).weight w.1 =
      x.val (subtypeFaceEquiv K P i ⟨w, hwm⟩)
    rw [faceInclusion_weight_of_mem K _ i.2.1 x w.1 hw]
    congr 1
  · have hwm : w ∉ i.1.subtype P := by
      simpa only [Finset.mem_subtype] using hw
    rw [faceInclusion_weight_of_not_mem _ _ _ _ w hwm]
    change (faceInclusion K i.1 i.2.1 x).weight w.1 = 0
    exact faceInclusion_weight_of_not_mem K _ i.2.1 x w.1 hw

theorem supportedToFull_continuous
    (K : AbstractSimplicialComplex V) (P : V → Prop) :
    Continuous (supportedToFull K P) := by
  classical
  apply (fullFaceCoverMap_isQuotientMap K P).continuous_iff.mpr
  apply continuous_sigma_iff.mpr
  intro i
  have heq : supportedToFull K P ∘ fullFaceInclusion K P i =
      faceInclusion (fullSubcomplex K P) (i.1.subtype P)
        (subtypeFace_mem_full K P i) ∘ subtypeSimplexMap K P i := by
    funext x
    exact supportedToFull_fullFaceInclusion K P i x
  change Continuous (supportedToFull K P ∘ fullFaceInclusion K P i)
  rw [heq]
  exact (continuous_faceInclusion (fullSubcomplex K P) _
    (subtypeFace_mem_full K P i)).comp
      (subtypeSimplexMap_continuous K P i)

/-- The actual weak realization of the full subcomplex is the subspace of
ambient points whose weights vanish outside its vertex set. -/
noncomputable def fullSubcomplexHomeomorphSupported
    (K : AbstractSimplicialComplex V) (P : V → Prop) :
    RealizationPoint (fullSubcomplex K P) ≃ₜ fullSupportLocus K P where
  toFun x := ⟨fullToAmbient K P x, fullToAmbient_mem_supported K P x⟩
  invFun := supportedToFull K P
  left_inv := supportedToFull_fullToAmbient K P
  right_inv := by
    intro x
    apply Subtype.ext
    exact fullToAmbient_supportedToFull K P x
  continuous_toFun := (fullToAmbient_continuous K P).subtype_mk _
  continuous_invFun := supportedToFull_continuous K P

end CurveComplex
