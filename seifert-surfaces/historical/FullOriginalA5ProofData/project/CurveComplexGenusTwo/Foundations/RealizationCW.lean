import CurveComplexGenusTwo.Foundations.GenericRealization

/-!
The geometric realization uses the weak topology on an infinite simplicial
complex, not the product topology on all vertex coordinates.
-/

namespace CurveComplex

variable {V : Type*}

@[ext] theorem RealizationPoint.ext {K : AbstractSimplicialComplex V}
    {p q : RealizationPoint K} (h : p.weight = q.weight) : p = q := by
  cases p with
  | mk pw pn pl =>
    cases q with
    | mk qw qn ql =>
      cases h
      rfl

instance finiteSimplexCompactSpace (σ : Finset V) : CompactSpace (FiniteSimplex σ) := by
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

theorem continuous_faceInclusion (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    Continuous (faceInclusion K σ hσ) := by
  rw [continuous_def]
  intro U hU
  exact hU σ hσ

theorem continuous_iff_continuous_on_faces
    (K : AbstractSimplicialComplex V) {X : Type*} [TopologicalSpace X]
    (f : RealizationPoint K → X) :
    Continuous f ↔ ∀ (σ : Finset V) (hσ : σ ∈ K.faces),
      Continuous (f ∘ faceInclusion K σ hσ) := by
  constructor
  · intro hf σ hσ
    exact hf.comp (continuous_faceInclusion K σ hσ)
  · intro hf
    rw [continuous_def]
    intro U hU σ hσ
    simpa [Set.preimage_comp] using
      (hf σ hσ).isOpen_preimage U hU

theorem faceInclusion_injective (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    Function.Injective (faceInclusion K σ hσ) := by
  intro x y hxy
  apply Subtype.ext
  funext v
  have hv : (v : V) ∈ σ := v.property
  have hweight := congrArg (fun z : RealizationPoint K => z.weight (v : V)) hxy
  simpa [faceInclusion, hv] using hweight

theorem faceInclusion_weight_of_mem (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (x : FiniteSimplex σ)
    (v : V) (hv : v ∈ σ) :
    (faceInclusion K σ hσ x).weight v = x.val ⟨v, hv⟩ := by
  classical
  simp [faceInclusion, hv]

theorem faceInclusion_weight_of_not_mem (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (x : FiniteSimplex σ)
    (v : V) (hv : v ∉ σ) :
    (faceInclusion K σ hσ x).weight v = 0 := by
  classical
  simp [faceInclusion, hv]

theorem faceInclusion_support_subset (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (x : FiniteSimplex σ) :
    {v | (faceInclusion K σ hσ x).weight v ≠ 0} ⊆ σ := by
  classical
  intro v hv
  by_contra hvs
  have hz : (faceInclusion K σ hσ x).weight v = 0 :=
    faceInclusion_weight_of_not_mem K σ hσ x v hvs
  exact hv hz

theorem exists_faceInclusion_eq (K : AbstractSimplicialComplex V)
    (p : RealizationPoint K) :
    ∃ (σ : Finset V) (hσ : σ ∈ K.faces) (x : FiniteSimplex σ),
      faceInclusion K σ hσ x = p := by
  classical
  rcases p.liesInFace with ⟨σ, hσ, hzero, hsum⟩
  let x : FiniteSimplex σ :=
    ⟨fun v => p.weight v,
      (fun v => p.nonneg v), by
        rw [← Finset.sum_attach] at hsum
        simpa [Finset.univ_eq_attach] using hsum⟩
  refine ⟨σ, hσ, x, ?_⟩
  cases p with
  | mk pw pn pl =>
    apply RealizationPoint.ext
    funext v
    by_cases hv : v ∈ σ
    · simp [faceInclusion, x, hv]
    · simpa [faceInclusion, hv] using (hzero v hv).symm

theorem continuous_weight (K : AbstractSimplicialComplex V) (v : V) :
    Continuous (fun p : RealizationPoint K => p.weight v) := by
  apply (continuous_iff_continuous_on_faces K _).2
  intro σ hσ
  classical
  by_cases hv : v ∈ σ
  · have h : (fun p : RealizationPoint K => p.weight v) ∘ faceInclusion K σ hσ =
        (fun x : FiniteSimplex σ => x.val ⟨v, hv⟩) := by
      funext x
      exact faceInclusion_weight_of_mem K σ hσ x v hv
    rw [h]
    exact (continuous_apply (⟨v, hv⟩ : σ)).comp continuous_subtype_val
  · have h : (fun p : RealizationPoint K => p.weight v) ∘ faceInclusion K σ hσ =
        (fun _ : FiniteSimplex σ => (0 : ℝ)) := by
      funext x
      exact faceInclusion_weight_of_not_mem K σ hσ x v hv
    rw [h]
    exact continuous_const

theorem isClosed_weight_eq_zero (K : AbstractSimplicialComplex V) (v : V) :
    IsClosed {p : RealizationPoint K | p.weight v = 0} := by
  exact isClosed_eq (continuous_weight K v) continuous_const

instance realizationT2Space (K : AbstractSimplicialComplex V) :
    T2Space (RealizationPoint K) := by
  constructor
  intro p q hpq
  have h : ∃ v : V, p.weight v ≠ q.weight v := by
    by_contra hn
    push Not at hn
    exact hpq (RealizationPoint.ext (funext hn))
  obtain ⟨v, hv⟩ := h
  exact separated_by_continuous (continuous_weight K v) hv

/-- Points whose barycentric support is contained in a finite face. -/
def faceCarrier (K : AbstractSimplicialComplex V) (σ : Finset V) :
    Set (RealizationPoint K) :=
  {p | ∀ v ∉ σ, p.weight v = 0}

theorem isClosed_faceCarrier (K : AbstractSimplicialComplex V)
    (σ : Finset V) : IsClosed (faceCarrier K σ) := by
  have h : faceCarrier K σ =
      ⋂ v : {v : V // v ∉ σ}, {p : RealizationPoint K | p.weight v.1 = 0} := by
    ext p
    simp [faceCarrier]
  rw [h]
  exact isClosed_iInter (fun v => isClosed_weight_eq_zero K v.1)

theorem faceInclusion_mem_faceCarrier (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (x : FiniteSimplex σ) :
    faceInclusion K σ hσ x ∈ faceCarrier K σ := by
  intro v hv
  exact faceInclusion_weight_of_not_mem K σ hσ x v hv

theorem faceCarrier_eq_range_faceInclusion (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    faceCarrier K σ = Set.range (faceInclusion K σ hσ) := by
  classical
  ext p
  constructor
  · intro hp
    rcases p.liesInFace with ⟨τ, hτ, hzero, hsum⟩
    have hτu : (∑ v ∈ τ, p.weight v) = ∑ v ∈ τ ∪ σ, p.weight v := by
      apply Finset.sum_subset Finset.subset_union_left
      intro v hv hvτ
      exact hzero v hvτ
    have hσu : (∑ v ∈ σ, p.weight v) = ∑ v ∈ τ ∪ σ, p.weight v := by
      apply Finset.sum_subset Finset.subset_union_right
      intro v hv hvσ
      exact hp v hvσ
    have hσsum : ∑ v ∈ σ, p.weight v = 1 := by
      rw [hσu, ← hτu]
      exact hsum
    let x : FiniteSimplex σ :=
      ⟨fun v => p.weight v, (fun v => p.nonneg v), by
        rw [← Finset.sum_attach] at hσsum
        simpa [Finset.univ_eq_attach] using hσsum⟩
    refine ⟨x, ?_⟩
    apply RealizationPoint.ext
    funext v
    by_cases hv : v ∈ σ
    · exact faceInclusion_weight_of_mem K σ hσ x v hv
    · rw [faceInclusion_weight_of_not_mem K σ hσ x v hv, hp v hv]
  · rintro ⟨x, rfl⟩
    exact faceInclusion_mem_faceCarrier K σ hσ x

theorem isClosed_range_faceInclusion (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    IsClosed (Set.range (faceInclusion K σ hσ)) := by
  rw [← faceCarrier_eq_range_faceInclusion K σ hσ]
  exact isClosed_faceCarrier K σ

theorem faceInclusion_isClosedEmbedding (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    Topology.IsClosedEmbedding (faceInclusion K σ hσ) := by
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_faceInclusion K σ hσ) (faceInclusion_injective K σ hσ)
  intro s hs
  exact (hs.isCompact.image (continuous_faceInclusion K σ hσ)).isClosed

/-- The exact finite set of vertices with nonzero barycentric coordinate. -/
noncomputable def supportFinset (K : AbstractSimplicialComplex V)
    (p : RealizationPoint K) : Finset V :=
  (Classical.choose p.liesInFace).filter (fun v => p.weight v ≠ 0)

theorem mem_supportFinset_iff (K : AbstractSimplicialComplex V)
    (p : RealizationPoint K) (v : V) :
    v ∈ supportFinset K p ↔ p.weight v ≠ 0 := by
  classical
  constructor
  · intro hv
    exact (Finset.mem_filter.mp hv).2
  · intro hv
    apply Finset.mem_filter.mpr
    constructor
    · by_contra hn
      exact hv ((Classical.choose_spec p.liesInFace).2.1 v hn)
    · exact hv

theorem supportFinset_nonempty (K : AbstractSimplicialComplex V)
    (p : RealizationPoint K) : (supportFinset K p).Nonempty := by
  classical
  by_contra hn
  have hzero : ∀ v : V, p.weight v = 0 := by
    intro v
    by_contra hv
    exact hn ⟨v, (mem_supportFinset_iff K p v).mpr hv⟩
  rcases p.liesInFace with ⟨σ, hσ, houtside, hsum⟩
  have hsumzero : (∑ v ∈ σ, p.weight v) = 0 := by
    simp [hzero]
  linarith

theorem supportFinset_mem_faces (K : AbstractSimplicialComplex V)
    (p : RealizationPoint K) : supportFinset K p ∈ K.faces := by
  have hσ := (Classical.choose_spec p.liesInFace).1
  exact (K.isRelLowerSet_faces hσ).2 (Finset.filter_subset _ _)
    (supportFinset_nonempty K p)

theorem mem_supportFinset_iff_pos (K : AbstractSimplicialComplex V)
    (p : RealizationPoint K) (v : V) :
    v ∈ supportFinset K p ↔ 0 < p.weight v := by
  rw [mem_supportFinset_iff]
  constructor
  · intro h
    exact lt_of_le_of_ne (p.nonneg v) h.symm
  · exact ne_of_gt

/-- The relative interior of the face indexed by `σ`. -/
def openFace (K : AbstractSimplicialComplex V) (σ : Finset V) :
    Set (RealizationPoint K) :=
  {p | supportFinset K p = σ}

theorem mem_faceCarrier_iff_support_subset (K : AbstractSimplicialComplex V)
    (σ : Finset V) (p : RealizationPoint K) :
    p ∈ faceCarrier K σ ↔ supportFinset K p ⊆ σ := by
  constructor
  · intro hp v hv
    by_contra hvs
    exact ((mem_supportFinset_iff K p v).mp hv) (hp v hvs)
  · intro hp v hv
    by_contra hw
    exact hv (hp ((mem_supportFinset_iff K p v).mpr hw))

theorem mem_openFace_iff (K : AbstractSimplicialComplex V)
    (σ : Finset V) (p : RealizationPoint K) :
    p ∈ openFace K σ ↔ ∀ v, (0 < p.weight v ↔ v ∈ σ) := by
  simp only [openFace, Set.mem_ofPred_eq]
  constructor
  · intro hp v
    rw [← hp, mem_supportFinset_iff_pos]
  · intro hp
    ext v
    rw [mem_supportFinset_iff_pos]
    exact hp v

theorem exists_unique_openFace (K : AbstractSimplicialComplex V)
    (p : RealizationPoint K) :
    ∃! σ : Finset V, σ ∈ K.faces ∧ p ∈ openFace K σ := by
  refine ⟨supportFinset K p, ⟨supportFinset_mem_faces K p, rfl⟩, ?_⟩
  intro σ hσ
  exact hσ.2.symm

theorem openFace_disjoint (K : AbstractSimplicialComplex V)
    {σ τ : Finset V} (h : σ ≠ τ) :
    Disjoint (openFace K σ) (openFace K τ) := by
  apply Set.disjoint_left.mpr
  intro p hpσ hpτ
  exact h (hpσ.symm.trans hpτ)

theorem union_openFaces (K : AbstractSimplicialComplex V) :
    (⋃ σ ∈ K.faces, openFace K σ) = Set.univ := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨supportFinset K p, supportFinset_mem_faces K p, rfl⟩

theorem faceCarrier_eq_union_openFaces (K : AbstractSimplicialComplex V)
    (σ : Finset V) :
    faceCarrier K σ =
      ⋃ τ ∈ σ.powerset, openFace K τ := by
  ext p
  simp only [Set.mem_iUnion, Finset.mem_powerset]
  constructor
  · intro hp
    exact ⟨supportFinset K p, (mem_faceCarrier_iff_support_subset K σ p).mp hp, rfl⟩
  · rintro ⟨τ, hτσ, hp⟩
    exact (mem_faceCarrier_iff_support_subset K σ p).mpr (hp.symm ▸ hτσ)

open Classical in
theorem faceFrontier_eq_union_proper_openFaces (K : AbstractSimplicialComplex V)
    (σ : Finset V) :
    faceCarrier K σ \ openFace K σ =
      ⋃ τ ∈ σ.powerset.erase σ, openFace K τ := by
  ext p
  simp only [Set.mem_sdiff, Set.mem_iUnion, Finset.mem_erase, Finset.mem_powerset,
    openFace, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hp, hnot⟩
    exact ⟨supportFinset K p,
      ⟨hnot, (mem_faceCarrier_iff_support_subset K σ p).mp hp⟩, rfl⟩
  · rintro ⟨τ, ⟨hne, hsub⟩, hp⟩
    constructor
    · exact (mem_faceCarrier_iff_support_subset K σ p).mpr (hp.symm ▸ hsub)
    · exact fun h => hne (hp.symm.trans h)

/-! ### Characteristic maps on closed simplices -/

/-- The characteristic map of a closed simplex, with its image identified as a face carrier. -/
noncomputable def faceCharacteristicHomeomorph (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    FiniteSimplex σ ≃ₜ faceCarrier K σ := by
  let e := (faceInclusion_isClosedEmbedding K σ hσ).isEmbedding.homeomorphImage
    (Set.univ : Set (FiniteSimplex σ))
  exact (Homeomorph.Set.univ (FiniteSimplex σ)).symm.trans
    (e.trans (Homeomorph.setCongr (by
      simpa using (faceCarrier_eq_range_faceInclusion K σ hσ).symm)))

/-- The relative interior of the standard finite simplex consists exactly of
the points with every barycentric coordinate positive. -/
def finiteSimplexInterior (σ : Finset V) : Set (FiniteSimplex σ) :=
  {x | ∀ v : σ, 0 < x.val v}

def finiteSimplexBoundary (σ : Finset V) : Set (FiniteSimplex σ) :=
  {x | ∃ v : σ, x.val v = 0}

theorem faceInclusion_mem_openFace_iff (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (x : FiniteSimplex σ) :
    faceInclusion K σ hσ x ∈ openFace K σ ↔
      x ∈ finiteSimplexInterior σ := by
  classical
  rw [mem_openFace_iff]
  simp only [finiteSimplexInterior, Set.mem_setOf_eq]
  constructor
  · intro hx v
    rw [← faceInclusion_weight_of_mem K σ hσ x v.val v.property]
    exact (hx v).2 v.property
  · intro hx v
    by_cases hv : v ∈ σ
    · rw [faceInclusion_weight_of_mem K σ hσ x v hv]
      exact iff_of_true (hx ⟨v, hv⟩) hv
    · simp [faceInclusion_weight_of_not_mem K σ hσ x v hv, hv]

theorem faceInclusion_mem_frontier_iff (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (x : FiniteSimplex σ) :
    faceInclusion K σ hσ x ∈ faceCarrier K σ \ openFace K σ ↔
      x ∈ finiteSimplexBoundary σ := by
  classical
  simp only [Set.mem_sdiff, faceInclusion_mem_faceCarrier K σ hσ x,
    true_and, faceInclusion_mem_openFace_iff]
  simp only [finiteSimplexInterior, finiteSimplexBoundary, Set.mem_setOf_eq,
    not_forall]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, le_antisymm (le_of_not_gt hv) (x.property.1 v)⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [hv]; exact lt_irrefl _⟩

theorem faceCharacteristicHomeomorph_image_interior
    (K : AbstractSimplicialComplex V) (σ : Finset V) (hσ : σ ∈ K.faces) :
    (faceCharacteristicHomeomorph K σ hσ) '' finiteSimplexInterior σ =
      {p : faceCarrier K σ | (p : RealizationPoint K) ∈ openFace K σ} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (faceInclusion_mem_openFace_iff K σ hσ x).2 hx
  · intro hp
    let x := (faceCharacteristicHomeomorph K σ hσ).symm p
    refine ⟨x, ?_, by simp [x]⟩
    exact (faceInclusion_mem_openFace_iff K σ hσ x).1 (by
      have heq : faceInclusion K σ hσ x = p.1 := by
        have h := (faceCharacteristicHomeomorph K σ hσ).apply_symm_apply p
        change (faceCharacteristicHomeomorph K σ hσ x).1 = p.1
        exact congrArg Subtype.val h
      rwa [heq])

theorem faceCharacteristicHomeomorph_image_boundary
    (K : AbstractSimplicialComplex V) (σ : Finset V) (hσ : σ ∈ K.faces) :
    (faceCharacteristicHomeomorph K σ hσ) '' finiteSimplexBoundary σ =
      {p : faceCarrier K σ | (p : RealizationPoint K) ∉ openFace K σ} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (faceInclusion_mem_frontier_iff K σ hσ x).2 hx |>.2
  · intro hp
    let x := (faceCharacteristicHomeomorph K σ hσ).symm p
    refine ⟨x, ?_, by simp [x]⟩
    apply (faceInclusion_mem_frontier_iff K σ hσ x).1
    have heq : faceInclusion K σ hσ x = p.1 := by
      have h := (faceCharacteristicHomeomorph K σ hσ).apply_symm_apply p
      change (faceCharacteristicHomeomorph K σ hσ x).1 = p.1
      exact congrArg Subtype.val h
    rw [heq]
    exact ⟨p.property, hp⟩

theorem faceInclusion_image_interior (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    faceInclusion K σ hσ '' finiteSimplexInterior σ = openFace K σ := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (faceInclusion_mem_openFace_iff K σ hσ x).2 hx
  · intro hp
    have hcar : p ∈ faceCarrier K σ := by
      apply (mem_faceCarrier_iff_support_subset K σ p).2
      change supportFinset K p ⊆ σ
      rw [show supportFinset K p = σ from hp]
    rw [faceCarrier_eq_range_faceInclusion K σ hσ] at hcar
    rcases hcar with ⟨x, rfl⟩
    exact ⟨x, (faceInclusion_mem_openFace_iff K σ hσ x).1 hp, rfl⟩

theorem faceInclusion_image_boundary (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    faceInclusion K σ hσ '' finiteSimplexBoundary σ =
      faceCarrier K σ \ openFace K σ := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (faceInclusion_mem_frontier_iff K σ hσ x).2 hx
  · intro hp
    have hcar : p ∈ faceCarrier K σ := hp.1
    rw [faceCarrier_eq_range_faceInclusion K σ hσ] at hcar
    rcases hcar with ⟨x, rfl⟩
    exact ⟨x, (faceInclusion_mem_frontier_iff K σ hσ x).1 hp, rfl⟩

private theorem finiteSimplex_nonempty_of_face (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) : Nonempty (FiniteSimplex σ) := by
  classical
  obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces hσ).1
  let v₀ : σ := ⟨v, hv⟩
  refine ⟨⟨fun w => if w = v₀ then 1 else 0, ?_, ?_⟩⟩
  · intro w
    dsimp
    split_ifs <;> norm_num
  · simp [v₀]

/-- The partial equivalence on the open simplex cell. Its source is the positive
barycentric part of the closed simplex, and its target is the open face. -/
noncomputable def simplexCellPartialEquiv (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    PartialEquiv (FiniteSimplex σ) (RealizationPoint K) := by
  letI : Nonempty (FiniteSimplex σ) := finiteSimplex_nonempty_of_face K σ hσ
  exact (Set.InjOn.toPartialEquiv (faceInclusion K σ hσ)
    (finiteSimplexInterior σ) (fun _ _ _ _ h =>
      faceInclusion_injective K σ hσ h))

theorem simplexCellPartialEquiv_source (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    (simplexCellPartialEquiv K σ hσ).source = finiteSimplexInterior σ := by
  simp [simplexCellPartialEquiv]

theorem simplexCellPartialEquiv_target (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    (simplexCellPartialEquiv K σ hσ).target = openFace K σ := by
  simp [simplexCellPartialEquiv, faceInclusion_image_interior]

end CurveComplex

/-! The affine coordinate region of an `n`-simplex in `Fin n → ℝ`. -/

namespace CurveComplex

open Metric Set Bornology

private def simplexRegion (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1}

private def simplexRegionInterior (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ (∑ i, x i) < 1}

private theorem simplexRegionInterior_isOpen (n : ℕ) :
    IsOpen (simplexRegionInterior n) := by
  have hcoord : IsOpen {x : Fin n → ℝ | ∀ i, 0 < x i} := by
    simpa only [Set.iInter_setOf] using
      (isOpen_iInter_of_finite (fun i : Fin n =>
        isOpen_lt continuous_const (continuous_apply i)))
  have hsum : Continuous (fun x : Fin n → ℝ => ∑ i, x i) :=
    continuous_finsetSum _ (fun i _ => continuous_apply i)
  exact hcoord.inter (isOpen_lt hsum continuous_const)

private theorem simplexRegionInterior_subset (n : ℕ) :
    simplexRegionInterior n ⊆ simplexRegion n := by
  intro x hx
  exact ⟨fun i => (hx.1 i).le, hx.2.le⟩

private theorem simplexRegion_convex (n : ℕ) : Convex ℝ (simplexRegion n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    change 0 ≤ (a • x + b • y) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · have hsum : (∑ i, (a • x + b • y) i) =
        a * (∑ i, x i) + b * (∑ i, y i) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsum]
    nlinarith [mul_le_mul_of_nonneg_left hx.2 ha,
      mul_le_mul_of_nonneg_left hy.2 hb]

private theorem simplexRegion_isBounded (n : ℕ) : IsBounded (simplexRegion n) := by
  apply (isCompact_Icc.isBounded).subset
  intro x hx
  constructor
  · exact hx.1
  · intro i
    calc
      x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
      _ ≤ 1 := hx.2

private theorem simplexRegion_isClosed (n : ℕ) : IsClosed (simplexRegion n) := by
  have hsum : Continuous (fun x : Fin n → ℝ => ∑ i, x i) :=
    continuous_finsetSum _ (fun i _ => continuous_apply i)
  have h : IsClosed ((⋂ i : Fin n, {x : Fin n → ℝ | 0 ≤ x i}) ∩
      {x : Fin n → ℝ | ∑ i, x i ≤ 1}) :=
    (isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))).inter
      (isClosed_le hsum continuous_const)
  convert h using 1
  ext x
  simp [simplexRegion]

private def simplexSumLinearMap (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum]

private theorem simplexSumLinearMap_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (simplexSumLinearMap n) := by
  intro y
  let i₀ : Fin n := ⟨0, hn⟩
  refine ⟨Pi.single i₀ y, ?_⟩
  simp [simplexSumLinearMap, i₀]

private theorem simplexRegion_interior_eq (n : ℕ) :
    interior (simplexRegion n) = simplexRegionInterior n := by
  apply Subset.antisymm
  · intro x hx
    by_cases hn : n = 0
    · subst n
      constructor
      · intro i
        exact i.elim0
      · simp
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      constructor
      · intro i
        have hsub : simplexRegion n ⊆
            (fun x : Fin n → ℝ => x i) ⁻¹' Set.Ici 0 := by
          intro y hy
          exact hy.1 i
        have hxi : x ∈ interior ((fun x : Fin n → ℝ => x i) ⁻¹' Set.Ici 0) :=
          interior_mono hsub hx
        have hxi' := (isOpenMap_eval i).interior_preimage_subset_preimage_interior hxi
        simpa [interior_Ici] using hxi'
      · have hsub : simplexRegion n ⊆
            (simplexSumLinearMap n) ⁻¹' Set.Iic 1 := by
          intro y hy
          exact hy.2
        have hxi : x ∈ interior ((simplexSumLinearMap n) ⁻¹' Set.Iic 1) :=
          interior_mono hsub hx
        have hopen : IsOpenMap (simplexSumLinearMap n) :=
          IsModuleTopology.isOpenMap_of_surjective
            (simplexSumLinearMap_surjective hnpos)
        have hxi' := hopen.interior_preimage_subset_preimage_interior hxi
        simpa [simplexSumLinearMap, interior_Iic] using hxi'
  · exact interior_maximal (simplexRegionInterior_subset n)
      (simplexRegionInterior_isOpen n)

private theorem simplexRegion_interior_nonempty (n : ℕ) :
    (interior (simplexRegion n)).Nonempty := by
  let c : Fin n → ℝ := fun _ => (1 : ℝ) / (n + 1)
  have hsum : (∑ i, c i) = (n : ℝ) / (n + 1) := by
    simp [c, Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hc : c ∈ simplexRegionInterior n := by
    constructor
    · intro i
      dsimp [c]
      positivity
    · rw [hsum]
      have hn : (0 : ℝ) < n + 1 := by positivity
      rw [div_lt_iff₀ hn]
      nlinarith
  exact ⟨c, (interior_maximal (simplexRegionInterior_subset n)
    (simplexRegionInterior_isOpen n)) hc⟩

/-- An ambient homeomorphism sending the standard affine simplex region and
its interior and boundary to the unit closed ball, open ball, and sphere. -/
noncomputable def simplexRegionBallHomeomorph (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (simplexRegion_convex n) (simplexRegion_interior_nonempty n)
    (simplexRegion_isBounded n)).choose

theorem simplexRegionBallHomeomorph_interior (n : ℕ) :
    simplexRegionBallHomeomorph n '' interior (simplexRegion n) = ball 0 1 :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (simplexRegion_convex n) (simplexRegion_interior_nonempty n)
    (simplexRegion_isBounded n)).choose_spec.1

theorem simplexRegionBallHomeomorph_closure (n : ℕ) :
    simplexRegionBallHomeomorph n '' closure (simplexRegion n) = closedBall 0 1 :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (simplexRegion_convex n) (simplexRegion_interior_nonempty n)
    (simplexRegion_isBounded n)).choose_spec.2.1

theorem simplexRegionBallHomeomorph_frontier (n : ℕ) :
    simplexRegionBallHomeomorph n '' frontier (simplexRegion n) = sphere 0 1 :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (simplexRegion_convex n) (simplexRegion_interior_nonempty n)
    (simplexRegion_isBounded n)).choose_spec.2.2

theorem simplexRegionBallHomeomorph_region (n : ℕ) :
    simplexRegionBallHomeomorph n '' simplexRegion n = closedBall 0 1 := by
  simpa [(simplexRegion_isClosed n).closure_eq] using
    simplexRegionBallHomeomorph_closure n

private abbrev finSimplex (n : ℕ) :=
  {x : Fin (n + 1) → ℝ // (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

private def affineChart (n : ℕ) (x : simplexRegion n) : finSimplex n := by
  refine ⟨Fin.snoc x.1 (1 - ∑ i, x.1 i), ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa using sub_nonneg.mpr x.2.2
    · intro j
      simpa using x.2.1 j
  · simp [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

private def affineChartInv (n : ℕ) (x : finSimplex n) : simplexRegion n := by
  refine ⟨Fin.init x.1, ?_, ?_⟩
  · intro i
    exact x.2.1 i.castSucc
  · have hsum := x.2.2
    rw [Fin.sum_univ_castSucc] at hsum
    have hlast := x.2.1 (Fin.last n)
    change (∑ i : Fin n, x.1 i.castSucc) ≤ 1
    linarith

private theorem affineChart_left_inv (n : ℕ) :
    Function.LeftInverse (affineChartInv n) (affineChart n) := by
  intro x
  apply Subtype.ext
  funext i
  simp [affineChartInv, affineChart, Fin.init, Fin.snoc_castSucc]

private theorem affineChart_right_inv (n : ℕ) :
    Function.RightInverse (affineChartInv n) (affineChart n) := by
  intro x
  apply Subtype.ext
  funext i
  refine Fin.lastCases ?_ ?_ i
  · have hsum := x.2.2
    rw [Fin.sum_univ_castSucc] at hsum
    simp only [affineChart, affineChartInv, Fin.snoc_last]
    change 1 - (∑ i : Fin n, x.1 i.castSucc) = x.1 (Fin.last n)
    linarith
  · intro j
    simp [affineChart, affineChartInv, Fin.snoc_castSucc, Fin.init]

noncomputable def affineChartHomeomorph (n : ℕ) : simplexRegion n ≃ₜ finSimplex n where
  toEquiv := ⟨affineChart n, affineChartInv n, affineChart_left_inv n,
    affineChart_right_inv n⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ ?_ i
    · have hsum : Continuous (fun x : simplexRegion n => ∑ j : Fin n, x.1 j) :=
        continuous_finsetSum _ (fun j _ =>
          (continuous_apply j).comp continuous_subtype_val)
      have hc : Continuous (fun _ : simplexRegion n => (1 : ℝ)) := continuous_const
      convert hc.sub hsum using 1
      funext x
      simp only [Pi.sub_apply, affineChart, Fin.snoc_last]
    · intro j
      simpa only [affineChart, Fin.snoc_castSucc, Function.comp_def] using
        (continuous_apply j).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    simpa only [affineChartInv, Fin.init, Function.comp_def] using
      (continuous_apply i.castSucc).comp continuous_subtype_val

private def finSimplexInterior (n : ℕ) : Set (finSimplex n) :=
  {x | ∀ i, 0 < x.1 i}

private theorem affineChartHomeomorph_apply (n : ℕ) (x : simplexRegion n) :
    (affineChartHomeomorph n x).1 =
      Fin.snoc x.1 (1 - ∑ i, x.1 i) := rfl

private theorem affineChart_mem_interior_iff (n : ℕ) (x : simplexRegion n) :
    affineChartHomeomorph n x ∈ finSimplexInterior n ↔
      x.1 ∈ interior (simplexRegion n) := by
  rw [simplexRegion_interior_eq]
  constructor
  · intro hx
    constructor
    · intro i
      simpa only [affineChartHomeomorph_apply, Fin.snoc_castSucc] using hx i.castSucc
    · have hlast := hx (Fin.last n)
      have hlast' : 0 < 1 - ∑ i, x.1 i := by
        simpa only [affineChartHomeomorph_apply, Fin.snoc_last, sub_pos] using hlast
      linarith
  · intro hx i
    refine Fin.lastCases ?_ ?_ i
    · simpa only [affineChartHomeomorph_apply, Fin.snoc_last, sub_pos] using hx.2
    · intro j
      simpa only [affineChartHomeomorph_apply, Fin.snoc_castSucc] using hx.1 j

private theorem affineChartHomeomorph_image_interior (n : ℕ) :
    affineChartHomeomorph n ''
      {x : simplexRegion n | x.1 ∈ interior (simplexRegion n)} =
      finSimplexInterior n := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (affineChart_mem_interior_iff n x).2 hx
  · intro hy
    let x := (affineChartHomeomorph n).symm y
    refine ⟨x, ?_, by simp [x]⟩
    exact (affineChart_mem_interior_iff n x).1 (by
      simpa [x] using hy)

theorem simplexRegionBallHomeomorph_symm_image (n : ℕ) :
    (simplexRegionBallHomeomorph n).symm ''
      (closedBall 0 1 : Set (Fin n → ℝ)) = simplexRegion n := by
  rw [← simplexRegionBallHomeomorph_region n]
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨simplexRegionBallHomeomorph n x, ⟨x, hx, rfl⟩, by simp⟩

/-- A homeomorphism from the closed unit `n`-ball to the standard finite
`n`-simplex. -/
noncomputable def closedBallFinSimplexHomeomorph (n : ℕ) :
    (closedBall 0 1 : Set (Fin n → ℝ)) ≃ₜ finSimplex n :=
  ((Homeomorph.image (simplexRegionBallHomeomorph n).symm
    (closedBall 0 1 : Set (Fin n → ℝ))).trans
    (Homeomorph.setCongr (simplexRegionBallHomeomorph_symm_image n))).trans
    (affineChartHomeomorph n)

private def openBallInClosedBall (n : ℕ) :
    Set (closedBall 0 1 : Set (Fin n → ℝ)) :=
  {x | x.1 ∈ ball 0 1}

private theorem simplexRegionBallHomeomorph_symm_mem_interior_iff
    (n : ℕ) (x : Fin n → ℝ) :
    (simplexRegionBallHomeomorph n).symm x ∈ interior (simplexRegion n) ↔
      x ∈ ball 0 1 := by
  rw [← simplexRegionBallHomeomorph_interior n]
  constructor
  · intro hx
    exact ⟨_, hx, by simp⟩
  · rintro ⟨y, hy, hxy⟩
    have h : (simplexRegionBallHomeomorph n).symm x = y := by
      simpa using (congrArg (simplexRegionBallHomeomorph n).symm hxy).symm
    rwa [h]

private theorem closedBallFinSimplexHomeomorph_mem_interior_iff
    (n : ℕ) (x : (closedBall 0 1 : Set (Fin n → ℝ))) :
    closedBallFinSimplexHomeomorph n x ∈ finSimplexInterior n ↔
      x ∈ openBallInClosedBall n := by
  have hx : (simplexRegionBallHomeomorph n).symm x.1 ∈ simplexRegion n := by
    rw [← simplexRegionBallHomeomorph_symm_image n]
    exact ⟨x.1, x.2, rfl⟩
  have heq : closedBallFinSimplexHomeomorph n x =
      affineChartHomeomorph n ⟨(simplexRegionBallHomeomorph n).symm x.1, hx⟩ := rfl
  rw [heq, affineChart_mem_interior_iff]
  exact simplexRegionBallHomeomorph_symm_mem_interior_iff n x.1

theorem closedBallFinSimplexHomeomorph_image_openBall (n : ℕ) :
    closedBallFinSimplexHomeomorph n '' openBallInClosedBall n =
      finSimplexInterior n := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (closedBallFinSimplexHomeomorph_mem_interior_iff n x).2 hx
  · intro hy
    let x := (closedBallFinSimplexHomeomorph n).symm y
    refine ⟨x, ?_, by simp [x]⟩
    exact (closedBallFinSimplexHomeomorph_mem_interior_iff n x).1 (by
      simpa [x] using hy)

private abbrev chartFiniteSimplex {V : Type*} (σ : Finset V) :=
  {x : σ → ℝ // (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1}

private def reindexFiniteSimplex {V : Type*} (σ : Finset V) (n : ℕ)
    (e : Fin (n + 1) ≃ σ) : finSimplex n ≃ₜ chartFiniteSimplex σ := by
  let h : (Fin (n + 1) → ℝ) ≃ₜ (σ → ℝ) :=
    Homeomorph.piCongrLeft (Y := fun _ : σ => ℝ) e
  have himage : h '' {x : Fin (n + 1) → ℝ |
      (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1} =
      {x : σ → ℝ | (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      constructor
      · intro v
        have hv : h y v = y (e.symm v) := by
          simpa only [e.apply_symm_apply] using
            (Homeomorph.piCongrLeft_apply_apply (Y := fun _ : σ => ℝ) e y (e.symm v))
        rw [hv]
        exact hy.1 (e.symm v)
      · calc
          (∑ v : σ, h y v) = ∑ i : Fin (n + 1), y i := by
            symm
            apply Fintype.sum_equiv e
            intro i
            simp [h]
          _ = 1 := hy.2
    · intro hx
      let y := h.symm x
      refine ⟨y, ?_, by simp [y]⟩
      constructor
      · intro i
        have hi := hx.1 (e i)
        simpa [y, h] using hi
      · calc
          (∑ i : Fin (n + 1), y i) = ∑ v : σ, x v := by
            apply Fintype.sum_equiv e
            intro i
            simp [y, h]
          _ = 1 := hx.2
  exact (Homeomorph.image h _).trans (Homeomorph.setCongr himage)

private theorem reindexFiniteSimplex_apply {V : Type*} (σ : Finset V) (n : ℕ)
    (e : Fin (n + 1) ≃ σ) (x : finSimplex n) (v : σ) :
    (reindexFiniteSimplex σ n e x).1 v = x.1 (e.symm v) := by
  change (Homeomorph.piCongrLeft (Y := fun _ : σ => ℝ) e x.1) v = _
  simpa only [e.apply_symm_apply] using
    Homeomorph.piCongrLeft_apply_apply (Y := fun _ : σ => ℝ) e x.1 (e.symm v)

private def chartFiniteSimplexInterior {V : Type*} (σ : Finset V) :
    Set (chartFiniteSimplex σ) := {x | ∀ v : σ, 0 < x.1 v}

private theorem reindexFiniteSimplex_mem_interior_iff {V : Type*}
    (σ : Finset V) (n : ℕ) (e : Fin (n + 1) ≃ σ) (x : finSimplex n) :
    reindexFiniteSimplex σ n e x ∈ chartFiniteSimplexInterior σ ↔
      x ∈ finSimplexInterior n := by
  constructor
  · intro hx i
    have hv := hx (e i)
    rw [reindexFiniteSimplex_apply] at hv
    simpa using hv
  · intro hx v
    rw [reindexFiniteSimplex_apply]
    exact hx (e.symm v)

/-- A closed unit `n`-ball chart for any `(n+1)`-vertex face. -/
noncomputable def closedBallFaceSimplexHomeomorph {V : Type*} (σ : Finset V)
    {n : ℕ} (hcard : σ.card = n + 1) :
    (closedBall 0 1 : Set (Fin n → ℝ)) ≃ₜ chartFiniteSimplex σ :=
  (closedBallFinSimplexHomeomorph n).trans
    (reindexFiniteSimplex σ n (Finset.equivFinOfCardEq hcard).symm)

private theorem closedBallFaceSimplexHomeomorph_mem_interior_iff {V : Type*}
    (σ : Finset V) {n : ℕ} (hcard : σ.card = n + 1)
    (x : (closedBall 0 1 : Set (Fin n → ℝ))) :
    closedBallFaceSimplexHomeomorph σ hcard x ∈ chartFiniteSimplexInterior σ ↔
      x ∈ openBallInClosedBall n := by
  change reindexFiniteSimplex σ n (Finset.equivFinOfCardEq hcard).symm
    (closedBallFinSimplexHomeomorph n x) ∈ chartFiniteSimplexInterior σ ↔ _
  rw [reindexFiniteSimplex_mem_interior_iff,
    closedBallFinSimplexHomeomorph_mem_interior_iff]

theorem closedBallFaceSimplexHomeomorph_mem_pos_iff {V : Type*}
    (σ : Finset V) {n : ℕ} (hcard : σ.card = n + 1)
    (x : (closedBall 0 1 : Set (Fin n → ℝ))) :
    (∀ v : σ, 0 < (closedBallFaceSimplexHomeomorph σ hcard x).1 v) ↔
      (x.1 : Fin n → ℝ) ∈ ball 0 1 :=
  closedBallFaceSimplexHomeomorph_mem_interior_iff σ hcard x

theorem closedBallFaceSimplexHomeomorph_mem_zero_iff {V : Type*}
    (σ : Finset V) {n : ℕ} (hcard : σ.card = n + 1)
    (x : (closedBall 0 1 : Set (Fin n → ℝ))) :
    (∃ v : σ, (closedBallFaceSimplexHomeomorph σ hcard x).1 v = 0) ↔
      (x.1 : Fin n → ℝ) ∈ sphere 0 1 := by
  classical
  have hpos := closedBallFaceSimplexHomeomorph_mem_pos_iff σ hcard x
  rw [← Metric.closedBall_sdiff_ball]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨x.2, ?_⟩
    intro hb
    have hp := hpos.2 hb v
    rw [hv] at hp
    exact (lt_irrefl 0) hp
  · intro hx
    have hn : ¬∀ v : σ, 0 < (closedBallFaceSimplexHomeomorph σ hcard x).1 v := by
      intro hp
      exact hx.2 (hpos.1 hp)
    push_neg at hn
    rcases hn with ⟨v, hv⟩
    exact ⟨v, le_antisymm hv
      ((closedBallFaceSimplexHomeomorph σ hcard x).2.1 v)⟩

end CurveComplex
namespace CurveComplex

open Metric Set

/-- Total extension of the characteristic disk map. On the closed unit ball it
is the disk/simplex homeomorphism followed by inclusion of the face. -/
noncomputable def faceDiskMap {V : Type*} (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ}
    (hcard : σ.card = n + 1) : (Fin n → ℝ) → RealizationPoint K := by
  classical
  exact fun x =>
  let z : (closedBall 0 1 : Set (Fin n → ℝ)) :=
    if hx : x ∈ closedBall 0 1 then ⟨x, hx⟩ else ⟨0, by simp⟩
  faceInclusion K σ hσ (closedBallFaceSimplexHomeomorph σ hcard z)

theorem faceDiskMap_apply_of_mem {V : Type*} (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ}
    (hcard : σ.card = n + 1) (x : Fin n → ℝ) (hx : x ∈ closedBall 0 1) :
    faceDiskMap K σ hσ hcard x =
      faceInclusion K σ hσ
        (closedBallFaceSimplexHomeomorph σ hcard ⟨x, hx⟩) := by
  simp [faceDiskMap, hx]

theorem faceDiskMap_continuousOn {V : Type*} (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ}
    (hcard : σ.card = n + 1) :
    ContinuousOn (faceDiskMap K σ hσ hcard)
      (closedBall 0 1 : Set (Fin n → ℝ)) := by
  rw [continuousOn_iff_continuous_restrict]
  have h : Continuous (fun x : (closedBall 0 1 : Set (Fin n → ℝ)) =>
      faceInclusion K σ hσ (closedBallFaceSimplexHomeomorph σ hcard x)) :=
    (continuous_faceInclusion K σ hσ).comp
      (closedBallFaceSimplexHomeomorph σ hcard).continuous
  convert h using 1
  funext x
  exact faceDiskMap_apply_of_mem K σ hσ hcard x.1 x.2

theorem faceDiskMap_mem_openFace_iff {V : Type*} (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ}
    (hcard : σ.card = n + 1) (x : Fin n → ℝ)
    (hx : x ∈ closedBall 0 1) :
    faceDiskMap K σ hσ hcard x ∈ openFace K σ ↔ x ∈ ball 0 1 := by
  rw [faceDiskMap_apply_of_mem K σ hσ hcard x hx,
    faceInclusion_mem_openFace_iff]
  exact closedBallFaceSimplexHomeomorph_mem_pos_iff σ hcard ⟨x, hx⟩

theorem faceDiskMap_mem_frontier_iff {V : Type*} (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ}
    (hcard : σ.card = n + 1) (x : Fin n → ℝ)
    (hx : x ∈ closedBall 0 1) :
    faceDiskMap K σ hσ hcard x ∈ faceCarrier K σ \ openFace K σ ↔
      x ∈ sphere 0 1 := by
  rw [faceDiskMap_apply_of_mem K σ hσ hcard x hx,
    faceInclusion_mem_frontier_iff]
  exact closedBallFaceSimplexHomeomorph_mem_zero_iff σ hcard ⟨x, hx⟩

theorem faceDiskMap_bijOn_openBall {V : Type*} (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ}
    (hcard : σ.card = n + 1) :
    Set.BijOn (faceDiskMap K σ hσ hcard)
      (ball 0 1 : Set (Fin n → ℝ)) (openFace K σ) := by
  classical
  constructor
  · intro x hx
    exact (faceDiskMap_mem_openFace_iff K σ hσ hcard x
      (Metric.ball_subset_closedBall hx)).2 hx
  constructor
  · intro x hx y hy hxy
    have hxc : x ∈ closedBall 0 1 := Metric.ball_subset_closedBall hx
    have hyc : y ∈ closedBall 0 1 := Metric.ball_subset_closedBall hy
    rw [faceDiskMap_apply_of_mem K σ hσ hcard x hxc,
      faceDiskMap_apply_of_mem K σ hσ hcard y hyc] at hxy
    have hs := (faceInclusion_injective K σ hσ) hxy
    have hd := (closedBallFaceSimplexHomeomorph σ hcard).injective hs
    exact congrArg Subtype.val hd
  · intro p hp
    have hrep : p ∈ faceInclusion K σ hσ '' finiteSimplexInterior σ := by
      rw [faceInclusion_image_interior K σ hσ]
      exact hp
    rcases hrep with ⟨s, hs, rfl⟩
    let x := (closedBallFaceSimplexHomeomorph σ hcard).symm s
    have hball : (x.1 : Fin n → ℝ) ∈ ball 0 1 := by
      have hpos : ∀ v : σ, 0 <
          (closedBallFaceSimplexHomeomorph σ hcard x).1 v := by
        have heq : closedBallFaceSimplexHomeomorph σ hcard x = s := by simp [x]
        rw [heq]
        exact hs
      exact (closedBallFaceSimplexHomeomorph_mem_pos_iff σ hcard x).1 hpos
    refine ⟨x.1, hball, ?_⟩
    rw [faceDiskMap_apply_of_mem K σ hσ hcard x.1 x.2]
    simp [x]

/-- The CW characteristic partial equivalence. Its source is exactly the
open unit ball and its target is the barycentric open face. -/
noncomputable def faceCWPartialEquiv {V : Type*} (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ}
    (hcard : σ.card = n + 1) : PartialEquiv (Fin n → ℝ) (RealizationPoint K) :=
  (faceDiskMap_bijOn_openBall K σ hσ hcard).toPartialEquiv
    (faceDiskMap K σ hσ hcard) (ball 0 1) (openFace K σ)

theorem faceCWPartialEquiv_source {V : Type*} (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ}
    (hcard : σ.card = n + 1) :
    (faceCWPartialEquiv K σ hσ hcard).source = ball 0 1 := by
  simp [faceCWPartialEquiv]

theorem faceCWPartialEquiv_target {V : Type*} (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ}
    (hcard : σ.card = n + 1) :
    (faceCWPartialEquiv K σ hσ hcard).target = openFace K σ := by
  simp [faceCWPartialEquiv]

theorem faceCWPartialEquiv_apply {V : Type*} (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ}
    (hcard : σ.card = n + 1) (x : Fin n → ℝ) :
    faceCWPartialEquiv K σ hσ hcard x = faceDiskMap K σ hσ hcard x := rfl

theorem faceCWPartialEquiv_continuousOn {V : Type*} (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ}
    (hcard : σ.card = n + 1) :
    ContinuousOn (faceCWPartialEquiv K σ hσ hcard)
      (closedBall 0 1 : Set (Fin n → ℝ)) := by
  exact (faceDiskMap_continuousOn K σ hσ hcard).congr
    (fun x _ => (faceCWPartialEquiv_apply K σ hσ hcard x).symm)

theorem faceCWPartialEquiv_image_closedBall {V : Type*}
    (K : AbstractSimplicialComplex V) (σ : Finset V) (hσ : σ ∈ K.faces)
    {n : ℕ} (hcard : σ.card = n + 1) :
    faceCWPartialEquiv K σ hσ hcard ''
      (closedBall 0 1 : Set (Fin n → ℝ)) = faceCarrier K σ := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [faceCWPartialEquiv_apply,
      faceDiskMap_apply_of_mem K σ hσ hcard x hx]
    exact faceInclusion_mem_faceCarrier K σ hσ _
  · intro hp
    rw [faceCarrier_eq_range_faceInclusion K σ hσ] at hp
    rcases hp with ⟨s, rfl⟩
    let x := (closedBallFaceSimplexHomeomorph σ hcard).symm s
    refine ⟨x.1, x.2, ?_⟩
    rw [faceCWPartialEquiv_apply,
      faceDiskMap_apply_of_mem K σ hσ hcard x.1 x.2]
    simp [x]

theorem faceCWPartialEquiv_image_sphere {V : Type*}
    (K : AbstractSimplicialComplex V) (σ : Finset V) (hσ : σ ∈ K.faces)
    {n : ℕ} (hcard : σ.card = n + 1) :
    faceCWPartialEquiv K σ hσ hcard ''
      (sphere 0 1 : Set (Fin n → ℝ)) =
      faceCarrier K σ \ openFace K σ := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxc : x ∈ closedBall 0 1 := Metric.sphere_subset_closedBall hx
    rw [faceCWPartialEquiv_apply]
    exact (faceDiskMap_mem_frontier_iff K σ hσ hcard x hxc).2 hx
  · intro hp
    have hcar : p ∈ faceCarrier K σ := hp.1
    rw [← faceCWPartialEquiv_image_closedBall K σ hσ hcard] at hcar
    rcases hcar with ⟨x, hxc, rfl⟩
    have hsphere : x ∈ sphere 0 1 :=
      (faceDiskMap_mem_frontier_iff K σ hσ hcard x hxc).1 (by
        simpa only [faceCWPartialEquiv_apply] using hp)
    exact ⟨x, hsphere, rfl⟩

theorem faceCWPartialEquiv_continuousOn_symm {V : Type*}
    (K : AbstractSimplicialComplex V) (σ : Finset V) (hσ : σ ∈ K.faces)
    {n : ℕ} (hcard : σ.card = n + 1) :
    ContinuousOn (faceCWPartialEquiv K σ hσ hcard).symm
      (faceCWPartialEquiv K σ hσ hcard).target := by
  let e := faceCWPartialEquiv K σ hσ hcard
  have hb : Topology.IsEmbedding (fun x : (ball 0 1 : Set (Fin n → ℝ)) =>
      faceDiskMap K σ hσ hcard x.1) := by
    have hc : Topology.IsEmbedding (fun x : (closedBall 0 1 : Set (Fin n → ℝ)) =>
        faceInclusion K σ hσ (closedBallFaceSimplexHomeomorph σ hcard x)) :=
      (faceInclusion_isClosedEmbedding K σ hσ).isEmbedding.comp
        (closedBallFaceSimplexHomeomorph σ hcard).isEmbedding
    have hco : Continuous (fun x : (ball 0 1 : Set (Fin n → ℝ)) =>
        (⟨x.1, Metric.ball_subset_closedBall x.2⟩ :
          (closedBall 0 1 : Set (Fin n → ℝ)))) := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val
    have hio : Topology.IsEmbedding (fun x : (ball 0 1 : Set (Fin n → ℝ)) =>
        (⟨x.1, Metric.ball_subset_closedBall x.2⟩ :
          (closedBall 0 1 : Set (Fin n → ℝ)))) := by
      apply Topology.IsEmbedding.of_comp hco continuous_subtype_val
      convert (Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding ((↑) : (ball 0 1 : Set (Fin n → ℝ)) → (Fin n → ℝ))) using 1
      rfl
    convert (hc.comp hio) using 1
    funext x
    exact faceDiskMap_apply_of_mem K σ hσ hcard x.1
      (Metric.ball_subset_closedBall x.2)
  have hrange : Set.range (fun x : (ball 0 1 : Set (Fin n → ℝ)) =>
      faceDiskMap K σ hσ hcard x.1) = openFace K σ := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact (faceDiskMap_bijOn_openBall K σ hσ hcard).mapsTo x.2
    · intro hp
      rcases (faceDiskMap_bijOn_openBall K σ hσ hcard).surjOn hp with ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let hhomeo :
      (ball 0 1 : Set (Fin n → ℝ)) ≃ₜ openFace K σ :=
    hb.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have hcont : Continuous (fun p : openFace K σ =>
      (hhomeo.symm p).1) := continuous_subtype_val.comp hhomeo.symm.continuous
  have hfun : ∀ p : openFace K σ, e.symm p.1 = (hhomeo.symm p).1 := by
    intro p
    have hp : p.1 ∈ e.target := by
      rw [faceCWPartialEquiv_target]
      exact p.2
    have hleft := e.right_inv hp
    have hright := hhomeo.apply_symm_apply p
    have hball : e.symm p.1 ∈ ball 0 1 := by
      rw [← faceCWPartialEquiv_source K σ hσ hcard]
      exact e.map_target hp
    have heq : e (e.symm p.1) =
        e (hhomeo.symm p).1 := by
      rw [hleft]
      change p.1 = faceDiskMap K σ hσ hcard (hhomeo.symm p).1
      have hhomeo_apply : (hhomeo (hhomeo.symm p)).1 =
          faceDiskMap K σ hσ hcard (hhomeo.symm p).1 := by
        change ((hb.toHomeomorph.trans (Homeomorph.setCongr hrange))
          (hhomeo.symm p)).1 = _
        rfl
      rw [← hhomeo_apply]
      exact congrArg Subtype.val hright.symm
    exact (faceDiskMap_bijOn_openBall K σ hσ hcard).injOn hball
      (hhomeo.symm p).2 heq
  rw [continuousOn_iff_continuous_restrict]
  have h := hcont.congr (fun p => (hfun p).symm)
  rw [faceCWPartialEquiv_target]
  change Continuous (fun p : openFace K σ =>
    (faceCWPartialEquiv K σ hσ hcard).symm p.1)
  exact h

end CurveComplex

namespace CurveComplex
open Metric Set

private abbrev FaceCell {V : Type*} (K : AbstractSimplicialComplex V) (n : ℕ) :=
  {σ : Finset V // σ ∈ K.faces ∧ σ.card = n + 1}

private noncomputable def faceCellMap {V : Type*} (K : AbstractSimplicialComplex V)
    (n : ℕ) (i : FaceCell K n) : PartialEquiv (Fin n → ℝ) (RealizationPoint K) :=
  faceCWPartialEquiv K i.1 i.2.1 i.2.2

private theorem faceCellMap_source {V : Type*} (K : AbstractSimplicialComplex V)
    (n : ℕ) (i : FaceCell K n) : (faceCellMap K n i).source = ball 0 1 :=
  faceCWPartialEquiv_source K i.1 i.2.1 i.2.2

private theorem faceCellMap_target {V : Type*} (K : AbstractSimplicialComplex V)
    (n : ℕ) (i : FaceCell K n) : (faceCellMap K n i).target = openFace K i.1 :=
  faceCWPartialEquiv_target K i.1 i.2.1 i.2.2

private theorem faceCellMap_image_openBall {V : Type*} (K : AbstractSimplicialComplex V)
    (n : ℕ) (i : FaceCell K n) : faceCellMap K n i '' ball 0 1 = openFace K i.1 := by
  rw [← faceCellMap_source K n i, PartialEquiv.image_source_eq_target, faceCellMap_target]

private theorem faceCellMap_image_closedBall {V : Type*} (K : AbstractSimplicialComplex V)
    (n : ℕ) (i : FaceCell K n) : faceCellMap K n i '' closedBall 0 1 = faceCarrier K i.1 :=
  faceCWPartialEquiv_image_closedBall K i.1 i.2.1 i.2.2

private theorem faceCellMap_image_sphere {V : Type*} (K : AbstractSimplicialComplex V)
    (n : ℕ) (i : FaceCell K n) : faceCellMap K n i '' sphere 0 1 = faceCarrier K i.1 \ openFace K i.1 :=
  faceCWPartialEquiv_image_sphere K i.1 i.2.1 i.2.2

private theorem faceCell_pairwise {V : Type*} (K : AbstractSimplicialComplex V) :
    (Set.univ : Set (Σ n, FaceCell K n)).PairwiseDisjoint
      (fun ni => faceCellMap K ni.1 ni.2 '' ball 0 1) := by
  intro a ha b hb hab
  change Disjoint (faceCellMap K a.1 a.2 '' ball 0 1)
    (faceCellMap K b.1 b.2 '' ball 0 1)
  rw [faceCellMap_image_openBall, faceCellMap_image_openBall]
  apply openFace_disjoint K
  intro heq
  apply hab
  cases a with
  | mk n i =>
    cases b with
    | mk m j =>
      have hcard : n = m := by
        have hi : i.1.card = n + 1 := i.2.2
        have hj : j.1.card = m + 1 := j.2.2
        have hcards : i.1.card = j.1.card := congrArg Finset.card heq
        omega
      subst m
      have hij : i = j := Subtype.ext heq
      subst j
      rfl

private theorem faceCell_union {V : Type*} (K : AbstractSimplicialComplex V) :
    (⋃ (n : ℕ) (i : FaceCell K n), faceCellMap K n i '' closedBall 0 1) =
      (Set.univ : Set (RealizationPoint K)) := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  obtain ⟨σ, hσ, x, rfl⟩ := exists_faceInclusion_eq K p
  have hpos : 0 < σ.card := (K.isRelLowerSet_faces hσ).1.card_pos
  let n := σ.card - 1
  have hn : σ.card = n + 1 := by omega
  let i : FaceCell K n := ⟨σ, hσ, hn⟩
  refine ⟨n, i, ?_⟩
  rw [faceCellMap_image_closedBall]
  exact faceInclusion_mem_faceCarrier K σ hσ x

private theorem faceCell_weak_closed {V : Type*} (K : AbstractSimplicialComplex V)
    (A : Set (RealizationPoint K))
    (h : ∀ n (i : FaceCell K n), IsClosed (A ∩ faceCellMap K n i '' closedBall 0 1)) :
    IsClosed A := by
  rw [← isOpen_compl_iff]
  intro σ hσ
  have hpos : 0 < σ.card := (K.isRelLowerSet_faces hσ).1.card_pos
  let n := σ.card - 1
  have hn : σ.card = n + 1 := by omega
  let i : FaceCell K n := ⟨σ, hσ, hn⟩
  have hc : IsClosed ((faceInclusion K σ hσ) ⁻¹' A) := by
    have hh := h n i
    rw [faceCellMap_image_closedBall] at hh
    have heq : (faceInclusion K σ hσ) ⁻¹' A =
        (faceInclusion K σ hσ) ⁻¹' (A ∩ faceCarrier K σ) := by
      ext x
      simp [faceInclusion_mem_faceCarrier K σ hσ]
    rw [heq]
    exact hh.preimage (continuous_faceInclusion K σ hσ)
  simpa [Set.preimage_compl] using hc.isOpen_compl

end CurveComplex

namespace CurveComplex
open Metric Set

private theorem faceCell_mapsTo {V : Type*} (K : AbstractSimplicialComplex V)
    {n : ℕ} (i : FaceCell K n) :
    ∃ I : Π m, Finset (FaceCell K m),
      MapsTo (faceCellMap K n i) (sphere 0 1)
        (⋃ (m < n) (j ∈ I m), faceCellMap K m j '' closedBall 0 1) := by
  classical
  let I : ∀ m, Finset (FaceCell K m) := fun m =>
    (i.1.powerset.erase i.1).filterMap
      (fun τ => if h : τ ∈ K.faces ∧ τ.card = m + 1 then
        some (⟨τ, h.1, h.2⟩ : FaceCell K m) else none) (by
          intro a a' b hb hb'
          by_cases hA : a ∈ K.faces ∧ a.card = m + 1
          · by_cases hB : a' ∈ K.faces ∧ a'.card = m + 1
            · simp [hA] at hb
              simp [hB] at hb'
              exact congrArg Subtype.val (hb.trans hb'.symm)
            · simp [hB] at hb'
          · simp [hA] at hb)
  refine ⟨I, ?_⟩
  intro x hx
  have hp : faceCellMap K n i x ∈ faceCarrier K i.1 \ openFace K i.1 := by
    rw [← faceCellMap_image_sphere K n i]
    exact ⟨x, hx, rfl⟩
  rw [faceFrontier_eq_union_proper_openFaces] at hp
  rcases Set.mem_iUnion.mp hp with ⟨τ, hp⟩
  rcases Set.mem_iUnion.mp hp with ⟨hτ, hp⟩
  obtain ⟨hne, hsubset⟩ := Finset.mem_erase.mp hτ
  have hsubset' : τ ⊆ i.1 := Finset.mem_powerset.mp hsubset
  have hsub : τ ⊂ i.1 := Finset.ssubset_iff_subset_ne.mpr ⟨hsubset', hne⟩
  have hnonempty : τ.Nonempty := by
    rw [← hp]
    exact supportFinset_nonempty K (faceCellMap K n i x)
  have hface : τ ∈ K.faces := (K.isRelLowerSet_faces i.2.1).2 hsubset' hnonempty
  let m := τ.card - 1
  have hm : τ.card = m + 1 := by
    have hpos : 0 < τ.card := hnonempty.card_pos
    omega
  have hmn : m < n := by
    have hcard : τ.card < i.1.card := Finset.card_lt_card hsub
    have hi : i.1.card = n + 1 := i.2.2
    have hpos : 0 < τ.card := hnonempty.card_pos
    omega
  have hj : (⟨τ, hface, hm⟩ : FaceCell K m) ∈ I m := by
    simp [I, hface, hm]
    exact ⟨hne, hsubset'⟩
  refine Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hmn, ?_⟩⟩
  refine Set.mem_iUnion.mpr ⟨⟨τ, hface, hm⟩, Set.mem_iUnion.mpr ⟨hj, ?_⟩⟩
  rw [faceCellMap_image_closedBall]
  exact (mem_faceCarrier_iff_support_subset K τ _).mpr (by
    change supportFinset K (faceCellMap K n i x) = τ at hp
    rw [hp])

end CurveComplex

namespace CurveComplex

noncomputable instance realizationPointCWComplex {V : Type*}
    (K : AbstractSimplicialComplex V) :
    Topology.CWComplex (Set.univ : Set (RealizationPoint K)) where
  cell := FaceCell K
  map := faceCellMap K
  source_eq := faceCellMap_source K
  continuousOn n i := faceCWPartialEquiv_continuousOn K i.1 i.2.1 i.2.2
  continuousOn_symm n i := faceCWPartialEquiv_continuousOn_symm K i.1 i.2.1 i.2.2
  pairwiseDisjoint' := faceCell_pairwise K
  mapsTo' n i := faceCell_mapsTo K i
  closed' A hAC h := faceCell_weak_closed K A h
  union' := faceCell_union K

end CurveComplex
