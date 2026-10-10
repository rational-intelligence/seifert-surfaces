import CurveComplexGenusTwo.Foundations.GenericRealization

set_option maxHeartbeats 1000000

namespace CurveComplex

variable {V : Type*} [DecidableEq V] (K : AbstractSimplicialComplex V)

abbrev ConeTime := Set.Icc (0 : ℝ) 1

private theorem realizationPoint_ext {x y : RealizationPoint K}
    (h : x.weight = y.weight) : x = y := by
  cases x with
  | mk wx hx px =>
    cases y with
    | mk wy hy py =>
      cases h
      rfl

def HasConeApex (a : V) : Prop :=
  ∀ σ : Finset V, σ ∈ K.faces → insert a σ ∈ K.faces

noncomputable def coneVertex (a : V) : RealizationPoint K := by
  classical
  exact {
    weight := fun v => if v = a then 1 else 0
    nonneg := by intro v; split_ifs <;> norm_num
    liesInFace := by
      refine ⟨{a}, K.singleton_mem a, ?_, ?_⟩
      · intro v hv
        simp only [Finset.mem_singleton] at hv
        simp [hv]
      · simp
  }

noncomputable def coneWeight (a : V) (t : ConeTime)
    (x : RealizationPoint K) (v : V) : ℝ :=
  (1 - (t : ℝ)) * x.weight v + if v = a then (t : ℝ) else 0

theorem coneWeight_nonneg (a : V) (t : ConeTime)
    (x : RealizationPoint K) (v : V) : 0 ≤ coneWeight K a t x v := by
  unfold coneWeight
  apply add_nonneg
  · exact mul_nonneg (sub_nonneg.mpr t.property.2) (x.nonneg v)
  · split_ifs
    · exact t.property.1
    · exact le_refl 0

theorem coneWeight_zero_outside (a : V) (t : ConeTime)
    (x : RealizationPoint K) (σ : Finset V)
    (hσ : ∀ v ∉ σ, x.weight v = 0) (v : V)
    (hv : v ∉ insert a σ) : coneWeight K a t x v = 0 := by
  have hna : v ≠ a := by
    intro h
    exact hv (h ▸ Finset.mem_insert_self a σ)
  have hns : v ∉ σ := by
    intro h
    exact hv (Finset.mem_insert_of_mem h)
  simp [coneWeight, hσ v hns, hna]

theorem coneWeight_sum (a : V) (t : ConeTime)
    (x : RealizationPoint K) (σ : Finset V)
    (hσ : ∀ v ∉ σ, x.weight v = 0)
    (hsum : ∑ v ∈ σ, x.weight v = 1) :
    ∑ v ∈ insert a σ, coneWeight K a t x v = 1 := by
  classical
  have hsum' : ∑ v ∈ insert a σ, x.weight v = 1 := by
    by_cases ha : a ∈ σ
    · simpa [Finset.insert_eq_of_mem ha] using hsum
    · rw [Finset.sum_insert ha, hσ a ha, zero_add]
      exact hsum
  have hdelta : ∑ v ∈ insert a σ, (if v = a then (t : ℝ) else 0) = t := by
    simp
  simp only [coneWeight, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsum', hdelta]
  ring

noncomputable def coneInterpolate (a : V) (ha : HasConeApex K a)
    (t : ConeTime) (x : RealizationPoint K) : RealizationPoint K := by
  classical
  refine ⟨coneWeight K a t x, coneWeight_nonneg K a t x, ?_⟩
  obtain ⟨σ, hσ, hzero, hsum⟩ := x.liesInFace
  exact ⟨insert a σ, ha σ hσ,
    coneWeight_zero_outside K a t x σ hzero,
    coneWeight_sum K a t x σ hzero hsum⟩

theorem coneInterpolate_zero (a : V) (ha : HasConeApex K a)
    (x : RealizationPoint K) :
    coneInterpolate K a ha ⟨0, by norm_num⟩ x = x := by
  cases x with
  | mk weight nonneg liesInFace =>
    simp only [coneInterpolate, RealizationPoint.mk.injEq]
    funext v
    simp [coneWeight]

theorem coneInterpolate_one (a : V) (ha : HasConeApex K a)
    (x : RealizationPoint K) :
    coneInterpolate K a ha ⟨1, by norm_num⟩ x = coneVertex K a := by
  cases x with
  | mk weight nonneg liesInFace =>
    simp only [coneInterpolate, coneVertex, RealizationPoint.mk.injEq]
    funext v
    simp [coneWeight]

theorem faceInclusion_continuous (σ : Finset V) (hσ : σ ∈ K.faces) :
    Continuous (faceInclusion K σ hσ) := by
  refine ⟨?_⟩
  intro U hU
  exact hU σ hσ

noncomputable def finiteConeMap (a : V) (ha : HasConeApex K a)
    (t : ConeTime) (σ : Finset V) (hσ : σ ∈ K.faces) :
    FiniteSimplex σ → FiniteSimplex (insert a σ) := by
  classical
  intro x
  let y := faceInclusion K σ hσ x
  refine ⟨fun v => coneWeight K a t y v, ?_, ?_⟩
  · intro v
    exact coneWeight_nonneg K a t y v
  · have hzero : ∀ v ∉ σ, y.weight v = 0 := by
      intro v hv
      simp [y, faceInclusion, hv]
    have hsum : ∑ v ∈ σ, y.weight v = 1 := by
      calc
        (∑ v ∈ σ, y.weight v) = ∑ v ∈ σ.attach, y.weight v := by
          rw [← Finset.sum_attach]
        _ = ∑ v : σ, x.val v := by
          simp [y, faceInclusion, Finset.univ_eq_attach]
        _ = 1 := by simpa [Finset.univ_eq_attach] using x.property.2
    simpa only [Finset.sum_attach, Finset.univ_eq_attach] using
      coneWeight_sum K a t y σ hzero hsum

theorem finiteConeMap_continuous (a : V) (ha : HasConeApex K a)
    (t : ConeTime) (σ : Finset V) (hσ : σ ∈ K.faces) :
    Continuous (finiteConeMap K a ha t σ hσ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  have hw : Continuous (fun x : FiniteSimplex σ =>
      (faceInclusion K σ hσ x).weight v.1) := by
    unfold faceInclusion
    by_cases hv : (v : V) ∈ σ
    · simp only [dif_pos hv]
      exact (continuous_apply (⟨v, hv⟩ : σ)).comp continuous_subtype_val
    · simp only [dif_neg hv]
      exact continuous_const
  dsimp [finiteConeMap, coneWeight]
  fun_prop

theorem finiteConeMap_faceInclusion (a : V) (ha : HasConeApex K a)
    (t : ConeTime) (σ : Finset V) (hσ : σ ∈ K.faces)
    (x : FiniteSimplex σ) :
    faceInclusion K (insert a σ) (ha σ hσ) (finiteConeMap K a ha t σ hσ x) =
      coneInterpolate K a ha t (faceInclusion K σ hσ x) := by
  apply realizationPoint_ext K
  funext v
  unfold faceInclusion coneInterpolate
  dsimp only [RealizationPoint.weight]
  by_cases hv : v ∈ insert a σ
  · rw [dif_pos hv]
    rfl
  · have hna : v ≠ a := by
      intro h
      exact hv (h ▸ Finset.mem_insert_self a σ)
    have hns : v ∉ σ := by
      intro h
      exact hv (Finset.mem_insert_of_mem h)
    rw [dif_neg hv]
    simp [coneWeight, hna, hns]

theorem coneInterpolate_continuous (a : V) (ha : HasConeApex K a)
    (t : ConeTime) : Continuous (coneInterpolate K a ha t) := by
  refine ⟨?_⟩
  intro U hU
  intro σ hσ
  have heq : (coneInterpolate K a ha t ∘ faceInclusion K σ hσ) =
      faceInclusion K (insert a σ) (ha σ hσ) ∘ finiteConeMap K a ha t σ hσ := by
    funext x
    exact (finiteConeMap_faceInclusion K a ha t σ hσ x).symm
  change IsOpen ((coneInterpolate K a ha t ∘ faceInclusion K σ hσ) ⁻¹' U)
  rw [heq]
  exact hU (insert a σ) (ha σ hσ) |>.preimage
    (finiteConeMap_continuous K a ha t σ hσ)

noncomputable def finiteConeMapJoint (a : V) (ha : HasConeApex K a)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    ConeTime × FiniteSimplex σ → FiniteSimplex (insert a σ) :=
  fun p => finiteConeMap K a ha p.1 σ hσ p.2

theorem finiteConeMapJoint_continuous (a : V) (ha : HasConeApex K a)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    Continuous (finiteConeMapJoint K a ha σ hσ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  have hw : Continuous (fun p : ConeTime × FiniteSimplex σ =>
      (faceInclusion K σ hσ p.2).weight v.1) := by
    unfold faceInclusion
    by_cases hv : (v : V) ∈ σ
    · simp only [dif_pos hv]
      exact (continuous_apply (⟨v, hv⟩ : σ)).comp
        (continuous_subtype_val.comp continuous_snd)
    · simp only [dif_neg hv]
      exact continuous_const
  change Continuous (fun p : ConeTime × FiniteSimplex σ =>
    coneWeight K a p.1 (faceInclusion K σ hσ p.2) v.1)
  dsimp [coneWeight]
  have ht : Continuous (fun p : ConeTime × FiniteSimplex σ => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  by_cases hva : (v : V) = a
  · simp [hva]
    have hc : Continuous (fun p : ConeTime × FiniteSimplex σ => (1 : ℝ) - (p.1 : ℝ)) :=
      continuous_const.sub ht
    convert (hc.mul hw).add ht using 1
    funext p
    simp [hva]
  · simp [hva]
    exact ((continuous_const.sub ht).mul hw)

theorem finiteConeMapJoint_faceInclusion (a : V) (ha : HasConeApex K a)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (p : ConeTime × FiniteSimplex σ) :
    faceInclusion K (insert a σ) (ha σ hσ)
        (finiteConeMapJoint K a ha σ hσ p) =
      coneInterpolate K a ha p.1 (faceInclusion K σ hσ p.2) := by
  exact finiteConeMap_faceInclusion K a ha p.1 σ hσ p.2

noncomputable def coneInterpolateJoint (a : V) (ha : HasConeApex K a) :
    ConeTime × RealizationPoint K → RealizationPoint K :=
  fun p => coneInterpolate K a ha p.1 p.2

theorem coneInterpolateJoint_chart_continuous (a : V) (ha : HasConeApex K a)
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    Continuous (fun p : ConeTime × FiniteSimplex σ =>
      coneInterpolateJoint K a ha (p.1, faceInclusion K σ hσ p.2)) := by
  refine ⟨?_⟩
  intro U hU
  have heq :
      (coneInterpolateJoint K a ha ∘
        (fun p : ConeTime × FiniteSimplex σ =>
          (p.1, faceInclusion K σ hσ p.2))) =
      faceInclusion K (insert a σ) (ha σ hσ) ∘
        finiteConeMapJoint K a ha σ hσ := by
    funext p
    exact (finiteConeMapJoint_faceInclusion K a ha σ hσ p).symm
  change IsOpen ((coneInterpolateJoint K a ha ∘
    (fun p : ConeTime × FiniteSimplex σ =>
      (p.1, faceInclusion K σ hσ p.2))) ⁻¹' U)
  rw [heq]
  exact hU (insert a σ) (ha σ hσ) |>.preimage
    (finiteConeMapJoint_continuous K a ha σ hσ)

private abbrev FaceSimplex (K : AbstractSimplicialComplex V) :=
  Σ σ : {σ : Finset V // σ ∈ K.faces}, FiniteSimplex σ.1

private noncomputable def faceSimplexMap : FaceSimplex K → RealizationPoint K :=
  fun p => faceInclusion K p.1.1 p.1.2 p.2

private theorem faceSimplexMap_quotient :
    Topology.IsQuotientMap (faceSimplexMap K) := by
  refine ⟨⟨?_⟩, ?_⟩
  · apply TopologicalSpace.ext
    funext U
    apply propext
    change IsOpen U ↔ IsOpen ((faceSimplexMap K) ⁻¹' U)
    constructor
    · intro hU
      exact isOpen_sigma_iff.mpr (fun i => hU i.1 i.2)
    · intro hU σ hσ
      exact isOpen_sigma_iff.mp hU ⟨σ, hσ⟩
  · intro x
    obtain ⟨σ, hσ, hzero, hsum⟩ := x.liesInFace
    let y : FiniteSimplex σ := ⟨fun v => x.weight v, (fun v => x.nonneg v), by
      simpa only [Finset.sum_attach, Finset.univ_eq_attach] using hsum⟩
    refine ⟨⟨⟨σ, hσ⟩, y⟩, ?_⟩
    apply realizationPoint_ext K
    funext v
    by_cases hv : v ∈ σ
    · simp [faceSimplexMap, faceInclusion, y, hv]
    · simp [faceSimplexMap, faceInclusion, y, hv, hzero v hv]

theorem coneInterpolateJoint_continuous (a : V) (ha : HasConeApex K a) :
    Continuous (coneInterpolateJoint K a ha) := by
  apply (faceSimplexMap_quotient K).continuous_lift_prod_right
  have h : Continuous (fun p : FaceSimplex K × ConeTime =>
      coneInterpolateJoint K a ha (p.2, faceSimplexMap K p.1)) := by
    let g : (Σ i : {σ : Finset V // σ ∈ K.faces}, FiniteSimplex i.1 × ConeTime) →
        RealizationPoint K := fun p =>
      coneInterpolateJoint K a ha (p.2.2, faceInclusion K p.1.1 p.1.2 p.2.1)
    have hg : Continuous g := continuous_sigma_iff.mpr (by
      intro i
      exact (coneInterpolateJoint_chart_continuous K a ha i.1 i.2).comp continuous_swap)
    exact hg.comp (Homeomorph.sigmaProdDistrib (Y := ConeTime)).continuous
  exact h.comp continuous_swap

noncomputable def coneHomotopy (a : V) (ha : HasConeApex K a) :
    ContinuousMap.Homotopy (ContinuousMap.id (RealizationPoint K))
      (ContinuousMap.const (RealizationPoint K) (coneVertex K a)) where
  toFun := coneInterpolateJoint K a ha
  continuous_toFun := coneInterpolateJoint_continuous K a ha
  map_zero_left := coneInterpolate_zero K a ha
  map_one_left := coneInterpolate_one K a ha

theorem coneApex_contractible (a : V) (ha : HasConeApex K a) :
    ContractibleSpace (RealizationPoint K) := by
  apply (contractible_iff_id_nullhomotopic (RealizationPoint K)).2
  exact ⟨coneVertex K a, ⟨coneHomotopy K a ha⟩⟩

end CurveComplex
