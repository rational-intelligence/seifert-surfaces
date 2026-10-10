import CurveComplexGenusTwo.Topology.StarConeChart
import CurveComplexGenusTwo.Topology.FiniteLinkCompact
import CurveComplexGenusTwo.Topology.LinkWeakTopology

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set

variable {V : Type*} [DecidableEq V]

private theorem point_ext_weight
    (K : AbstractSimplicialComplex V) {x y : RealizationPoint K}
    (h : x.weight = y.weight) : x = y := by
  cases x with
  | mk wx hx px =>
    cases y with
    | mk wy hy py =>
      cases h
      rfl

private theorem realizationT2Space_here
    (K : AbstractSimplicialComplex V) : T2Space (RealizationPoint K) := by
  constructor
  intro p q hpq
  have h : ∃ w : V, p.weight w ≠ q.weight w := by
    by_contra hn
    push Not at hn
    exact hpq (point_ext_weight K (funext hn))
  obtain ⟨w, hw⟩ := h
  exact separated_by_continuous (realization_weight_continuous K w) hw

private theorem finiteSimplex_compact_here (σ : Finset V) :
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

private theorem isClosed_nonseparatingWeightLocus_here
    (K : AbstractSimplicialComplex V) (separating : V → Prop) :
    IsClosed (NonseparatingWeightLocus K separating) := by
  have heq : NonseparatingWeightLocus K separating =
      ⋂ v : {w : V // separating w},
        {x : RealizationPoint K | x.weight v.1 = 0} := by
    ext x
    simp [NonseparatingWeightLocus]
  rw [heq]
  exact isClosed_iInter (fun v =>
    isClosed_eq (realization_weight_continuous K v.1) continuous_const)

private theorem isClosed_realizedSeparatingLink_here
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hcurve : ∀ τ : Finset V, τ ∈ K.faces → CurveFace intersect 1 τ)
    (hface : ∀ τ : Finset V, τ.Nonempty →
      CurveFace intersect 1 τ → τ ∈ K.faces)
    (v : {u : V // separating u}) :
    IsClosed (RealizedSeparatingLink K intersect separating v) := by
  exact (isClosed_closedStarLocus K intersect v hcurve hface).inter
    (isClosed_nonseparatingWeightLocus_here K separating)

private theorem isCompact_link_supported_on_face
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hcurve : ∀ τ : Finset V, τ ∈ K.faces → CurveFace intersect 1 τ)
    (hface : ∀ τ : Finset V, τ.Nonempty →
      CurveFace intersect 1 τ → τ ∈ K.faces)
    (v : {u : V // separating u})
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    IsCompact {x : RealizedSeparatingLink K intersect separating v |
      ∀ w ∉ σ, x.1.weight w = 0} := by
  letI := finiteSimplex_compact_here σ
  have hfacecompact : IsCompact (Set.range (faceInclusion K σ hσ)) := by
    simpa only [Set.image_univ] using
      (isCompact_univ.image (faceInclusion_continuous K σ hσ))
  have hcarrier : IsClosed
      {x : RealizationPoint K | ∀ w ∉ σ, x.weight w = 0} := by
    have heq : {x : RealizationPoint K | ∀ w ∉ σ, x.weight w = 0} =
        ⋂ w : {w : V // w ∉ σ},
          {x : RealizationPoint K | x.weight w.1 = 0} := by
      ext x
      simp
    rw [heq]
    exact isClosed_iInter (fun w =>
      isClosed_eq (realization_weight_continuous K w.1) continuous_const)
  have hclosed : IsClosed
      {x : RealizationPoint K |
        x ∈ RealizedSeparatingLink K intersect separating v ∧
        ∀ w ∉ σ, x.weight w = 0} :=
    (isClosed_realizedSeparatingLink_here K intersect separating hcurve hface v).inter
      hcarrier
  have hsubset :
      {x : RealizationPoint K |
        x ∈ RealizedSeparatingLink K intersect separating v ∧
        ∀ w ∉ σ, x.weight w = 0} ⊆
      Set.range (faceInclusion K σ hσ) := by
    intro x hx
    obtain ⟨ρ, _, hρzero, hρsum⟩ := x.liesInFace
    have hσu : ∑ w ∈ σ, x.weight w = ∑ w ∈ σ ∪ ρ, x.weight w := by
      apply Finset.sum_subset_zero_on_sdiff
      · exact Finset.subset_union_left
      · intro w hw
        exact hx.2 w (Finset.mem_sdiff.mp hw).2
      · intro w hw
        rfl
    have hρu : ∑ w ∈ ρ, x.weight w = ∑ w ∈ σ ∪ ρ, x.weight w := by
      apply Finset.sum_subset_zero_on_sdiff
      · exact Finset.subset_union_right
      · intro w hw
        exact hρzero w (Finset.mem_sdiff.mp hw).2
      · intro w hw
        rfl
    have hsum : ∑ w ∈ σ, x.weight w = 1 := by
      calc
        _ = ∑ w ∈ σ ∪ ρ, x.weight w := hσu
        _ = ∑ w ∈ ρ, x.weight w := hρu.symm
        _ = 1 := hρsum
    let p : FiniteSimplex σ :=
      ⟨fun w => x.weight w, (fun w => x.nonneg w), by
        simpa only [Finset.sum_attach, Finset.univ_eq_attach] using hsum⟩
    refine ⟨p, ?_⟩
    apply point_ext_weight K
    funext w
    by_cases hw : w ∈ σ
    · simp [faceInclusion, p, hw]
    · simp [faceInclusion, p, hw, hx.2 w hw]
  have hc : IsCompact
      {x : RealizationPoint K |
        x ∈ RealizedSeparatingLink K intersect separating v ∧
        ∀ w ∉ σ, x.weight w = 0} :=
    IsCompact.of_isClosed_subset hfacecompact hclosed hsubset
  apply Subtype.isCompact_iff.mpr
  convert hc using 1
  ext x
  simp [and_comm]

private def compactConeFaceBound
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop) (v : {u : V // separating u})
    (hne : Nonempty (RealizedSeparatingLink K intersect separating v))
    (σ : Finset V) :
    Set (TopologicalCone (RealizedSeparatingLink K intersect separating v)) :=
  (fun p : ConeTime × RealizedSeparatingLink K intersect separating v =>
    topologicalConeMk p.1 p.2) ''
      (Set.univ ×ˢ {x : RealizedSeparatingLink K intersect separating v |
        ∀ w ∉ σ, x.1.weight w = 0}) ∪
    {topologicalConeApex (Classical.choice hne)}

private theorem isCompact_compactConeFaceBound
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hcurve : ∀ τ : Finset V, τ ∈ K.faces → CurveFace intersect 1 τ)
    (hface : ∀ τ : Finset V, τ.Nonempty →
      CurveFace intersect 1 τ → τ ∈ K.faces)
    (v : {u : V // separating u})
    (hne : Nonempty (RealizedSeparatingLink K intersect separating v))
    (σ : Finset V) (hσ : σ ∈ K.faces) :
    IsCompact (compactConeFaceBound K intersect separating v hne σ) := by
  have hlink := isCompact_link_supported_on_face K intersect separating
    hcurve hface v σ hσ
  unfold compactConeFaceBound
  exact ((isCompact_univ.prod hlink).image topologicalConeMk_continuous).union
    isCompact_singleton

private theorem closedStarConeMap_mem_compactConeFaceBound
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop) (v : {u : V // separating u})
    (hfull : HasRealizedStarFaces K intersect v)
    (hne : Nonempty (RealizedSeparatingLink K intersect separating v))
    (σ : Finset V)
    (c : TopologicalCone (RealizedSeparatingLink K intersect separating v))
    (hsupport : ∀ w ∉ σ,
      (closedStarConeMap K intersect separating v hfull c).1.weight w = 0) :
    c ∈ compactConeFaceBound K intersect separating v hne σ := by
  induction c using Quotient.inductionOn with
  | _ p =>
    rcases p with ⟨t, x⟩
    by_cases htop : t = 1
    · apply Set.mem_union_right
      change topologicalConeMk t x = topologicalConeApex (Classical.choice hne)
      rw [htop]
      exact topologicalConeApex_eq x (Classical.choice hne)
    · apply Set.mem_union_left
      change topologicalConeMk t x ∈
        (fun p : ConeTime × RealizedSeparatingLink K intersect separating v =>
          topologicalConeMk p.1 p.2) ''
          (Set.univ ×ˢ {x : RealizedSeparatingLink K intersect separating v |
            ∀ w ∉ σ, x.1.weight w = 0})
      refine ⟨(t, x), ⟨Set.mem_univ _, ?_⟩, rfl⟩
      intro w hwσ
      by_cases hwv : w = (v : V)
      · subst w
        exact x.property.2 v v.property
      · have hzero := hsupport w hwσ
        change (closedStarConeMap K intersect separating v hfull
          (topologicalConeMk t x)).1.weight w = 0 at hzero
        rw [closedStarConeMap_mk, closedStarInterpolate_weight] at hzero
        simp only [coneWeight, if_neg hwv] at hzero
        have hfactor : (1 - (t : ℝ)) ≠ 0 := by
          intro hz
          apply htop
          apply Subtype.ext
          have htval : (t : ℝ) = 1 := by linarith only [hz]
          simpa using htval
        have hmul : (1 - (t : ℝ)) * x.1.weight w = 0 := by
          simpa only [add_zero] using hzero
        exact (mul_eq_zero.mp hmul).resolve_left hfactor

/-- A continuous map to a weakly covered Hausdorff space is closed when each
chart has a compact preimage bound. -/
private theorem isClosedMap_of_compact_chart_bounds
    {A B J : Type*} [TopologicalSpace A] [TopologicalSpace B] [T2Space B]
    (f : A → B) (hf : Continuous f) (charts : J → Set B)
    (hweak : ∀ S : Set B,
      (∀ j, IsClosed ((fun z : charts j => (z : B)) ⁻¹' S)) → IsClosed S)
    (bounds : J → Set A) (hcompact : ∀ j, IsCompact (bounds j))
    (hbound : ∀ j a, f a ∈ charts j → a ∈ bounds j) :
    IsClosedMap f := by
  intro C hC
  apply hweak
  intro j
  have hCi : IsCompact (C ∩ bounds j) :=
    (hcompact j).inter_left hC
  have hIm : IsClosed (f '' (C ∩ bounds j)) :=
    (hCi.image hf).isClosed
  have heq : ((fun z : charts j => (z : B)) ⁻¹' (f '' C)) =
      ((fun z : charts j => (z : B)) ⁻¹' (f '' (C ∩ bounds j))) := by
    ext z
    constructor
    · rintro ⟨a, haC, haz⟩
      refine ⟨a, ⟨haC, ?_⟩, haz⟩
      exact hbound j a (haz ▸ z.property)
    · rintro ⟨a, ha, haz⟩
      exact ⟨a, ha.1, haz⟩
  rw [heq]
  exact hIm.preimage continuous_subtype_val

private noncomputable def finiteClosedStarConeMap
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (hfull : HasRealizedStarFaces K intersect v)
    (t : ConeTime) (σ : Finset V) (hσ : σ ∈ K.faces)
    (hstar : ClosedStarFace intersect v σ) :
    FiniteSimplex σ → FiniteSimplex (insert v σ) := by
  classical
  intro x
  let y := faceInclusion K σ hσ x
  refine ⟨fun w => coneWeight K v t y w, ?_, ?_⟩
  · intro w
    exact coneWeight_nonneg K v t y w
  · have hzero : ∀ w ∉ σ, y.weight w = 0 := by
      intro w hw
      simp [y, faceInclusion, hw]
    have hsum : ∑ w ∈ σ, y.weight w = 1 := by
      calc
        (∑ w ∈ σ, y.weight w) = ∑ w ∈ σ.attach, y.weight w := by
          rw [← Finset.sum_attach]
        _ = ∑ w : σ, x.val w := by
          simp [y, faceInclusion, Finset.univ_eq_attach]
        _ = 1 := by simpa [Finset.univ_eq_attach] using x.property.2
    simpa only [Finset.sum_attach, Finset.univ_eq_attach] using
      coneWeight_sum K v t y σ hzero hsum

private theorem finiteClosedStarConeMap_continuous
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (hfull : HasRealizedStarFaces K intersect v)
    (t : ConeTime) (σ : Finset V) (hσ : σ ∈ K.faces)
    (hstar : ClosedStarFace intersect v σ) :
    Continuous (finiteClosedStarConeMap K intersect v hfull t σ hσ hstar) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro w
  have hw : Continuous (fun x : FiniteSimplex σ =>
      (faceInclusion K σ hσ x).weight w.1) := by
    unfold faceInclusion
    by_cases hwσ : (w : V) ∈ σ
    · simp only [dif_pos hwσ]
      exact (continuous_apply (⟨w, hwσ⟩ : σ)).comp continuous_subtype_val
    · simp only [dif_neg hwσ]
      exact continuous_const
  dsimp [finiteClosedStarConeMap, coneWeight]
  fun_prop

private theorem finiteClosedStarConeMap_faceInclusion
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (hfull : HasRealizedStarFaces K intersect v)
    (t : ConeTime) (σ : Finset V) (hσ : σ ∈ K.faces)
    (hstar : ClosedStarFace intersect v σ) (x : FiniteSimplex σ) :
    faceInclusion K (insert v σ) (hfull σ hσ hstar)
        (finiteClosedStarConeMap K intersect v hfull t σ hσ hstar x) =
      closedStarInterpolate K intersect v hfull t
        (⟨faceInclusion K σ hσ x, σ, hσ, hstar,
          by intro w hw; simp [faceInclusion, hw]⟩ :
          ClosedStarLocus K intersect v) := by
  apply point_ext_weight K
  funext w
  unfold faceInclusion finiteClosedStarConeMap closedStarInterpolate
  dsimp only [RealizationPoint.weight]
  by_cases hw : w ∈ insert v σ
  · rw [dif_pos hw]
    rfl
  · have hwv : w ≠ v := by
      intro h
      exact hw (h ▸ Finset.mem_insert_self v σ)
    have hws : w ∉ σ := by
      intro h
      exact hw (Finset.mem_insert_of_mem h)
    rw [dif_neg hw]
    simp [coneWeight, hwv, hws]

theorem closedStarConeMap_face_continuous
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (hfull : HasRealizedStarFaces K intersect v)
    (t : ConeTime) (σ : Finset V) (hσ : σ ∈ K.faces)
    (hstar : ClosedStarFace intersect v σ) :
    Continuous (fun x : FiniteSimplex σ =>
      (closedStarInterpolate K intersect v hfull t
        (⟨faceInclusion K σ hσ x, σ, hσ, hstar,
          by intro w hw; simp [faceInclusion, hw]⟩ :
          ClosedStarLocus K intersect v))) := by
  apply Continuous.subtype_mk
  have heq :
      (fun x : FiniteSimplex σ =>
        (closedStarInterpolate K intersect v hfull t
          (⟨faceInclusion K σ hσ x, σ, hσ, hstar,
            by intro w hw; simp [faceInclusion, hw]⟩ :
            ClosedStarLocus K intersect v)).1) =
      faceInclusion K (insert v σ) (hfull σ hσ hstar) ∘
        finiteClosedStarConeMap K intersect v hfull t σ hσ hstar := by
    funext x
    exact (finiteClosedStarConeMap_faceInclusion K intersect v hfull t σ hσ hstar x).symm
  change Continuous (fun x : FiniteSimplex σ =>
    (closedStarInterpolate K intersect v hfull t
      (⟨faceInclusion K σ hσ x, σ, hσ, hstar,
        by intro w hw; simp [faceInclusion, hw]⟩ :
        ClosedStarLocus K intersect v)).1)
  rw [heq]
  exact (faceInclusion_continuous K (insert v σ) (hfull σ hσ hstar)).comp
    (finiteClosedStarConeMap_continuous K intersect v hfull t σ hσ hstar)

private noncomputable def finiteClosedStarConeMapJoint
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (hfull : HasRealizedStarFaces K intersect v)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (hstar : ClosedStarFace intersect v σ) :
    ConeTime × FiniteSimplex σ → FiniteSimplex (insert v σ) :=
  fun p => finiteClosedStarConeMap K intersect v hfull p.1 σ hσ hstar p.2

private theorem finiteClosedStarConeMapJoint_continuous
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (hfull : HasRealizedStarFaces K intersect v)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (hstar : ClosedStarFace intersect v σ) :
    Continuous (finiteClosedStarConeMapJoint K intersect v hfull σ hσ hstar) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro w
  have hw : Continuous (fun p : ConeTime × FiniteSimplex σ =>
      (faceInclusion K σ hσ p.2).weight w.1) := by
    unfold faceInclusion
    by_cases hwσ : (w : V) ∈ σ
    · simp only [dite_eq_left_iff, dif_pos hwσ]
      exact (continuous_apply (⟨w, hwσ⟩ : σ)).comp
        (continuous_subtype_val.comp continuous_snd)
    · simp only [dif_neg hwσ]
      exact continuous_const
  change Continuous (fun p : ConeTime × FiniteSimplex σ =>
    coneWeight K v p.1 (faceInclusion K σ hσ p.2) w.1)
  dsimp [coneWeight]
  have ht : Continuous (fun p : ConeTime × FiniteSimplex σ => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  by_cases hwv : (w : V) = v
  · simp [hwv]
    have hc : Continuous (fun p : ConeTime × FiniteSimplex σ =>
        (1 : ℝ) - (p.1 : ℝ)) := continuous_const.sub ht
    convert (hc.mul hw).add ht using 1
    funext p
    simp [hwv]
  · simp [hwv]
    exact (continuous_const.sub ht).mul hw

theorem closedStarConeMap_face_joint_continuous
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (hfull : HasRealizedStarFaces K intersect v)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (hstar : ClosedStarFace intersect v σ) :
    Continuous (fun p : ConeTime × FiniteSimplex σ =>
      closedStarInterpolate K intersect v hfull p.1
        (⟨faceInclusion K σ hσ p.2, σ, hσ, hstar,
          by intro w hw; simp [faceInclusion, hw]⟩ :
          ClosedStarLocus K intersect v)) := by
  apply Continuous.subtype_mk
  have heq :
      (fun p : ConeTime × FiniteSimplex σ =>
        (closedStarInterpolate K intersect v hfull p.1
          (⟨faceInclusion K σ hσ p.2, σ, hσ, hstar,
            by intro w hw; simp [faceInclusion, hw]⟩ :
            ClosedStarLocus K intersect v)).1) =
      faceInclusion K (insert v σ) (hfull σ hσ hstar) ∘
        finiteClosedStarConeMapJoint K intersect v hfull σ hσ hstar := by
    funext p
    exact (finiteClosedStarConeMap_faceInclusion K intersect v hfull p.1 σ hσ hstar p.2).symm
  change Continuous (fun p : ConeTime × FiniteSimplex σ =>
    (closedStarInterpolate K intersect v hfull p.1
      (⟨faceInclusion K σ hσ p.2, σ, hσ, hstar,
        by intro w hw; simp [faceInclusion, hw]⟩ :
        ClosedStarLocus K intersect v)).1)
  rw [heq]
  exact (faceInclusion_continuous K (insert v σ) (hfull σ hσ hstar)).comp
    (finiteClosedStarConeMapJoint_continuous K intersect v hfull σ hσ hstar)

private theorem closedStarConeMap_isClosedMap_of_continuous
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hcurve : ∀ τ : Finset V, τ ∈ K.faces → CurveFace intersect 1 τ)
    (hface : ∀ τ : Finset V, τ.Nonempty →
      CurveFace intersect 1 τ → τ ∈ K.faces)
    (v : {u : V // separating u})
    (hfull : HasRealizedStarFaces K intersect v)
    (hne : Nonempty (RealizedSeparatingLink K intersect separating v))
    (hf : Continuous (closedStarConeMap K intersect separating v hfull)) :
    IsClosedMap (closedStarConeMap K intersect separating v hfull) := by
  letI := realizationT2Space_here K
  intro C hC
  have hclosedAmbient : IsClosed
      ((fun x : ClosedStarLocus K intersect v => (x : RealizationPoint K)) ''
        (closedStarConeMap K intersect separating v hfull '' C)) := by
    rw [← isOpen_compl_iff]
    change ∀ σ : Finset V, ∀ hσ : σ ∈ K.faces,
      IsOpen ((faceInclusion K σ hσ) ⁻¹'
        (((fun x : ClosedStarLocus K intersect v => (x : RealizationPoint K)) ''
          (closedStarConeMap K intersect separating v hfull '' C))ᶜ))
    intro σ hσ
    have hcompact := isCompact_compactConeFaceBound K intersect separating
      hcurve hface v hne σ hσ
    have hCi : IsCompact (C ∩ compactConeFaceBound K intersect separating v hne σ) :=
      hcompact.inter_left hC
    have hIm : IsClosed
        ((fun x : ClosedStarLocus K intersect v => (x : RealizationPoint K)) ''
          (closedStarConeMap K intersect separating v hfull ''
            (C ∩ compactConeFaceBound K intersect separating v hne σ))) := by
      have hc : Continuous (fun c =>
          ((closedStarConeMap K intersect separating v hfull c :
            ClosedStarLocus K intersect v) : RealizationPoint K)) :=
        continuous_subtype_val.comp hf
      convert (hCi.image hc).isClosed using 1
      ext x
      simp only [Set.mem_image, Set.mem_inter_iff]
      constructor
      · rintro ⟨y, ⟨c, hc, rfl⟩, rfl⟩
        exact ⟨c, hc, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    have heq :
        (faceInclusion K σ hσ) ⁻¹'
          ((fun x : ClosedStarLocus K intersect v => (x : RealizationPoint K)) ''
            (closedStarConeMap K intersect separating v hfull '' C)) =
        (faceInclusion K σ hσ) ⁻¹'
          ((fun x : ClosedStarLocus K intersect v => (x : RealizationPoint K)) ''
            (closedStarConeMap K intersect separating v hfull ''
              (C ∩ compactConeFaceBound K intersect separating v hne σ))) := by
      ext p
      constructor
      · rintro ⟨y, ⟨c, hc, rfl⟩, hcp⟩
        have hsupport : ∀ w ∉ σ,
            (closedStarConeMap K intersect separating v hfull c).1.weight w = 0 := by
          intro w hw
          have heq := congrArg (fun z : RealizationPoint K => z.weight w) hcp
          simpa [faceInclusion, hw] using heq
        have hb := closedStarConeMap_mem_compactConeFaceBound
          K intersect separating v hfull hne σ c hsupport
        exact ⟨_, ⟨c, ⟨hc, hb⟩, rfl⟩, hcp⟩
      · rintro ⟨y, ⟨c, hc, rfl⟩, hcp⟩
        exact ⟨_, ⟨c, hc.1, rfl⟩, hcp⟩
    rw [Set.preimage_compl, heq]
    exact (hIm.preimage (faceInclusion_continuous K σ hσ)).isOpen_compl
  have hclosed := hclosedAmbient.preimage
    (continuous_subtype_val : Continuous
      (fun x : ClosedStarLocus K intersect v => (x : RealizationPoint K)))
  have heq :
      (fun x : ClosedStarLocus K intersect v => (x : RealizationPoint K)) ⁻¹'
        ((fun x : ClosedStarLocus K intersect v => (x : RealizationPoint K)) ''
          (closedStarConeMap K intersect separating v hfull '' C)) =
      closedStarConeMap K intersect separating v hfull '' C := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have h : y = x := Subtype.ext hxy
      simpa [h] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [heq] at hclosed
  exact hclosed

private theorem closedStarConeMap_joint_continuous
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hface : ∀ σ : Finset V, σ.Nonempty →
      CurveFace intersect 1 σ → σ ∈ K.faces)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u})
    (hfull : HasRealizedStarFaces K intersect v) :
    Continuous (fun p : ConeTime ×
      RealizedSeparatingLink K intersect separating v =>
      closedStarInterpolate K intersect v hfull p.1
        ⟨p.2.1, p.2.property.1⟩) := by
  have hq := realizedLinkFaceCoverMap_isQuotientMap K intersect
    separating hsep v hcurve hface
  apply hq.continuous_lift_prod_right
  have h : Continuous (fun p :
      (Σ i : FiniteLinkFaceIndex K intersect v, FiniteSimplex i.1) ×
        ConeTime =>
      closedStarInterpolate K intersect v hfull p.2
        ⟨(realizedLinkFaceCoverMap K intersect separating hsep v p.1).1,
          (realizedLinkFaceCoverMap K intersect separating hsep v p.1).property.1⟩) := by
    let g : (Σ i : FiniteLinkFaceIndex K intersect v,
        FiniteSimplex i.1 × ConeTime) → ClosedStarLocus K intersect v :=
      fun p => closedStarInterpolate K intersect v hfull p.2.2
        ⟨(finiteLinkFaceMap K intersect separating hsep v
          p.1.1 p.1.2.1 p.1.2.2 p.2.1).1,
          (finiteLinkFaceMap K intersect separating hsep v
          p.1.1 p.1.2.1 p.1.2.2 p.2.1).property.1⟩
    have hg : Continuous g := continuous_sigma_iff.mpr (by
      intro i
      change Continuous (fun p : FiniteSimplex i.1 × ConeTime =>
        closedStarInterpolate K intersect v hfull p.2
          ⟨(finiteLinkFaceMap K intersect separating hsep v
            i.1 i.2.1 i.2.2 p.1).1,
            (finiteLinkFaceMap K intersect separating hsep v
            i.1 i.2.1 i.2.2 p.1).property.1⟩)
      convert (closedStarConeMap_face_joint_continuous K intersect v hfull
        i.1 i.2.1 i.2.2.2).comp continuous_swap using 1
      funext p
      apply Subtype.ext
      rfl)
    exact hg.comp (Homeomorph.sigmaProdDistrib (Y := ConeTime)).continuous
  exact h.comp continuous_swap

private theorem closedStarConeMap_continuous
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hface : ∀ σ : Finset V, σ.Nonempty →
      CurveFace intersect 1 σ → σ ∈ K.faces)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u})
    (hfull : HasRealizedStarFaces K intersect v) :
    Continuous (closedStarConeMap K intersect separating v hfull) := by
  apply (topologicalConeMk_quotient
    (X := RealizedSeparatingLink K intersect separating v)).continuous_iff.mpr
  simpa only [Function.comp_def, closedStarConeMap_mk] using
    closedStarConeMap_joint_continuous K intersect separating
      hcurve hface hsep v hfull

/-- The explicit cone chart is a quotient map for the full face realization.
The hypotheses ensure that the star and its link inherit the intended weak
subcomplex topologies. -/
theorem closedStarConeMap_isQuotientMap
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hcurve : ∀ (tau : Finset V), tau ∈ K.faces → CurveFace intersect 1 tau)
    (hface : ∀ (tau : Finset V), tau.Nonempty →
      CurveFace intersect 1 tau → tau ∈ K.faces)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u})
    (hfull : HasRealizedStarFaces K intersect v)
    (hne : Nonempty (RealizedSeparatingLink K intersect separating v)) :
    Topology.IsQuotientMap
      (closedStarConeMap K intersect separating v hfull) := by
  have hf := closedStarConeMap_continuous K intersect separating
    hcurve hface hsep v hfull
  have hclosed := closedStarConeMap_isClosedMap_of_continuous K intersect
    separating hcurve hface v hfull hne hf
  exact hclosed.isQuotientMap hf
    (closedStarConeMap_surjective K intersect separating hsep v hfull hne)

end CurveComplexGenusTwo.Topology
