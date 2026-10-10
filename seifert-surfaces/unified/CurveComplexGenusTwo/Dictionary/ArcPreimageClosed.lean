import CurveComplexGenusTwo.Foundations.Definitions
import CurveComplexGenusTwo.Dictionary.MarkedSphere
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Convex.Contractible
open Filter Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)
theorem exists_markedArc_lift (a : MarkedArc M) :
    ∃ γ : C(Interval, E), ∀ t, M.cover.projection (γ t) = a.map t := by
  classical
  let q := M.cover
  have endpoint (w : E) (hw : q.projection w ∈ q.branch)
      (l : Filter Interval) (f : Interval → E)
      (hf : Tendsto (fun t => q.projection (f t)) l (𝓝 (q.projection w))) :
      Tendsto f l (𝓝 w) := by
      let c := q.branch_chart w hw
      have hc : Tendsto (fun t => c.downstairs (q.projection (f t))) l (𝓝 0) := by
        simpa only [c.downstairs_center, Function.comp_def] using
          (c.downstairs.continuousAt c.downstairs_mem).tendsto.comp hf
      have hr : Tendsto (fun t => Complex.sqrt (c.downstairs (q.projection (f t)))) l (𝓝 0) := by
        have hnorm (z : ℂ) : ‖Complex.sqrt z‖ = Real.sqrt ‖z‖ := by
          have hs : ‖Complex.sqrt z‖ ^ 2 = ‖z‖ := by
            rw [← norm_pow]
            congr 1
            exact Complex.cpow_nat_inv_pow _ (by decide : (2 : ℕ) ≠ 0)
          rw [← hs, Real.sqrt_sq (norm_nonneg _)]
        apply tendsto_zero_iff_norm_tendsto_zero.mpr
        have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hc.norm
        simpa only [Function.comp_def, hnorm, norm_zero, Real.sqrt_zero] using hn
      have hzero : (0 : ℂ) ∈ c.upstairs.target := by
        simpa only [c.upstairs_center] using c.upstairs.map_source c.upstairs_mem
      let g : Interval → E := fun t => c.upstairs.symm (Complex.sqrt (c.downstairs (q.projection (f t))))
      have hg : Tendsto g l (𝓝 w) := by
        have hi : c.upstairs.symm 0 = w := by
          rw [← c.upstairs_center, c.upstairs.left_inv c.upstairs_mem]
        simpa only [hi, Function.comp_def, g] using (c.upstairs.continuousAt_symm hzero).tendsto.comp hr
      have htarget : ∀ᶠ t in l, Complex.sqrt (c.downstairs (q.projection (f t))) ∈ c.upstairs.target :=
        hr.eventually (c.upstairs.open_target.mem_nhds hzero)
      have hbase : ∀ᶠ t in l, q.projection (f t) ∈ c.downstairs.source :=
        hf.eventually (c.downstairs.open_source.mem_nhds c.downstairs_mem)
      have hproj : ∀ᶠ t in l, q.projection (g t) = q.projection (f t) := by
        filter_upwards [htarget, hbase] with t ht hb
        have hu : g t ∈ c.upstairs.source := c.upstairs.map_target ht
        apply c.downstairs.injOn (c.image_mem _ hu) hb
        rw [c.square _ hu]
        change (c.upstairs (c.upstairs.symm _)) ^ 2 = _
        rw [c.upstairs.right_inv ht]
        exact Complex.cpow_nat_inv_pow _ (by decide : (2 : ℕ) ≠ 0)
      have hd : Tendsto (fun t => q.deck (g t)) l (𝓝 w) := by
        simpa only [(q.fixed_iff_branch w).2 hw, Function.comp_def] using q.deck.continuous.continuousAt.tendsto.comp hg
      rw [tendsto_def] at hg hd ⊢
      intro U hU
      filter_upwards [hg U hU, hd U hU, hproj] with t ht hdt hp
      rcases (q.fiber_pair (g t) (f t)).1 hp with h | h
      · change f t ∈ U
        rw [h]
        exact ht
      · change f t ∈ U
        rw [h]
        exact hdt
  let J := Set.Ioo (0 : ℝ) 1
  letI : ContractibleSpace J := (convex_Ioo (0 : ℝ) 1).contractibleSpace
    ⟨(1 / 2 : ℝ), by norm_num⟩
  letI : LocallyPathConnectedSpace J := isOpen_Ioo.locallyPathConnectedSpace
  let k : J → Interval := fun t => ⟨t.val, le_of_lt t.property.1, le_of_lt t.property.2⟩
  have hk : Continuous k := by fun_prop
  have hunmarked (t : J) : a.map (k t) ∉ q.branch := by
    intro h
    rcases a.marked_only_at_ends (k t) h with h | h
    · have he := congrArg Subtype.val h
      change t.val = 0 at he
      linarith [t.property.1]
    · have he := congrArg Subtype.val h
      change t.val = 1 at he
      linarith [t.property.2]
  let b : C(J, q.unramifiedBase) :=
    ⟨fun t => ⟨a.map (k t), hunmarked t⟩, (a.continuous.comp hk).subtype_mk _⟩
  let t₀ : J := ⟨1 / 2, by norm_num [J]⟩
  obtain ⟨e, he⟩ := q.projection_surjective (a.map (k t₀))
  let e₀ : q.unramifiedTotal := ⟨e, by
    change q.projection e ∉ q.branch
    rw [he]
    exact hunmarked t₀⟩
  obtain ⟨F, hF, _⟩ := q.unramified_isCoveringMap.existsUnique_continuousMap_lifts b t₀ e₀
    (by apply Subtype.ext; exact he)
  have hFlift (t : J) : q.projection (F t).val = a.map (k t) := by
    exact congrArg Subtype.val (congrFun hF.2 t)
  let γ : Interval → E := fun t =>
    if h : (0 : ℝ) < t.val ∧ t.val < 1 then (F ⟨t.val, h⟩).val
    else (q.projection_surjective (a.map t)).choose
  have hγ (t : Interval) : q.projection (γ t) = a.map t := by
    dsimp [γ]
    split_ifs with ht
    · exact hFlift ⟨t.val, ht⟩
    · exact (q.projection_surjective (a.map t)).choose_spec
  have hγcont : Continuous γ := by
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : (0 : ℝ) < t.val ∧ t.val < 1
    · let K : Set Interval := {t | (0 : ℝ) < t.val ∧ t.val < 1}
      have hK : IsOpen K := isOpen_Ioo.preimage continuous_subtype_val
      have hc : ContinuousOn γ K := by
        rw [continuousOn_iff_continuous_restrict]
        have hfun : (K.domRestrict γ) = fun u : K => (F ⟨u.val.val, u.property⟩).val := by
          funext u
          exact dif_pos u.property
        rw [hfun]
        exact continuous_subtype_val.comp (F.continuous.comp
          ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))
      exact hc.continuousAt (hK.mem_nhds ht)
    · have hend : t = ⟨0, by norm_num⟩ ∨ t = ⟨1, by norm_num⟩ := by
        have hb := t.property
        rcases le_or_gt t.val 0 with hz | hz
        · left
          apply Subtype.ext
          exact le_antisymm hz hb.1
        · right
          apply Subtype.ext
          exact le_antisymm hb.2 (not_lt.mp (fun ho => ht ⟨hz, ho⟩))
      have hb : q.projection (γ t) ∈ q.branch := by
        rw [hγ]
        rcases hend with rfl | rfl
        · exact a.start_marked
        · exact a.end_marked
      apply endpoint (γ t) hb (𝓝 t) γ
      simpa only [hγ] using a.continuous.continuousAt (x := t).tendsto
  exact ⟨⟨γ, hγcont⟩, hγ⟩
end CurveComplex.HyperellipticModel

namespace CurveComplex
open Set Topology
private theorem loop_collision {X : Type*} [TopologicalSpace X]
    (f g : C(Interval, X))
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hinter : ∀ s t : Interval, f s = g t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    let p : Path (f 0) (f 1) := ⟨f, rfl, rfl⟩
    let q : Path (f 0) (f 1) := ⟨g, h0.symm, h1.symm⟩
    ∀ s t, (p.trans q.symm) s = (p.trans q.symm) t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  dsimp only
  intro s t h
  simp only [Path.trans_apply, Path.symm_apply] at h
  split_ifs at h with hs ht ht
  · left
    have he := congrArg Subtype.val (hf h)
    apply Subtype.ext
    dsimp at he
    linarith
  · have he := hinter _ _ h
    rcases he with ⟨hs0, ht0⟩ | ⟨hs1, ht1⟩
    · right; left
      constructor <;> apply Subtype.ext
      · change (s : ℝ) = 0
        have := congrArg Subtype.val hs0; dsimp at this; linarith
      · change (t : ℝ) = 1
        have := congrArg Subtype.val ht0; simp only [unitInterval.coe_symm_eq] at this; dsimp at this; linarith
    · exfalso
      have := congrArg Subtype.val ht1
      simp only [unitInterval.coe_symm_eq] at this
      dsimp at this
      linarith
  · have he := hinter _ _ h.symm
    rcases he with ⟨ht0, hs0⟩ | ⟨ht1, hs1⟩
    · right; right
      constructor <;> apply Subtype.ext
      · change (s : ℝ) = 1
        have := congrArg Subtype.val hs0; simp only [unitInterval.coe_symm_eq] at this; dsimp at this; linarith
      · change (t : ℝ) = 0
        have := congrArg Subtype.val ht0; dsimp at this; linarith
    · exfalso
      have := congrArg Subtype.val hs1
      simp only [unitInterval.coe_symm_eq] at this
      dsimp at this
      linarith
  · left
    have he := congrArg Subtype.val (hg h)
    apply Subtype.ext
    simp only [unitInterval.coe_symm_eq] at he
    linarith

private theorem exists_curve_of_loop {X : Type*} [TopologicalSpace X] [T2Space X]
    (l : C(Interval, X)) (hend : l 0 = l 1)
    (hcoll : ∀ s t, l s = l t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    ∃ c : Curve X, c.image = Set.range l := by
  let r := AddCircle.EndpointIdent (1 : ℝ) 0
  let j : Icc (0 : ℝ) (0 + 1) → Interval := fun t => ⟨t.val, by simpa using t.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hrespect : ∀ a b, r a b → l (j a) = l (j b) := by
    rintro a b ⟨⟩
    simpa [j] using hend
  let L : Quot r → X := Quot.lift (fun t => l (j t)) hrespect
  have hL : Continuous L := continuous_quot_lift _ (l.continuous.comp hj)
  have hLi : Function.Injective L := by
    intro a b
    induction a using Quot.inductionOn with | h a =>
      induction b using Quot.inductionOn with | h b =>
        intro hab
        rcases hcoll (j a) (j b) hab with he | ⟨ha, hb⟩ | ⟨ha, hb⟩
        · apply congrArg (Quot.mk r)
          exact Subtype.ext (congrArg (fun t : Interval => t.val) he)
        · have ha' : a = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) ha)
          have hb' : b = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) hb)
          subst a; subst b
          exact Quot.sound AddCircle.EndpointIdent.mk
        · have ha' : a = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) ha)
          have hb' : b = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) hb)
          subst a; subst b
          exact (Quot.sound AddCircle.EndpointIdent.mk).symm
  let e : Circle ≃ₜ Quot r :=
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.trans
      (AddCircle.homeoIccQuot (1 : ℝ) 0)
  let c : Curve X := ⟨L ∘ e, ((hL.comp e.continuous).isClosedEmbedding (hLi.comp e.injective)).isEmbedding⟩
  refine ⟨c, ?_⟩
  change range (L ∘ e) = range l
  rw [e.surjective.range_comp]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quot.inductionOn with | h t =>
      exact ⟨j t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Quot.mk r ⟨t.val, by simpa using t.property⟩, rfl⟩

/-- Two embedded interval arcs with common corresponding endpoints and no other
intersection form an embedded circle whose image is their union. -/
theorem exists_curve_of_two_arcs {X : Type*} [TopologicalSpace X] [T2Space X]
    (f g : C(Interval, X))
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hinter : ∀ s t : Interval, f s = g t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    ∃ c : Curve X, c.image = Set.range f ∪ Set.range g := by
  let p : Path (f 0) (f 1) := ⟨f, rfl, rfl⟩
  let q : Path (f 0) (f 1) := ⟨g, h0.symm, h1.symm⟩
  obtain ⟨c, hc⟩ := exists_curve_of_loop (p.trans q.symm).toContinuousMap
    (by simp) (loop_collision f g hf hg h0 h1 hinter)
  refine ⟨c, hc.trans ?_⟩
  change Set.range (p.trans q.symm) = Set.range f ∪ Set.range g
  rw [Path.trans_range, Path.symm_range]
  rfl
#print axioms exists_curve_of_two_arcs
end CurveComplex

namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)

theorem nonloop_preimage_two_arcs (a : NonLoopArc M) :
    ∃ γ : C(Interval, E),
      Topology.IsEmbedding γ ∧
      (∀ t, M.cover.projection (γ t) = a.val.map t) ∧
      Set.range γ ∪ Set.range (fun t => M.cover.deck (γ t)) =
        M.cover.projection ⁻¹' a.image ∧
      Set.range γ ∩ Set.range (fun t => M.cover.deck (γ t)) =
        {γ ⟨0, by norm_num⟩, γ ⟨1, by norm_num⟩} := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  obtain ⟨γ, hγ⟩ := M.exists_markedArc_lift a.val
  have hi : Function.Injective γ := by
    intro s t h
    apply a.injective
    rw [← hγ s, ← hγ t, h]
  have hfix0 : M.cover.deck (γ 0) = γ 0 :=
    (M.cover.fixed_iff_branch _).mpr (by rw [hγ]; exact a.val.start_marked)
  have hfix1 : M.cover.deck (γ 1) = γ 1 :=
    (M.cover.fixed_iff_branch _).mpr (by rw [hγ]; exact a.val.end_marked)
  refine ⟨γ, (γ.continuous.isClosedEmbedding hi).isEmbedding, hγ, ?_, ?_⟩
  · ext x
    constructor
    · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · exact ⟨t, (hγ t).symm⟩
      · exact ⟨t, ((M.cover.projection_deck _).trans (hγ t)).symm⟩
    · rintro ⟨t, ht⟩
      rcases (M.cover.fiber_pair (γ t) x).mp ((hγ t).trans ht) with hx | hx
      · exact Or.inl ⟨t, hx.symm⟩
      · exact Or.inr ⟨t, hx.symm⟩
  · ext x
    constructor
    · rintro ⟨⟨s, rfl⟩, t, ht⟩
      have hst : s = t := a.injective (by
        rw [← hγ s, ← hγ t, ← ht, M.cover.projection_deck])
      subst t
      have hb := (M.cover.fixed_iff_branch (γ s)).mp ht
      rw [hγ] at hb
      rcases a.val.marked_only_at_ends s hb with hs | hs
      · simp [hs]
      · simp [hs]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨⟨0, rfl⟩, ⟨0, hfix0⟩⟩
      · exact ⟨⟨1, rfl⟩, ⟨1, hfix1⟩⟩

theorem nonloop_arc_preimage_curve (a : NonLoopArc M) :
    ∃ c : Curve E, c.image = M.cover.projection ⁻¹' a.image := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  obtain ⟨γ, hγemb, hγ, hunion, hinter⟩ := M.nonloop_preimage_two_arcs a
  let δ : C(Interval, E) := ⟨fun t => M.cover.deck (γ t),
    M.cover.deck.continuous.comp γ.continuous⟩
  have hδi : Function.Injective δ := M.cover.deck.injective.comp hγemb.injective
  have h0 : γ 0 = δ 0 :=
    ((M.cover.fixed_iff_branch _).mpr (by rw [hγ]; exact a.val.start_marked)).symm
  have h1 : γ 1 = δ 1 :=
    ((M.cover.fixed_iff_branch _).mpr (by rw [hγ]; exact a.val.end_marked)).symm
  have hcross : ∀ s t : Interval, γ s = δ t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t h
    have hx : γ s ∈ Set.range γ ∩ Set.range (fun t => M.cover.deck (γ t)) :=
      ⟨⟨s, rfl⟩, ⟨t, h.symm⟩⟩
    rw [hinter] at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · exact Or.inl ⟨hγemb.injective hx, hδi (h.symm.trans (hx.trans h0))⟩
    · exact Or.inr ⟨hγemb.injective hx, hδi (h.symm.trans (hx.trans h1))⟩
  obtain ⟨c, hc⟩ := CurveComplex.exists_curve_of_two_arcs γ δ
    hγemb.injective hδi h0 h1 hcross
  exact ⟨c, hc.trans hunion⟩
end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.nonloop_arc_preimage_curve
