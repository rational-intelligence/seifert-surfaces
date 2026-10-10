import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualSourceCornerBypass

namespace CurveComplex
open Set Topology

/-- At an arbitrary actual transverse crossing, construct a whole local strip.
Each transverse track has exactly one target crossing, and every nonzero track
avoids the current curve. The center crossing remains the specified point. -/
theorem source_transverse_crossing_strip_in_open
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} {p : S} (hp : CrossesAt a b p)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ E : Interval × Set.Icc (-1:ℝ) 1 → S,
      IsEmbedding E ∧ Set.range E ⊆ W ∧
      E (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩) = p ∧
      (∀ z, E z ∈ a.image ↔ z.1 = (⟨1/2,by norm_num⟩ : Interval)) ∧
      (∀ z, E z ∈ b.image ↔ (z.2:ℝ) = 0) ∧
      ∀ w : Set.Icc (-1:ℝ) 1,
        Set.range (fun t : Interval => E (t,w)) ∩ a.image =
          {E (⟨1/2,by norm_num⟩,w)} := by
  obtain ⟨U,V,hpU,e,hU,hV,hep,haxes⟩ := hp
  have hzero : (0 : ℝ × ℝ) ∈ V := by
    change (0,0) ∈ V
    rw [← hep]
    exact (e ⟨p,hpU⟩).property
  let T : Set U := {u | (u:S) ∈ W}
  have hT : IsOpen T := hW.preimage continuous_subtype_val
  let V0 : Set (ℝ × ℝ) := Subtype.val '' (e '' T)
  have hV0 : IsOpen V0 := hV.isOpenMap_subtype_val _ (e.isOpenMap T hT)
  have hzV0 : (0 : ℝ × ℝ) ∈ V0 :=
    ⟨e ⟨p,hpU⟩,⟨⟨p,hpU⟩,hpW,rfl⟩,hep⟩
  obtain ⟨r,hr,hrV0⟩ := Metric.isOpen_iff.mp hV0 0 hzV0
  have hV0V : V0 ⊆ V := by
    rintro x ⟨y,hy,rfl⟩
    exact y.property
  have hrV : Metric.ball 0 r ⊆ V := hrV0.trans hV0V
  let δ : ℝ := r / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδr : δ < r := by dsimp [δ]; linarith
  let z : Interval × Set.Icc (-1:ℝ) 1 → ℝ × ℝ :=
    fun v => (δ*(2*(v.1:ℝ)-1),δ*(v.2:ℝ))
  have hzV (v) : z v ∈ V := by
    apply hrV
    rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    simp only [Prod.fst_zero,Prod.snd_zero,sub_zero]
    dsimp [z]
    rw [abs_mul,abs_mul,abs_of_pos hδ]
    apply max_lt
    · have ha : |2*(v.1:ℝ)-1| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [v.1.property.1,v.1.property.2]
      exact lt_of_le_of_lt (by nlinarith) hδr
    · have ha : |(v.2:ℝ)| ≤ 1 := abs_le.mpr v.2.property
      exact lt_of_le_of_lt (by nlinarith) hδr
  let zv : Interval × Set.Icc (-1:ℝ) 1 → V := fun v => ⟨z v,hzV v⟩
  have hzc : Continuous z := by dsimp [z]; fun_prop
  have hzvc : Continuous zv := hzc.subtype_mk _
  let E : Interval × Set.Icc (-1:ℝ) 1 → S := fun v => (e.symm (zv v) : S)
  have hEc : Continuous E :=
    continuous_subtype_val.comp (e.symm.continuous.comp hzvc)
  have hEW : Set.range E ⊆ W := by
    rintro x ⟨v,rfl⟩
    have hv0 : z v ∈ V0 := hrV0 (by
      rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
      simp only [Prod.fst_zero,Prod.snd_zero,sub_zero]
      dsimp [z]
      rw [abs_mul,abs_mul,abs_of_pos hδ]
      apply max_lt
      · have ha : |2*(v.1:ℝ)-1| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [v.1.property.1,v.1.property.2]
        exact lt_of_le_of_lt (by nlinarith) hδr
      · have ha : |(v.2:ℝ)| ≤ 1 := abs_le.mpr v.2.property
        exact lt_of_le_of_lt (by nlinarith) hδr)
    obtain ⟨y,⟨u,hu,heu⟩,hy⟩ := hv0
    have hyz : y = zv v := Subtype.ext hy
    have heuz : e u = zv v := heu.trans hyz
    change (e.symm (zv v) : S) ∈ W
    rw [← heuz,e.symm_apply_apply]
    exact hu
  have hcoord (v) :
      (e ⟨E v,(e.symm (zv v)).property⟩ : ℝ × ℝ) = z v :=
    congrArg Subtype.val (e.apply_symm_apply (zv v))
  have hEi : Function.Injective E := by
    intro v w he
    have heU : e.symm (zv v) = e.symm (zv w) := Subtype.ext he
    have heV := e.symm.injective heU
    have hx := congrArg (fun q : V => (q:ℝ × ℝ).1) heV
    have hy := congrArg (fun q : V => (q:ℝ × ℝ).2) heV
    have hx' := mul_left_cancel₀ (ne_of_gt hδ) hx
    have hy' := mul_left_cancel₀ (ne_of_gt hδ) hy
    apply Prod.ext
    · apply Subtype.ext
      linarith
    · exact Subtype.ext hy'
  have ha (v) : E v ∈ a.image ↔ v.1 = (⟨1/2,by norm_num⟩ : Interval) := by
    rw [(haxes (E v) (e.symm (zv v)).property).1,hcoord]
    change δ*(2*(v.1:ℝ)-1) = 0 ↔ v.1 = _
    constructor
    · intro h
      apply Subtype.ext
      change (v.1:ℝ) = 1/2
      have hh := (mul_eq_zero.mp h).resolve_left (ne_of_gt hδ)
      linarith
    · intro h
      rw [h]
      norm_num
  have hb (v) : E v ∈ b.image ↔ (v.2:ℝ) = 0 := by
    rw [(haxes (E v) (e.symm (zv v)).property).2,hcoord]
    change δ*(v.2:ℝ) = 0 ↔ (v.2:ℝ) = 0
    exact mul_eq_zero.trans (or_iff_right (ne_of_gt hδ))
  refine ⟨E,(hEc.isClosedEmbedding hEi).isEmbedding,hEW,?_,ha,hb,?_⟩
  · have hz0 : zv (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩) = e ⟨p,hpU⟩ := by
      apply Subtype.ext
      rw [hep]
      norm_num [zv,z]
    change (e.symm _ : S) = p
    rw [hz0,e.symm_apply_apply]
  · intro w
    ext x
    constructor
    · rintro ⟨⟨t,rfl⟩,ht⟩
      have ht' := (ha (t,w)).mp ht
      change t = (⟨1/2,by norm_num⟩ : Interval) at ht'
      exact Set.mem_singleton_iff.mpr (congrArg (fun t => E (t,w)) ht')
    · rintro rfl
      exact ⟨Set.mem_range_self _,(ha _).mpr rfl⟩

end CurveComplex

#print axioms CurveComplex.source_transverse_crossing_strip_in_open
