import CurveComplexGenusTwo.Topology.ThetaRetention.ActualSourceSurgeryBranches

namespace CurveComplex
open Set Topology

/-- At an actual transverse crossing, construct a compact embedded bypass in
one quadrant. Its intersections with the two original curves are exactly its
opposite endpoints; its interior avoids both curves and the crossing itself. -/
theorem source_transverse_corner_bypass
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} {p : S} (hp : CrossesAt a b p) :
    ∃ f : C(Interval,S),
      IsEmbedding f ∧ f 0 ≠ f 1 ∧
      Set.range f ∩ a.image = {f 1} ∧
      Set.range f ∩ b.image = {f 0} ∧
      p ∉ Set.range f ∧
      ∀ t : Interval, t ≠ 0 → t ≠ 1 →
        f t ∉ a.image ∧ f t ∉ b.image := by
  obtain ⟨U,V,hpU,e,hU,hV,hep,haxes⟩ := hp
  have hzero : (0 : ℝ × ℝ) ∈ V := by
    change (0,0) ∈ V
    rw [← hep]
    exact (e ⟨p,hpU⟩).property
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 hzero
  let ε : ℝ := r / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεr : ε < r := by dsimp [ε]; linarith
  let z : Interval → ℝ × ℝ := fun t => (ε*(1-(t:ℝ)),ε*(t:ℝ))
  have hzV (t : Interval) : z t ∈ V := by
    apply hrV
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [Prod.fst_zero,Prod.snd_zero,sub_zero]
    dsimp [z]
    rw [abs_of_nonneg (mul_nonneg hε.le (sub_nonneg.mpr t.property.2)),
      abs_of_nonneg (mul_nonneg hε.le t.property.1)]
    exact max_lt (by nlinarith [t.property.1]) (by nlinarith [t.property.2])
  let zv : Interval → V := fun t => ⟨z t,hzV t⟩
  have hzc : Continuous z := by dsimp [z]; fun_prop
  have hzvc : Continuous zv := hzc.subtype_mk _
  let f : C(Interval,S) :=
    ⟨fun t => (e.symm (zv t) : S),
      continuous_subtype_val.comp (e.symm.continuous.comp hzvc)⟩
  have hcoord (t : Interval) :
      (e ⟨f t,(e.symm (zv t)).property⟩ : ℝ × ℝ) = z t := by
    exact congrArg Subtype.val (e.apply_symm_apply (zv t))
  have hinj : Function.Injective f := by
    intro t u he
    have heU : e.symm (zv t) = e.symm (zv u) := Subtype.ext he
    have heV := e.symm.injective heU
    have hey := congrArg (fun w : V => (w:ℝ × ℝ).2) heV
    apply Subtype.ext
    exact mul_left_cancel₀ (ne_of_gt hε) hey
  have ha (t : Interval) : f t ∈ a.image ↔ t = 1 := by
    rw [(haxes (f t) (e.symm (zv t)).property).1,hcoord]
    change ε*(1-(t:ℝ)) = 0 ↔ t = 1
    constructor
    · intro ht
      apply Subtype.ext
      change (t : ℝ) = 1
      have := (mul_eq_zero.mp ht).resolve_left (ne_of_gt hε)
      linarith
    · rintro rfl
      norm_num
  have hb (t : Interval) : f t ∈ b.image ↔ t = 0 := by
    rw [(haxes (f t) (e.symm (zv t)).property).2,hcoord]
    change ε*(t:ℝ) = 0 ↔ t = 0
    constructor
    · intro ht
      exact Subtype.ext ((mul_eq_zero.mp ht).resolve_left (ne_of_gt hε))
    · rintro rfl
      norm_num
  refine ⟨f,(f.continuous.isClosedEmbedding hinj).isEmbedding,?_,?_,?_,?_,?_⟩
  · intro he
    have := congrArg Subtype.val (hinj he)
    norm_num at this
  · ext x
    constructor
    · rintro ⟨⟨t,rfl⟩,ht⟩
      rw [ha] at ht
      simp [ht]
    · rintro rfl
      exact ⟨Set.mem_range_self _,(ha 1).mpr rfl⟩
  · ext x
    constructor
    · rintro ⟨⟨t,rfl⟩,ht⟩
      rw [hb] at ht
      simp [ht]
    · rintro rfl
      exact ⟨Set.mem_range_self _,(hb 0).mpr rfl⟩
  · rintro ⟨t,ht⟩
    have htU : (⟨f t,(e.symm (zv t)).property⟩ : U) = ⟨p,hpU⟩ := Subtype.ext ht
    have htcoord : z t = (0 : ℝ × ℝ) := by
      change z t = (0,0)
      rw [← hcoord,htU,hep]
    have hx := congrArg Prod.fst htcoord
    have hy := congrArg Prod.snd htcoord
    dsimp [z] at hx hy
    have ht0 := (mul_eq_zero.mp hy).resolve_left (ne_of_gt hε)
    rw [ht0] at hx
    simp only [sub_zero,mul_one] at hx
    exact (ne_of_gt hε) hx
  · intro t ht0 ht1
    exact ⟨fun h => ht1 ((ha t).mp h), fun h => ht0 ((hb t).mp h)⟩

end CurveComplex

#print axioms CurveComplex.source_transverse_corner_bypass
