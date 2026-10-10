import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualSourceCrossingStrip
import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualSourceSurgeryCrossingPartition

namespace CurveComplex
open Set Topology

/-- Construct one actual count-preserving strip at every retained old crossing.
The strips are mutually disjoint and avoid the whole first-return arc. Every
transverse track has precisely one target intersection and every nonzero
track avoids the current curve. No strip family or crossing budget is assumed. -/
theorem source_retained_crossing_strips
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool) :
    ∃ E : ↥(source_surgery_retained_crossings B i) →
        Interval × Set.Icc (-1:ℝ) 1 → S,
      (∀ p, IsEmbedding (E p)) ∧
      (∀ p, E p (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩) = p.val) ∧
      (∀ p q, p ≠ q → Disjoint (Set.range (E p)) (Set.range (E q))) ∧
      (∀ p, Disjoint (Set.range (E p)) (Set.range D.first)) ∧
      (∀ p z, E p z ∈ a.image ↔ z.1 = (⟨1/2,by norm_num⟩ : Interval)) ∧
      (∀ p z, E p z ∈ b.image ↔ (z.2:ℝ) = 0) ∧
      ∀ p (w : Set.Icc (-1:ℝ) 1),
        Set.range (fun t : Interval => E p (t,w)) ∩ a.image =
          {E p (⟨1/2,by norm_num⟩,w)} := by
  classical
  let R := source_surgery_retained_crossings B i
  have hRfin : R.Finite :=
    (source_surgery_closing_crossings_budget D B ht i).1
  have hclosing (x : S) (hx : x ∈ Set.range (B.closing i)) : x ∈ b.image := by
    rw [← B.closing_cover]
    cases i
    · exact Or.inl hx
    · exact Or.inr hx
  have hRold (p : R) : p.val ∈ a.image ∩ b.image :=
    ⟨p.property.1.2,hclosing _ p.property.1.1⟩
  have hRfirst (p : R) : p.val ∉ Set.range D.first := by
    rintro ⟨t,htp⟩
    by_cases ht0 : t = 0
    · apply p.property.2
      left
      exact htp.symm.trans (ht0 ▸ D.first_zero)
    by_cases ht1 : t = 1
    · apply p.property.2
      right
      exact htp.symm.trans (ht1 ▸ D.first_one)
    exact D.first_interior_avoids t ht0 ht1 (htp.symm ▸ (hRold p).2)
  obtain ⟨N,hN,hNdis⟩ := hRfin.t2_separation
  let U : R → Set S := fun p => N p.val ∩ (Set.range D.first)ᶜ
  have hU (p : R) : IsOpen (U p) :=
    (hN p.val).2.inter (isCompact_range D.first.continuous).isClosed.isOpen_compl
  have hpU (p : R) : p.val ∈ U p := ⟨(hN p.val).1,hRfirst p⟩
  have hproduce (p : R) : ∃ F : Interval × Set.Icc (-1:ℝ) 1 → S,
      IsEmbedding F ∧ Set.range F ⊆ U p ∧
      F (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩) = p.val ∧
      (∀ z, F z ∈ a.image ↔ z.1 = (⟨1/2,by norm_num⟩ : Interval)) ∧
      (∀ z, F z ∈ b.image ↔ (z.2:ℝ) = 0) ∧
      ∀ w : Set.Icc (-1:ℝ) 1,
        Set.range (fun t : Interval => F (t,w)) ∩ a.image =
          {F (⟨1/2,by norm_num⟩,w)} :=
    source_transverse_crossing_strip_in_open (ht.2 p.val (hRold p)) (U p) (hU p) (hpU p)
  choose E hE hEU hcenter ha hb hcount using hproduce
  refine ⟨E,hE,hcenter,?_,?_,ha,hb,hcount⟩
  · intro p q hpq
    apply (hNdis p.property q.property (fun he => hpq (Subtype.ext he))).mono
    · intro x hx
      exact (hEU p hx).1
    · intro x hx
      exact (hEU q hx).1
  · intro p
    rw [Set.disjoint_left]
    intro x hxE hxf
    exact (hEU p hxE).2 hxf

end CurveComplex

#print axioms CurveComplex.source_retained_crossing_strips
