import CurveComplexGenusTwo.Topology.ThetaRetention.ActualSourceSurgeryBranches

namespace CurveComplex

/-- The old target crossings on one retained closing arc, excluding the two
common surgery corners. This is not the intersection set of the raw boundary,
which still shares the whole return arc with the target. -/
def source_surgery_retained_crossings
    {S : Type} [TopologicalSpace S] {a b : Curve S}
    {D : SourceFirstReturnBoundary a b} (B : SourceTwoSurgeryBranches D) (i : Bool) : Set S :=
  (Set.range (B.closing i) ∩ a.image) \ {D.start,D.finish}

theorem source_surgery_retained_crossings_partition
    {S : Type} [TopologicalSpace S] {a b : Curve S}
    {D : SourceFirstReturnBoundary a b} (B : SourceTwoSurgeryBranches D) :
    source_surgery_retained_crossings B false ∪ source_surgery_retained_crossings B true =
      (a.image ∩ b.image) \ {D.start,D.finish} := by
  ext z
  simp only [source_surgery_retained_crossings,Set.mem_union,Set.mem_inter_iff,Set.mem_sdiff]
  have hcover : (z ∈ Set.range (B.closing false) ∨ z ∈ Set.range (B.closing true)) ↔
      z ∈ b.image := by
    change z ∈ Set.range (B.closing false) ∪ Set.range (B.closing true) ↔ _
    rw [B.closing_cover]
  tauto

theorem source_surgery_retained_crossings_disjoint
    {S : Type} [TopologicalSpace S] {a b : Curve S}
    {D : SourceFirstReturnBoundary a b} (B : SourceTwoSurgeryBranches D) :
    Disjoint (source_surgery_retained_crossings B false)
      (source_surgery_retained_crossings B true) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨⟨hz0,hza⟩,hn⟩ ⟨⟨hz1,hza'⟩,hn'⟩
  apply hn
  have hmeet : z ∈ Set.range (B.closing false) ∩ Set.range (B.closing true) := ⟨hz0,hz1⟩
  rwa [B.closing_inter] at hmeet

/-- The two actual retained crossing sets partition exactly all old crossings
other than the two corners; their finite cardinalities therefore add exactly. -/
theorem source_surgery_retained_crossings_exact_count
    {S : Type} [TopologicalSpace S] {a b : Curve S}
    {D : SourceFirstReturnBoundary a b} (B : SourceTwoSurgeryBranches D)
    (ht : Transverse a b) :
    (source_surgery_retained_crossings B false).ncard +
      (source_surgery_retained_crossings B true).ncard + 2 =
      (a.image ∩ b.image).ncard := by
  have hfin (i : Bool) : (source_surgery_retained_crossings B i).Finite :=
    (source_surgery_closing_crossings_budget D B ht i).1
  have hunion := Set.ncard_union_eq (source_surgery_retained_crossings_disjoint B)
    (hfin false) (hfin true)
  rw [source_surgery_retained_crossings_partition B] at hunion
  have hP : ({D.start,D.finish} : Set S) ⊆ a.image ∩ b.image := by
    intro x hx
    rcases hx with hx | hx
    · exact hx ▸ D.start_mem
    · exact (Set.mem_singleton_iff.mp hx) ▸ D.finish_mem
  have hcount := Set.ncard_sdiff_add_ncard (a.image ∩ b.image)
    ({D.start,D.finish} : Set S) ht.1 (by simp)
  rw [Set.union_eq_self_of_subset_right hP,Set.ncard_pair D.distinct] at hcount
  omega

/-- One of the two produced closing arcs retains at most half the old
crossings after deleting the two corners. The side is selected from the
actual finite crossing counts, not supplied as an assumption. -/
theorem source_surgery_short_closing_side
    {S : Type} [TopologicalSpace S] {a b : Curve S}
    {D : SourceFirstReturnBoundary a b} (B : SourceTwoSurgeryBranches D)
    (ht : Transverse a b) :
    ∃ i : Bool,
      2 * (source_surgery_retained_crossings B i).ncard + 2 ≤
        (a.image ∩ b.image).ncard := by
  have hsum := source_surgery_retained_crossings_exact_count B ht
  rcases le_total (source_surgery_retained_crossings B false).ncard
    (source_surgery_retained_crossings B true).ncard with h | h
  · exact ⟨false,by omega⟩
  · exact ⟨true,by omega⟩

end CurveComplex

#print axioms CurveComplex.source_surgery_retained_crossings_partition
#print axioms CurveComplex.source_surgery_retained_crossings_disjoint
#print axioms CurveComplex.source_surgery_retained_crossings_exact_count
#print axioms CurveComplex.source_surgery_short_closing_side
