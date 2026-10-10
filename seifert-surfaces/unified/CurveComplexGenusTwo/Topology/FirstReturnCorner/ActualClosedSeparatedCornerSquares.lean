import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualLocalizedCornerSquare
namespace CurveComplex
open Set Topology Schoenflies
/-- Produce actual corner charts whose CLOSED ambient supports remain
separated from each other and from all retained crossings. -/
theorem source_first_return_closed_separated_corner_squares
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool) :
    ∃ E : Bool → OpenPartialHomeomorph S Plane,
      (∀ k, (if k then D.finish else D.start) ∈ (E k).source ∧
        E k (if k then D.finish else D.start)=0) ∧
      (∀ k, Plane.closedSquare 0 1 ⊆ (E k).target) ∧
      Disjoint (closure (E false).source) (closure (E true).source) ∧
      (∀ k, Disjoint (closure (E k).source) (source_surgery_retained_crossings B i)) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ a.image ↔ E k x 0=0)) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ b.image ↔ E k x 1=0)) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ (B.boundary i).image ↔
        (E k x 0=0 ∧ 0≤E k x 1) ∨ (0≤E k x 0 ∧ E k x 1=0))) := by
  classical
  obtain ⟨A,hpA,hsquareA,hdisA,hAR,haA,hbA,hbranchA⟩ :=
    source_first_return_disjoint_corner_squares S D B ht i
  have hex (k : Bool) : ∃ W : Set S, IsOpen W ∧
      (if k then D.finish else D.start) ∈ W ∧ closure W ⊆ (A k).source := by
    obtain ⟨W,hW,hpW,hclW⟩ := normal_exists_closure_subset
      (isClosed_singleton : IsClosed ({if k then D.finish else D.start} : Set S))
      (A k).open_source (Set.singleton_subset_iff.mpr (hpA k).1)
    exact ⟨W,hW,hpW (Set.mem_singleton _),hclW⟩
  choose W hW hpW hclW using hex
  choose E hpE hE0 hEW hsquare hER ha hb hbranch using fun k =>
    source_first_return_corner_square_in_open S D B ht i k (W k) (hW k) (hpW k)
  have hclosed (k : Bool) : closure (E k).source ⊆ (A k).source :=
    (closure_mono (hEW k)).trans (hclW k)
  exact ⟨E,(fun k => ⟨hpE k,hE0 k⟩),hsquare,
    (hdisA false true (by decide)).mono (hclosed false) (hclosed true),
    (fun k => (hAR k).mono_left (hclosed k)),ha,hb,hbranch⟩
end CurveComplex
#print axioms CurveComplex.source_first_return_closed_separated_corner_squares
