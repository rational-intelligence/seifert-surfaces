import CurveComplexGenusTwo.Topology.FirstReturnCorner.CornerChartProducer

namespace CurveComplex
open Set Topology Schoenflies

/-- Localize the actual corner square in any prescribed open neighborhood.
The construction restricts and positively rescales the proved chart, so the
actual two axes and positive corner germ remain exact. -/
theorem source_first_return_corner_square_in_open
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i k : Bool)
    (W : Set S) (hW : IsOpen W) (hpW : (if k then D.finish else D.start) ∈ W) :
    let p := if k then D.finish else D.start
    ∃ F : OpenPartialHomeomorph S Plane,
      p ∈ F.source ∧ F p = 0 ∧ F.source ⊆ W ∧
      Plane.closedSquare 0 1 ⊆ F.target ∧
      Disjoint F.source (source_surgery_retained_crossings B i) ∧
      (∀ x ∈ F.source, x ∈ a.image ↔ F x 0 = 0) ∧
      (∀ x ∈ F.source, x ∈ b.image ↔ F x 1 = 0) ∧
      (∀ x ∈ F.source, x ∈ (B.boundary i).image ↔
        (F x 0 = 0 ∧ 0 ≤ F x 1) ∨ (0 ≤ F x 0 ∧ F x 1 = 0)) := by
  let p := if k then D.finish else D.start
  obtain ⟨E,hpE,hEp,hqE,hsq,hER,ha,hb,hbr⟩ :=
    source_first_return_corner_square S D B ht i k
  let R := E.restr W
  have hRs : R.source = E.source ∩ W := by simp [R,hW.interior_eq]
  let L : Plane ≃ₜ (ℝ × ℝ) := {
    toEquiv := {
      toFun := fun z => (z 0,z 1)
      invFun := fun z => Plane.mk z.1 z.2
      left_inv := by intro z; ext j; fin_cases j <;> rfl
      right_inv := by intro z; apply Prod.ext <;> rfl }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let H := R.trans L.toOpenPartialHomeomorph
  have hHs : H.source = R.source := by simp [H]
  have hpH : p ∈ H.source := by rw [hHs,hRs]; exact ⟨hpE,hpW⟩
  have hHp : H p = (0,0) := by change (E p 0,E p 1) = (0,0); rw [hEp]; rfl
  obtain ⟨F,δ,hδ,hFs,hFsq,hFp,hcoords⟩ := source_crossing_chart_unit_square H p hpH hHp
  have hFsource : F.source = E.source ∩ W := hFs.trans (hHs.trans hRs)
  have hc0 (x : S) : F x 0 = E x 0/δ := (hcoords x).1
  have hc1 (x : S) : F x 1 = E x 1/δ := (hcoords x).2
  have hz0 (x : S) : F x 0 = 0 ↔ E x 0 = 0 := by rw [hc0]; simp [ne_of_gt hδ]
  have hz1 (x : S) : F x 1 = 0 ↔ E x 1 = 0 := by rw [hc1]; simp [ne_of_gt hδ]
  have hn0 (x : S) : 0 ≤ F x 0 ↔ 0 ≤ E x 0 := by rw [hc0,le_div_iff₀ hδ,zero_mul]
  have hn1 (x : S) : 0 ≤ F x 1 ↔ 0 ≤ E x 1 := by rw [hc1,le_div_iff₀ hδ,zero_mul]
  refine ⟨F,hFs.symm ▸ hpH,hFp,?_,hFsq,?_,?_,?_,?_⟩
  · exact fun _ hx => ((hFsource).le hx).2
  · exact hER.mono_left (fun _ hx => ((hFsource).le hx).1)
  · intro x hx; rw [hz0]; exact ha x ((hFsource).le hx).1
  · intro x hx; rw [hz1]; exact hb x ((hFsource).le hx).1
  · intro x hx
    rw [hz0,hz1,hn0,hn1]
    exact hbr x ((hFsource).le hx).1

/-- Produce the TWO actual corner repair charts with disjoint ambient sources.
Their locations and local boundary germs are constructed, not supplied. -/
theorem source_first_return_disjoint_corner_squares
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool) :
    ∃ E : Bool → OpenPartialHomeomorph S Plane,
      (∀ k, (if k then D.finish else D.start) ∈ (E k).source ∧
        E k (if k then D.finish else D.start) = 0) ∧
      (∀ k, Plane.closedSquare 0 1 ⊆ (E k).target) ∧
      (∀ k l, k ≠ l → Disjoint (E k).source (E l).source) ∧
      (∀ k, Disjoint (E k).source (source_surgery_retained_crossings B i)) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ a.image ↔ E k x 0 = 0)) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ b.image ↔ E k x 1 = 0)) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ (B.boundary i).image ↔
        (E k x 0 = 0 ∧ 0 ≤ E k x 1) ∨ (0 ≤ E k x 0 ∧ E k x 1 = 0))) := by
  classical
  obtain ⟨U,V,hU,hV,hstart,hfinish,hUV⟩ := t2_separation D.distinct
  let W : Bool → Set S := fun k => if k then V else U
  have hW (k : Bool) : IsOpen (W k) := by cases k <;> assumption
  have hpW (k : Bool) : (if k then D.finish else D.start) ∈ W k := by cases k <;> assumption
  choose E hpE hE0 hEW hsquare hER ha hb hbranch using fun k =>
    source_first_return_corner_square_in_open S D B ht i k (W k) (hW k) (hpW k)
  refine ⟨E,(fun k => ⟨hpE k,hE0 k⟩),hsquare,?_,hER,ha,hb,hbranch⟩
  intro k l hkl
  apply Disjoint.mono (hEW k) (hEW l)
  cases k <;> cases l
  · exact (hkl rfl).elim
  · exact hUV
  · exact hUV.symm
  · exact (hkl rfl).elim

end CurveComplex
#print axioms CurveComplex.source_first_return_corner_square_in_open
#print axioms CurveComplex.source_first_return_disjoint_corner_squares
