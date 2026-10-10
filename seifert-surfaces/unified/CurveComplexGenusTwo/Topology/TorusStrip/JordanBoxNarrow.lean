import CurveComplexGenusTwo.Topology.TorusStrip.PlaneNarrowBox
import CurveComplexGenusTwo.Topology.TorusStrip.JordanCoordinateUpper
import CurveComplexGenusTwo.Topology.CompletedJordan
import Mathlib

open Set Schoenflies Bornology

/-! Boundary-to-closure bounds for a Jordan inside region.  These are the
analytic boundary route needed before the short-box lattice separation lemma:
the coordinate bounds are assumed only on the Jordan boundary and propagated
to the closure of the bounded component. -/

theorem jordan_coordinate_lower_bound
    {C : Set Plane} (hC : IsJordanCurve C) (i : Fin 2) (B : ℝ)
    (hB : ∀ z ∈ C, B ≤ z i) :
    ∀ z ∈ closure (inside C), B ≤ z i := by
  have hsep := jordan_curve_theorem hC
  let H : Set Plane := {z | z i < B}
  let p : Plane := Plane.mk (if i = 0 then B - 1 else 0) (if i = 1 then B - 1 else 0)
  have hn : H.Nonempty := by
    refine ⟨p, ?_⟩
    change p i < B
    fin_cases i
    · simp [p]
    · simp [p]
  have hc : IsConnected H := by
    apply Convex.isConnected _ hn
    exact (convex_Iio B).is_linear_preimage (EuclideanSpace.proj i).isLinear
  have hnb : ¬ IsBounded H := by
    intro hb
    obtain ⟨M,hM⟩ := (hb.isCompact_closure.image (EuclideanSpace.proj i).continuous).bddBelow
    let z : Plane := Plane.mk (if i = 0 then min M B - 1 else 0) (if i = 1 then min M B - 1 else 0)
    have hz : z ∈ H := by
      change z i < B
      fin_cases i
      · simp [z]
        exact lt_of_lt_of_le (sub_lt_self _ zero_lt_one) (min_le_right M B)
      · simp [z]
        exact lt_of_lt_of_le (sub_lt_self _ zero_lt_one) (min_le_right M B)
    have hm : M ≤ z i := hM ⟨z, subset_closure hz, rfl⟩
    fin_cases i
    · simp [z] at hm
      have hMlt : min M B - 1 < M :=
        lt_of_lt_of_le (sub_lt_self _ zero_lt_one) (min_le_left M B)
      linarith
    · simp [z] at hm
      have hMlt : min M B - 1 < M :=
        lt_of_lt_of_le (sub_lt_self _ zero_lt_one) (min_le_left M B)
      linarith
  have hcomp : H ⊆ Cᶜ := by
    intro z hz hzc
    exact not_lt_of_ge (hB z hzc) hz
  have hout : H ⊆ outside C := by
    have hr : H ⊆ inside C ∪ outside C := by
      rw [inside_union_outside]
      exact hcomp
    rcases hc.isPreconnected.subset_or_subset hsep.isOpen_inside hsep.isOpen_outside
      disjoint_inside_outside hr with h | h
    · exact False.elim (hnb (hsep.isBounded_inside.subset h))
    · exact h
  have hin : inside C ⊆ {z : Plane | B ≤ z i} := by
    intro z hz
    by_contra hh
    have hzH : z ∈ H := by
      change ¬ B ≤ z i at hh
      change z i < B
      exact lt_of_not_ge hh
    exact disjoint_left.1 disjoint_inside_outside hz (hout hzH)
  have hclosed : IsClosed {z : Plane | B ≤ z i} :=
    isClosed_le continuous_const (EuclideanSpace.proj i).continuous
  exact closure_minimal hin hclosed

theorem jordan_closed_inside_box
    {C : Set Plane} (hC : IsJordanCurve C) (a b w h : ℝ)
    (hboundary : ∀ z ∈ C,
      a ≤ z 0 ∧ z 0 ≤ a+w ∧ b ≤ z 1 ∧ z 1 ≤ b+h) :
    ∀ z ∈ closure (inside C),
      a ≤ z 0 ∧ z 0 ≤ a+w ∧ b ≤ z 1 ∧ z 1 ≤ b+h := by
  intro z hz
  have hlow0 := jordan_coordinate_lower_bound hC 0 a
    (fun y hy => (hboundary y hy).1) z hz
  have hupp0 := jordan_coordinate_upper_bound hC 0 (a+w)
    (fun y hy => (hboundary y hy).2.1) z hz
  have hlow1 := jordan_coordinate_lower_bound hC 1 b
    (fun y hy => (hboundary y hy).2.2.1) z hz
  have hupp1 := jordan_coordinate_upper_bound hC 1 (b+h)
    (fun y hy => (hboundary y hy).2.2.2) z hz
  exact ⟨hlow0, hupp0, hlow1, hupp1⟩

/-- Direct consumer: a Jordan region whose boundary lies in a rectangle of
widths below the deck period has pairwise-disjoint nonzero lattice translates. -/
theorem jordan_inside_box_lattice_disjoint
    (C : Set Plane) (T a b w h : ℝ) (hC : IsJordanCurve C)
    (hT : 0 < T) (hw : w < T) (hh : h < T)
    (hboundary : ∀ z ∈ C,
      a ≤ z 0 ∧ z 0 ≤ a+w ∧ b ≤ z 1 ∧ z 1 ≤ b+h) :
    ∀ v : ℤ × ℤ, v ≠ 0 → Disjoint (closure (inside C))
      ((fun z : Plane => z + Plane.mk ((v.1 : ℝ) * T) ((v.2 : ℝ) * T)) ''
        closure (inside C)) := by
  apply plane_narrow_box_lattice_disjoint (closure (inside C)) T a b w h hT hw hh
  exact jordan_closed_inside_box hC a b w h hboundary

#print axioms jordan_coordinate_lower_bound
#print axioms jordan_closed_inside_box
#print axioms jordan_inside_box_lattice_disjoint
