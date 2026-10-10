import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualBigonShortness
import Mathlib.Analysis.Convex.PathConnected

open Set Topology Schoenflies Metric

/-- At an actual vertical boundary segment of a Jordan disk lying to the
right of the fiber, the entire sufficiently small right half-ball is interior.
This is derived from the Jordan frontier and connected half-ball, not from a
supplied local interior certificate. -/
theorem jordan_straight_fiber_right_halfball_inside
    (C : Set Plane) (hC : IsJordanCurve C) (q : Plane) (hq : q∈C)
    (c ρ : ℝ) (_hqc : q 0=c) (hρ : 0<ρ)
    (hside : ∀ z∈C, c≤z 0)
    (hlocal : ∀ z∈ball q ρ, z∈C → z 0=c) :
    ball q ρ ∩ {z : Plane | c<z 0} ⊆ inside C := by
  let H := ball q ρ ∩ {z : Plane | c<z 0}
  have hc := jordan_curve_theorem hC
  have hconn : IsPreconnected H := by
    apply Convex.isPreconnected
    exact (convex_ball q ρ).inter
      ((convex_Ioi c).is_linear_preimage (EuclideanSpace.proj 0).isLinear)
  have hdis : H⊆Cᶜ := by
    intro z hz hzC
    exact (ne_of_lt hz.2).symm (hlocal z hz.1 hzC)
  have hpart : H⊆inside C ∪ outside C := by
    rw [inside_union_outside]
    exact hdis
  have hqcl : q∈closure (inside C) :=
    frontier_subset_closure (hc.frontier_inside.symm ▸ hq)
  obtain ⟨z,⟨hzball,hzin⟩⟩ :=
    (_root_.mem_closure_iff.mp hqcl) (ball q ρ) isOpen_ball (mem_ball_self hρ)
  have hzlower : c≤z 0 := jordan_coordinate_lower_bound hC 0 c hside z (subset_closure hzin)
  have hzneq : z 0≠c := jordan_inside_avoids_supporting_vertical_fiber C hC c (Or.inr hside) z hzin
  have hzH : z∈H := ⟨hzball,lt_of_le_of_ne hzlower (Ne.symm hzneq)⟩
  exact hconn.subset_left_of_subset_union hc.isOpen_inside hc.isOpen_outside
    disjoint_inside_outside hpart ⟨z,hzH,hzin⟩

/-- The analogous left half-ball belongs to the actual left-sided Jordan disk. -/
theorem jordan_straight_fiber_left_halfball_inside
    (C : Set Plane) (hC : IsJordanCurve C) (q : Plane) (hq : q∈C)
    (c ρ : ℝ) (_hqc : q 0=c) (hρ : 0<ρ)
    (hside : ∀ z∈C, z 0≤c)
    (hlocal : ∀ z∈ball q ρ, z∈C → z 0=c) :
    ball q ρ ∩ {z : Plane | z 0<c} ⊆ inside C := by
  let H := ball q ρ ∩ {z : Plane | z 0<c}
  have hc := jordan_curve_theorem hC
  have hconn : IsPreconnected H := by
    apply Convex.isPreconnected
    exact (convex_ball q ρ).inter
      ((convex_Iio c).is_linear_preimage (EuclideanSpace.proj 0).isLinear)
  have hdis : H⊆Cᶜ := by
    intro z hz hzC
    exact (ne_of_lt hz.2) (hlocal z hz.1 hzC)
  have hpart : H⊆inside C ∪ outside C := by
    rw [inside_union_outside]
    exact hdis
  have hqcl : q∈closure (inside C) :=
    frontier_subset_closure (hc.frontier_inside.symm ▸ hq)
  obtain ⟨z,⟨hzball,hzin⟩⟩ :=
    (_root_.mem_closure_iff.mp hqcl) (ball q ρ) isOpen_ball (mem_ball_self hρ)
  have hzupper : z 0≤c := jordan_coordinate_upper_bound hC 0 c hside z (subset_closure hzin)
  have hzneq : z 0≠c := jordan_inside_avoids_supporting_vertical_fiber C hC c (Or.inl hside) z hzin
  have hzH : z∈H := ⟨hzball,lt_of_le_of_ne hzupper hzneq⟩
  exact hconn.subset_left_of_subset_union hc.isOpen_inside hc.isOpen_outside
    disjoint_inside_outside hpart ⟨z,hzH,hzin⟩

#print axioms jordan_straight_fiber_right_halfball_inside
#print axioms jordan_straight_fiber_left_halfball_inside
