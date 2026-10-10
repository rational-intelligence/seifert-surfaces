import CurveComplexGenusTwo.Topology.CompletedJordan
import Mathlib
open Set Schoenflies Bornology

/-- Jordan inside closure inherits any coordinate upper bound already true on
its boundary. This is the separation fact needed to turn a narrow boundary
bigon into a narrow closed support region. -/
theorem jordan_coordinate_upper_bound
    {C : Set Plane} (hC : IsJordanCurve C) (i : Fin 2) (B : ℝ)
    (hB : ∀ z ∈ C, z i ≤ B) :
    ∀ z ∈ closure (inside C), z i ≤ B := by
  have hsep := jordan_curve_theorem hC
  let H : Set Plane := {z | B < z i}
  let p : Plane := Plane.mk (if i = 0 then B + 1 else 0) (if i = 1 then B + 1 else 0)
  have hn : H.Nonempty := by
    refine ⟨p, ?_⟩
    change B < p i
    fin_cases i <;> simp [p]
  have hc : IsConnected H := by
    apply Convex.isConnected _ hn
    exact (convex_Ioi B).is_linear_preimage (EuclideanSpace.proj i).isLinear
  have hnb : ¬ IsBounded H := by
    intro hb
    obtain ⟨M,hM⟩ := (hb.isCompact_closure.image (EuclideanSpace.proj i).continuous).bddAbove
    let z : Plane := Plane.mk (if i = 0 then max M B + 1 else 0) (if i = 1 then max M B + 1 else 0)
    have hz : z ∈ H := by
      change B < z i
      fin_cases i <;> simp [z] <;>
        exact lt_of_le_of_lt (le_max_right M B) (lt_add_one _)
    have hm : z i ≤ M := hM ⟨z,subset_closure hz,rfl⟩
    fin_cases i
    · simp [z] at hm
      have hMlt : M < max M B + 1 :=
        lt_of_le_of_lt (le_max_left M B) (lt_add_one _)
      linarith
    · simp [z] at hm
      have hMlt : M < max M B + 1 :=
        lt_of_le_of_lt (le_max_left M B) (lt_add_one _)
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
  have hin : inside C ⊆ {z : Plane | z i ≤ B} := by
    intro z hz
    by_contra hh
    have hzH : z ∈ H := by
      change ¬ z i ≤ B at hh
      change B < z i
      exact lt_of_not_ge hh
    exact disjoint_left.1 disjoint_inside_outside hz (hout hzH)
  have hclosed : IsClosed {z : Plane | z i ≤ B} :=
    isClosed_le (EuclideanSpace.proj i).continuous continuous_const
  exact closure_minimal hin hclosed

#print axioms jordan_coordinate_upper_bound
