import CurveComplexGenusTwo.Topology.ActualFareyClassification.MinimumAllGridBigon

open Set Topology Schoenflies

/-- Avoidance of the supporting and its adjacent grid fibers places the
actual closed Jordan disk in one of the two adjacent closed lattice slabs. -/
theorem grid_free_jordan_boundary_in_adjacent_slab
    (C : Set Plane) (hC : IsJordanCurve C) (c T : ℝ) (hT : 0<T)
    (p : Plane) (hp : p∈C) (hpc : p 0=c)
    (hno : ∀ z∈inside C, z 0≠c ∧ z 0≠c-T ∧ z 0≠c+T) :
    (∀ z∈C, c-T≤z 0 ∧ z 0≤c) ∨ (∀ z∈C, c≤z 0 ∧ z 0≤c+T) := by
  let f : Plane → ℝ := fun z => z 0
  have hf : Continuous f := by fun_prop
  have hc := jordan_curve_theorem hC
  let S := f '' inside C
  have hs : IsPreconnected S := hc.isConnected_inside.isPreconnected.image f hf.continuousOn
  have part (d : ℝ) (hd : ∀ z∈inside C, z 0≠d) :
      S⊆Iio d ∨ S⊆Ioi d := by
    apply hs.subset_or_subset isOpen_Iio isOpen_Ioi (disjoint_left.mpr (by intro x hx hy; exact lt_asymm (show x<d from hx) (show d<x from hy)))
    rintro x ⟨z,hz,rfl⟩
    exact lt_or_gt_of_ne (hd z hz)
  have hpcl : p∈closure (inside C) :=
    frontier_subset_closure (hc.frontier_inside.symm ▸ hp)
  have closedBound (d : ℝ) (hd : S⊆Iio d) : ∀ z∈C, z 0≤d := by
    have hi : inside C⊆f ⁻¹' Iic d := by
      intro z hz
      exact le_of_lt (show f z<d from hd ⟨z,hz,rfl⟩)
    have hcl := (isClosed_Iic.preimage hf).closure_subset_iff.mpr hi
    intro z hz
    exact hcl (frontier_subset_closure (hc.frontier_inside.symm ▸ hz))
  have closedLower (d : ℝ) (hd : S⊆Ioi d) : ∀ z∈C, d≤z 0 := by
    have hi : inside C⊆f ⁻¹' Ici d := by
      intro z hz
      exact le_of_lt (show d<f z from hd ⟨z,hz,rfl⟩)
    have hcl := (isClosed_Ici.preimage hf).closure_subset_iff.mpr hi
    intro z hz
    exact hcl (frontier_subset_closure (hc.frontier_inside.symm ▸ hz))
  rcases part c (fun z hz => (hno z hz).1) with hl|hr
  · left
    rcases part (c-T) (fun z hz => (hno z hz).2.1) with hll|hlr
    · have hh := closedBound (c-T) hll p hp
      rw [hpc] at hh
      linarith
    · exact fun z hz => ⟨closedLower (c-T) hlr z hz,closedBound c hl z hz⟩
  · right
    rcases part (c+T) (fun z hz => (hno z hz).2.2) with hrl|hrr
    · exact fun z hz => ⟨closedLower c hr z hz,closedBound (c+T) hrl z hz⟩
    · have hh := closedLower (c+T) hrr p hp
      rw [hpc] at hh
      linarith

#print axioms grid_free_jordan_boundary_in_adjacent_slab
