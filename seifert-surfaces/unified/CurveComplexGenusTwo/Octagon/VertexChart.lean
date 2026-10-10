import CurveComplexGenusTwo.Foundations.OctagonQuotient

namespace CurveComplex.Octagon

/-! The cyclic combinatorics of the eight sectors at the unique quotient vertex. -/

/-- Crossing the outgoing side at vertex `i` leads to the vertex at the far end
of its paired side. This is the successor sector in the quotient vertex star. -/
def vertexSuccessor (i : Side) : Side := next (pair i)

/-- Explicit cyclic numbering of the eight source sectors. -/
def vertexCycle : Fin 8 → Side
  | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1
  | 4 => 4 | 5 => 7 | 6 => 6 | _ => 5

theorem vertexCycle_bijective : Function.Bijective vertexCycle := by
  decide

theorem vertexCycle_next (k : Fin 8) :
    vertexCycle (next k) = vertexSuccessor (vertexCycle k) := by
  fin_cases k <;> decide

theorem vertexSuccessor_cycle (i : Side) :
    ∃! k : Fin 8, vertexCycle k = i := by
  obtain ⟨k, hk⟩ := vertexCycle_bijective.2 i
  refine ⟨k, hk, ?_⟩
  intro j hj
  exact vertexCycle_bijective.1 (hj.trans hk.symm)

theorem vertexSuccessor_glue (i : Side) :
    mk (vertexPoint i) = mk (vertexPoint (vertexSuccessor i)) := by
  exact vertex_pair_start i

theorem vertexCycle_glue (k : Fin 8) :
    mk (vertexPoint (vertexCycle k)) =
      mk (vertexPoint (vertexCycle (next k))) := by
  rw [vertexCycle_next]
  exact vertexSuccessor_glue _

/-- The outgoing ray of sector `i` is paired with the incoming ray of its
successor; the parameter is reversed on the paired polygon side. -/
theorem vertex_seam_pairing (i : Side) (t : unitInterval) :
    mk (side i t) = mk (side (pair i) (unitInterval.symm t)) :=
  side_pairing i t

/-- The quotient has exactly the prescribed two representatives on a seam
away from its endpoints. -/
theorem vertex_seam_exact_fiber (i : Side) (t : unitInterval)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    mk ⁻¹' ({mk (side i t)} : Set Surface) =
      {side i t, side (pair i) (unitInterval.symm t)} := by
  exact edge_interior_fiber_eq_pair i t ht0 ht1

/-! A geometric parameter rectangle centered at each source polygon vertex.
The first coordinate is radial depth, and the second spans half of each
adjacent polygon side. -/

noncomputable def radialSector (i : Side) (r t : unitInterval) : Disk :=
  ⟨(1 - (r : ℝ)) •
      (Circle.exp (2 * Real.pi * ((i.val : ℝ) + (t : ℝ) - 1 / 2) / 8) : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Circle.norm_coe, mul_one,
      Real.norm_eq_abs, abs_of_nonneg]
    · have hr0 : (0 : ℝ) ≤ r := r.property.1
      linarith
    · have hr1 : (r : ℝ) ≤ 1 := r.property.2
      linarith⟩

theorem continuous_radialSector (i : Side) :
    Continuous (fun p : unitInterval × unitInterval => radialSector i p.1 p.2) := by
  apply Continuous.subtype_mk
  have ha : Continuous (fun p : unitInterval × unitInterval =>
      2 * Real.pi * ((i.val : ℝ) + (p.2 : ℝ) - 1 / 2) / 8) := by
    fun_prop
  have hr : Continuous (fun p : unitInterval × unitInterval => (1 - (p.1 : ℝ))) := by
    fun_prop
  exact hr.smul (continuous_subtype_val.comp (Circle.exp.continuous.comp ha))

theorem radialSector_center (i : Side) :
    radialSector i 0 (⟨1 / 2, by constructor <;> norm_num⟩ : unitInterval) =
      vertexPoint i := by
  apply Subtype.ext
  simp [radialSector, vertexPoint, side]

theorem radialSector_boundary_norm (i : Side) (t : unitInterval) :
    ‖(radialSector i 0 t : ℂ)‖ = 1 := by
  change ‖(1 - (0 : ℝ)) •
      (Circle.exp (2 * Real.pi * ((i.val : ℝ) + (t : ℝ) - 1 / 2) / 8) : ℂ)‖ = 1
  rw [norm_smul, Circle.norm_coe]
  norm_num

theorem radialSector_interior_norm (i : Side) (r t : unitInterval)
    (hr : r ≠ 0) : ‖(radialSector i r t : ℂ)‖ < 1 := by
  have hrne : (r : ℝ) ≠ 0 := by
    intro h
    exact hr (Subtype.ext h)
  have hr0 : (0 : ℝ) < r := lt_of_le_of_ne r.property.1 (Ne.symm hrne)
  have hr1 : (r : ℝ) ≤ 1 := r.property.2
  change ‖(1 - (r : ℝ)) •
      (Circle.exp (2 * Real.pi * ((i.val : ℝ) + (t : ℝ) - 1 / 2) / 8) : ℂ)‖ < 1
  have hnonneg : (0 : ℝ) ≤ 1 - r := by linarith
  rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  linarith

theorem radialSector_center_quotient (i : Side) :
    mk (radialSector i 0 (⟨1 / 2, by constructor <;> norm_num⟩ : unitInterval)) =
      mk (vertexPoint 0) := by
  rw [radialSector_center]
  exact all_geometric_vertices_equal i 0

end CurveComplex.Octagon
