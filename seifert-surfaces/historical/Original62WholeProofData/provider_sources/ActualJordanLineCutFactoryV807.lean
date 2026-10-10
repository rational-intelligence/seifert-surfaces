import ActualJordanClosedCrosscutTilingV806

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology
open Schoenflies
noncomputable section
namespace CompressionActualJordanLineCutFactoryV807

/-- A full first-hit chord and both exact closed cells are derived for an
    arbitrary Jordan domain. No polygonal access to prescribed boundary
    points, crosscut certificate, or annular coverage assumption is supplied. -/
theorem jordan_line_cut_factory
    {C : Set Plane} (hC : IsJordanCurve C)
    (a b y : Plane) (hab : a ≠ b) (hy : y ∈ Plane.line a b ∩ inside C) :
    ∃ p q : Plane,p ≠ q ∧ p ∈ Plane.line a b ∧ q ∈ Plane.line a b ∧
      p ∈ C ∧ q ∈ C ∧
      connectedComponentIn (Plane.line a b ∩ inside C) y = openSegment ℝ p q ∧
      closure (connectedComponentIn (Plane.line a b ∩ inside C) y) = segment ℝ p q ∧
      ∃ A₁ A₂ : Set Plane,IsCutPair C p q A₁ A₂ ∧
        IsJordanCurve (A₁ ∪ segment ℝ p q) ∧ IsJordanCurve (A₂ ∪ segment ℝ p q) ∧
        closure (inside (A₁ ∪ segment ℝ p q)) ∪
          closure (inside (A₂ ∪ segment ℝ p q)) = closure (inside C) ∧
        closure (inside (A₁ ∪ segment ℝ p q)) ∩
          closure (inside (A₂ ∪ segment ℝ p q)) = segment ℝ p q ∧
        closure (inside (A₁ ∪ segment ℝ p q)) ∩ C = A₁ ∧
        closure (inside (A₂ ∪ segment ℝ p q)) ∩ C = A₂ := by
  have hsep := jordan_curve_theorem hC
  obtain ⟨p,q,hpq,hpℓ,hqℓ,hcomp,hclos,hpfr,hqfr⟩ :=
    Plane.exists_openSegment_eq_connectedComponentIn hab hsep.isOpen_inside
      hsep.isBounded_inside hy
  have hpC : p ∈ C := hsep.frontier_inside ▸ hpfr
  have hqC : q ∈ C := hsep.frontier_inside ▸ hqfr
  have hseg : segment ℝ p q \ {p,q} ⊆ inside C := by
    intro x hx
    have hxp : x ≠ p := by intro he; exact hx.2 (by simp [he])
    have hxq : x ≠ q := by intro he; exact hx.2 (by simp [he])
    have hxopen : x ∈ openSegment ℝ p q := mem_openSegment_of_ne_left_right hxp.symm hxq.symm hx.1
    exact (connectedComponentIn_subset _ _ (hcomp.symm ▸ hxopen)).2
  let cut : IsCrosscut C (segment ℝ p q) p q := {
    curve := hC
    arc := isArcBetween_segment hpq
    polygonal := isPolygonal_segment p q
    left_mem := hpC
    right_mem := hqC
    sdiff_subset := hseg }
  obtain ⟨A₁,A₂,hcut⟩ := exists_isCutPair hC hpC hqC hpq
  have hcollars := hasArcCollars_segment hpq hsep.isOpen_inside
    (fun hp => inside_subset_compl hp hpC) (fun hq => inside_subset_compl hq hqC) hseg
  exact ⟨p,q,hpq,hpℓ,hqℓ,hpC,hqC,hcomp,hclos,A₁,A₂,hcut,
    CompressionActualJordanClosedCrosscutTilingV806.closed_crosscut_tiling cut hcut hcollars⟩

#print axioms jordan_line_cut_factory
end CompressionActualJordanLineCutFactoryV807
