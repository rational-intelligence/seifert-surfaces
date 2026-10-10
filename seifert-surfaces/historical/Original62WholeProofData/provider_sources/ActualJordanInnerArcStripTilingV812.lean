import ActualJordanCutPairArcUniquenessV811

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology
open Schoenflies
noncomputable section
namespace CompressionActualJordanInnerArcStripTilingV812

/-- Cutting an outer cell along the inner boundary arc gives the inner
    closed cell and a genuine second Jordan disk. Identify the entire
    inner chord among the boundary arcs before using the crosscut tiling. -/
theorem inner_arc_strip_tiling
    {J A P : Set Plane} {p q : Plane}
    (h : IsCrosscut J A p q) (hP : IsArcBetween P p q) (hPJ : P ⊆ J) :
    ∃ T : Set Plane, IsCutPair J p q P T ∧
      IsJordanCurve (P ∪ A) ∧ IsJordanCurve (T ∪ A) ∧
      closure (inside (P ∪ A)) ∪ closure (inside (T ∪ A)) = closure (inside J) ∧
      closure (inside (P ∪ A)) ∩ closure (inside (T ∪ A)) = A ∧
      closure (inside (T ∪ A)) ∩ J = T := by
  have hpq : p ≠ q := by
    obtain ⟨f,-,hinj,-,h0,h1⟩ := hP
    intro heq
    exact zero_ne_one (hinj zero_mem_I one_mem_I (h0.trans (heq.trans h1.symm)))
  obtain ⟨B₁,B₂,hcut⟩ := exists_isCutPair h.curve h.left_mem h.right_mem hpq
  have hc : ∃ T : Set Plane, IsCutPair J p q P T := by
    rcases CompressionActualJordanCutPairArcUniquenessV811.arc_eq_one_of_cut_pair hcut hP hPJ with heq | heq
    · exact ⟨B₂,heq.symm ▸ hcut⟩
    · exact ⟨B₁,heq.symm ▸ hcut.symm⟩
  obtain ⟨T,hcut⟩ := hc
  obtain ⟨h₁,h₂,hcover,hinter,-,hT⟩ :=
    CompressionActualJordanClosedCrosscutTilingV806.closed_crosscut_tiling h hcut h.hasArcCollars
  exact ⟨T,hcut,h₁,h₂,hcover,hinter,hT⟩

#print axioms inner_arc_strip_tiling
end CompressionActualJordanInnerArcStripTilingV812
