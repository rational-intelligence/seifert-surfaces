import ActualNestedJordanLineRegionsV809

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology
open Schoenflies
noncomputable section
namespace CompressionActualNestedJordanCompatibleCutsV810

/-- Derive compatible labels for both whole closed cells of two nested
    Jordan domains with convex inner domain, using one common line. -/
theorem nested_jordan_compatible_cuts
    {C B : Set Plane} (hC : IsJordanCurve C) (hB : IsJordanCurve B)
    (hCV : Convex ℝ (inside C)) (hsub : closure (inside C) ⊆ inside B)
    (a b y : Plane) (hab : a ≠ b) (hy : y ∈ Plane.line a b ∩ inside C) :
    ∃ p q u v : Plane,p ≠ q ∧ u ≠ v ∧
      ∃ A₁ A₂ B₁ B₂ : Set Plane,
        IsCrosscut C (segment ℝ p q) p q ∧ IsCutPair C p q A₁ A₂ ∧
        IsCrosscut B (segment ℝ u v) u v ∧ IsCutPair B u v B₁ B₂ ∧
        segment ℝ p q ⊆ segment ℝ u v ∧
        inside C ∩ segment ℝ u v = openSegment ℝ p q ∧
        closure (inside (A₁ ∪ segment ℝ p q)) ⊆ closure (inside (B₁ ∪ segment ℝ u v)) ∧
        closure (inside (A₂ ∪ segment ℝ p q)) ⊆ closure (inside (B₂ ∪ segment ℝ u v)) ∧
        A₁ \ {p,q} ⊆ inside (B₁ ∪ segment ℝ u v) ∧
        A₂ \ {p,q} ⊆ inside (B₂ ∪ segment ℝ u v) := by
  have hCB : inside C ⊆ inside B := subset_closure.trans hsub
  have hsepC := jordan_curve_theorem hC
  have hsepB := jordan_curve_theorem hB
  obtain ⟨p,q,u,v,hpq,huv,hpC,hqC,huB,hvB,hlineC,hlineB,hsegSub,hinter⟩ :=
    CompressionActualNestedJordanLineRegionsV809.inner_line_chord_in_outer hC hB hCV hCB a b y hab hy
  have hiSeg : segment ℝ p q \ {p,q} ⊆ inside C := by
    intro x hx
    have hxp : p ≠ x := by intro he; exact hx.2 (by simp [← he])
    have hxq : q ≠ x := by intro he; exact hx.2 (by simp [← he])
    exact (hlineC ▸ mem_openSegment_of_ne_left_right hxp hxq hx.1).2
  have hoSeg : segment ℝ u v \ {u,v} ⊆ inside B := by
    intro x hx
    have hxu : u ≠ x := by intro he; exact hx.2 (by simp [← he])
    have hxv : v ≠ x := by intro he; exact hx.2 (by simp [← he])
    have hxopen := mem_openSegment_of_ne_left_right hxu hxv hx.1
    exact (connectedComponentIn_subset _ _ (hlineB ▸ hxopen)).2
  let ci : IsCrosscut C (segment ℝ p q) p q :=
    ⟨hC,isArcBetween_segment hpq,isPolygonal_segment p q,hpC,hqC,hiSeg⟩
  let co : IsCrosscut B (segment ℝ u v) u v :=
    ⟨hB,isArcBetween_segment huv,isPolygonal_segment u v,huB,hvB,hoSeg⟩
  obtain ⟨A₁,A₂,hAi⟩ := exists_isCutPair hC hpC hqC hpq
  obtain ⟨B₁,B₂,hBo⟩ := exists_isCutPair hB huB hvB huv
  have hiCollar := hasArcCollars_segment hpq hsepC.isOpen_inside
    (fun hp => inside_subset_compl hp hpC) (fun hq => inside_subset_compl hq hqC) hiSeg
  have hoCollar := hasArcCollars_segment huv hsepB.isOpen_inside
    (fun hu => inside_subset_compl hu huB) (fun hv => inside_subset_compl hv hvB) hoSeg
  have hdiff : inside C \ segment ℝ u v = inside C \ segment ℝ p q := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1,fun h => hx.2 (hsegSub h)⟩
    · intro hx
      refine ⟨hx.1,?_⟩
      intro hxo
      have hxi : x ∈ openSegment ℝ p q := hinter ▸ ⟨hx.1,hxo⟩
      exact hx.2 (openSegment_subset_segment _ _ _ hxi)
  have hinnerCover : inside C \ segment ℝ u v =
      inside (A₁ ∪ segment ℝ p q) ∪ inside (A₂ ∪ segment ℝ p q) :=
    hdiff.trans (ci.inside_diff_eq (fun _ => jordan_curve_theorem) hAi hiCollar)
  have houterCover := co.inside_diff_eq (fun _ => jordan_curve_theorem) hBo hoCollar
  have hySeg : y ∈ segment ℝ u v := by
    apply openSegment_subset_segment
    exact hlineB.symm ▸ mem_connectedComponentIn ⟨hy.1,hCB hy.2⟩
  have hyclose₁ : y ∈ closure (inside (B₁ ∪ segment ℝ u v)) :=
    (IsRegionOf.inside _).subset_closure (co.isSeparating_union (fun _ => jordan_curve_theorem) hBo)
      (Or.inr hySeg)
  have hyclose₂ : y ∈ closure (inside (B₂ ∪ segment ℝ u v)) :=
    (IsRegionOf.inside _).subset_closure (co.isSeparating_union (fun _ => jordan_curve_theorem) hBo.symm)
      (Or.inr hySeg)
  have hlabels := CompressionActualNestedCrosscutCellLabelsV808.nested_closed_cell_labels
    (inside C) (inside B) (segment ℝ u v)
    (inside (A₁ ∪ segment ℝ p q)) (inside (A₂ ∪ segment ℝ p q))
    (inside (B₁ ∪ segment ℝ u v)) (inside (B₂ ∪ segment ℝ u v))
    hsepC.isOpen_inside hCB hinnerCover houterCover
    (ci.isConnected_side (fun _ => jordan_curve_theorem) hAi)
    (ci.isConnected_side (fun _ => jordan_curve_theorem) hAi.symm)
    (co.isOpen_side (fun _ => jordan_curve_theorem) hBo)
    (co.isOpen_side (fun _ => jordan_curve_theorem) hBo.symm)
    (co.disjoint_sides (fun _ => jordan_curve_theorem) hBo) y hy.2 hyclose₁ hyclose₂
  have hedge (AA BB DD : Set Plane) (hcuti : IsCutPair C p q AA DD)
      (hcutO : IsJordanCurve (BB ∪ segment ℝ u v))
      (hBB : BB ⊆ B)
      (hcl : closure (inside (AA ∪ segment ℝ p q)) ⊆ closure (inside (BB ∪ segment ℝ u v))) :
      AA \ {p,q} ⊆ inside (BB ∪ segment ℝ u v) := by
    intro x hx
    have hxcl : x ∈ closure (inside (AA ∪ segment ℝ p q)) :=
      (IsRegionOf.inside _).subset_closure (ci.isSeparating_union (fun _ => jordan_curve_theorem) hcuti)
        (Or.inl hx.1)
    have hxC : x ∈ C := hcuti.fst_subset hx.1
    have hxB : x ∈ inside B := hsub ((IsRegionOf.inside _).subset_closure hsepC hxC)
    have hxNotSeg : x ∉ segment ℝ u v := by
      intro hxseg
      have hline : x ∈ Plane.line a b := by
        have hCclosed : IsClosed (Plane.line a b) := Plane.isClosed_line a b
        have huseg : segment ℝ u v ⊆ Plane.line a b := by
          rw [← closure_openSegment, hlineB]
          exact closure_minimal (fun z hz => (connectedComponentIn_subset _ _ hz).1) hCclosed
        exact huseg hxseg
      have hxpq : x ∈ segment ℝ p q := by
        rw [← closure_openSegment, hlineC]
        have hinsideClosure : x ∈ closure (Plane.line a b ∩ inside C) := by
          have hlineConvex : Convex ℝ (Plane.line a b) := by
            rw [Plane.line_eq_affineSpan]
            exact (affineSpan ℝ ({a,b}:Set Plane)).convex
          have hxin : x ∈ closure (inside C) := (IsRegionOf.inside _).subset_closure hsepC hxC
          have hsmall : openSegment ℝ y x ⊆ Plane.line a b ∩ inside C := by
            intro z hz
            refine ⟨hlineConvex.segment_subset hy.1 hline (openSegment_subset_segment _ _ _ hz),?_⟩
            have hyy : y ∈ interior (inside C) := hsepC.isOpen_inside.interior_eq.symm ▸ hy.2
            have hzz := hCV.openSegment_interior_closure_subset_interior hyy hxin hz
            exact interior_subset hzz
          apply closure_mono hsmall
          rw [closure_openSegment]
          exact right_mem_segment _ _ _
        exact hinsideClosure
      have hxpair : x ∈ ({p,q} : Set Plane) := by
        have hnotinside : x ∉ inside C := fun h => inside_subset_compl h hxC
        by_contra hpair
        exact hnotinside (hiSeg ⟨hxpq,hpair⟩)
      exact hx.2 hxpair
    have hxout := hcl hxcl
    rw [(IsRegionOf.inside _).closure_eq (jordan_curve_theorem hcutO)] at hxout
    rcases hxout with hxout | hxout
    · exact hxout
    · rcases hxout with hxout | hxout
      · exact False.elim (inside_subset_compl hxB (hBB hxout))
      · exact False.elim (hxNotSeg hxout)
  rcases hlabels with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact ⟨p,q,u,v,hpq,huv,A₁,A₂,B₁,B₂,ci,hAi,co,hBo,hsegSub,hinter,h₁,h₂,
      hedge A₁ B₁ A₂ hAi (co.isJordanCurve_union hBo) hBo.fst_subset h₁,
      hedge A₂ B₂ A₁ hAi.symm (co.isJordanCurve_union hBo.symm) hBo.snd_subset h₂⟩
  · exact ⟨p,q,u,v,hpq,huv,A₁,A₂,B₂,B₁,ci,hAi,co,hBo.symm,hsegSub,hinter,h₁,h₂,
      hedge A₁ B₂ A₂ hAi (co.isJordanCurve_union hBo.symm) hBo.snd_subset h₁,
      hedge A₂ B₁ A₁ hAi.symm (co.isJordanCurve_union hBo) hBo.fst_subset h₂⟩

#print axioms nested_jordan_compatible_cuts

end CompressionActualNestedJordanCompatibleCutsV810
