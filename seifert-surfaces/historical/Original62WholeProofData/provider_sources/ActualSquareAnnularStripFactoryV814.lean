import ActualNestedJordanAnnularStripTilingV813

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology
open Schoenflies
noncomputable section
namespace CompressionActualSquareAnnularStripFactoryV814

private theorem corners_ne : cornerNE ≠ cornerSW := by
  intro heq
  have h := congrArg (fun x : Plane => x 0) heq
  norm_num [cornerNE,cornerSW] at h

theorem diagonal_curve_point (x : Plane)
    (hxline : x ∈ Plane.line cornerNE cornerSW) (hxcurve : x ∈ modelCurve) :
    x = cornerNE ∨ x = cornerSW := by
  have hd := (Plane.mem_line_iff_det_eq_zero corners_ne).mp hxline
  have hcoord : x 0 = x 1 := by
    simp [Plane.det,cornerNE,cornerSW] at hd
    linarith
  have ha : |x 0| = 1 := by
    simpa only [modelCurve,mem_ofPred_eq,Plane.supNorm,hcoord,max_self] using hxcurve
  have he : x 0 = 1 ∨ x 0 = -1 := (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp ha
  rcases he with he | he
  · left
    ext i
    fin_cases i
    · simpa [cornerNE] using he
    · simp only [cornerNE]
      exact hcoord.symm.trans he
  · right
    ext i
    fin_cases i
    · simpa [cornerSW] using he
    · simp only [cornerSW]
      exact hcoord.symm.trans he

/-- An arbitrary Jordan disk containing the whole square core admits two
    genuine Jordan strips covering its entire closed annular difference.
    The first-hit chord and both polygonal inner arcs are constructed. -/
theorem square_annular_strip_factory
    {B : Set Plane} (hB : IsJordanCurve B)
    (hsub : closure (inside modelCurve) ⊆ inside B) :
    ∃ J₁ J₂ K : Set Plane, IsJordanCurve J₁ ∧ IsJordanCurve J₂ ∧
      closure (inside J₁) ∪ closure (inside J₂) =
        closure (inside B) \ inside modelCurve ∧
      closure (inside J₁) ∩ closure (inside J₂) = K \ inside modelCurve := by
  have hyline : (0 : Plane) ∈ Plane.line cornerNE cornerSW := by
    apply (Plane.mem_line_iff_det_eq_zero corners_ne).mpr
    norm_num [Plane.det,cornerNE,cornerSW]
  have hyinside : (0 : Plane) ∈ inside modelCurve := by
    rw [inside_modelCurve,mem_openSquare_zero_one]
    norm_num [Plane.supNorm]
  have hconv : Convex ℝ (inside modelCurve) := by
    rw [inside_modelCurve]
    exact Plane.convex_openSquare 0 1
  have hinnerSub : inside modelCurve ⊆ inside B := subset_closure.trans hsub
  obtain ⟨p,q,u,v,hpq,huv,hpc,hqc,huB,hvB,hlineC,hlineB,hLK,hinter⟩ :=
    CompressionActualNestedJordanLineRegionsV809.inner_line_chord_in_outer
      isJordanCurve_modelCurve hB hconv hinnerSub cornerNE cornerSW 0 corners_ne ⟨hyline,hyinside⟩
  have hpLine : p ∈ Plane.line cornerNE cornerSW := by
    have hs : segment ℝ p q ⊆ Plane.line cornerNE cornerSW := by
      rw [← closure_openSegment,hlineC]
      exact closure_minimal inter_subset_left (Plane.isClosed_line _ _)
    exact hs (left_mem_segment _ _ _)
  have hqLine : q ∈ Plane.line cornerNE cornerSW := by
    have hs : segment ℝ p q ⊆ Plane.line cornerNE cornerSW := by
      rw [← closure_openSegment,hlineC]
      exact closure_minimal inter_subset_left (Plane.isClosed_line _ _)
    exact hs (right_mem_segment _ _ _)
  have hpqCorners : (p = cornerNE ∧ q = cornerSW) ∨ (p = cornerSW ∧ q = cornerNE) := by
    rcases diagonal_curve_point p hpLine hpc with hp | hp <;>
      rcases diagonal_curve_point q hqLine hqc with hq | hq
    · exact False.elim (hpq (hp.trans hq.symm))
    · exact Or.inl ⟨hp,hq⟩
    · exact Or.inr ⟨hp,hq⟩
    · exact False.elim (hpq (hp.trans hq.symm))
  have hsegmentInner : segment ℝ p q \ {p,q} ⊆ inside modelCurve := by
    intro x hx
    have hxp : p ≠ x := by intro he; exact hx.2 (by simp [← he])
    have hxq : q ≠ x := by intro he; exact hx.2 (by simp [← he])
    exact (hlineC ▸ mem_openSegment_of_ne_left_right hxp hxq hx.1).2
  have hsegmentOuter : segment ℝ u v \ {u,v} ⊆ inside B := by
    intro x hx
    have hxu : u ≠ x := by intro he; exact hx.2 (by simp [← he])
    have hxv : v ≠ x := by intro he; exact hx.2 (by simp [← he])
    have ho := mem_openSegment_of_ne_left_right hxu hxv hx.1
    exact (connectedComponentIn_subset _ _ (hlineB ▸ ho)).2
  let ci : IsCrosscut modelCurve (segment ℝ p q) p q :=
    ⟨isJordanCurve_modelCurve,isArcBetween_segment hpq,isPolygonal_segment p q,hpc,hqc,hsegmentInner⟩
  let co : IsCrosscut B (segment ℝ u v) u v :=
    ⟨hB,isArcBetween_segment huv,isPolygonal_segment u v,huB,hvB,hsegmentOuter⟩
  obtain ⟨A₁,A₂,hai⟩ := exists_isCutPair isJordanCurve_modelCurve hpc hqc hpq
  obtain ⟨B₁,B₂,hbo⟩ := exists_isCutPair hB huB hvB huv
  have hpolyInner : IsPolygonal A₁ ∧ IsPolygonal A₂ := by
    have hup : IsPolygonal (sideTop ∪ sideLeft) :=
      (isPolygonal_segment _ _).union (isPolygonal_segment _ _)
        ⟨cornerNW,right_mem_segment _ _ _,left_mem_segment _ _ _⟩
    have hlo : IsPolygonal (sideBottom ∪ sideRight) :=
      (isPolygonal_segment _ _).union (isPolygonal_segment _ _)
        ⟨cornerSE,right_mem_segment _ _ _,left_mem_segment _ _ _⟩
    have hmodel : IsCutPair modelCurve cornerNE cornerSW (sideTop ∪ sideLeft) (sideBottom ∪ sideRight) :=
      ⟨isArcBetween_upperSides,isArcBetween_lowerSides.reverse,
        modelCurve_eq_sides.symm,by
          apply Subset.antisymm
          · intro x hx
            simpa only [mem_insert_iff,mem_singleton_iff] using upperSides_meet_lowerSides x hx.1 hx.2
          · exact pair_subset
              ⟨isArcBetween_upperSides.left_mem,isArcBetween_lowerSides.right_mem⟩
              ⟨isArcBetween_upperSides.right_mem,isArcBetween_lowerSides.left_mem⟩⟩
    have hmodelpq : IsCutPair modelCurve p q (sideTop ∪ sideLeft) (sideBottom ∪ sideRight) := by
      rcases hpqCorners with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hmodel
      · exact ⟨hmodel.fst.reverse,hmodel.snd.reverse,hmodel.union_eq,
          by rw [pair_comm]; exact hmodel.inter_eq⟩
    constructor
    · rcases CompressionActualJordanCutPairArcUniquenessV811.arc_eq_one_of_cut_pair
        hmodelpq hai.fst hai.fst_subset with he | he
      · exact he.symm ▸ hup
      · exact he.symm ▸ hlo
    · rcases CompressionActualJordanCutPairArcUniquenessV811.arc_eq_one_of_cut_pair
        hmodelpq hai.snd hai.snd_subset with he | he
      · exact he.symm ▸ hup
      · exact he.symm ▸ hlo
  have hdiff : inside modelCurve \ segment ℝ u v = inside modelCurve \ segment ℝ p q := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1,fun hs => hx.2 (hLK hs)⟩
    · intro hx
      refine ⟨hx.1,?_⟩
      intro hs
      have hxo : x ∈ openSegment ℝ p q := hinter ▸ ⟨hx.1,hs⟩
      exact hx.2 (openSegment_subset_segment _ _ _ hxo)
  have hcoverInner := hdiff.trans (ci.inside_diff_eq (fun _ => jordan_curve_theorem) hai ci.hasArcCollars)
  have hcoverOuter := co.inside_diff_eq (fun _ => jordan_curve_theorem) hbo co.hasArcCollars
  have hyK : (0 : Plane) ∈ segment ℝ u v := by
    apply openSegment_subset_segment
    exact hlineB.symm ▸ mem_connectedComponentIn ⟨hyline,hinnerSub hyinside⟩
  have hy₁ := (IsRegionOf.inside _).subset_closure
    (co.isSeparating_union (fun _ => jordan_curve_theorem) hbo) (Or.inr hyK)
  have hy₂ := (IsRegionOf.inside _).subset_closure
    (co.isSeparating_union (fun _ => jordan_curve_theorem) hbo.symm) (Or.inr hyK)
  have hlabels := CompressionActualNestedCrosscutCellLabelsV808.nested_closed_cell_labels
    (inside modelCurve) (inside B) (segment ℝ u v)
    (inside (A₁ ∪ segment ℝ p q)) (inside (A₂ ∪ segment ℝ p q))
    (inside (B₁ ∪ segment ℝ u v)) (inside (B₂ ∪ segment ℝ u v))
    (jordan_curve_theorem isJordanCurve_modelCurve).isOpen_inside hinnerSub hcoverInner hcoverOuter
    (ci.isConnected_side (fun _ => jordan_curve_theorem) hai)
    (ci.isConnected_side (fun _ => jordan_curve_theorem) hai.symm)
    (co.isOpen_side (fun _ => jordan_curve_theorem) hbo)
    (co.isOpen_side (fun _ => jordan_curve_theorem) hbo.symm)
    (co.disjoint_sides (fun _ => jordan_curve_theorem) hbo) 0 hyinside hy₁ hy₂
  -- The compatible-cut factory gives the needed placement of both inner arcs.
  -- Here the arcs are the constructed square sides, whose polygonality is paid above.
  have hedge (AA BB DD : Set Plane) (hi : IsCutPair modelCurve p q AA DD)
      (ho : IsJordanCurve (BB ∪ segment ℝ u v)) (hBB : BB ⊆ B)
      (hcl : closure (inside (AA ∪ segment ℝ p q)) ⊆ closure (inside (BB ∪ segment ℝ u v))) :
      AA \ {p,q} ⊆ inside (BB ∪ segment ℝ u v) := by
    intro x hx
    have hxcl := (IsRegionOf.inside _).subset_closure
      (ci.isSeparating_union (fun _ => jordan_curve_theorem) hi) (Or.inl hx.1)
    have hxC := hi.fst_subset hx.1
    have hxB : x ∈ inside B := hsub ((IsRegionOf.inside _).subset_closure
      (jordan_curve_theorem isJordanCurve_modelCurve) hxC)
    have hxNotSeg : x ∉ segment ℝ u v := by
      intro hs
      have hline : x ∈ Plane.line cornerNE cornerSW := by
        have hsegLine : segment ℝ u v ⊆ Plane.line cornerNE cornerSW := by
          rw [← closure_openSegment,hlineB]
          exact closure_minimal (fun z hz => (connectedComponentIn_subset _ _ hz).1)
            (Plane.isClosed_line _ _)
        exact hsegLine hs
      rcases diagonal_curve_point x hline hxC with he | he <;>
        rcases hpqCorners with ⟨hp,hq⟩ | ⟨hp,hq⟩
      · exact hx.2 (by simp [he,hp])
      · exact hx.2 (by simp [he,hq])
      · exact hx.2 (by simp [he,hq])
      · exact hx.2 (by simp [he,hp])
    have hxout := hcl hxcl
    rw [(IsRegionOf.inside _).closure_eq (jordan_curve_theorem ho)] at hxout
    rcases hxout with hxout | (hxout | hxout)
    · exact hxout
    · exact False.elim (inside_subset_compl hxB (hBB hxout))
    · exact False.elim (hxNotSeg hxout)
  have hinnerK : inside modelCurve ∩ segment ℝ u v ⊆ segment ℝ p q := by
    rw [hinter]
    exact openSegment_subset_segment _ _ _
  rcases hlabels with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · obtain ⟨T₁,T₂,-,-,hj₁,hj₂,hcover,hmeet⟩ :=
      CompressionActualNestedJordanAnnularStripTilingV813.annular_strip_tiling ci hai co hbo hLK hinnerK
        (hedge A₁ B₁ A₂ hai (co.isJordanCurve_union hbo) hbo.fst_subset h₁)
        (hedge A₂ B₂ A₁ hai.symm (co.isJordanCurve_union hbo.symm) hbo.snd_subset h₂)
        hpolyInner.1 hpolyInner.2
    exact ⟨T₁ ∪ A₁,T₂ ∪ A₂,segment ℝ u v,hj₁,hj₂,hcover,hmeet⟩
  · obtain ⟨T₁,T₂,-,-,hj₁,hj₂,hcover,hmeet⟩ :=
      CompressionActualNestedJordanAnnularStripTilingV813.annular_strip_tiling ci hai co hbo.symm hLK hinnerK
        (hedge A₁ B₂ A₂ hai (co.isJordanCurve_union hbo.symm) hbo.snd_subset h₁)
        (hedge A₂ B₁ A₁ hai.symm (co.isJordanCurve_union hbo) hbo.fst_subset h₂)
        hpolyInner.1 hpolyInner.2
    exact ⟨T₁ ∪ A₁,T₂ ∪ A₂,segment ℝ u v,hj₁,hj₂,hcover,hmeet⟩

#print axioms diagonal_curve_point
#print axioms square_annular_strip_factory
end CompressionActualSquareAnnularStripFactoryV814
