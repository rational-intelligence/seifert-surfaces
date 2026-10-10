import ActualJordanInnerArcStripTilingV812

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology
open Schoenflies
noncomputable section
namespace CompressionActualNestedJordanAnnularStripTilingV813

/-- Two compatible cuts, followed by cuts along both polygonal inner
    boundary arcs, tile the entire closed annular difference by two
    Jordan disks. Their intersection consists of the whole connecting
    chord outside the inner open disk. -/
theorem annular_strip_tiling
    {C B L K A₁ A₂ B₁ B₂ : Set Plane} {p q u v : Plane}
    (ci : IsCrosscut C L p q) (ai : IsCutPair C p q A₁ A₂)
    (co : IsCrosscut B K u v) (bo : IsCutPair B u v B₁ B₂)
    (hLK : L ⊆ K) (hinnerK : inside C ∩ K ⊆ L)
    (hA₁ : A₁ \ {p,q} ⊆ inside (B₁ ∪ K))
    (hA₂ : A₂ \ {p,q} ⊆ inside (B₂ ∪ K))
    (hpoly₁ : IsPolygonal A₁) (hpoly₂ : IsPolygonal A₂) :
    ∃ T₁ T₂ : Set Plane,
      IsCutPair (B₁ ∪ K) p q L T₁ ∧ IsCutPair (B₂ ∪ K) p q L T₂ ∧
      IsJordanCurve (T₁ ∪ A₁) ∧ IsJordanCurve (T₂ ∪ A₂) ∧
      closure (inside (T₁ ∪ A₁)) ∪ closure (inside (T₂ ∪ A₂)) =
        closure (inside B) \ inside C ∧
      closure (inside (T₁ ∪ A₁)) ∩ closure (inside (T₂ ∪ A₂)) = K \ inside C := by
  let c₁ : IsCrosscut (B₁ ∪ K) A₁ p q :=
    ⟨co.isJordanCurve_union bo,ai.fst,hpoly₁,
      Or.inr (hLK ci.arc.left_mem),Or.inr (hLK ci.arc.right_mem),hA₁⟩
  let c₂ : IsCrosscut (B₂ ∪ K) A₂ p q :=
    ⟨co.isJordanCurve_union bo.symm,ai.snd,hpoly₂,
      Or.inr (hLK ci.arc.left_mem),Or.inr (hLK ci.arc.right_mem),hA₂⟩
  obtain ⟨T₁,ht₁,-,hj₁,hcover₁,hinter₁,-⟩ :=
    CompressionActualJordanInnerArcStripTilingV812.inner_arc_strip_tiling c₁ ci.arc
      (hLK.trans subset_union_right)
  obtain ⟨T₂,ht₂,-,hj₂,hcover₂,hinter₂,-⟩ :=
    CompressionActualJordanInnerArcStripTilingV812.inner_arc_strip_tiling c₂ ci.arc
      (hLK.trans subset_union_right)
  have hh₁ : closure (inside (L ∪ A₁)) = closure (inside (A₁ ∪ L)) := by rw [union_comm]
  have hh₂ : closure (inside (L ∪ A₂)) = closure (inside (A₂ ∪ L)) := by rw [union_comm]
  rw [hh₁] at hcover₁ hinter₁
  rw [hh₂] at hcover₂ hinter₂
  obtain ⟨-,-,hcoveri,hinteri,-,-⟩ :=
    CompressionActualJordanClosedCrosscutTilingV806.closed_crosscut_tiling ci ai ci.hasArcCollars
  obtain ⟨-,-,hcovero,hintero,-,-⟩ :=
    CompressionActualJordanClosedCrosscutTilingV806.closed_crosscut_tiling co bo co.hasArcCollars
  let I₁ := closure (inside (A₁ ∪ L))
  let I₂ := closure (inside (A₂ ∪ L))
  let O₁ := closure (inside (B₁ ∪ K))
  let O₂ := closure (inside (B₂ ∪ K))
  let S₁ := closure (inside (T₁ ∪ A₁))
  let S₂ := closure (inside (T₂ ∪ A₂))
  change I₁ ∪ S₁ = O₁ at hcover₁
  change I₂ ∪ S₂ = O₂ at hcover₂
  change I₁ ∩ S₁ = A₁ at hinter₁
  change I₂ ∩ S₂ = A₂ at hinter₂
  change I₁ ∪ I₂ = closure (inside C) at hcoveri
  change O₁ ∪ O₂ = closure (inside B) at hcovero
  change O₁ ∩ O₂ = K at hintero
  have hO₁ : S₁ ⊆ O₁ := by
    intro x hx
    exact hcover₁ ▸ (Or.inr hx)
  have hO₂ : S₂ ⊆ O₂ := by
    intro x hx
    exact hcover₂ ▸ (Or.inr hx)
  have hL₁ : L ⊆ I₁ := by
    intro x hx
    exact (IsRegionOf.inside _).subset_closure
      (ci.isSeparating_union (fun _ => jordan_curve_theorem) ai) (Or.inr hx)
  have hL₂ : L ⊆ I₂ := by
    intro x hx
    exact (IsRegionOf.inside _).subset_closure
      (ci.isSeparating_union (fun _ => jordan_curve_theorem) ai.symm) (Or.inr hx)
  have hnot₁ : S₁ ⊆ (inside C)ᶜ := by
    intro x hx hxin
    have hxi : x ∈ I₁ ∪ I₂ := hcoveri.symm ▸ subset_closure hxin
    have hinI₁ : x ∈ I₁ := by
      rcases hxi with hi | hi
      · exact hi
      · have hxO₂ : x ∈ O₂ := hcover₂ ▸ (Or.inl hi)
        have hxK : x ∈ K := hintero ▸ ⟨hO₁ hx,hxO₂⟩
        exact hL₁ (hinnerK ⟨hxin,hxK⟩)
    have hxA : x ∈ A₁ := hinter₁ ▸ ⟨hinI₁,hx⟩
    exact inside_subset_compl hxin (ai.fst_subset hxA)
  have hnot₂ : S₂ ⊆ (inside C)ᶜ := by
    intro x hx hxin
    have hxi : x ∈ I₁ ∪ I₂ := hcoveri.symm ▸ subset_closure hxin
    have hinI₂ : x ∈ I₂ := by
      rcases hxi with hi | hi
      · have hxO₁ : x ∈ O₁ := hcover₁ ▸ (Or.inl hi)
        have hxK : x ∈ K := hintero ▸ ⟨hxO₁,hO₂ hx⟩
        exact hL₂ (hinnerK ⟨hxin,hxK⟩)
      · exact hi
    have hxA : x ∈ A₂ := hinter₂ ▸ ⟨hinI₂,hx⟩
    exact inside_subset_compl hxin (ai.snd_subset hxA)
  have hboundary₁ : I₁ \ inside C ⊆ S₁ := by
    intro x hx
    have hcl := (IsRegionOf.inside _).closure_eq
      (ci.isSeparating_union (fun _ => jordan_curve_theorem) ai)
    have hxcurve : x ∈ A₁ ∪ L := by
      have hxcase : x ∈ inside (A₁ ∪ L) ∪ (A₁ ∪ L) := hcl ▸ hx.1
      rcases hxcase with hin | hcur
      · exact False.elim (hx.2 (ci.side_subset (fun _ => jordan_curve_theorem) ai hin).1)
      · exact hcur
    have hxA : x ∈ A₁ := by
      rcases hxcurve with hxA | hxL
      · exact hxA
      · by_cases hpair : x ∈ ({p,q} : Set Plane)
        · exact pair_subset ai.fst.left_mem ai.fst.right_mem hpair
        · exact False.elim (hx.2 (ci.sdiff_subset ⟨hxL,hpair⟩))
    exact (IsRegionOf.inside _).subset_closure (jordan_curve_theorem hj₁) (Or.inr hxA)
  have hboundary₂ : I₂ \ inside C ⊆ S₂ := by
    intro x hx
    have hcl := (IsRegionOf.inside _).closure_eq
      (ci.isSeparating_union (fun _ => jordan_curve_theorem) ai.symm)
    have hxcurve : x ∈ A₂ ∪ L := by
      have hxcase : x ∈ inside (A₂ ∪ L) ∪ (A₂ ∪ L) := hcl ▸ hx.1
      rcases hxcase with hin | hcur
      · exact False.elim (hx.2 (ci.side_subset (fun _ => jordan_curve_theorem) ai.symm hin).1)
      · exact hcur
    have hxA : x ∈ A₂ := by
      rcases hxcurve with hxA | hxL
      · exact hxA
      · by_cases hpair : x ∈ ({p,q} : Set Plane)
        · exact pair_subset ai.snd.left_mem ai.snd.right_mem hpair
        · exact False.elim (hx.2 (ci.sdiff_subset ⟨hxL,hpair⟩))
    exact (IsRegionOf.inside _).subset_closure (jordan_curve_theorem hj₂) (Or.inr hxA)
  have hout₁ : O₁ \ inside C ⊆ S₁ := by
    intro x hx
    rcases hcover₁.symm ▸ hx.1 with hi | hs
    · exact hboundary₁ ⟨hi,hx.2⟩
    · exact hs
  have hout₂ : O₂ \ inside C ⊆ S₂ := by
    intro x hx
    rcases hcover₂.symm ▸ hx.1 with hi | hs
    · exact hboundary₂ ⟨hi,hx.2⟩
    · exact hs
  have hcover : S₁ ∪ S₂ = closure (inside B) \ inside C := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · exact ⟨hcovero ▸ Or.inl (hO₁ hx),hnot₁ hx⟩
      · exact ⟨hcovero ▸ Or.inr (hO₂ hx),hnot₂ hx⟩
    · intro x hx
      rcases hcovero.symm ▸ hx.1 with ho | ho
      · exact Or.inl (hout₁ ⟨ho,hx.2⟩)
      · exact Or.inr (hout₂ ⟨ho,hx.2⟩)
  have hinter : S₁ ∩ S₂ = K \ inside C := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨hintero ▸ ⟨hO₁ hx.1,hO₂ hx.2⟩,hnot₁ hx.1⟩
    · intro x hx
      have ho : x ∈ O₁ ∩ O₂ := hintero.symm ▸ hx.1
      exact ⟨hout₁ ⟨ho.1,hx.2⟩,hout₂ ⟨ho.2,hx.2⟩⟩
  exact ⟨T₁,T₂,ht₁,ht₂,hj₁,hj₂,hcover,hinter⟩

#print axioms annular_strip_tiling
end CompressionActualNestedJordanAnnularStripTilingV813
