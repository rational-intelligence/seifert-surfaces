import ActualNestedCrosscutCellLabelsV808
import Mathlib.Analysis.Convex.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology
open Schoenflies
noncomputable section
namespace CompressionActualNestedJordanLineRegionsV809

/-- The first-hit chord of a convex inner Jordan region is exactly the
    portion of the outer first-hit chord inside that region. -/
theorem inner_line_chord_in_outer
    {C B : Set Plane} (hC : IsJordanCurve C) (hB : IsJordanCurve B)
    (hCV : Convex ℝ (inside C)) (hsub : inside C ⊆ inside B)
    (a b y : Plane) (hab : a ≠ b) (hy : y ∈ Plane.line a b ∩ inside C) :
    ∃ p q u v : Plane,p ≠ q ∧ u ≠ v ∧ p ∈ C ∧ q ∈ C ∧ u ∈ B ∧ v ∈ B ∧
      openSegment ℝ p q = Plane.line a b ∩ inside C ∧
      openSegment ℝ u v = connectedComponentIn (Plane.line a b ∩ inside B) y ∧
      segment ℝ p q ⊆ segment ℝ u v ∧
      inside C ∩ segment ℝ u v = openSegment ℝ p q := by
  have hline : Convex ℝ (Plane.line a b) := by
    rw [Plane.line_eq_affineSpan]
    exact (affineSpan ℝ ({a,b}:Set Plane)).convex
  have hconn : IsPreconnected (Plane.line a b ∩ inside C) := (hline.inter hCV).isPreconnected
  obtain ⟨p,q,hpq,hpℓ,hqℓ,hpc,hqc,hpqcomp,hpqclos,rest⟩ :=
    CompressionActualJordanLineCutFactoryV807.jordan_line_cut_factory hC a b y hab hy
  obtain ⟨u,v,huv,huℓ,hvℓ,huB,hvB,huvcomp,huvclos,restB⟩ :=
    CompressionActualJordanLineCutFactoryV807.jordan_line_cut_factory hB a b y hab ⟨hy.1,hsub hy.2⟩
  have hpqeq : openSegment ℝ p q = Plane.line a b ∩ inside C :=
    hpqcomp.symm.trans (hconn.connectedComponentIn hy)
  have hcompSub : connectedComponentIn (Plane.line a b ∩ inside C) y ⊆
      connectedComponentIn (Plane.line a b ∩ inside B) y :=
    connectedComponentIn_mono y (inter_subset_inter_right _ hsub)
  have hsegSub : segment ℝ p q ⊆ segment ℝ u v := by
    rw [← hpqclos,← huvclos]
    exact closure_mono hcompSub
  have houterLine : segment ℝ u v ⊆ Plane.line a b := by
    rw [← huvclos]
    exact closure_minimal (fun x hx => (connectedComponentIn_subset _ _ hx).1)
      (Plane.isClosed_line a b)
  refine ⟨p,q,u,v,hpq,huv,hpc,hqc,huB,hvB,hpqeq,huvcomp.symm,hsegSub,?_⟩
  apply Subset.antisymm
  · intro x hx
    rw [hpqeq]
    exact ⟨houterLine hx.2,hx.1⟩
  · intro x hx
    have hxC : x ∈ inside C := (hpqeq ▸ hx).2
    have hxseg : x ∈ segment ℝ p q := openSegment_subset_segment _ _ _ hx
    exact ⟨hxC,hsegSub hxseg⟩

#print axioms inner_line_chord_in_outer
end CompressionActualNestedJordanLineRegionsV809
