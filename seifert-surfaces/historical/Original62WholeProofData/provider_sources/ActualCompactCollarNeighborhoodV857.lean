import ActualAnnulusEmbeddingOpenMiddleV853

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology Metric
open SeifertSurfaces.Foundations
noncomputable section
namespace CompressionActualCompactCollarNeighborhoodV857

/-- An actual compact circle collar can be shortened uniformly into any
    prescribed open neighborhood of its whole zero edge. -/
theorem compact_collar_neighborhood {X : Type} [TopologicalSpace X]
    (c : C(Circle × Time,X)) (U : Set X) (hU : IsOpen U)
    (hzero : ∀ z,c (z,0) ∈ U) :
    ∃ a : ℝ,0 < a ∧ a < 1 ∧
      ∀ (z : Circle) (t : Time),t.val ≤ a → c (z,t) ∈ U := by
  let O : Set (Circle × Time) := c ⁻¹' U
  have hO : IsOpen O := hU.preimage c.continuous
  have hcontain : (univ : Set Circle) ×ˢ ({0} : Set Time) ⊆ O := by
    rintro ⟨z,t⟩ ⟨hz,ht⟩
    have ht0 : t = 0 := mem_singleton_iff.mp ht
    exact ht0 ▸ hzero z
  obtain ⟨V,N,hV,hN,hCV,h0N,hVN⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (univ : Set Circle)) (isCompact_singleton (x := (0:Time))) hO hcontain
  obtain ⟨δ,hδ,hδN⟩ := Metric.isOpen_iff.mp hN 0 (h0N (mem_singleton 0))
  let a : ℝ := min (δ/2) (1/2)
  have ha : 0 < a := lt_min (half_pos hδ) (by norm_num)
  have haδ : a < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  refine ⟨a,ha,(min_le_right _ _).trans_lt (by norm_num),?_⟩
  intro z t ht
  have htn : t ∈ N := hδN (by
    rw [mem_ball,Subtype.dist_eq,Real.dist_eq]
    change |t.val-0| < δ
    rw [sub_zero,abs_of_nonneg t.property.1]
    exact ht.trans_lt haδ)
  exact @hVN (z,t) ⟨hCV (mem_univ z),htn⟩

#print axioms compact_collar_neighborhood
end CompressionActualCompactCollarNeighborhoodV857
