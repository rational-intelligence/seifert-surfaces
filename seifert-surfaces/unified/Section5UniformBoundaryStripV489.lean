import Section5CompactSurfaceInverseV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
open SeifertSurfaces.Foundations
noncomputable section

/-- One positive radial size works over the entire compact base. -/
theorem compact_boundary_uniform_strip {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {U : Set (X × Time)} (hU : IsOpen U) (hzero : ∀ x : X, (x,0) ∈ U) :
    ∃ d : ℝ, 0 < d ∧ d < 1 ∧ ∀ x : X, ∀ t : Time, (t : ℝ) ≤ d → (x,t) ∈ U := by
  have hcore : (univ : Set X) ×ˢ ({(0:Time)} : Set Time) ⊆ U := by
    rintro ⟨x,t⟩ ⟨_,ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact hzero x
  obtain ⟨A,B,hA,hB,hall,hzeroB,hAB⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (univ : Set X)) isCompact_singleton hU hcore
  obtain ⟨e,he,heB⟩ := Metric.isOpen_iff.mp hB (0:Time) (hzeroB (by simp))
  refine ⟨min (e/2) (1/2),lt_min (half_pos he) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num),?_⟩
  intro x t ht
  apply hAB
  refine ⟨hall (mem_univ x),heB ?_⟩
  rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
  change |(t:ℝ)-0| < e
  rw [sub_zero,abs_of_nonneg t.property.1]
  exact ht.trans_lt ((min_le_left _ _).trans_lt (half_lt_self he))

#print axioms compact_boundary_uniform_strip
end
end SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
