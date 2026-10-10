import ActualTaperedNormalBlockIsotopyV837

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology Metric
noncomputable section
namespace CompressionActualThinCompactNormalNeighborhoodV847

/-- Compactness of an entire zero slice gives one positive thickness for
    the whole closed normal block in a prescribed open neighborhood. -/
theorem compact_zero_slice_thickening {X : Type} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (U : Set (X × ℝ)) (hU : IsOpen U)
    (hKU : K ×ˢ ({0} : Set ℝ) ⊆ U) :
    ∃ δ : ℝ,0 < δ ∧ K ×ˢ Icc (-δ) δ ⊆ U := by
  obtain ⟨V,N,hV,hN,hKV,h0N,hVN⟩ := generalized_tube_lemma hK
    (isCompact_singleton (x := (0:ℝ))) hU hKU
  obtain ⟨ε,hε,hεN⟩ := Metric.isOpen_iff.mp hN 0 (h0N (mem_singleton 0))
  refine ⟨ε/2,half_pos hε,?_⟩
  rintro ⟨x,z⟩ ⟨hx,hz⟩
  have hzn : z ∈ N := hεN (mem_ball_zero_iff.mpr (by
    rw [Real.norm_eq_abs]
    exact (abs_le.mpr hz).trans_lt (half_lt_self hε)))
  exact @hVN (x,z) ⟨hKV hx,hzn⟩

/-- The thin whole closed chart block avoids every point of the supplied
    closed forbidden set. The thickness is constructed from zero-slice
    avoidance rather than supplied as a collar-separation premise. -/
theorem chart_normal_block_away_closed_set
    {X M : Type} [TopologicalSpace X] [TopologicalSpace M]
    (e : OpenPartialHomeomorph (X × ℝ) M)
    (K : Set X) (hK : IsCompact K)
    (hKs : K ×ˢ ({0} : Set ℝ) ⊆ e.source)
    (Z : Set M) (hZ : IsClosed Z) (haway : Disjoint (e '' (K ×ˢ {0})) Z) :
    ∃ δ : ℝ,0 < δ ∧ K ×ˢ Icc (-δ) δ ⊆ e.source ∧
      Disjoint (e '' (K ×ˢ Icc (-δ) δ)) Z := by
  let U : Set (X × ℝ) := e.source ∩ e ⁻¹' Zᶜ
  have hU : IsOpen U := e.isOpen_inter_preimage hZ.isOpen_compl
  have hKU : K ×ˢ ({0} : Set ℝ) ⊆ U := by
    intro p hp
    exact ⟨hKs hp,fun hz => disjoint_left.mp haway ⟨p,hp,rfl⟩ hz⟩
  obtain ⟨δ,hδ,hδU⟩ := compact_zero_slice_thickening K hK U hU hKU
  refine ⟨δ,hδ,fun p hp => (hδU hp).1,disjoint_left.mpr ?_⟩
  rintro y ⟨p,hp,rfl⟩ hy
  exact (hδU hp).2 hy

#print axioms compact_zero_slice_thickening
#print axioms chart_normal_block_away_closed_set
end CompressionActualThinCompactNormalNeighborhoodV847
