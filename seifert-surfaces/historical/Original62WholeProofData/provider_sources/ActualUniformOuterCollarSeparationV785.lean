import ActualAnnulusWholeFamilyWithSideChoiceV780

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology Metric
open SeifertSurfaces.Foundations
noncomputable section
namespace CompressionActualUniformOuterCollarSeparationV785

/-- A compact whole collar base which misses a closed core at normal level zero
    misses it uniformly for all sufficiently small positive normal levels. -/
theorem uniform_outer_collar_separation
    {Z Y : Type} [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace Y]
    (out : C(Time × Z,Y)) (K : Set Y) (hK : IsClosed K)
    (hzero : ∀ z,out (0,z) ∉ K) :
    ∃ r : Time,0 < r.val ∧ ∀ s z,s.val ≤ r.val → out (s,z) ∉ K := by
  let O : Set (Time × Z) := out ⁻¹' Kᶜ
  have hO : IsOpen O := hK.isOpen_compl.preimage out.continuous
  have hcontain : ({0} : Set Time) ×ˢ (univ : Set Z) ⊆ O := by
    rintro ⟨s,z⟩ ⟨hs,hz⟩
    have he : s = 0 := hs
    subst s
    exact hzero z
  obtain ⟨U,V,hU,hV,h0,hall,hUV⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({0}:Set Time))
    (isCompact_univ : IsCompact (univ:Set Z)) hO hcontain
  have h0U : (0:Time) ∈ U := h0 (mem_singleton 0)
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  let a : ℝ := min (δ/2) (1/2)
  have ha : 0 < a := lt_min (half_pos hδ) (by norm_num)
  have ha1 : a ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have haδ : a < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  let r : Time := ⟨a,ha.le,ha1⟩
  refine ⟨r,ha,?_⟩
  intro s z hs
  have hsδ : s ∈ Metric.ball (0:Time) δ := by
    change dist s (0:Time) < δ
    rw [Subtype.dist_eq,Real.dist_eq]
    change |s.val-0| < δ
    rw [sub_zero,abs_of_nonneg s.property.1]
    exact hs.trans_lt haδ
  have hp : (s,z) ∈ U ×ˢ V := ⟨hδU hsδ,hall (mem_univ z)⟩
  have hval : (s,z) ∈ O := hUV hp
  exact hval

end CompressionActualUniformOuterCollarSeparationV785
