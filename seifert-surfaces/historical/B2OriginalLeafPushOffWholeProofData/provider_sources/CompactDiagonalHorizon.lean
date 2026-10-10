import Foundations
import Mathlib.Topology.Order.Compact

open scoped Manifold ContDiff
open Set Filter Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v
variable {M : Type v} [TopologicalSpace M]

/-- An open neighbourhood of the time diagonal has one positive horizon over
any compact spatial set. Compactness of the ambient space is unnecessary. -/
theorem compact_time_diagonal_horizon
    {K : Set M} (hK : IsCompact K) {A : Set ((Time × Time) × M)}
    (hA : IsOpen A) (hdiag : ∀ t x, x ∈ K → ((t,t),x) ∈ A) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s t : Time, ∀ x ∈ K,
      dist (s : ℝ) (t : ℝ) < ε → ((s,t),x) ∈ A := by
  let B : Set ((Time × Time) × M) := (univ ×ˢ K) ∩ Aᶜ
  have hB : IsCompact B := (isCompact_univ.prod hK).inter_right hA.isClosed_compl
  let d : (Time × Time) × M → ℝ := fun q => dist (q.1.1 : ℝ) (q.1.2 : ℝ)
  have hd : Continuous d :=
    (continuous_subtype_val.comp continuous_fst.fst).dist
      (continuous_subtype_val.comp continuous_fst.snd)
  by_cases hne : B.Nonempty
  · obtain ⟨p,hp,hmin⟩ := hB.exists_isMinOn hne hd.continuousOn
    have hp0 : 0 < d p := by
      apply dist_pos.mpr
      intro h
      have hs : p.1.1 = p.1.2 := Subtype.ext h
      exact hp.2 (by
        change ((p.1.1,p.1.2),p.2) ∈ A
        rw [← hs]
        exact hdiag _ _ hp.1.2)
    refine ⟨d p,hp0,?_⟩
    intro s t x hx hst
    by_contra hnot
    have hq : ((s,t),x) ∈ B := ⟨⟨mem_univ _,hx⟩,hnot⟩
    exact (not_lt_of_ge (hmin hq)) hst
  · refine ⟨1,zero_lt_one,?_⟩
    intro s t x hx _
    by_contra hnot
    exact hne ⟨((s,t),x),⟨⟨mem_univ _,hx⟩,hnot⟩⟩

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
