import B1InteriorLocalZeroContinuation_v475
noncomputable section
open Set Topology Function Filter
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates

/-- Restriction to an open neighborhood preserves accumulation of literal
open zero germs. -/
theorem native_planar_zero_germ_accumulation_restrict_v475
    (O N : Set E2) (hN : IsOpen N) (hNO : N ⊆ O) (u : E2 → ℝ) (p : E2)
    (hpN : p ∈ N)
    (hacc : p ∈ closure {z | z ∈ O ∧ native_planar_zero_germ_v475 O u z}) :
    p ∈ closure {z | z ∈ N ∧ native_planar_zero_germ_v475 N u z} := by
  rw [mem_closure_iff]
  intro V hV hpV
  obtain ⟨z,hzVN,hzO,U,hU,hzU,hUO,hUz⟩ := mem_closure_iff.mp hacc (V ∩ N)
    (hV.inter hN) ⟨hpV,hpN⟩
  exact ⟨z,hzVN.1,hzVN.2,U ∩ N,hU.inter hN,⟨hzU,hzVN.2⟩,
    inter_subset_right,fun y hy => hUz hy.1⟩

#print axioms native_planar_zero_germ_accumulation_restrict_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
