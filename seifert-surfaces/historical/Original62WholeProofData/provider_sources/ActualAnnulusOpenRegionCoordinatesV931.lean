import ActualAnnulusFullFamilyGluingV774

set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualAnnulusHalfCoordinatesV772
open CompressionActualAnnulusHalfPolarModelV768
noncomputable section
namespace CompressionActualAnnulusOpenRegionCoordinatesV931

theorem polar_open_region :
    polar '' {p : Circle × Time | 0 < p.2.val ∧ p.2.val < 1} =
      {x : Plane | 1 < ‖x‖ ∧ ‖x‖ < 2} := by
  apply Subset.antisymm
  · rintro x ⟨p,hp,rfl⟩
    rw [mem_setOf_eq,polar_norm]
    exact ⟨by linarith [hp.1],by linarith [hp.2]⟩
  · intro x hx
    let p := coord x hx.1.le hx.2.le
    refine ⟨p,?_,polar_coord x hx.1.le hx.2.le⟩
    change 0 < ‖x‖-1 ∧ ‖x‖-1 < 1
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

theorem half_open_region (k : Fin 2) (p : Circle × Time)
    (hp : 0 < p.2.val ∧ p.2.val < 1) :
    0 < (half k p).2.val ∧ (half k p).2.val < 1 := by
  fin_cases k <;> dsimp [half,halfTime] <;> constructor <;>
    linarith [hp.1,hp.2]

theorem open_middle_decomposition :
    {p : Circle × Time | 0 < p.2.val ∧ p.2.val < 1} =
      range (fun z : Circle => (z,middleTime)) ∪
        ⋃ k : Fin 2, half k '' {p : Circle × Time | 0 < p.2.val ∧ p.2.val < 1} := by
  classical
  apply Subset.antisymm
  · intro p hp
    obtain ⟨k,q,hq⟩ := CompressionActualAnnulusFullFamilyGluingV774.half_cover p
    by_cases hq0 : q.2 = 0
    · left
      exact ⟨q.1,(by rw [← hq,show q = (q.1,0) from Prod.ext rfl hq0,half_core])⟩
    · right
      apply mem_iUnion.mpr
      refine ⟨k,q,⟨?_,?_⟩,hq⟩
      · exact lt_of_le_of_ne q.2.property.1 (by intro h; exact hq0 (Subtype.ext h.symm))
      · rw [← hq] at hp
        fin_cases k <;> dsimp [half,halfTime] at hp <;> linarith [hp.1,hp.2]
  · intro p hp
    rcases hp with ⟨z,rfl⟩ | hp
    · change 0 < (1/2:ℝ) ∧ (1/2:ℝ) < 1
      norm_num
    · obtain ⟨k,q,hq,rfl⟩ := mem_iUnion.mp hp
      exact half_open_region k q hq

#print axioms polar_open_region
#print axioms half_open_region
#print axioms open_middle_decomposition
end CompressionActualAnnulusOpenRegionCoordinatesV931
