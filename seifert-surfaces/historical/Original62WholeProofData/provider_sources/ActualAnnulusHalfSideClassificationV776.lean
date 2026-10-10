import ActualAnnulusFullFamilyGluingV774
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualAnnulusHalfCoordinatesV772
open CompressionActualAnnulusFullFamilyGluingV774
noncomputable section
namespace CompressionActualAnnulusHalfSideClassificationV776

theorem half_avoids_core
    (β : C(Circle × Time,Circle × Time)) (hβ : IsEmbedding β)
    (hcore : ∀ z,β (z,middleTime) = (z,middleTime))
    (k : Fin 2) (z : Circle) (t : Time) (ht : t ≠ 0) :
    (β (half k (z,t))).2.val ≠ 1/2 := by
  intro he
  have ht' : (β (half k (z,t))).2 = middleTime := Subtype.ext he
  have hp : β (half k (z,t)) = ((β (half k (z,t))).1,middleTime) := Prod.ext rfl ht'
  have hh : half k (z,t) = half k ((β (half k (z,t))).1,0) :=
    hβ.injective (hp.trans (hcore _).symm) |>.trans (half_core k _).symm
  have h := half_injective k hh
  exact ht (congrArg (fun p : Circle × Time => p.2) h)

/-- Each connected half chooses one side; this choice is a derived fact,
    not a premise asserting that arbitrary original labels have the right side. -/
theorem half_has_one_side
    (β : C(Circle × Time,Circle × Time)) (hβ : IsEmbedding β)
    (hcore : ∀ z,β (z,middleTime) = (z,middleTime)) (k : Fin 2) :
    ∃ l : Fin 2,∀ p,side l (β (half k p)) := by
  let S : Set (Circle × Time) := Set.univ ×ˢ Set.Ioi (0:Time)
  have hS : IsPreconnected S := isPreconnected_univ.prod isPreconnected_Ioi
  let f : Circle × Time → ℝ := fun p => (β (half k p)).2.val
  have hfc : Continuous f := (β.continuous.comp (half_continuous k)).snd.subtype_val
  have hne (p : Circle × Time) (hp : p ∈ S) : f p ≠ 1/2 :=
    half_avoids_core β hβ hcore k p.1 p.2 (ne_of_gt hp.2)
  obtain hpos | hneg := hS.mapsTo_Ioi_or_Iio hfc.continuousOn hne
  · refine ⟨1,?_⟩
    intro p
    by_cases hp : p.2 = 0
    · have he : p = (p.1,0) := Prod.ext rfl hp
      rw [he,half_core,hcore]
      change (1/2:ℝ) ≤ 1/2
      rfl
    · exact (hpos ⟨mem_univ _,lt_of_le_of_ne p.2.property.1
        (by intro he; exact hp (Subtype.ext he.symm))⟩).le
  · refine ⟨0,?_⟩
    intro p
    by_cases hp : p.2 = 0
    · have he : p = (p.1,0) := Prod.ext rfl hp
      rw [he,half_core,hcore]
      change (1/2:ℝ) ≤ 1/2
      rfl
    · exact (hneg ⟨mem_univ _,lt_of_le_of_ne p.2.property.1
        (by intro he; exact hp (Subtype.ext he.symm))⟩).le

end CompressionActualAnnulusHalfSideClassificationV776
