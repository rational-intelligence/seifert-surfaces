import CurveComplexGenusTwo.Topology.CompletedJordan
import Mathlib

open Set Topology Schoenflies

/-- The actual full vertical deck orbit has only finitely many fiber events
in any compact support, even though its global event set is infinite. -/
theorem actual_vertical_deck_fiber_events_finite_in_compact
    (G : ℝ → Plane) (T c : ℝ)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (hlf : LocallyFinite (fun j : ℤ => range (fun t => G t+Plane.mk 0 ((j:ℝ)*T))))
    (K : Set Plane) (hK : IsCompact K) :
    (((⋃ j : ℤ, range (fun t => G t+Plane.mk 0 ((j:ℝ)*T))) ∩
      {z : Plane | z 0=c}) ∩ K).Finite := by
  let L := fun j : ℤ => range (fun t => G t+Plane.mk 0 ((j:ℝ)*T))
  let V : Set Plane := {z | z 0=c}
  have hOne (j : ℤ) : (L j ∩ V).Finite := by
    apply (hfinite.image (fun t => G t+Plane.mk 0 ((j:ℝ)*T))).subset
    rintro z ⟨⟨t,rfl⟩,ht⟩
    refine ⟨t,?_,rfl⟩
    change (G t+Plane.mk 0 ((j:ℝ)*T)) 0=c at ht
    simpa [Plane.mk] using ht
  have hJ : {j : ℤ | (L j ∩ K).Nonempty}.Finite := hlf.finite_nonempty_inter_compact hK
  have hAll := hJ.biUnion (fun j _ => (hOne j).inter_of_left K)
  apply hAll.subset
  rintro z ⟨⟨hz,hzV⟩,hzK⟩
  obtain ⟨j,hj⟩ := mem_iUnion.mp hz
  exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨⟨z,hj,hzK⟩,⟨⟨hj,hzV⟩,hzK⟩⟩⟩

#print axioms actual_vertical_deck_fiber_events_finite_in_compact
