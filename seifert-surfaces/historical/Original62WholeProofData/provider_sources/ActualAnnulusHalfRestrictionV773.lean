import ActualAnnulusHalfCoordinatesV772

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualAnnulusHalfCoordinatesV772
noncomputable section
namespace CompressionActualAnnulusHalfRestrictionV773

/-- Restrict a literal core-fixed annulus embedding to one preserved half,
    retaining every point and the strict separation from the core. -/
theorem annulus_half_restriction
    (β : C(Circle × Time,Circle × Time)) (hβ : IsEmbedding β)
    (hcore : ∀ z,β (z,middleTime) = (z,middleTime))
    (k : Fin 2) (hside : ∀ p,side k (β (half k p))) :
    ∃ βh : C(Circle × Time,Circle × Time),
      (∀ p,half k (βh p) = β (half k p)) ∧ IsEmbedding βh ∧
      (∀ z,βh (z,0) = (z,0)) ∧
      ∀ z t,t ≠ 0 → 0 < (βh (z,t)).2.val := by
  let f : Circle × Time → Circle × Time := fun p => unhalf k (β (half k p)) (hside p)
  have hfhalf (p : Circle × Time) : half k (f p) = β (half k p) := half_unhalf _ _ _
  have hcomp : Continuous (fun p : Circle × Time => β (half k p)) :=
    β.continuous.comp (half_continuous k)
  have hfc : Continuous f := by
    apply Continuous.prodMk
    · exact hcomp.fst
    · apply Continuous.subtype_mk
      fin_cases k
      · exact continuous_const.sub (continuous_const.mul hcomp.snd.subtype_val)
      · exact (continuous_const.mul hcomp.snd.subtype_val).sub continuous_const
  have hfinj : Function.Injective f := by
    intro p q he
    have hh : β (half k p) = β (half k q) :=
      (hfhalf p).symm.trans ((congrArg (half k) he).trans (hfhalf q))
    exact half_injective k (hβ.injective hh)
  have hfcore (z : Circle) : f (z,0) = (z,0) := by
    apply half_injective k
    rw [hfhalf,half_core,hcore]
  refine ⟨⟨f,hfc⟩,hfhalf,(hfc.isClosedEmbedding hfinj).isEmbedding,hfcore,?_⟩
  intro z t ht
  change 0 < (f (z,t)).2.val
  have hn : (f (z,t)).2 ≠ 0 := by
    intro he
    have hp : f (z,t) = ((f (z,t)).1,0) := Prod.ext rfl he
    have hh : (z,t) = ((f (z,t)).1,0) := hfinj (hp.trans (hfcore _).symm)
    exact ht (congrArg (fun p : Circle × Time => p.2) hh)
  have hv : (f (z,t)).2.val ≠ 0 := by
    intro he
    exact hn (Subtype.ext he)
  exact lt_of_le_of_ne (f (z,t)).2.property.1 hv.symm

end CompressionActualAnnulusHalfRestrictionV773
