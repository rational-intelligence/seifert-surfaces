import A5InteriorChartDerivativeV466

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
open SeifertSurfaces.Foundations
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
universe u

private def reducedPlaneChart (R : CompactOrientedSurface.{0}) (S : A5CompactSmoothCarrier.{u})
    (h : R ≃ₜ S) (p : S) : OpenPartialHomeomorph R ℂ :=
  h.toOpenPartialHomeomorph.trans (a5NativeComplexChart S p)

private theorem reducedPlaneChart_source (R : CompactOrientedSurface.{0}) (S : A5CompactSmoothCarrier.{u})
    (h : R ≃ₜ S) (p : S) (x : R) :
    x ∈ (reducedPlaneChart R S h p).source ↔ h x ∈ (a5NativeComplexChart S p).source := by
  simp [reducedPlaneChart,OpenPartialHomeomorph.trans_source]

def a5TransportedChartSign (R : CompactOrientedSurface.{0}) (S : A5CompactSmoothCarrier.{u})
    (h : R ≃ₜ S) (p : S) (x : (a5NativeComplexChart S p).source) : ℝ :=
  nativeTopologicalChartSign R (reducedPlaneChart R S h p)
    ⟨h.symm x.val,(reducedPlaneChart_source R S h p (h.symm x.val)).mpr
      (by simpa only [h.apply_symm_apply] using x.property)⟩

theorem a5TransportedChartSign_unit (R : CompactOrientedSurface.{0}) (S : A5CompactSmoothCarrier.{u})
    (h : R ≃ₜ S) (p : S) (x : (a5NativeComplexChart S p).source) :
    a5TransportedChartSign R S h p x = 1 ∨ a5TransportedChartSign R S h p x = -1 :=
  nativeTopologicalChartSign_unit _ _ _

theorem a5TransportedChartSign_locally_constant
    (R : CompactOrientedSurface.{0}) (S : A5CompactSmoothCarrier.{u}) (h : R ≃ₜ S) (p : S) :
    IsLocallyConstant (a5TransportedChartSign R S h p) := by
  let g : (a5NativeComplexChart S p).source → (reducedPlaneChart R S h p).source :=
    fun x => ⟨h.symm x.val,(reducedPlaneChart_source R S h p (h.symm x.val)).mpr
      (by simpa only [h.apply_symm_apply] using x.property)⟩
  have hg : Continuous g := (h.symm.continuous.comp continuous_subtype_val).subtype_mk _
  exact (nativeTopologicalChartSign_locally_constant R _).comp_continuous hg

/-- The old topological orientation corrects the determinant of every new interior transition. -/
theorem a5TransportedChartSign_positive_transition
    (R : CompactOrientedSurface.{0}) (S : A5CompactSmoothCarrier.{u}) (h : R ≃ₜ S)
    (p q x : S) (hp : x ∈ (a5NativeComplexChart S p).source)
    (hq : x ∈ (a5NativeComplexChart S q).source) :
    0 < a5TransportedChartSign R S h q ⟨x,hq⟩ *
      a5TransportedChartSign R S h p ⟨x,hp⟩ * (a5TransitionJacobian S p q x).det := by
  let e := a5NativeComplexChart S p
  let f := a5NativeComplexChart S q
  let er := reducedPlaneChart R S h p
  let fr := reducedPlaneChart R S h q
  have hep : h.symm x ∈ er.source := (reducedPlaneChart_source R S h p _).mpr (by simpa using hp)
  have hfp : h.symm x ∈ fr.source := (reducedPlaneChart_source R S h q _).mpr (by simpa using hq)
  obtain ⟨A,_,hder,hdet⟩ := a5_native_complex_transition_derivative S p q x hp hq
  have hmap :
      ((er.trans (Homeomorph.addRight (-er (h.symm x))).toOpenPartialHomeomorph).symm.trans
        (fr.trans (Homeomorph.addRight (-fr (h.symm x))).toOpenPartialHomeomorph) : ℂ → ℂ) =
      ((a5ShiftChart e x).symm.trans (a5ShiftChart f x) : ℂ → ℂ) := by
    funext z
    simp [e,f,er,fr,reducedPlaneChart,a5ShiftChart,OpenPartialHomeomorph.trans_apply,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  have hderR : HasFDerivAt
      ((er.trans (Homeomorph.addRight (-er (h.symm x))).toOpenPartialHomeomorph).symm.trans
        (fr.trans (Homeomorph.addRight (-fr (h.symm x))).toOpenPartialHomeomorph))
      A.toContinuousLinearMap 0 := by
    rw [hmap]
    exact hder
  have hrel := nativeTopologicalChartSign_derivative_comparison R er fr (h.symm x) hep hfp A hderR
  change a5TransportedChartSign R S h q ⟨x,hq⟩ =
    if 0 < LinearMap.det A.toLinearEquiv.toLinearMap
    then a5TransportedChartSign R S h p ⟨x,hp⟩
    else -(a5TransportedChartSign R S h p ⟨x,hp⟩) at hrel
  rw [hdet] at hrel
  have hpn := a5TransportedChartSign_unit R S h p ⟨x,hp⟩
  have hqn := a5TransportedChartSign_unit R S h q ⟨x,hq⟩
  have hdne := a5_transitionJacobian_det_ne_zero S p q x
    ((a5_native_complex_chart_source S p x).mp hp).1
    ((a5_native_complex_chart_source S q x).mp hq).1
  by_cases hdpos : 0 < (a5TransitionJacobian S p q x).det
  · simp only [hdpos,ite_true] at hrel
    rw [hrel]
    rcases hpn with hs|hs <;> rw [hs] <;> nlinarith
  · simp only [hdpos,ite_false] at hrel
    have hdneg : (a5TransitionJacobian S p q x).det < 0 := lt_of_le_of_ne (le_of_not_gt hdpos) hdne
    rw [hrel]
    rcases hpn with hs|hs <;> rw [hs] <;> nlinarith

#print axioms a5TransportedChartSign_positive_transition
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
