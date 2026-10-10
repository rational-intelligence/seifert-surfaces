import AppendixACoordinatesReady
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option autoImplicit false
open scoped ContDiff Topology
open Set Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.A2NativeTests
open SeifertSurfaces.AppendixACoordinates

/-- A rank-two smooth parametrization has an actual smooth local left inverse
obtained by inverting a linear projection of the same parametrization. -/
theorem exists_smooth_local_left_inverse (f : E2 → E3) (U : Set E2)
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (x : E2) (hx : x ∈ U)
    (hinj : Function.Injective (fderiv ℝ f x)) :
    ∃ (V : Set E3) (W : Set E2) (R : E3 → E2), IsOpen V ∧ f x ∈ V ∧
      IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ContDiffOn ℝ ∞ R V ∧
      MapsTo f W V ∧ ∀ y ∈ W, R (f y) = y := by
  obtain ⟨A,hA⟩ := (fderiv ℝ f x).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let P : E3 →L[ℝ] E2 := A.toContinuousLinearMap
  have hPA : P.comp (fderiv ℝ f x) = ContinuousLinearMap.id ℝ E2 := by
    apply ContinuousLinearMap.ext
    intro v
    exact DFunLike.congr_fun hA v
  have hpf : ContDiffOn ℝ ∞ (P ∘ f) U := P.contDiff.comp_contDiffOn hf
  have hder : HasFDerivAt (P ∘ f) (ContinuousLinearEquiv.refl ℝ E2 : E2 →L[ℝ] E2) x := by
    change HasFDerivAt (P ∘ f) (ContinuousLinearMap.id ℝ E2) x
    rw [← hPA]
    exact P.hasFDerivAt.comp x ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt
      (by simp)).hasFDerivAt
  obtain ⟨e,hxe,heU,_,heinv,hemap⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv hpf hU hx hder
  simp only [Function.comp_apply] at hemap
  let V := P ⁻¹' e.target
  let R := e.symm ∘ P
  have hfx : f x ∈ V := by
    change P (f x) ∈ e.target
    rw [← hemap x]
    exact e.map_source hxe
  refine ⟨V,e.source,R,e.open_target.preimage P.continuous,hfx,e.open_source,hxe,heU,
    heinv.comp P.contDiff.contDiffOn (fun _ hz => hz),?_,?_⟩
  · intro y hy
    change P (f y) ∈ e.target
    rw [← hemap y]
    exact e.map_source hy
  · intro y hy
    change e.symm (P (f y)) = y
    rw [← hemap y,e.left_inv hy]

#print axioms exists_smooth_local_left_inverse
end SeifertSurfaces.OriginalEndpoints.A2NativeTests
