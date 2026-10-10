import A5UniverseOrientationProducerV466
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology
open scoped Manifold ContDiff
open SeifertSurfaces.Foundations
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 2) X]
  [IsManifold (𝓡∂ 2) ∞ X]

/-- Derivatives of full halfspace coordinate transitions are invertible, including at boundary points. -/
theorem a5_transition_fderivWithin_invertible (p q x : X)
    (hp : x ∈ (extChartAt (𝓡∂ 2) p).source)
    (hq : x ∈ (extChartAt (𝓡∂ 2) q).source) :
    (fderivWithin ℝ ((extChartAt (𝓡∂ 2) q) ∘ (extChartAt (𝓡∂ 2) p).symm)
      (extChartAt (𝓡∂ 2) p).target (extChartAt (𝓡∂ 2) p x)).IsInvertible := by
  let cp := extChartAt (𝓡∂ 2) p
  let cq := extChartAt (𝓡∂ 2) q
  let y := cp x
  have ht : y ∈ cp.target := cp.map_source hp
  have hdu : UniqueMDiffWithinAt 𝓘(ℝ,Euc 2) cp.target y :=
    (uniqueDiffOn_extChartAt_target p y ht).uniqueMDiffWithinAt
  have hd := (mdifferentiableWithinAt_extChartAt_symm ht).mfderivWithin_mono hdu
    (extChartAt_target_subset_range p)
  have hBInv : (mfderivWithin 𝓘(ℝ,Euc 2) (𝓡∂ 2) cp.symm cp.target y).IsInvertible := by
    rw [hd]
    exact isInvertible_mfderivWithin_extChartAt_symm ht
  obtain ⟨B,hB⟩ := hBInv
  obtain ⟨D,hD⟩ := isInvertible_mfderiv_extChartAt hq
  let A : Euc 2 ≃L[ℝ] Euc 2 := B.trans D
  have hBs : MDifferentiableWithinAt 𝓘(ℝ,Euc 2) (𝓡∂ 2) cp.symm cp.target y :=
    mdifferentiableOn_extChartAt_symm y ht
  have hDs : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ,Euc 2) cq x := by
    apply mdifferentiableAt_extChartAt
    simpa only [extChartAt_source] using hq
  have hDc : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ,Euc 2) cq (cp.symm y) := by
    rwa [cp.left_inv hp]
  have hchain := hDc.hasMFDerivAt.comp_hasMFDerivWithinAt y hBs.hasMFDerivWithinAt
  have hder : HasFDerivWithinAt (cq ∘ cp.symm) A.toContinuousLinearMap cp.target y := by
    have hc := hchain.hasFDerivWithinAt
    rw [cp.left_inv hp,← hB,← hD] at hc
    exact hc
  exact ⟨A,hder.fderivWithin (uniqueDiffOn_extChartAt_target p y ht) |>.symm⟩

theorem a5_transitionJacobian_det_ne_zero (S : A5CompactSmoothCarrier.{u}) (p q x : S)
    (hp : x ∈ (extChartAt (𝓡∂ 2) p).source)
    (hq : x ∈ (extChartAt (𝓡∂ 2) q).source) :
    (a5TransitionJacobian S p q x).det ≠ 0 := by
  obtain ⟨A,hA⟩ := a5_transition_fderivWithin_invertible p q x hp hq
  have hm : (a5TransitionJacobian S p q x).det = LinearMap.det A.toLinearEquiv.toLinearMap := by
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
    congr 1
    ext i j
    simp only [a5TransitionJacobian,LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply,EuclideanSpace.basisFun_repr]
    rw [←hA]
    rw [show (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis j=EuclideanSpace.single j 1 from
      EuclideanSpace.basisFun_apply _ _ _]
    rfl
  rw [hm]
  intro hz
  have hk : A.toLinearMap.ker = ⊥ := LinearMap.ker_eq_bot.mpr A.injective
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) hk

#print axioms a5_transitionJacobian_det_ne_zero
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
