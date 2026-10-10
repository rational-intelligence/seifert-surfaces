import SurfaceInvariants
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.LinearAlgebra.Determinant

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Module
open SeifertSurfaces.Foundations
namespace SeifertSurfaces.GenusLinking
noncomputable section

private def actualChartFrame (S : CompactOrientedSurface.{0}) (p x : S) :
    Fin 2 → TangentSpace (𝓡∂ 2) x :=
  fun k => mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2)
    (extChartAt (𝓡∂ 2) p).symm (extChartAt (𝓡∂ 2) p).target
    (extChartAt (𝓡∂ 2) p x)
    ((tangentSpaceCastModel 𝓘(ℝ, Euc 2)
      (extChartAt (𝓡∂ 2) p x)).symm (EuclideanSpace.single k 1))

private def actualChartCoefficient (S : CompactOrientedSurface.{0}) (p x : S) : ℝ :=
  S.orientation.form x (actualChartFrame S p x)

private def actualTransitionJacobian (S : CompactOrientedSurface.{0}) (p q x : S) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => fderivWithin ℝ
    ((extChartAt (𝓡∂ 2) q) ∘ (extChartAt (𝓡∂ 2) p).symm)
    (extChartAt (𝓡∂ 2) p).target (extChartAt (𝓡∂ 2) p x)
    (EuclideanSpace.single j 1) i

private theorem actual_chart_frame_inverse
    (S : CompactOrientedSurface.{0}) (p x : S)
    (hx : x ∈ (extChartAt (𝓡∂ 2) p).source) :
    (mfderiv (𝓡∂ 2) 𝓘(ℝ, Euc 2) (extChartAt (𝓡∂ 2) p) x) ∘L
      (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2)
        (extChartAt (𝓡∂ 2) p).symm (extChartAt (𝓡∂ 2) p).target
        (extChartAt (𝓡∂ 2) p x)) = ContinuousLinearMap.id ℝ (Euc 2) := by
  have ht := (extChartAt (𝓡∂ 2) p).map_source hx
  have hd := (mdifferentiableWithinAt_extChartAt_symm ht).mfderivWithin_mono
    (((uniqueDiffOn_extChartAt_target (I := 𝓡∂ 2) p) _ ht).uniqueMDiffWithinAt)
    (extChartAt_target_subset_range (I := 𝓡∂ 2) p)
  rw [hd]
  exact mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' hx

private theorem actual_chart_frame_transition
    (S : CompactOrientedSurface.{0}) (p q x : S)
    (hp : x ∈ (extChartAt (𝓡∂ 2) p).source)
    (hq : x ∈ (extChartAt (𝓡∂ 2) q).source) :
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.det
      (fun k => (mfderiv (𝓡∂ 2) 𝓘(ℝ, Euc 2)
        (extChartAt (𝓡∂ 2) q) x) (actualChartFrame S p x k)) =
        (actualTransitionJacobian S p q x).det := by
  have ht := (extChartAt (𝓡∂ 2) p).map_source hp
  have hd : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡∂ 2)
      (extChartAt (𝓡∂ 2) p).symm (extChartAt (𝓡∂ 2) p).target
      (extChartAt (𝓡∂ 2) p x) :=
    (contMDiffWithinAt_extChartAt_symm_target p ht
      (n := (∞ : ℕ∞ω))).mdifferentiableWithinAt (by simp)
  have hdu := (uniqueDiffOn_extChartAt_target p _ ht).uniqueMDiffWithinAt
  have he := (extChartAt (𝓡∂ 2) p).left_inv hp
  have hg : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ, Euc 2)
      (extChartAt (𝓡∂ 2) q)
      ((extChartAt (𝓡∂ 2) p).symm (extChartAt (𝓡∂ 2) p x)) := by
    rw [he]
    exact mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hq)
  have hc := mfderiv_comp_mfderivWithin (extChartAt (𝓡∂ 2) p x) hg hd hdu
  rw [he, mfderivWithin_eq_fderivWithin] at hc
  rw [Module.Basis.det_apply]
  congr 1
  ext a b
  simp only [Module.Basis.toMatrix_apply]
  simp only [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  exact congrArg (fun L : Euc 2 →L[ℝ] Euc 2 =>
    (L (EuclideanSpace.single b (1 : ℝ))).ofLp a) hc.symm

private theorem actual_orientation_coefficient_transition
    (S : CompactOrientedSurface.{0}) (p q x : S)
    (hp : x ∈ (extChartAt (𝓡∂ 2) p).source)
    (hq : x ∈ (extChartAt (𝓡∂ 2) q).source) :
    actualChartCoefficient S p x = actualChartCoefficient S q x *
      (actualTransitionJacobian S p q x).det := by
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  let A : Euc 2 →L[ℝ] Euc 2 :=
    mfderiv (𝓡∂ 2) 𝓘(ℝ, Euc 2) (extChartAt (𝓡∂ 2) q) x
  let B : Euc 2 →L[ℝ] Euc 2 := mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2)
    (extChartAt (𝓡∂ 2) q).symm (extChartAt (𝓡∂ 2) q).target
    (extChartAt (𝓡∂ 2) q x)
  let vol : Euc 2 [⋀^Fin 2]→ₗ[ℝ] ℝ := S.orientation.form x
  have hinv : A ∘L B = ContinuousLinearMap.id ℝ (Euc 2) :=
    actual_chart_frame_inverse S q x hq
  have hd : LinearMap.det A.toLinearMap * LinearMap.det B.toLinearMap = 1 := by
    rw [← LinearMap.det_comp]
    change LinearMap.det (A ∘L B).toLinearMap = 1
    rw [hinv]
    exact LinearMap.det_id
  have hcq : actualChartCoefficient S q x = vol b * LinearMap.det B.toLinearMap := by
    have h := congrArg (fun f : Euc 2 [⋀^Fin 2]→ₗ[ℝ] ℝ =>
      f (B.toLinearMap ∘ b)) (vol.eq_smul_basis_det b)
    simp only [AlternatingMap.smul_apply, smul_eq_mul] at h
    have hdet := b.det_comp B.toLinearMap (b : Fin 2 → Euc 2)
    rw [Module.Basis.det_self, mul_one] at hdet
    rw [hdet] at h
    have he : actualChartFrame S q x = B.toLinearMap ∘ b := by
      funext k
      change B (EuclideanSpace.single k 1) = B (b k)
      rw [show b k = EuclideanSpace.single k 1 from
        EuclideanSpace.basisFun_apply _ _ _]
    change vol (actualChartFrame S q x) = _
    rw [he]
    exact h
  have hcp : actualChartCoefficient S p x = vol b * b.det (actualChartFrame S p x) := by
    exact congrArg (fun f : Euc 2 [⋀^Fin 2]→ₗ[ℝ] ℝ =>
      f (actualChartFrame S p x)) (vol.eq_smul_basis_det b)
  have ht := actual_chart_frame_transition S p q x hp hq
  change b.det (A.toLinearMap ∘ actualChartFrame S p x) = _ at ht
  rw [Module.Basis.det_comp] at ht
  rw [hcp, hcq, ← ht]
  have hd' : LinearMap.det B.toLinearMap * LinearMap.det A.toLinearMap = 1 := by
    simpa only [mul_comm] using hd
  calc
    vol b * b.det (actualChartFrame S p x) =
      (vol b * (LinearMap.det B.toLinearMap * LinearMap.det A.toLinearMap)) *
        b.det (actualChartFrame S p x) := by rw [hd', mul_one]
    _ = _ := by ring

private theorem actual_chart_coefficient_ne_zero
    (S : CompactOrientedSurface.{0}) (p x : S)
    (hx : x ∈ (extChartAt (𝓡∂ 2) p).source) :
    actualChartCoefficient S p x ≠ 0 := by
  have ht := (extChartAt (𝓡∂ 2) p).map_source hx
  have hd := (mdifferentiableWithinAt_extChartAt_symm ht).mfderivWithin_mono
    (((uniqueDiffOn_extChartAt_target (I := 𝓡∂ 2) p) _ ht).uniqueMDiffWithinAt)
    (extChartAt_target_subset_range (I := 𝓡∂ 2) p)
  obtain ⟨e, he⟩ := isInvertible_mfderivWithin_extChartAt_symm ht
  have hb := (S.orientation.form x).map_basis_ne_zero_iff
    ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.map e.toLinearEquiv)
  have h := hb.mpr (S.orientation.nowhere_zero x)
  change S.orientation.form x
    (fun i => mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2)
      (extChartAt (𝓡∂ 2) p).symm (extChartAt (𝓡∂ 2) p).target
      (extChartAt (𝓡∂ 2) p x) (EuclideanSpace.single i 1)) ≠ 0
  rw [hd, ← he]
  convert h using 2 <;> try rfl
  funext i
  change e (EuclideanSpace.single i 1) = e ((EuclideanSpace.basisFun (Fin 2) ℝ) i)
  rw [EuclideanSpace.basisFun_apply]

private theorem actual_transition_det_eq_coefficient_ratio
    (S : CompactOrientedSurface.{0}) (p q x : S)
    (hp : x ∈ (extChartAt (𝓡∂ 2) p).source)
    (hq : x ∈ (extChartAt (𝓡∂ 2) q).source) :
    (actualTransitionJacobian S p q x).det =
      actualChartCoefficient S p x / actualChartCoefficient S q x := by
  apply (eq_div_iff (actual_chart_coefficient_ne_zero S q x hq)).mpr
  simpa only [mul_comm] using (actual_orientation_coefficient_transition S p q x hp hq).symm

private theorem actual_transition_det_ne_zero
    (S : CompactOrientedSurface.{0}) (p q x : S)
    (hp : x ∈ (extChartAt (𝓡∂ 2) p).source)
    (hq : x ∈ (extChartAt (𝓡∂ 2) q).source) :
    (actualTransitionJacobian S p q x).det ≠ 0 := by
  rw [actual_transition_det_eq_coefficient_ratio S p q x hp hq]
  exact div_ne_zero (actual_chart_coefficient_ne_zero S p x hp)
    (actual_chart_coefficient_ne_zero S q x hq)

private theorem actual_transition_det_pos_iff_coefficient_sign
    (S : CompactOrientedSurface.{0}) (p q x : S)
    (hp : x ∈ (extChartAt (𝓡∂ 2) p).source)
    (hq : x ∈ (extChartAt (𝓡∂ 2) q).source) :
    0 < (actualTransitionJacobian S p q x).det ↔
      (0 < actualChartCoefficient S p x ↔ 0 < actualChartCoefficient S q x) := by
  rw [actual_transition_det_eq_coefficient_ratio S p q x hp hq]
  have hp' := actual_chart_coefficient_ne_zero S p x hp
  have hq' := actual_chart_coefficient_ne_zero S q x hq
  rcases lt_or_gt_of_ne hp' with hp' | hp'
  · rcases lt_or_gt_of_ne hq' with hq' | hq'
    · simp [div_pos_iff, hp', hq', not_lt_of_ge hp'.le, not_lt_of_ge hq'.le]
    · simp [div_pos_iff, hp', hq', not_lt_of_ge hp'.le, not_lt_of_ge hq'.le]
  · rcases lt_or_gt_of_ne hq' with hq' | hq'
    · simp [div_pos_iff, hp', hq', not_lt_of_ge hp'.le, not_lt_of_ge hq'.le]
    · simp [div_pos_iff, hp', hq', not_lt_of_ge hp'.le, not_lt_of_ge hq'.le]

#print axioms actual_orientation_coefficient_transition
#print axioms actual_chart_coefficient_ne_zero
#print axioms actual_transition_det_pos_iff_coefficient_sign
end
end SeifertSurfaces.GenusLinking
