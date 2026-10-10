import A7PlaneAlgebraV464
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.AppendixACoordinates

def standardPlaneMap : E2 × ℝ →L[ℝ] E3 :=
  ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).comp (ContinuousLinearMap.fst ℝ E2 ℝ)).smulRight
    (EuclideanSpace.single 0 1) +
  ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).comp (ContinuousLinearMap.fst ℝ E2 ℝ)).smulRight
    (EuclideanSpace.single 1 1) +
  (ContinuousLinearMap.snd ℝ E2 ℝ).smulRight (EuclideanSpace.single 2 1)

theorem standardPlaneMap_zero (q : E2 × ℝ) : standardPlaneMap q 0 = q.1 0 := by
  simp [standardPlaneMap,PiLp.add_apply,PiLp.smul_apply,EuclideanSpace.single]
theorem standardPlaneMap_one (q : E2 × ℝ) : standardPlaneMap q 1 = q.1 1 := by
  simp [standardPlaneMap,PiLp.add_apply,PiLp.smul_apply,EuclideanSpace.single]
theorem standardPlaneMap_two (q : E2 × ℝ) : standardPlaneMap q 2 = q.2 := by
  simp [standardPlaneMap,PiLp.add_apply,PiLp.smul_apply,EuclideanSpace.single]

theorem standardPlaneMap_injective : Injective standardPlaneMap := by
  intro q r hqr
  have h0 := congrArg (fun z : E3 => z 0) hqr
  have h1 := congrArg (fun z : E3 => z 1) hqr
  have h2 := congrArg (fun z : E3 => z 2) hqr
  rw [standardPlaneMap_zero,standardPlaneMap_zero] at h0
  rw [standardPlaneMap_one,standardPlaneMap_one] at h1
  rw [standardPlaneMap_two,standardPlaneMap_two] at h2
  apply Prod.ext
  · ext i
    fin_cases i
    · exact h0
    · exact h1
  · exact h2

def standardPlaneEquiv : (E2 × ℝ) ≃L[ℝ] E3 :=
  (standardPlaneMap.toLinearMap.linearEquivOfInjective standardPlaneMap_injective
    (by simp [E2,E3])).toContinuousLinearEquiv

theorem standardPlaneEquiv_zero (q : E2 × ℝ) : standardPlaneEquiv q 0 = q.1 0 :=
  standardPlaneMap_zero q

end SeifertSurfaces.OriginalEndpoints.A7Support
