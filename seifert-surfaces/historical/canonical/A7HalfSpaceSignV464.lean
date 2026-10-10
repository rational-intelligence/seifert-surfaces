import EndpointGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.AppendixACoordinates

def boundaryProjection : E2 →L[ℝ] E2 :=
  ContinuousLinearMap.id ℝ E2 -
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).smulRight (EuclideanSpace.single 0 1)

theorem boundaryProjection_zero (z : E2) : boundaryProjection z 0 = 0 := by
  simp [boundaryProjection,EuclideanSpace.single,PiLp.sub_apply,PiLp.smul_apply]

theorem boundaryProjection_fix {z : E2} (hz : z 0 = 0) : boundaryProjection z = z := by
  simp [boundaryProjection,hz]

theorem boundaryProjection_difference (z : E2) :
    z - boundaryProjection z = z 0 • EuclideanSpace.single 0 (1 : ℝ) := by
  simp only [boundaryProjection,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,EuclideanSpace.proj,PiLp.proj_apply,sub_sub_cancel]

theorem halfspace_sign_of_strict_derivative {q : E2 → ℝ} {a : E2} (ha : a 0 = 0)
    {c : ℝ} (hc : 0 < c)
    (hq : HasStrictFDerivAt q (c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) a)
    (hb : ∀ᶠ z : E2 in 𝓝 a, z 0 = 0 → q z = 0) :
    ∀ᶠ z : E2 in 𝓝 a, 0 ≤ q z ↔ 0 ≤ z 0 := by
  have hpa : boundaryProjection a = a := boundaryProjection_fix ha
  have hp : Tendsto boundaryProjection (𝓝 a) (𝓝 a) := by
    simpa only [hpa] using boundaryProjection.continuous.continuousAt (x := a) |>.tendsto
  have ht : Tendsto (fun z : E2 => (z,boundaryProjection z)) (𝓝 a) (𝓝 (a,a)) :=
    tendsto_id.prodMk_nhds hp
  have hbound := ht.eventually (hq.isLittleO.bound (half_pos hc))
  filter_upwards [hbound,hp.eventually hb] with z hz hzero
  have hqzero : q (boundaryProjection z) = 0 := hzero (boundaryProjection_zero z)
  have hnorm : ‖z - boundaryProjection z‖ = |z 0| := by
    rw [boundaryProjection_difference,norm_smul]
    simp [PiLp.norm_single,Real.norm_eq_abs]
  have hbnd : |q z - c * z 0| ≤ c / 2 * |z 0| := by
    simpa only [hqzero,sub_zero,ContinuousLinearMap.smul_apply,EuclideanSpace.proj,
      PiLp.proj_apply,smul_eq_mul,PiLp.sub_apply,boundaryProjection_zero,hnorm,Real.norm_eq_abs] using hz
  constructor
  · intro hqz
    by_contra hneg
    have hneg' : z 0 < 0 := lt_of_not_ge hneg
    rw [abs_of_neg hneg'] at hbnd
    have hhi := le_abs_self (q z - c * z 0)
    nlinarith
  · intro hz0
    rw [abs_of_nonneg hz0] at hbnd
    have hlo := neg_abs_le (q z - c * z 0)
    nlinarith

end SeifertSurfaces.OriginalEndpoints.A7Support
