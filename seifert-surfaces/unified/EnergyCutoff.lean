import WeakTestExtension
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization
open SeifertSurfaces.QuasilinearLocalization.Helpers

theorem cutoff_for_energy (x₀ : E2) (r : ℝ) (hr : 0 < r) :
    ∃ (η : E2 → ℝ) (D : ℝ), ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Metric.ball x₀ (2 * r) ∧
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ (∀ x ∈ Metric.ball x₀ r, η x = 1) ∧
      0 ≤ D ∧ (∀ x, ‖fderiv ℝ η x‖ ≤ D) ∧ (∀ x, ‖planarGradient η x‖ ≤ D) := by
  let η : ContDiffBump x₀ := ⟨r, 3 * r / 2, hr, by linarith⟩
  obtain ⟨D, hD⟩ := (η.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (η.contDiff.continuous_fderiv (by simp : (∞ : WithTop ℕ∞) ≠ 0))
  refine ⟨η, D, η.contDiff, η.hasCompactSupport, ?_, ?_, ?_, ?_, hD, ?_⟩
  · rw [η.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [η]; linarith)
  · exact fun x => ⟨η.nonneg, η.le_one⟩
  · exact fun x hx => η.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
  · exact (norm_nonneg _).trans (hD x₀)
  · intro x
    have hn := congrArg norm (gradient_dual (η : E2 → ℝ) x)
    simpa using hn.le.trans (hD x)

theorem classical_witness (B : Set E2) (hB : IsOpen B) (v : E2 → ℝ)
    (hC1 : ContDiffOn ℝ 1 v B) (hv : MemLp v 2 (volume.restrict B))
    (hG : MemLp (planarGradient v) 2 (volume.restrict B)) :
    ∃ hw : DeGiorgi.MemW1pWitness 2 v B, hw.weakGrad = planarGradient v := by
  exact ⟨⟨hv, planarGradient v, vector_component_memLp _ _ hG,
    SeifertSurfaces.QuasilinearProviderBridge.Helpers.C1_hasWeakGrad B hB v hC1⟩, rfl⟩

theorem squared_cutoff_test (B : Set E2) (hB : IsOpen B) (v η : E2 → ℝ)
    (hv : DeGiorgi.MemW1pWitness 2 v B)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) (hηB : tsupport η ⊆ B)
    (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (D : ℝ) (hD : 0 ≤ D) (hDη : ∀ x, ‖fderiv ℝ η x‖ ≤ D) :
    DeGiorgi.MemH01 (fun x => η x ^ 2 * v x) B ∧
      ∃ hw : DeGiorgi.MemW1pWitness 2 (fun x => η x ^ 2 * v x) B,
        ∀ x, hw.weakGrad x = η x ^ 2 • hv.weakGrad x +
          (2 * η x * v x) • planarGradient η x := by
  have hη2 : ContDiff ℝ ∞ (fun x => η x ^ 2) := hη.pow 2
  have hη2bound (x : E2) : |η x ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [(hη01 x).1, (hη01 x).2]
  have hη2der (x : E2) : fderiv ℝ (fun y => η y ^ 2) x =
      (2 * η x) • fderiv ℝ η x := by
    simpa using (hη.differentiable (by simp) x).hasFDerivAt.pow 2 |>.fderiv
  have hη2D (x : E2) : ‖fderiv ℝ (fun y => η y ^ 2) x‖ ≤ 2 * D := by
    rw [hη2der, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (hη01 x).1]
    calc
      _ ≤ (2 * 1) * D := mul_le_mul (by nlinarith [(hη01 x).2]) (hDη x)
        (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  let hw := hv.mulSmoothBoundedP (by norm_num) hB hη2 (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : 0 ≤ 2 * D) hη2bound hη2D
  have hcompact : HasCompactSupport (fun x => η x ^ 2 * v x) := by
    have hh := (hηc.mul_right (f' := η)).mul_right (f' := v)
    change HasCompactSupport (fun x => (η x * η x) * v x) at hh
    simpa only [pow_two] using hh
  have hsub : tsupport (fun x => η x ^ 2 * v x) ⊆ B := by
    simpa only [pow_two] using
      (tsupport_mul_subset_left (f := fun x => η x * η x) (g := v)).trans
        (tsupport_mul_subset_left.trans hηB)
  refine ⟨?_, hw, ?_⟩
  · simpa using DeGiorgi.memW01p_of_memW1p_of_tsupport_subset hB
      (by norm_num : (1 : ℝ) < 2)
      (by simpa only [ENNReal.ofReal_ofNat] using hw.memW1p) hcompact hsub
  · intro x
    ext i
    simp only [hw, DeGiorgi.MemW1pWitness.mulSmoothBoundedP, PiLp.add_apply,
      PiLp.smul_apply, PiLp.toLp_apply, hη2der, ContinuousLinearMap.smul_apply,
      smul_eq_mul, gradient_apply, coordinateVector]
    ring

end SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
