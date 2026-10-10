import B1ChartMetricProvider
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Determinant-one isothermal metric identity gives the literal density
leading matrix equal to the identity. -/
theorem native_interior_isothermal_density_algebra_v475
    (A M : Mat2) (ha : A.det = 1) (hm : M.det ≠ 0)
    (lam : ℝ) (hlam : 0 < lam)
    (hi : A⁻¹ = lam • (M.transpose*M)) :
    |M.det|⁻¹ • (M*A*M.transpose) = 1 := by
  have hau : IsUnit A.det := by rw [ha]; exact isUnit_one
  have hmu : IsUnit M.det := isUnit_iff_ne_zero.mpr hm
  have he : lam • (M * A * M.transpose) = 1 := by
    calc
      _ = M * (A * A⁻¹) * M⁻¹ := by
        rw [hi]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
          Matrix.mul_nonsing_inv M hmu, Matrix.mul_one]
      _ = 1 := by rw [Matrix.mul_nonsing_inv A hau, Matrix.mul_one, Matrix.mul_nonsing_inv M hmu]
  have hdetinv : A⁻¹.det = 1 := by
    simpa only [ha, mul_one] using Matrix.det_nonsing_inv_mul_det A hau
  have hh := congrArg Matrix.det hi
  rw [hdetinv, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose] at hh
  have hprod : lam * |M.det| = 1 := by
    have hn : 0 ≤ lam * |M.det| := mul_nonneg hlam.le (abs_nonneg _)
    have hsq : (lam * |M.det|) ^ 2 = 1 := by
      simpa only [Fintype.card_fin, mul_pow, sq_abs, ← pow_two] using hh.symm
    nlinarith
  have hlam_eq : lam = |M.det|⁻¹ := by
    simpa only [one_div] using (eq_div_iff (abs_ne_zero.mpr hm)).mpr hprod
  change |M.det|⁻¹ • (M * A * M.transpose) = 1
  rw [← hlam_eq]
  exact he
#print axioms native_interior_isothermal_density_algebra_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
