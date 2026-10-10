import B1ActualAreaLocalization_v475

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations

theorem metric_gram_density_comp_v475
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    (B : F → F → ℝ)
    (hadd₁ : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul₁ : ∀ (a : ℝ) x z, B (a • x) z = a * B x z)
    (hadd₂ : ∀ x y z, B x (y + z) = B x y + B x z)
    (hsmul₂ : ∀ (a : ℝ) x z, B x (a • z) = a * B x z)
    (d : Euc 2 →ₗ[ℝ] F) (A : Euc 2 →ₗ[ℝ] Euc 2) :
    Real.sqrt (Matrix.det (fun i j : Fin 2 =>
      B ((d.comp A) (coordinateVector 2 i)) ((d.comp A) (coordinateVector 2 j)))) =
      |A.det| * Real.sqrt (Matrix.det (fun i j : Fin 2 =>
        B (d (coordinateVector 2 i)) (d (coordinateVector 2 j)))) := by
  let G : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    B (d (coordinateVector 2 i)) (d (coordinateVector 2 j))
  let C : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    B ((d.comp A) (coordinateVector 2 i)) ((d.comp A) (coordinateVector 2 j))
  let P := LinearMap.toMatrix ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)
    ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis) A
  have hP (i j : Fin 2) : P i j = (A (coordinateVector 2 j)) i := by
    simp [P,LinearMap.toMatrix_apply,coordinateVector]
  have hexpand (v : Euc 2) : v = ∑ k : Fin 2, v k • coordinateVector 2 k := by
    ext i
    fin_cases i <;> simp [coordinateVector, EuclideanSpace.single, PiLp.single_apply,
      Fin.sum_univ_two]
  have hdi (i : Fin 2) : d (A (coordinateVector 2 i)) =
      ∑ k : Fin 2, (A (coordinateVector 2 i)) k • d (coordinateVector 2 k) := by
    calc
      d (A (coordinateVector 2 i)) = d (∑ k : Fin 2, (A (coordinateVector 2 i)) k • coordinateVector 2 k) := congrArg d (hexpand _)
      _ = _ := by simp only [map_sum, map_smul]
  have hC : C = P.transpose * G * P := by
    ext i j
    change B (d (A (coordinateVector 2 i))) (d (A (coordinateVector 2 j))) =
      ∑ k : Fin 2, (∑ l : Fin 2, P l i * G l k) * P k j
    rw [hdi i, hdi j]
    simp only [Fin.sum_univ_two, hP, G, hadd₁, hsmul₁, hadd₂, hsmul₂]
    ring
  have hPdet : P.det = A.det := LinearMap.det_toMatrix _ A
  have hdet : C.det = (A.det)^2 * G.det := by
    rw [hC, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,hPdet]
    ring
  have hsqrt : Real.sqrt C.det = |A.det| * Real.sqrt G.det := by
    rw [hdet]
    rw [Real.sqrt_mul (sq_nonneg (A.det))]
    rw [Real.sqrt_sq_eq_abs]
  exact hsqrt

#print axioms metric_gram_density_comp_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
