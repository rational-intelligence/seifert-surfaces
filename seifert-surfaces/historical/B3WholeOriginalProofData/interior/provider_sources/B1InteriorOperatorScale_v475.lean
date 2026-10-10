import B1LocalFluxClassical_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Exact scalar normalization of a divergence equation.  The induced drift
contains the minus A-gradient-factor term; no second derivative of a chart
enters this identity. -/
theorem native_scalar_normalized_classical_v475
    (A : E2 → Mat2) (B : E2 → E2) (v lam : E2 → ℝ) (x : E2)
    (hsym : ∀ i j : Fin 2, A x i j = A x j i)
    (hlam : DifferentiableAt ℝ lam x)
    (hP : ∀ i : Fin 2, DifferentiableAt ℝ
      (fun y => matrixAction (A y) (planarGradient v y) i) x) :
    classicalL (fun y => lam y • A y)
      (fun y => lam y • B y-matrixAction (A y) (planarGradient lam y))
      (fun _ => 0) v x = lam x * classicalL A B (fun _ => 0) v x := by
  let P : E2 → E2 := fun y => matrixAction (A y) (planarGradient v y)
  have heq (i : Fin 2) :
      (fun y => matrixAction (lam y • A y) (planarGradient v y) i) =
        fun y => lam y * P y i := by
    funext y
    simp [P,matrixAction,Fin.sum_univ_two]
    ring
  have hd (i : Fin 2) :
      fderiv ℝ (fun y => matrixAction (lam y • A y) (planarGradient v y) i) x
        (coordinateVector 2 i) =
      lam x * fderiv ℝ (fun y => P y i) x (coordinateVector 2 i)+
        P x i * fderiv ℝ lam x (coordinateVector 2 i) := by
    rw [heq,fderiv_fun_mul hlam (hP i)]
    simp [P]
  have hg (i : Fin 2) : planarGradient lam x i = fderiv ℝ lam x (coordinateVector 2 i) := by
    fin_cases i <;> simp [planarGradient,coordinateVector,Fin.sum_univ_two]
  have h01 := hsym 0 1
  unfold classicalL
  simp only [hd,zero_mul,add_zero,Fin.sum_univ_two]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,
    Pi.star_apply,star_trivial,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  simp only [← hg]
  simp [P,matrixAction,Fin.sum_univ_two,h01]
  <;> ring

#print axioms native_scalar_normalized_classical_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
