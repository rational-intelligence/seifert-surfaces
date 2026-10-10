import InitialActualArcPath_v411

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates

private theorem native_circle_derivative_v445 (t : ℝ) :
    HasDerivAt unitCircleParameter
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![-Real.sin t, Real.cos t]) t := by
  have hp : HasDerivAt (fun u : ℝ => ![Real.cos u, Real.sin u])
      ![-Real.sin t, Real.cos t] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact Real.hasDerivAt_cos t
    · exact Real.hasDerivAt_sin t
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt t hp

private theorem native_smooth_circle_chain_v445
    (phi : E2 → ℝ) (hphi : ContDiff ℝ ∞ phi) (x : E2) (q t : ℝ) :
    let grad : E2 → E2 := fun z =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun j => fderiv ℝ phi z (coordinateVector 2 j))
    let J : E2 → E2 := fun v =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
    deriv (fun u => phi (x + q • unitCircleParameter u)) t =
      q * inner ℝ (grad (x + q • unitCircleParameter t)) (J (unitCircleParameter t)) := by
  dsimp only
  let z := x + q • unitCircleParameter t
  let tangent : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-Real.sin t, Real.cos t]
  have hc : HasDerivAt (fun u => x + q • unitCircleParameter u) (q • tangent) t :=
    ((native_circle_derivative_v445 t).const_smul q).const_add x
  have hchain := (hphi.differentiable (by simp) z).hasFDerivAt.comp_hasDerivAt t hc
  change HasDerivAt (fun u => phi (x + q • unitCircleParameter u))
    (fderiv ℝ phi z (q • tangent)) t at hchain
  rw [hchain.deriv]
  have ht : tangent = (-Real.sin t) • coordinateVector 2 0 +
      Real.cos t • coordinateVector 2 1 := by
    ext i
    fin_cases i <;> simp [tangent, coordinateVector, EuclideanSpace.single]
  rw [ht]
  dsimp [z]
  simp [map_smul, map_add, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_two, unitCircleParameter, smul_eq_mul]
  ring_nf

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
