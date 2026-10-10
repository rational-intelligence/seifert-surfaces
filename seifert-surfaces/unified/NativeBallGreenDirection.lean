import NativeBallH1Extension

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem vector_coordinate_expansion (v : E2) :
    v = v 0 • coordinateVector 2 0 + v 1 • coordinateVector 2 1 := by
  ext i
  fin_cases i <;> simp [coordinateVector, EuclideanSpace.single]

theorem inner_coordinate (v w : E2) : inner ℝ v w = v 0 * w 0 + v 1 * w 1 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, mul_comm]

theorem inner_coordinateVector (v : E2) (j : Fin 2) :
    inner ℝ v (coordinateVector 2 j) = v j := by
  fin_cases j <;> simp [inner_coordinate, coordinateVector, EuclideanSpace.single]

theorem scalarCone_green_direction (x : E2) (q k : ℝ) (hq : 0 < q) (g : ℝ → ℝ)
    (hg : Periodic g (2 * Real.pi)) (hgc : Continuous g)
    (hga : AbsolutelyContinuousOnInterval g (-Real.pi) Real.pi)
    (psi : E2 → ℝ) (hs : ContDiff ℝ ∞ psi) (v : E2) :
    IntegrableOn (fun z => scalarCone x q k g z * fderiv ℝ psi z v +
      inner ℝ (scalarConeGrad x q g z) v * psi z) (Metric.ball x q) ∧
    IntegrableOn (fun t => (k + g t) * psi (x + q • unitCircleParameter t) *
      inner ℝ (unitCircleParameter t) v) (Icc (-Real.pi) Real.pi) ∧
    (∫ z in Metric.ball x q,
      scalarCone x q k g z * fderiv ℝ psi z v +
        inner ℝ (scalarConeGrad x q g z) v * psi z) =
      q * ∫ t in Icc (-Real.pi) Real.pi,
        (k + g t) * psi (x + q • unitCircleParameter t) *
          inner ℝ (unitCircleParameter t) v := by
  let H (j : Fin 2) (z : E2) := scalarCone x q k g z * fderiv ℝ psi z (coordinateVector 2 j) +
    scalarConeGrad x q g z j * psi z
  let T (j : Fin 2) (t : ℝ) := (k + g t) * psi (x + q • unitCircleParameter t) * unitCircleParameter t j
  have h0 := scalarCone_green x q k hq g hg hgc hga psi hs 0
  have h1 := scalarCone_green x q k hq g hg hgc hga psi hs 1
  have hH : (fun z => scalarCone x q k g z * fderiv ℝ psi z v +
      inner ℝ (scalarConeGrad x q g z) v * psi z) =
      (fun z => v 0 * H 0 z + v 1 * H 1 z) := by
    funext z
    have he : fderiv ℝ psi z v =
        v 0 * fderiv ℝ psi z (coordinateVector 2 0) +
        v 1 * fderiv ℝ psi z (coordinateVector 2 1) := by
      conv_lhs => rw [vector_coordinate_expansion v]
      simp
    rw [he, inner_coordinate]
    dsimp [H]
    ring
  have hT : (fun t => (k + g t) * psi (x + q • unitCircleParameter t) *
      inner ℝ (unitCircleParameter t) v) = (fun t => v 0 * T 0 t + v 1 * T 1 t) := by
    funext t
    rw [inner_coordinate]
    dsimp [T]
    ring
  rw [hH, hT]
  have hiH : IntegrableOn (fun z => v 0 * H 0 z + v 1 * H 1 z) (Metric.ball x q) :=
    (h0.1.const_mul (v 0)).add (h1.1.const_mul (v 1))
  have hiT : IntegrableOn (fun t => v 0 * T 0 t + v 1 * T 1 t) (Icc (-Real.pi) Real.pi) :=
    (h0.2.1.const_mul (v 0)).add (h1.2.1.const_mul (v 1))
  refine ⟨hiH, hiT, ?_⟩
  rw [integral_add (h0.1.const_mul (v 0)) (h1.1.const_mul (v 1)),
    integral_add (h0.2.1.const_mul (v 0)) (h1.2.1.const_mul (v 1))]
  simp only [integral_const_mul]
  change v 0 * (∫ z in Metric.ball x q, H 0 z) +
    v 1 * (∫ z in Metric.ball x q, H 1 z) = _
  dsimp only [H, T]
  rw [h0.2.2, h1.2.2]
  ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
