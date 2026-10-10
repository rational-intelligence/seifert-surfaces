import InitialCapTraceRadius_v411

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

private theorem native_green_smooth_product_v411
    (f : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)
    (green : HasGreenBoundaryTrace f d b)
    (phi : E2 → ℝ) (hphi : ContDiff ℝ ∞ phi) :
    let grad : E2 → E2 := fun z =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun j => fderiv ℝ phi z (coordinateVector 2 j))
    HasGreenBoundaryTrace (fun z => phi z • f z)
      (fun i z => phi z • d i z + f z i • grad z)
      (fun t => phi (unitCircleParameter t) • b t) := by
  classical
  dsimp only
  intro psi hpsi i j
  have hsmooth : ContDiff ℝ ∞ (fun z => phi z * psi z) := hphi.mul hpsi
  have hgreen := green (fun z => phi z * psi z) hsmooth i j
  have hformula (z : E2) :
      (phi z • f z) i * fderiv ℝ psi z (coordinateVector 2 j) +
        (phi z • d i z + f z i •
          (EuclideanSpace.equiv (Fin 2) ℝ).symm
            (fun j => fderiv ℝ phi z (coordinateVector 2 j))) j * psi z =
      f z i * fderiv ℝ (fun z => phi z * psi z) z (coordinateVector 2 j) +
        d i z j * (phi z * psi z) := by
    change (phi z • f z) i * fderiv ℝ psi z (coordinateVector 2 j) +
      (phi z • d i z + f z i •
        (EuclideanSpace.equiv (Fin 2) ℝ).symm
          (fun j => fderiv ℝ phi z (coordinateVector 2 j))) j * psi z =
      f z i * (fderiv ℝ (phi * psi) z) (coordinateVector 2 j) +
        d i z j * (phi z * psi z)
    rw [fderiv_mul (hphi.differentiable (by simp) z) (hpsi.differentiable (by simp) z)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, PiLp.smul_apply, PiLp.add_apply]
    change phi z * f z i * fderiv ℝ psi z (coordinateVector 2 j) +
      (phi z * d i z j + f z i * fderiv ℝ phi z (coordinateVector 2 j)) * psi z =
      f z i * (phi z * fderiv ℝ psi z (coordinateVector 2 j) +
        psi z * fderiv ℝ phi z (coordinateVector 2 j)) + d i z j * (phi z * psi z)
    ring
  have hboundary (t : ℝ) :
      (phi (unitCircleParameter t) • b t) i * psi (unitCircleParameter t) * unitCircleParameter t j =
      b t i * (phi (unitCircleParameter t) * psi (unitCircleParameter t)) * unitCircleParameter t j := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have hi : IntegrableOn (fun z =>
      (phi z • f z) i * fderiv ℝ psi z (coordinateVector 2 j) +
        (phi z • d i z + f z i •
          (EuclideanSpace.equiv (Fin 2) ℝ).symm
            (fun j => fderiv ℝ phi z (coordinateVector 2 j))) j * psi z) (disc 1) :=
    hgreen.1.congr (Eventually.of_forall fun z => (hformula z).symm)
  have hb : IntegrableOn (fun t =>
      (phi (unitCircleParameter t) • b t) i * psi (unitCircleParameter t) * unitCircleParameter t j)
      (Icc 0 (2 * Real.pi)) :=
    hgreen.2.1.congr (Eventually.of_forall fun t => (hboundary t).symm)
  refine ⟨hi, hb, ?_⟩
  exact (integral_congr_ae (Eventually.of_forall hformula)).trans
    (hgreen.2.2.trans (integral_congr_ae (Eventually.of_forall fun t => (hboundary t).symm)))

private theorem native_H1_smooth_product_rows_L2_v411
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun z => f z i) (d i))
    (phi : E2 → ℝ) (hphi : ContDiff ℝ ∞ phi) :
    let grad : E2 → E2 := fun z =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun j => fderiv ℝ phi z (coordinateVector 2 j))
    ∀ i, MemLp (fun z => phi z • d i z + f z i • grad z) 2
      (volume.restrict (disc 1)) := by
  classical
  dsimp only
  let μ : Measure E2 := volume.restrict (disc 1)
  let grad : E2 → E2 := fun z =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm
      (fun j => fderiv ℝ phi z (coordinateVector 2 j))
  have hgrad : Continuous grad := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi
    intro j
    exact (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hbphi : MemLp phi ∞ μ := by
    obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E2) 1).exists_bound_of_continuousOn
      hphi.continuous.continuousOn
    apply memLp_top_of_bound hphi.continuous.aestronglyMeasurable.restrict K
    filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet (disc 1))] with z hz
    exact hK z (Metric.ball_subset_closedBall hz)
  have hbgrad : MemLp grad ∞ μ := by
    obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E2) 1).exists_bound_of_continuousOn
      hgrad.continuousOn
    apply memLp_top_of_bound hgrad.aestronglyMeasurable.restrict K
    filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet (disc 1))] with z hz
    exact hK z (Metric.ball_subset_closedBall hz)
  intro i
  exact (hbphi.smul (hH1 i).2.2).add ((hH1 i).2.1.smul hbgrad)

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
