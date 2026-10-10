import InitialGreenProduct_v411

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

private theorem disc_integrable_continuous_weight_v457
    (g : E2 → ℝ) (hg : IntegrableOn g (disc 1))
    (w : E2 → ℝ) (hw : Continuous w) :
    IntegrableOn (fun z => g z * w z) (disc 1) := by
  obtain ⟨K,hK⟩ := (isCompact_closedBall (0:E2) 1).exists_bound_of_continuousOn hw.continuousOn
  apply hg.mul_bdd hw.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet (disc 1))] with z hz
  exact hK z (Metric.ball_subset_closedBall hz)

/- The actual global Green equation tested with a smooth squared-distance
cutoff. Its normal term retains the literal original map f and weak derivative d. -/
private theorem original_squared_radius_normal_green_v457
    (f : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)
    (H1 : ∀ i,H1On (disc 1) (fun z => f z i) (d i))
    (green : HasGreenBoundaryTrace f d b)
    (p : E2) (psi : E2 → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi) (i j : Fin 2) :
    let rho : E2 → ℝ := fun z => ‖z-p‖^2
    let bulk : E2 → ℝ := fun z =>
      f z i * fderiv ℝ psi z (coordinateVector 2 j)+d i z j*psi z
    let normal : E2 → ℝ := fun z => f z i*psi z*(z j-p j)
    IntegrableOn (fun z => chi (rho z)*bulk z) (disc 1) ∧
    IntegrableOn (fun z => 2*deriv chi (rho z)*normal z) (disc 1) ∧
    IntegrableOn (fun t => b t i*psi (unitCircleParameter t)*
      unitCircleParameter t j*chi (rho (unitCircleParameter t))) (Icc 0 (2*Real.pi)) ∧
    (∫ z in disc 1,chi (rho z)*bulk z)+
      (∫ z in disc 1,2*deriv chi (rho z)*normal z)=
      ∫ t in Icc 0 (2*Real.pi),b t i*psi (unitCircleParameter t)*
        unitCircleParameter t j*chi (rho (unitCircleParameter t)) := by
  classical
  dsimp only
  let rho : E2 → ℝ := fun z => ‖z-p‖^2
  let bulk : E2 → ℝ := fun z =>
    f z i*fderiv ℝ psi z (coordinateVector 2 j)+d i z j*psi z
  let normal : E2 → ℝ := fun z => f z i*psi z*(z j-p j)
  have hrho : ContDiff ℝ ∞ rho := (contDiff_id.sub contDiff_const).norm_sq ℝ
  have hrhod (z : E2) : fderiv ℝ rho z (coordinateVector 2 j)=2*(z j-p j) := by
    change (fderiv ℝ (fun x : E2=>‖id x-p‖^2) z) (coordinateVector 2 j)=_
    rw [((hasFDerivAt_id z).sub_const p).norm_sq.fderiv]
    simp [coordinateVector,EuclideanSpace.inner_single_right]
  have hweight : ContDiff ℝ ∞ (fun z => chi (rho z)) := hchi.comp hrho
  have hwd (z : E2) : fderiv ℝ (fun z => chi (rho z)) z (coordinateVector 2 j)=
      deriv chi (rho z)*(2*(z j-p j)) := by
    change (fderiv ℝ (chi ∘ rho) z) (coordinateVector 2 j)=_
    rw [fderiv_comp z (hchi.differentiable (by simp) (rho z))
      (hrho.differentiable (by simp) z)]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hrhod]
    exact fderiv_eq_deriv_mul
  have htest : ContDiff ℝ ∞ (fun z => psi z*chi (rho z)) := hpsi.mul hweight
  have htestd (z : E2) : fderiv ℝ (fun z => psi z*chi (rho z)) z (coordinateVector 2 j)=
      fderiv ℝ psi z (coordinateVector 2 j)*chi (rho z)+
        psi z*deriv chi (rho z)*(2*(z j-p j)) := by
    change (fderiv ℝ (psi*(fun z=>chi (rho z))) z) (coordinateVector 2 j)=_
    rw [fderiv_mul (hpsi.differentiable (by simp) z)
      (hweight.differentiable (by simp) z)]
    simp only [add_apply,smul_apply,smul_eq_mul,hwd]
    ring
  let : IsFiniteMeasure (volume.restrict (disc 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hfi : IntegrableOn (fun z => f z i) (disc 1) := (H1 i).2.1.integrable (by norm_num)
  have hbulk : IntegrableOn bulk (disc 1) := (green psi hpsi i j).1
  have hw1 := disc_integrable_continuous_weight_v457 bulk hbulk
    (fun z => chi (rho z)) hweight.continuous
  have hi1 : IntegrableOn (fun z => chi (rho z)*bulk z) (disc 1) := by
    simpa only [mul_comm] using hw1
  have hcder : Continuous (deriv chi) := hchi.continuous_deriv (by simp)
  have hw2 := disc_integrable_continuous_weight_v457 (fun z => f z i) hfi
    (fun z => 2*deriv chi (rho z)*psi z*(z j-p j)) (by fun_prop)
  have hi2 : IntegrableOn (fun z => 2*deriv chi (rho z)*normal z) (disc 1) := by
    apply hw2.congr
    filter_upwards [] with z
    dsimp only [normal]
    ring
  have ht := green (fun z=>psi z*chi (rho z)) htest i j
  have hb : IntegrableOn (fun t => b t i*psi (unitCircleParameter t)*
      unitCircleParameter t j*chi (rho (unitCircleParameter t))) (Icc 0 (2*Real.pi)) := by
    apply ht.2.1.congr
    filter_upwards [] with t
    ring
  refine ⟨hi1,hi2,hb,?_⟩
  rw [← integral_add hi1 hi2]
  calc
    _ = ∫ z in disc 1, f z i*fderiv ℝ (fun z=>psi z*chi (rho z)) z
        (coordinateVector 2 j)+d i z j*(psi z*chi (rho z)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [htestd]
      dsimp only [bulk,normal]
      ring
    _ = _ := ht.2.2.trans (integral_congr_ae (Eventually.of_forall fun t => by ring))

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
