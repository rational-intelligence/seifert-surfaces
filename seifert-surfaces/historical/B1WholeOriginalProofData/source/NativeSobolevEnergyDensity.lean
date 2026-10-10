import NativeLipschitzAreaReduction
import Mathlib.MeasureTheory.Covering.DensityTheorem

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent
set_option autoImplicit false
set_option maxHeartbeats 0

private theorem native_H1_energy_integrable
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i)) :
    IntegrableOn (euclideanJetDensity d) (disc 1) := by
  exact integrable_finsetSum _ (fun i _ => (hH1 i).2.2.norm.integrable_sq)

private theorem native_H1_ae_local_quadratic_energy_bound
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i)) :
    ∀ᵐ x ∂volume, ∃ C r0 : ℝ, 0 ≤ C ∧ 0 < r0 ∧
      ∀ r : ℝ, 0 < r → r ≤ r0 →
        (∫ z in planarCap x r, euclideanJetDensity d z) ≤ C * r ^ 2 := by
  classical
  let g : E2 → ℝ := (disc 1).indicator (euclideanJetDensity d)
  have hg : Integrable g volume :=
    (native_H1_energy_integrable u d hH1).integrable_indicator Metric.isOpen_ball.measurableSet
  have hgn : ∀ x, 0 ≤ g x := by
    intro x
    apply indicator_nonneg
    exact fun z _ => Finset.sum_nonneg (fun i _ => sq_nonneg ‖d i z‖)
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average volume hg.locallyIntegrable 1
  filter_upwards [hdiff] with x hx
  have hlim : Tendsto (fun r : ℝ => ⨍ z in Metric.closedBall x r, g z)
      (𝓝[>] 0) (𝓝 (g x)) := by
    apply hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [one_mul, Metric.mem_closedBall, dist_self]
    exact hr.le
  have hbound : ∀ᶠ r : ℝ in 𝓝[>] 0,
      (⨍ z in Metric.closedBall x r, g z) < g x + 1 :=
    hlim.eventually (gt_mem_nhds (by linarith : g x < g x + 1))
  obtain ⟨e, he, heBound⟩ := Metric.mem_nhdsWithin_iff.mp hbound
  have hgx := hgn x
  refine ⟨Real.pi * (g x + 1), e / 2, by positivity, half_pos he, ?_⟩
  intro r hr hre
  have hrb : r ∈ Metric.ball (0 : ℝ) e ∩ Ioi 0 := by
    refine ⟨?_, hr⟩
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hr]
    linarith
  have hstrict : (⨍ z in Metric.closedBall x r, g z) < g x + 1 := heBound hrb
  have hav := hstrict.le
  have hvol : (volume.restrict (Metric.closedBall x r)).real univ = r ^ 2 * Real.pi := by
    rw [measureReal_restrict_apply_univ, measureReal_def,
      EuclideanSpace.volume_closedBall_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
      ENNReal.toReal_ofReal Real.pi_pos.le]
  have hcv : 0 < r ^ 2 * Real.pi := by positivity
  rw [average_eq, smul_eq_mul, hvol] at hav
  have hint : (∫ z in Metric.closedBall x r, g z) ≤
      (g x + 1) * (r ^ 2 * Real.pi) := by
    exact (div_le_iff₀ hcv).mp (by simpa only [← div_eq_inv_mul] using hav)
  have hcap : (∫ z in planarCap x r, euclideanJetDensity d z) =
      ∫ z in planarCap x r, g z := by
    apply setIntegral_congr_fun (Metric.isOpen_ball.measurableSet.inter Metric.isOpen_ball.measurableSet)
    intro z hz
    exact (indicator_of_mem hz.1 (euclideanJetDensity d)).symm
  rw [hcap]
  calc
    _ ≤ ∫ z in Metric.closedBall x r, g z :=
      setIntegral_mono_set hg.integrableOn (Eventually.of_forall hgn)
        (show planarCap x r ⊆ Metric.closedBall x r from
          inter_subset_right.trans Metric.ball_subset_closedBall).eventuallyLE
    _ ≤ (g x + 1) * (r ^ 2 * Real.pi) := hint
    _ = (Real.pi * (g x + 1)) * r ^ 2 := by ring

#print axioms native_H1_energy_integrable
#print axioms native_H1_ae_local_quadratic_energy_bound
