import CapBaseMapBasics
import Mathlib.MeasureTheory.Integral.Prod
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def capTransverseDensity (s : ℝ) (b : ℝ→E2) (y : ℝ) : ℝ :=
  ‖deriv b (s+Real.arcsin y)‖^2/(1-y^2)

theorem cap_transverse_interval_bounds (q y : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (hy : y∈Icc (-capLensReach q) (capLensReach q)) :
    |y|<1 ∧ 0<1-y^2 ∧ 1/2≤Real.sqrt (1-y^2) := by
  have hv := cap_lens_reach q hq hq1
  have ha : |y|≤q := (abs_le.mpr hy).trans hv.2.1.le
  have h1 : |y|<1 := by linarith
  have hs : y^2≤q^2 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg y) hq.le).mpr ha
  refine ⟨h1,by nlinarith,?_⟩
  apply Real.le_sqrt_of_sq_le
  nlinarith

theorem cap_transverse_density_continuousOn (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (b : ℝ→E2) (hb : ContDiff ℝ ∞ b) :
    ContinuousOn (capTransverseDensity s b) (Icc (-capLensReach q) (capLensReach q)) := by
  unfold capTransverseDensity
  refine (((hb.continuous_deriv (by simp)).comp (continuous_const.add Real.continuous_arcsin)).norm.pow 2).continuousOn.div
    (continuous_const.sub (continuous_id.pow 2)).continuousOn ?_
  intro y hy
  exact ne_of_gt (cap_transverse_interval_bounds q y hq hq1 hy).2.1

theorem cap_transverse_energy (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (b : ℝ→E2) (hb : ContDiff ℝ ∞ b) :
    (∫ y in Icc (-capLensReach q) (capLensReach q), capTransverseDensity s b y) ≤
      2*(∫ t in Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)), ‖deriv b t‖^2) := by
  let V := capLensReach q
  let θ := fun y : ℝ => s+Real.arcsin y
  let θ' := fun y : ℝ => 1/Real.sqrt (1-y^2)
  have hV := cap_lens_reach q hq hq1
  have hab : -V≤V := by dsimp [V];linarith [hV.1]
  have hθ' : ContinuousOn θ' (Icc (-V) V) := by
    apply continuousOn_const.div (continuous_const.sub (continuous_id.pow 2)).sqrt.continuousOn
    intro y hy
    exact ne_of_gt (Real.sqrt_pos.mpr (cap_transverse_interval_bounds q y hq hq1 hy).2.1)
  have hd (y : ℝ) (hy : y∈uIcc (-V) V) : HasDerivAt θ (θ' y) y := by
    rw [uIcc_of_le hab] at hy
    have h1 := (cap_transverse_interval_bounds q y hq hq1 hy).1
    exact (Real.hasDerivAt_arcsin (ne_of_gt (abs_lt.mp h1).1) (ne_of_lt (abs_lt.mp h1).2)).const_add s
  have hg : Continuous (fun t : ℝ => ‖deriv b t‖^2) := (hb.continuous_deriv (by simp)).norm.pow 2
  have hi1 : IntegrableOn (capTransverseDensity s b) (Icc (-V) V) :=
    (cap_transverse_density_continuousOn s q hq hq1 b hb).integrableOn_Icc
  have hi2 : IntegrableOn (fun y => 2*(‖deriv b (θ y)‖^2*θ' y)) (Icc (-V) V) :=
    (continuousOn_const.mul ((hg.comp (continuous_const.add Real.continuous_arcsin)).continuousOn.mul hθ')).integrableOn_Icc
  have hm := setIntegral_mono_on hi1 hi2 measurableSet_Icc (fun y hy => by
    have hx := cap_transverse_interval_bounds q y hq hq1 hy
    have hs := Real.sq_sqrt hx.2.1.le
    have hp : 0<Real.sqrt (1-y^2) := Real.sqrt_pos.mpr hx.2.1
    have hden : Real.sqrt (1-y^2)≤2*(1-y^2) := by
      nlinarith [mul_nonneg (show 0≤2*Real.sqrt (1-y^2)-1 by linarith [hx.2.2]) hp.le]
    have hmul := mul_le_mul_of_nonneg_left hden (sq_nonneg (‖deriv b (s+Real.arcsin y)‖))
    change ‖deriv b (s+Real.arcsin y)‖^2/(1-y^2) ≤
      2*(‖deriv b (s+Real.arcsin y)‖^2*(1/Real.sqrt (1-y^2)))
    apply (div_le_iff₀ hx.2.1).mpr
    rw [div_eq_mul_inv,← mul_assoc]
    field_simp
    nlinarith)
  have hsub := intervalIntegral.integral_comp_mul_deriv hd
    (by rwa [uIcc_of_le hab]) hg
  have hend := cap_arcsin_tangent_endpoint q hq hq1
  change Real.arcsin (capLensReach q)=2*Real.arcsin (q/2) at hend
  have he := cap_arcsin_bounds q hq hq1
  have hθa : θ (-V)=s-2*Real.arcsin (q/2) := by dsimp [θ,V];rw [Real.arcsin_neg,hend];ring
  have hθb : θ V=s+2*Real.arcsin (q/2) := by dsimp [θ,V];rw [hend]
  rw [intervalIntegral.integral_of_le hab,← integral_Icc_eq_integral_Ioc,
    hθa,hθb,intervalIntegral.integral_of_le (by linarith [he.1]),← integral_Icc_eq_integral_Ioc] at hsub
  simp only [Function.comp_apply] at hsub
  calc
    _ ≤ ∫ y in Icc (-V) V, 2*(‖deriv b (θ y)‖^2*θ' y) := hm
    _ = 2*(∫ t in Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)), ‖deriv b t‖^2) := by
      rw [integral_const_mul,hsub]

theorem cap_rectangle_energy_integral (s q : ℝ) (hq : 0<q) (b : ℝ→E2) :
    (∫ p in Icc (1-q) 1 ×ˢ Icc (-capLensReach q) (capLensReach q), capTransverseDensity s b p.2) =
      q*(∫ y in Icc (-capLensReach q) (capLensReach q), capTransverseDensity s b y) := by
  have hh := setIntegral_prod_mul (μ:=volume) (ν:=volume) (fun _:ℝ => (1:ℝ))
    (capTransverseDensity s b) (Icc (1-q) 1) (Icc (-capLensReach q) (capLensReach q))
  change (∫ p in Icc (1-q) 1 ×ˢ Icc (-capLensReach q) (capLensReach q), capTransverseDensity s b p.2 ∂volume.prod volume) = _
  simpa [Real.volume_Icc,Measure.real,ENNReal.toReal_ofReal hq.le] using hh

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
