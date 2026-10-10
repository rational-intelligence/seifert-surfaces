import CapAreaEnergy
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem cap_measurableSet (s q : ℝ) : MeasurableSet (planarCap (unitCircleParameter s) q) :=
  (Metric.isOpen_ball.inter Metric.isOpen_ball).measurableSet

theorem cap_density_rectangle_integrable (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (b : ℝ→E2) (hb : ContDiff ℝ ∞ b) :
    IntegrableOn (fun p : ℝ×ℝ => capTransverseDensity s b p.2)
      (Icc (1-q) 1 ×ˢ Icc (-capLensReach q) (capLensReach q)) := by
  apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact (cap_transverse_density_continuousOn s q hq hq1 b hb).comp continuous_snd.continuousOn (fun _ hp => hp.2)

theorem cap_base_density_pullback (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (b : ℝ→E2) (p : ℝ×ℝ) (hp : capCoordinateEquiv s p∈planarCap (unitCircleParameter s) q) :
    euclideanJetDensity (capBaseJet s b) (capCoordinateEquiv s p)=capTransverseDensity s b p.2 := by
  have hy := (cap_coordinate_graph_iff s q hq hq1 p).mp hp
  have h1 : |p.2|<1 := by
    have hh := (abs_lt.mpr hy.1).trans (cap_lens_reach q hq hq1).2.1
    linarith
  exact cap_base_coordinate_energy s b p h1

theorem cap_base_density_integrable (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (b : ℝ→E2) (hb : ContDiff ℝ ∞ b) :
    IntegrableOn (euclideanJetDensity (capBaseJet s b)) (planarCap (unitCircleParameter s) q) := by
  apply ((capCoordinateEquiv_measurePreserving s).integrableOn_comp_preimage (capCoordinateEquiv s).measurableEmbedding).mp
  have hi := (cap_density_rectangle_integrable s q hq hq1 b hb).mono_set (cap_coordinate_rectangle s q hq hq1)
  apply hi.congr
  filter_upwards [ae_restrict_mem ((cap_measurableSet s q).preimage (capCoordinateEquiv s).measurable)] with p hp
  exact (cap_base_density_pullback s q hq hq1 b p hp).symm

theorem cap_base_area_energy (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (b : ℝ→E2) (hb : ContDiff ℝ ∞ b) :
    (∫ z in planarCap (unitCircleParameter s) q, euclideanJetDensity (capBaseJet s b) z) ≤
      2*q*(∫ t in Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)), ‖deriv b t‖^2) := by
  let V := (capCoordinateEquiv s) ⁻¹' planarCap (unitCircleParameter s) q
  let R := Icc (1-q) 1 ×ˢ Icc (-capLensReach q) (capLensReach q)
  have hVm : MeasurableSet V := (cap_measurableSet s q).preimage (capCoordinateEquiv s).measurable
  have hchange := (capCoordinateEquiv_measurePreserving s).setIntegral_preimage_emb
    (capCoordinateEquiv s).measurableEmbedding (euclideanJetDensity (capBaseJet s b)) (planarCap (unitCircleParameter s) q)
  have heq : (∫ p in V, euclideanJetDensity (capBaseJet s b) (capCoordinateEquiv s p)) =
      ∫ p in V, capTransverseDensity s b p.2 :=
    setIntegral_congr_fun hVm (fun p hp => cap_base_density_pullback s q hq hq1 b p hp)
  have hmono : (∫ p in V, capTransverseDensity s b p.2) ≤ ∫ p in R, capTransverseDensity s b p.2 := by
    apply setIntegral_mono_set (cap_density_rectangle_integrable s q hq hq1 b hb)
    · filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
      exact div_nonneg (sq_nonneg _) (cap_transverse_interval_bounds q p.2 hq hq1 hp.2).2.1.le
    · exact ae_of_all _ (cap_coordinate_rectangle s q hq hq1)
  calc
    _ = ∫ p in V, euclideanJetDensity (capBaseJet s b) (capCoordinateEquiv s p) := hchange.symm
    _ = ∫ p in V, capTransverseDensity s b p.2 := heq
    _ ≤ ∫ p in R, capTransverseDensity s b p.2 := hmono
    _ = q*(∫ y in Icc (-capLensReach q) (capLensReach q), capTransverseDensity s b y) := cap_rectangle_energy_integral s q hq b
    _ ≤ 2*q*(∫ t in Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)), ‖deriv b t‖^2) := by
      have hh := mul_le_mul_of_nonneg_left (cap_transverse_energy s q hq hq1 b hb) hq.le
      nlinarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
