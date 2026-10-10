import CapAreaEnergyFinal
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem cap_base_map_memLp (s q : ℝ) (b : ℝ→E2) (hb : ContDiff ℝ ∞ b) (i : Fin 2) :
    MemLp (fun z => capBaseMap s b z i) 2 (volume.restrict (planarCap (unitCircleParameter s) q)) := by
  have hc : Continuous (fun z => capBaseMap s b z i) :=
    (EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp (capBaseMap_continuous s b hb.continuous)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  exact ((hc.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall (0:E2) 1)).mono_set
    (fun z hz => Metric.ball_subset_closedBall hz.1)

theorem cap_base_jet_memLp (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (b : ℝ→E2) (hb : ContDiff ℝ ∞ b) (i : Fin 2) :
    MemLp (capBaseJet s b i) 2 (volume.restrict (planarCap (unitCircleParameter s) q)) := by
  have hm : AEStronglyMeasurable (capBaseJet s b i)
      (volume.restrict (planarCap (unitCircleParameter s) q)) :=
    (capBaseJet_measurable s b hb i).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (cap_base_density_integrable s q hq hq1 b hb).mono'
    ((hm.norm.pow 2))
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact Finset.single_le_sum (fun k _ => sq_nonneg (‖capBaseJet s b k z‖)) (Finset.mem_univ i)

theorem cap_native_energy_total (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (b : ℝ→E2) (hb : ContDiff ℝ ∞ b) :
    (∫ z in planarCap (unitCircleParameter s) q, euclideanJetDensity (capBaseJet s b) z) +
      (∫ t in Icc (s+Real.pi/2+Real.arcsin (q/2)) (s+3*Real.pi/2-Real.arcsin (q/2)),
        ‖deriv (fun t => b (capArtificialAngle s q t)) t‖^2) ≤
      4*q*(∫ t in Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)), ‖deriv b t‖^2) := by
  have ha := cap_base_area_energy s q hq hq1 b hb
  have hc := cap_artificial_trace_energy s q hq hq1 b hb
  linarith

theorem cap_native_L2_energy_package (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (b : ℝ→E2) (hb : ContDiff ℝ ∞ b) :
    (∀ i : Fin 2, MemLp (fun z => capBaseMap s b z i) 2
      (volume.restrict (planarCap (unitCircleParameter s) q))) ∧
    (∀ i : Fin 2, MemLp (capBaseJet s b i) 2
      (volume.restrict (planarCap (unitCircleParameter s) q))) ∧
    (∫ z in planarCap (unitCircleParameter s) q, euclideanJetDensity (capBaseJet s b) z) +
      (∫ t in Icc (s+Real.pi/2+Real.arcsin (q/2)) (s+3*Real.pi/2-Real.arcsin (q/2)),
        ‖deriv (fun t => b (capArtificialAngle s q t)) t‖^2) ≤
      4*q*(∫ t in Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)), ‖deriv b t‖^2) :=
  ⟨cap_base_map_memLp s q b hb,cap_base_jet_memLp s q hq hq1 b hb,cap_native_energy_total s q hq hq1 b hb⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
