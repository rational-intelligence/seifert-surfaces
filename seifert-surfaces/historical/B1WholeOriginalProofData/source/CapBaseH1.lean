import CapNativeGreen
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem cap_base_H1 (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (B b : ℝ→E2) (hB : Continuous B) (hBp : Periodic B (2*Real.pi))
    (hb : ContDiff ℝ ∞ b)
    (hagree : ∀t∈Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)), B t=b t) (i : Fin 2) :
    H1On (planarCap (unitCircleParameter s) q) (fun z => capBaseMap s b z i) (capBaseJet s b i) := by
  let A := planarCap (unitCircleParameter s) q
  have hfin : volume A≠(∞:ℝ≥0∞) := ne_of_lt ((measure_mono (show A⊆Metric.ball (0:E2) 1 from inter_subset_left)).trans_lt measure_ball_lt_top)
  letI : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hfin
  have hf := cap_base_map_memLp s q b hb i
  have hd := cap_base_jet_memLp s q hq hq1 b hb i
  refine ⟨⟨IntegrableOn.locallyIntegrableOn (hf.integrable (by norm_num)),
    IntegrableOn.locallyIntegrableOn (hd.integrable (by norm_num)),?_⟩,hf,hd⟩
  intro psi hs hsc hss j
  have hgreen := (cap_native_Green s q hq hq1 B b hB hBp hb hagree psi hs i j).2.2.2
  have htrue (t:ℝ) : psi (unitCircleParameter t)=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    have hball := (hss ht).1
    change dist (unitCircleParameter t) (0:E2)<1 at hball
    rw [dist_zero_right,circle_norm] at hball
    exact (lt_irrefl (1:ℝ)) hball
  have hart (t:ℝ) : psi (unitCircleParameter s+q • unitCircleParameter t)=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    have hball := (hss ht).2
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_of_pos hq,circle_norm,mul_one] at hball
    exact (lt_irrefl q) hball
  simp_rw [htrue,hart,mul_zero] at hgreen
  simp only [zero_mul,integral_zero,mul_zero,add_zero] at hgreen
  have htest : MemLp (fun z => fderiv ℝ psi z (coordinateVector 2 j)) 2 (volume.restrict A) :=
    ((hs.continuous_fderiv (by simp)).clm_apply continuous_const |>.memLp_of_hasCompactSupport
      (hsc.fderiv_apply ℝ _)).restrict _
  have hpsi : MemLp psi 2 (volume.restrict A) := (hs.continuous.memLp_of_hasCompactSupport hsc).restrict _
  have hl := hf.integrable_mul htest
  have hr := (hd.continuousLinearMap_comp (EuclideanSpace.proj (𝕜:=ℝ) j)).integrable_mul hpsi
  have he := integral_add hl hr
  simp only [Pi.mul_apply,EuclideanSpace.coe_proj] at he
  rw [he] at hgreen
  linarith only [hgreen]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
