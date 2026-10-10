import NativeBallH1Extension

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem native_H1_sum (U : Set E2) (f g : E2 → ℝ) (df dg : E2 → E2)
    (hf : H1On U f df) (hg : H1On U g dg) :
    H1On U (fun z => f z + g z) (fun z => df z + dg z) := by
  refine ⟨⟨hf.1.1.add hg.1.1, hf.1.2.1.add hg.1.2.1, ?_⟩,
    hf.2.1.add hg.2.1, hf.2.2.add hg.2.2⟩
  intro psi hs hsc hss j
  have htest : MemLp (fun z => fderiv ℝ psi z (coordinateVector 2 j)) 2 (volume.restrict U) :=
    ((hs.continuous_fderiv (by simp)).clm_apply continuous_const |>.memLp_of_hasCompactSupport
      (hsc.fderiv_apply ℝ _)).restrict _
  have hpsi : MemLp psi 2 (volume.restrict U) :=
    (hs.continuous.memLp_of_hasCompactSupport hsc).restrict _
  have hl0 := hf.2.1.integrable_mul htest
  have hl1 := hg.2.1.integrable_mul htest
  have hr0 := (hf.2.2.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)).integrable_mul hpsi
  have hr1 := (hg.2.2.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)).integrable_mul hpsi
  have he0 := hf.1.2.2 psi hs hsc hss j
  have he1 := hg.1.2.2 psi hs hsc hss j
  simp only [Pi.mul_apply, EuclideanSpace.coe_proj] at hl0 hl1 hr0 hr1
  simp only [PiLp.add_apply, add_mul]
  have hel := integral_add hl0 hl1
  have her := integral_add hr0 hr1
  simp only [Pi.mul_apply] at hel her
  rw [hel, her, he0, he1]
  ring

theorem norm_add_sq_bound (v w : E2) : ‖v + w‖ ^ 2 ≤ 2 * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  rw [norm_add_sq_real]
  have hs := norm_sub_sq_real v w
  nlinarith [sq_nonneg ‖v - w‖]

theorem norm_sub_sq_bound (v w : E2) : ‖v - w‖ ^ 2 ≤ 2 * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  simpa only [sub_eq_add_neg, norm_neg] using norm_add_sq_bound v (-w)

theorem native_rows_sum_energy (U : Set E2) (df dg : Fin 2 → E2 → E2)
    (hf : ∀ i, MemLp (df i) 2 (volume.restrict U))
    (hg : ∀ i, MemLp (dg i) 2 (volume.restrict U)) :
    (∫ z in U, euclideanJetDensity (fun i z => df i z + dg i z) z) ≤
      2 * ((∫ z in U, euclideanJetDensity df z) + ∫ z in U, euclideanJetDensity dg z) := by
  have hfi : IntegrableOn (euclideanJetDensity df) U :=
    integrable_finsetSum _ (fun i _ => (hf i).norm.integrable_sq)
  have hgi : IntegrableOn (euclideanJetDensity dg) U :=
    integrable_finsetSum _ (fun i _ => (hg i).norm.integrable_sq)
  have hsum : IntegrableOn (euclideanJetDensity (fun i z => df i z + dg i z)) U :=
    integrable_finsetSum _ (fun i _ => ((hf i).add (hg i)).norm.integrable_sq)
  have hp (z : E2) : euclideanJetDensity (fun i z => df i z + dg i z) z ≤
      2 * (euclideanJetDensity df z + euclideanJetDensity dg z) := by
    unfold euclideanJetDensity
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => norm_add_sq_bound (df i z) (dg i z))
  have hi := integral_mono hsum ((hfi.add hgi).const_mul 2) hp
  have he := integral_add hfi hgi
  simp only [Pi.add_apply] at hi he
  simpa only [integral_const_mul, he] using hi

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
