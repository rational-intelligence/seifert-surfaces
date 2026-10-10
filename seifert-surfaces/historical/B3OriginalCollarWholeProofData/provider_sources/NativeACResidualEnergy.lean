import NativeZeroCapVector

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem ac_vector_residual_energy (a b : ℝ) (hab : a ≤ b) (c d : ℝ → E2)
    (hca : ∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => c t i) a b)
    (hda : ∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => d t i) a b)
    (hcd : MemLp (deriv c) 2 (volume.restrict (Icc a b)))
    (hdd : MemLp (deriv d) 2 (volume.restrict (Icc a b))) :
    (∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => (c t - d t) i) a b) ∧
    MemLp (deriv (fun t => c t - d t)) 2 (volume.restrict (Icc a b)) ∧
    (∫ t in Icc a b, ‖deriv (fun t => c t - d t) t‖ ^ 2) ≤
      2 * ((∫ t in Icc a b, ‖deriv c t‖ ^ 2) + ∫ t in Icc a b, ‖deriv d t‖ ^ 2) := by
  have hcae := ae_deriv_coordinate c a b hab hca
  have hdae := ae_deriv_coordinate d a b hab hda
  have hd : deriv (fun t => c t - d t) =ᵐ[volume.restrict (Icc a b)]
      (fun t => deriv c t - deriv d t) := by
    filter_upwards [hcae, hdae] with t hc hd
    exact deriv_sub hc.1 hd.1
  have hp : MemLp (deriv (fun t => c t - d t)) 2 (volume.restrict (Icc a b)) :=
    (hcd.sub hdd).ae_eq hd.symm
  refine ⟨fun i => (hca i).sub (hda i), hp, ?_⟩
  have he := integral_mono_ae hp.norm.integrable_sq
    ((hcd.norm.integrable_sq.add hdd.norm.integrable_sq).const_mul 2) (by
      filter_upwards [hd] with t ht
      rw [ht]
      exact norm_sub_sq_bound (deriv c t) (deriv d t))
  have hs := integral_add hcd.norm.integrable_sq hdd.norm.integrable_sq
  simp only [Pi.add_apply] at he hs
  simpa only [integral_const_mul, hs] using he

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
