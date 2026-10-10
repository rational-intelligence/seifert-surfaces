import NativeBoundaryToolbox
set_option maxHeartbeats 2000000
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open SeifertSurfaces.AppendixACoordinates

theorem h1_restrict_subset (U V : Set E2) (hVU : V ⊆ U) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On U u du) : H1On V u du := by
  have hm : MemLp u 2 (volume.restrict V) := hu.2.1.mono_measure (Measure.restrict_mono hVU le_rfl)
  have hdm : MemLp du 2 (volume.restrict V) := hu.2.2.mono_measure (Measure.restrict_mono hVU le_rfl)
  refine ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hm.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hdm.locallyIntegrable (by norm_num)),?_⟩,hm,hdm⟩
  intro psi hs hc ht i
  have hz (A : Set E2) (hVA : V ⊆ A) (y : E2) (hy : y ∉ A) :
      psi y = 0 ∧ fderiv ℝ psi y (coordinateVector 2 i) = 0 := by
    refine ⟨image_eq_zero_of_notMem_tsupport (fun hh => hy (hVA (ht hh))),?_⟩
    exact image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ psi y (coordinateVector 2 i))
      (fun hh => hy (hVA (ht ((tsupport_fderiv_apply_subset ℝ _) hh))))
  have hi := hu.1.2.2 psi hs hc (ht.trans hVU) i
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [(hz U hVU y hy).2,mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [(hz U hVU y hy).1,mul_zero])] at hi
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [(hz V Subset.rfl y hy).2,mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [(hz V Subset.rfl y hy).1,mul_zero])]
  exact hi

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
