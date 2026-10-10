import B1ActualBoundaryTangentZeroTrace_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
set_option maxHeartbeats 200000

theorem native_full_linear_restrict_v468 (U V : Set E2) (hVU : V ⊆ U)
    (a : E2 → Mat2) (b : E2 → E2) (c u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On U u du) (heq : WeakLinearEquationOn U a b c u du) :
    WeakLinearEquationOn V a b c u du := by
  refine ⟨(h1_restrict_subset U V hVU u du hu).1,?_⟩
  intro phi hs hc ht
  obtain ⟨hi,hh⟩ := heq.2 phi hs hc (ht.trans hVU)
  refine ⟨hi.mono_set hVU,?_⟩
  have hz : ∀ x, x∉V → inner ℝ (matrixAction (a x) (du x)) (planarGradient phi x)-
      (inner ℝ (b x) (du x)+c x*u x)*phi x=0 := by
    intro x hx
    have hx' : x∉tsupport phi := fun hh => hx (ht hh)
    rw [QuasilinearLocalization.Helpers.gradient_zero_off_tsupport phi hx',
      image_eq_zero_of_notMem_tsupport hx']
    simp
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => hz x (fun hv => hx (hVU hv)))] at hh
  exact hh
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_full_linear_restrict_v468
