import B1ActualBoundaryTangentCutoffH2_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
set_option maxHeartbeats 800000

/-- A chosen Sobolev derivative is the literal derivative of the interior
smooth representative, also on domains approaching the flat edge. -/
theorem native_smooth_partial_memWkp_v468 (U : Set E2) (hU : IsOpen U)
    (u : E2 → ℝ) (hs : ContDiffOn ℝ ∞ u U) (m : ℕ)
    (hu : MemWkp (m+1) 2 u U) (i : Fin 2) :
    MemWkp m 2 (fun x => planarGradient u x i) U := by
  let hw := hu.memW1p.someWitness
  have hn := regular_witness_native_H1_v468 U u hw
  have hg := native_smooth_gradient_ae_v468 U hU u u hw.weakGrad hn hs EventuallyEq.rfl
  have hc := (chosenWeakPartialOrZero_isWeakPartial_of_mem hu.memW1p i).ae_eq hU
    (hw.isWeakGrad i) ((chosenWeakPartialOrZero_memLp_of_mem hu.memW1p i).locallyIntegrable (by norm_num))
    ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
  apply (MemWkp_congr_ae (by norm_num) hU _).mp (hu.chosenWeakPartial_mem i)
  filter_upwards [hc,hg] with x hx he
  exact hx.trans (congrArg (fun v : E2 => v i) he)

/-- Ambient smooth scalar multipliers have bounded jets on a compact closure. -/
theorem native_compact_smooth_mul_Wkp_v468 (U : Set E2) (hU : IsOpen U)
    (hUc : IsCompact (closure U)) (a f : E2 → ℝ) (ha : ContDiff ℝ ∞ a)
    (m : ℕ) (hf : MemWkp m 2 f U) : MemWkp m 2 (fun x => a x*f x) U := by
  obtain ⟨C,hCpos,hC⟩ := DifferentialGeometry.Analysis.Calculus.exists_uniform_iteratedFDerivWithin_bound_of_contDiffOn
    isOpen_univ ha.contDiffOn hUc (subset_univ _) m
  exact MemWkp.smul_smooth_bounded m (by norm_num) hU ha
    (fun j hj x hx => by simpa only [iteratedFDerivWithin_univ] using hC x (subset_closure hx) j hj) hf
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_smooth_partial_memWkp_v468
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_compact_smooth_mul_Wkp_v468
