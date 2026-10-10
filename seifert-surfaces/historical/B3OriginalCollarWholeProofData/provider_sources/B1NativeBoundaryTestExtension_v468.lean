import B1NativeBoundaryTangentialTests_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.DirectWeak
open ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
set_option maxHeartbeats 0

/-- Zero extension of a native H10 test into a larger actual domain preserves its
literal weak gradient and approximation, including the common flat boundary. -/
theorem native_h10_indicator_into_v468
    (U V : Set E2) (hU : MeasurableSet U) (hUV : U ⊆ V)
    (u : E2 → ℝ) (du : E2 → E2) (hu : H10On U u du) :
    H10On V (U.indicator u) (U.indicator du) := by
  classical
  have hzero := zero_extension U hU u du hu
  have h1 := h1_restrict_subset univ V (subset_univ V) _ _ hzero.1
  refine ⟨h1, ?_⟩
  intro eps heps
  obtain ⟨phi, hps, hpc, hpt, herr⟩ := hu.2 eps heps
  refine ⟨phi, hps, hpc, hpt.trans hUV, ?_⟩
  have hgrad (x : E2) (hx : x ∉ U) : planarGradient phi x=0 := by
    exact planarGradient_eq_zero_off_support phi (fun ht => hx (hpt ht))
  have hvalue (x : E2) (hx : x ∉ U) : phi x=0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hx (hpt ht))
  have he : (fun x => |U.indicator u x-phi x|^2+
      ‖U.indicator du x-planarGradient phi x‖^2) =
      U.indicator (fun x => |u x-phi x|^2+‖du x-planarGradient phi x‖^2) := by
    funext x
    by_cases hx : x∈U
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, hvalue x hx, hgrad x hx, sub_zero,
        norm_zero, abs_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
  rw [he, integral_indicator hU]
  rw [Measure.restrict_restrict hU, inter_eq_left.mpr hUV]
  exact herr

/-- Zero extension followed by restriction agrees with the original test on its domain. -/
theorem native_h10_indicator_self_v468
    (U : Set E2) (hU : MeasurableSet U) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H10On U u du) : H10On U (U.indicator u) (U.indicator du) :=
  native_h10_indicator_into_v468 U U hU Subset.rfl u du hu

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_h10_indicator_into_v468
