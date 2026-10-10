import NativeBoundarySchauderSameFunction

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

/-- C1 gain applies to the same actual continuous function on smaller CLOSED
caps, even though the scalar provider initially returns an a.e. representative. -/
theorem native_scalar_C1_gain_same_function
    (r s : ℝ) (hsr : s < r) (v w : E2 → ℝ)
    (hv : ContinuousOn v (closedHalfDisc r))
    (hw : ContDiffOn ℝ 1 w (closedHalfDisc r))
    (hae : w =ᵐ[volume.restrict (openHalfDisc r)] v) :
    ContDiffOn ℝ 1 v (closedHalfDisc s) := by
  have he := native_same_continuous_representative_on_smaller_cap r s hsr v w hv hw.continuousOn hae
  exact (hw.mono (closedHalfDisc_mono hsr.le)).congr he.symm

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
