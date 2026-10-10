import ApprovedDataClosure
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder

theorem H01Space_complete (Ω : Set V) : CompleteSpace (H01Space Ω) := by
  unfold H01Space
  infer_instance

end SeifertSurfaces.WeakSchauder
