import CurveComplexGenusTwo.CWHurewicz.DiskExtension
import CurveComplexGenusTwo.CWHurewicz.CWBasic

namespace CurveComplexGenusTwo.CWHurewicz

open Topology Metric

/-! Public bridge for the CW packet's domain abbreviations. -/
theorem cellSphereMap_extends_cellDisk (n : ℕ)
    {Y : Type*} [TopologicalSpace Y] (f : C(CellSphere n, Y)) (y₀ : Y)
    (H : ContinuousMap.Homotopy f (ContinuousMap.const (CellSphere n) y₀)) :
    ∃ F : C(CellDisk n, Y), ∀ z : CellSphere n,
      F ⟨z.1, sphere_subset_closedBall z.2⟩ = f z := by
  simpa [CellDisk, CellSphere] using
    (sphereMap_extends_disk_all n f y₀ H)

end CurveComplexGenusTwo.CWHurewicz
