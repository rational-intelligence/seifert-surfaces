import B1ActualVerticalField_v475
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def native_interior_graph_splitting_v475 : (E2 × ℝ) ≃L[ℝ] E3 :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun p => jetPoint (p.1,p.2,0)
    invFun := fun y => (native_collar_base_v475 y,y 2)
    left_inv := by
      intro p
      apply Prod.ext
      · ext i
        fin_cases i <;> simp [jetPoint,native_collar_base_v475]
      · simp [jetPoint]
    right_inv := by
      intro y
      ext i
      fin_cases i <;> simp [jetPoint,native_collar_base_v475]
    map_add' := by
      intro a b
      ext i
      fin_cases i <;> simp [jetPoint]
    map_smul' := by
      intro t a
      ext i
      fin_cases i <;> simp [jetPoint] }

@[simp] theorem native_interior_graph_splitting_apply_v475 (p : E2 × ℝ) :
    native_interior_graph_splitting_v475 p=jetPoint (p.1,p.2,0) := rfl
@[simp] theorem native_interior_graph_splitting_symm_apply_v475 (y : E3) :
    native_interior_graph_splitting_v475.symm y=(native_collar_base_v475 y,y 2) := rfl

#print axioms native_interior_graph_splitting_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
