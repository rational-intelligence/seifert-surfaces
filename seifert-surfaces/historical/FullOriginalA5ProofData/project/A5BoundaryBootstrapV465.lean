import A5BoundaryBootstrapDefinitionsV465
import NativeBoundaryAllFiniteOrders

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

/-- The full local Dirichlet boundary bootstrap used in source Proposition A.5:
a C¹ weak solution of the smooth uniformly elliptic quasilinear divergence
equation with smooth flat-boundary values is C∞ on every strictly smaller
closed half-disc. The conclusion includes its boundary and retains exactly `u`.

Source: `references/seifert-surfaces.txt`, lines 1271--1279, p. 26, after the
projected longitude boundary has been straightened. The geometric straightening
and its same-operator weak-equation bridge belong to the original A5 owner.
This declaration is an open proof obligation, not a supplied regularity oracle. -/
theorem smooth_of_C1_weak_uniformlyElliptic_dirichlet
    (ρ : ℝ) (hρ : 0 < ρ) (J : Set Jet) (Q : SmoothQuasilinearOperator J)
    (g : SmoothDirichletDatum ρ) (u : E2 → ℝ)
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (r : ℝ) (hr : 0 < r) (hrρ : r < ρ) :
    ContDiffOn ℝ ∞ u (closedHalfDisc r) := by
  apply contDiffOn_infty.mpr
  intro n
  exact hsolution.all_finite_orders_on_smaller_closedHalfDisc hρ r hr hrρ n

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
