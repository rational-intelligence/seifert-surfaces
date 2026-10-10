import AppendixAInteriorRegularity
import WeakScalarBoundaryLower

/-!
Native analytic data for the Dirichlet boundary regularity step in source
Proposition A.5, pp. 25--26, extracted lines 1271--1279. The closed half-disc,
jet space, quasilinear operator, ellipticity, and weak equation are the actual
Appendix A definitions. Coordinate 0 is the normal coordinate here.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

/-- The open half-disc corresponding to the native `closedHalfDisc`. -/
def openHalfDisc (ρ : ℝ) : Set E2 :=
  Metric.ball 0 ρ ∩ {x : E2 | 0 < x 0}

/-- The smooth, flat boundary portion; the artificial outer endpoints are omitted. -/
def flatBoundary (ρ : ℝ) : Set E2 :=
  Metric.ball 0 ρ ∩ {x : E2 | x 0 = 0}

/-- Gradient computed from the derivative within the specified actual set.
It places no condition on the arbitrary values of `u` outside that set. -/
def planarGradientWithin (u : E2 → ℝ) (s : Set E2) (x : E2) : E2 :=
  ∑ i : Fin 2, fderivWithin ℝ u s x (coordinateVector 2 i) • coordinateVector 2 i

/-- Actual first jet up to the boundary, using the closed half-disc derivative. -/
def firstJetWithin (ρ : ℝ) (u : E2 → ℝ) (x : E2) : Jet :=
  (x, u x, planarGradientWithin u (closedHalfDisc ρ) x)

/-- Smooth scalar Dirichlet values in the actual tangential coordinate `x 1`.
Only their values on `(-ρ, ρ)` matter; no regularity of the solution is encoded. -/
structure SmoothDirichletDatum (ρ : ℝ) where
  value : ℝ → ℝ
  smooth : ContDiffOn ℝ ∞ value (Ioo (-ρ) ρ)

/-- The complete starting analytic hypotheses for the same function and operator.
No Hölder gradient, boundary Schauder estimate, higher solution regularity, or
smooth solution representative is supplied. -/
structure C1QuasilinearDirichletSolution (ρ : ℝ) (J : Set Jet)
    (Q : SmoothQuasilinearOperator J) (g : SmoothDirichletDatum ρ)
    (u : E2 → ℝ) : Prop where
  jet_domain_open : IsOpen J
  uniformly_elliptic : UniformlyEllipticOn J Q.flux
  c1 : ContDiffOn ℝ 1 u (closedHalfDisc ρ)
  attained_jets : ∀ x ∈ closedHalfDisc ρ, firstJetWithin ρ u x ∈ J
  weak_equation : IsWeakDivergenceSolutionOn (openHalfDisc ρ) Q.flux Q.lowerOrder u
  dirichlet_values : ∀ x ∈ flatBoundary ρ, u x = g.value (x 1)

/-- Coordinate permutation for transporting A5 (normal coordinate 0) to the
paid B1 scalar estimate (normal coordinate 1). This is an actual linear isometry. -/
def coordinateSwap : E2 ≃ₗᵢ[ℝ] E2 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)

/-- The same scalar solution expressed in the B1 coordinates. -/
def functionInB1Coordinates (u : E2 → ℝ) : E2 → ℝ :=
  fun y => u (coordinateSwap.symm y)

/-- Both the position and gradient of a jet must be transported. -/
def jetFromB1Coordinates (j : Jet) : Jet :=
  (coordinateSwap.symm j.1, j.2.1, coordinateSwap.symm j.2.2)

/-- The same flux after the orthogonal coordinate change, not a new operator. -/
def fluxInB1Coordinates (A : Jet → E2) : Jet → E2 :=
  fun j => coordinateSwap (A (jetFromB1Coordinates j))

/-- The same lower-order coefficient in the transported coordinates. -/
def lowerOrderInB1Coordinates (B : Jet → ℝ) : Jet → ℝ :=
  fun j => B (jetFromB1Coordinates j)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
