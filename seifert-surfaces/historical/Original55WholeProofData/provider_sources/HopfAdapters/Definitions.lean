import AppendixACoordinates

/-
The `partialD` and `nondivOp` formulas below are adapted from EllipticPDE,
Copyright (c) 2026 Alejandro Soto Franco, released under Apache 2.0.
Exact upstream commit: eaf821d31b200bb6ea235f19eecc50cf0f38c294.
See provenance/LICENSE.EllipticPDE and source-map.md.
-/

noncomputable section

open Set Metric Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.AppendixACoordinates.HopfAdapters

/-- The classical coordinate partial used by the public Hopf operator. -/
def partialD {d : ℕ} (i : Fin d) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- Literal public convention: minus the second-order part, plus drift and potential. -/
def nondivOp {d : ℕ} (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ)
    (c : EuclideanSpace ℝ (Fin d) → ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -(∑ i, ∑ j, a x i j * partialD i (partialD j f) x) +
    ∑ i, b x i * partialD i f x + c x * f x

/-- The derivative field on the closed tangent ball uses within derivatives. -/
def boundaryGraphLinearization (K : Set E2) (L : E2 →L[ℝ] E3)
    (normal : E3) (w : E2 → ℝ) (x : E2) : E2 →L[ℝ] E3 :=
  L + (fderivWithin ℝ w K x).smulRight normal

def extendedGram (g : MetricTensor) (Φ : E2 → E3)
    (F : E2 → E2 →L[ℝ] E3) (x : E2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => coordinateInner g (Φ x) (F x (coordinateVector 2 i))
    (F x (coordinateVector 2 j))

def inverseGram (g : MetricTensor) (Φ : E2 → E3)
    (F : E2 → E2 →L[ℝ] E3) (x : E2) : Matrix (Fin 2) (Fin 2) ℝ :=
  (extendedGram g Φ F x)⁻¹

/-- The fixed projection along the normal onto the original graph plane. -/
structure GraphProjection (L : E2 →L[ℝ] E3) (normal : E3) where
  map : E3 →L[ℝ] E2
  leftInverse : map.comp L = ContinuousLinearMap.id ℝ E2
  killsNormal : map normal = 0

def christoffelVector (g : MetricTensor) (y u v : E3) : E3 :=
  ∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3,
    christoffel g y a b k * u a * v b) • coordinateVector 3 k

def tracedChristoffel (g : MetricTensor) (Φ : E2 → E3)
    (F : E2 → E2 →L[ℝ] E3) (a : E2 → Matrix (Fin 2) (Fin 2) ℝ)
    (x : E2) : E3 :=
  ∑ i : Fin 2, ∑ j : Fin 2, a x i j •
    christoffelVector g (Φ x) (F x (coordinateVector 2 i))
      (F x (coordinateVector 2 j))

def graphDrift (P : E3 →L[ℝ] E2) (C : E2 → E3) (x : E2) : E2 :=
  P (C x)

def interiorChristoffelTrace (g : MetricTensor) (Φ : E2 → E3) : E2 → E3 :=
  tracedChristoffel g Φ (fderiv ℝ Φ) (fun x => (inducedMetric g Φ x)⁻¹)

def hessianBilinear (g : MetricTensor) (r : E3 → ℝ) (y u v : E3) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, hessianCoefficient g r y a b * u a * v b

def pullbackHessian (g : MetricTensor) (r : E3 → ℝ) (Φ : E2 → E3)
    (x : E2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => hessianBilinear g r (Φ x) (graphTangent Φ x i) (graphTangent Φ x j)

def graphHeight (r : E3 → ℝ) (Φ : E2 → E3) (x : E2) : ℝ := r (Φ x)

/-- This extends one prescribed first-order jet; no global smoothness is claimed. -/
def affineOutsideExtension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (f : E → ℝ) (x₀ : E) (D : E →L[ℝ] ℝ) (x : E) : ℝ :=
  @ite ℝ (x ∈ K) (Classical.propDecidable _) (f x) (f x₀ + D (x - x₀))

/-- Actual scalar supplied to Hopf, equal to the negative graph height on the ball. -/
def hopfGraphExtension (c : E2) (R : ℝ) (p : E3) (L : E2 →L[ℝ] E3)
    (normal : E3) (w : E2 → ℝ) (r : E3 → ℝ) : E2 → ℝ :=
  affineOutsideExtension (closedBall c R)
    (fun x => -graphHeight r (graphMap p L normal w) x) 0
    (-((fderiv ℝ r p).comp L))

/-- The concrete coefficient estimates needed by Hopf, on the same closed ball. -/
structure CoefficientBounds (K : Set E2) (a : E2 → Matrix (Fin 2) (Fin 2) ℝ)
    (b : E2 → E2) where
  theta : ℝ
  secondBound : ℝ
  driftBound : ℝ
  thetaPositive : 0 < theta
  secondBoundNonnegative : 0 ≤ secondBound
  driftBoundNonnegative : 0 ≤ driftBound
  elliptic : ∀ x ∈ K, ∀ ξ : Fin 2 → ℝ,
    theta * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j
  secondBounded : ∀ x ∈ K, ∀ i j, |a x i j| ≤ secondBound
  driftBounded : ∀ x ∈ K, ∀ i, |b x i| ≤ driftBound

end SeifertSurfaces.AppendixACoordinates.HopfAdapters
