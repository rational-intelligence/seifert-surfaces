import B1ActualGeometry
import Mathlib.Topology.MetricSpace.Holder

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def disc (R : ℝ) : Set E2 := Metric.ball 0 R
def closedDisc (R : ℝ) : Set E2 := Metric.closedBall 0 R
def halfDisc (R : ℝ) : Set E2 := {x ∈ disc R | 0 < x 1}
def closedHalfDisc (R : ℝ) : Set E2 := {x ∈ closedDisc R | 0 ≤ x 1}
def flatArc (R : ℝ) : Set E2 := {x ∈ disc R | x 1 = 0}

def localCircle (D : B1OriginalData g J) (s : Circle) (t : ℝ) : Circle :=
  s * Circle.exp (2 * Real.pi * t / D.leafLength)
def localHeight (D : B1OriginalData g J) (s : Circle) (x : E2) : ℝ :=
  D.f (localCircle D s (x 0)) (x 1)
def localCollar (D : B1OriginalData g J) (s : Circle) (y : E3) : E.Carrier :=
  D.collar (localCircle D s (y 0), y 1, y 2)
def collarDomain (D : B1OriginalData g J) (R : ℝ) : Set E3 :=
  {y | |y 0| < 2 * R ∧ y 1 ∈ Icc (0 : ℝ) D.r0 ∧ |y 2| < D.eta}
def jetPoint (j : Jet) : E3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![j.1 0, j.1 1, j.2.1]
def jetTangent (p : E2) (i : Fin 2) : E3 :=
  coordinateVector 3 (Fin.castSucc i) + p i • coordinateVector 3 2

structure CollarWindow (D : B1OriginalData g J) (s : Circle) where
  R : ℝ
  R_pos : 0 < R
  R_radial : R < D.r0
  R_circle : 4 * R < D.leafLength
  U : Set E2
  U_open : IsOpen U
  U_contains : closedHalfDisc R ⊆ U
  height_smooth : ContDiffOn ℝ ∞ (localHeight D s) U
  V : Set E3
  V_open : IsOpen V
  metric : CoordinateMetric V
  jets_inside : ∀ x ∈ closedHalfDisc R, ∀ t ∈ Icc (0 : ℝ) 1,
    jetPoint (x, t * localHeight D s x, t • planarGradient (localHeight D s) x) ∈ V
  actual_metric : ∀ y ∈ V ∩ collarDomain D R, ∀ i j : Fin 3,
    metric.tensor y i j =
      g.inner (localCollar D s y)
        (mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (localCollar D s) (collarDomain D R) y
          ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 i)))
        (mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (localCollar D s) (collarDomain D R) y
          ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 j)))

namespace CollarWindow
variable {D : B1OriginalData g J} {s : Circle}
def gram (W : CollarWindow D s) (j : Jet) : Mat2 :=
  fun i k => coordinateInner W.metric.tensor (jetPoint j)
    (jetTangent j.2.2 i) (jetTangent j.2.2 k)
def density (W : CollarWindow D s) (j : Jet) : ℝ := Real.sqrt (Matrix.det (W.gram j))
def flux (W : CollarWindow D s) (j : Jet) : E2 :=
  planarGradient (fun p : E2 => W.density (j.1, j.2.1, p)) j.2.2
def lower (W : CollarWindow D s) (j : Jet) : ℝ :=
  -deriv (fun z : ℝ => W.density (j.1, z, j.2.2)) j.2.1
def residual (W : CollarWindow D s) (u : E2 → ℝ) (x : E2) : ℝ :=
  (∑ i : Fin 2, fderiv ℝ (fun y : E2 => W.flux (y, u y, planarGradient u y) i) x
    (coordinateVector 2 i)) + W.lower (x, u x, planarGradient u x)
def segmentJet (W : CollarWindow D s) (x : E2) (t : ℝ) : Jet :=
  (x, t * localHeight D s x, t • planarGradient (localHeight D s) x)
def a (W : CollarWindow D s) (x : E2) : Mat2 := fun i j =>
  ∫ t in (0 : ℝ)..1, fderiv ℝ
    (fun p : E2 => W.flux (x, (W.segmentJet x t).2.1, p) i)
    (W.segmentJet x t).2.2 (coordinateVector 2 j)
def q (W : CollarWindow D s) (x : E2) : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm fun i =>
  ∫ t in (0 : ℝ)..1, deriv
    (fun z : ℝ => W.flux (x, z, (W.segmentJet x t).2.2) i) (W.segmentJet x t).2.1
def lowerGradient (W : CollarWindow D s) (x : E2) : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm fun i =>
  ∫ t in (0 : ℝ)..1, fderiv ℝ
    (fun p : E2 => W.lower (x, (W.segmentJet x t).2.1, p))
    (W.segmentJet x t).2.2 (coordinateVector 2 i)
def lowerHeight (W : CollarWindow D s) (x : E2) : ℝ :=
  ∫ t in (0 : ℝ)..1, deriv
    (fun z : ℝ => W.lower (x, z, (W.segmentJet x t).2.2)) (W.segmentJet x t).2.1
def b (W : CollarWindow D s) (x : E2) : E2 := W.q x + W.lowerGradient x
def c (W : CollarWindow D s) (x : E2) : ℝ :=
  (∑ i : Fin 2, fderiv ℝ (fun y : E2 => W.q y i) x (coordinateVector 2 i)) + W.lowerHeight x
end CollarWindow

def matrixAction (a : Mat2) (p : E2) : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm fun i => ∑ j, a i j * p j
def classicalL (a : E2 → Mat2) (b : E2 → E2) (c u : E2 → ℝ) (x : E2) : ℝ :=
  (∑ i : Fin 2, fderiv ℝ (fun y : E2 => matrixAction (a y) (planarGradient u y) i) x
    (coordinateVector 2 i)) + inner ℝ (b x) (planarGradient u x) + c x * u x

def SmoothEllipticOn (a : E2 → Mat2) (b : E2 → E2) (c : E2 → ℝ) (H : Set E2) : Prop :=
  (∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) H) ∧ ContDiffOn ℝ ∞ b H ∧ ContDiffOn ℝ ∞ c H ∧
  (∀ x ∈ H, ∀ i j, a x i j = a x j i) ∧
  ∃ ell C : ℝ, 0 < ell ∧ 0 < C ∧ ∀ x ∈ H, ∀ p : E2,
    ell * ‖p‖ ^ 2 ≤ inner ℝ p (matrixAction (a x) p) ∧
    inner ℝ p (matrixAction (a x) p) ≤ C * ‖p‖ ^ 2

/- Local extension of the literal supplied collar metric and graph at s. -/
end SeifertSurfaces.OriginalEndpoints.B1Tangency
