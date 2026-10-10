import B1TangencyGraph

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

def WeakGradientOn (U : Set E2) (u : E2 → ℝ) (du : E2 → E2) : Prop :=
  LocallyIntegrableOn u U ∧ LocallyIntegrableOn du U ∧
  ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∀ i : Fin 2,
      (∫ x in U, u x * fderiv ℝ φ x (coordinateVector 2 i)) =
        -(∫ x in U, du x i * φ x)
def H1On (U : Set E2) (u : E2 → ℝ) (du : E2 → E2) : Prop :=
  WeakGradientOn U u du ∧ MemLp u 2 (volume.restrict U) ∧ MemLp du 2 (volume.restrict U)
def H10On (U : Set E2) (u : E2 → ℝ) (du : E2 → E2) : Prop :=
  H1On U u du ∧ ∀ ε : ℝ, 0 < ε → ∃ φ : E2 → ℝ,
    ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
    (∫ x in U, |u x - φ x| ^ 2 + ‖du x - planarGradient φ x‖ ^ 2) < ε

def WeakLinearEquationOn (U : Set E2) (a : E2 → Mat2) (b : E2 → E2)
    (c u : E2 → ℝ) (du : E2 → E2) : Prop :=
  WeakGradientOn U u du ∧
  ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    IntegrableOn (fun x => inner ℝ (matrixAction (a x) (du x)) (planarGradient φ x) -
      (inner ℝ (b x) (du x) + c x * u x) * φ x) U ∧
    (∫ x in U, inner ℝ (matrixAction (a x) (du x)) (planarGradient φ x) -
      (inner ℝ (b x) (du x) + c x * u x) * φ x) = 0

structure PositiveNormalization {D : B1OriginalData g J} {s : Circle}
    (W : CollarWindow D s) where
  R : ℝ
  R_pos : 0 < R
  R_inside : R < W.R
  h : E2 → ℝ
  h_continuous : ContinuousOn h (closedHalfDisc R)
  h_boundary_one : ∀ x ∈ frontier (halfDisc R), h x = 1
  h_lower_bound : ∀ x ∈ closedHalfDisc R, (1 / 2 : ℝ) ≤ h x
  dh : E2 → E2
  h_H1 : H1On (halfDisc R) h dh
  h_minus_one_H10 : H10On (halfDisc R) (fun x => h x - 1) dh
  h_weak : WeakLinearEquationOn (halfDisc R) W.a W.b W.c h dh
  N : Set E2
  N_open : IsOpen N
  N_contains : closedHalfDisc (R / 2) ⊆ N
  h_smooth_near_base : ContDiffOn ℝ ∞ h N
  h_smooth_interior : ContDiffOn ℝ ∞ h (halfDisc R)
  dh_exact : ∀ x ∈ halfDisc R, dh x = planarGradient h x
  h_classical : ∀ x ∈ halfDisc R, classicalL W.a W.b W.c h x = 0

namespace PositiveNormalization
variable {D : B1OriginalData g J} {s : Circle} {W : CollarWindow D s}
def v (N : PositiveNormalization W) (x : E2) : ℝ := localHeight D s x / N.h x
def leading (N : PositiveNormalization W) (x : E2) : Mat2 := N.h x • W.a x
def drift (N : PositiveNormalization W) (x : E2) : E2 :=
  matrixAction (W.a x) (planarGradient N.h x) + N.h x • W.b x
def factor (N : PositiveNormalization W) (x : E2) : ℝ :=
  (Real.sqrt (Matrix.det (N.leading x)))⁻¹
def normalizedA (N : PositiveNormalization W) (x : E2) : Mat2 :=
  N.factor x • N.leading x
def normalizedB (N : PositiveNormalization W) (x : E2) : E2 :=
  N.factor x • N.drift x - matrixAction (N.leading x) (planarGradient N.factor x)
end PositiveNormalization

def LipschitzBoundOn {F : Type*} [PseudoMetricSpace F] (f : E2 → F) (U : Set E2) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ y ∈ U, dist (f x) (f y) ≤ C * dist x y

def BoundedOn {F : Type*} [Norm F] (f : E2 → F) (U : Set E2) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ‖f x‖ ≤ C

/- Small-domain Dirichlet construction. The original coefficient c has no
sign hypothesis. GT Ch.8/Thm5.8 route remains a proof obligation. -/
end SeifertSurfaces.OriginalEndpoints.B1Tangency
