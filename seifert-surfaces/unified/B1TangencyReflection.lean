import B1TangencyCoordinates

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

def reflectPoint (x : E2) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x 0, -x 1]
def oddReflect (u : E2 → ℝ) (x : E2) : ℝ :=
  if 0 ≤ x 1 then u x else -u (reflectPoint x)
def driftReflect (b : E2 → E2) (x : E2) : E2 :=
  if 0 ≤ x 1 then b x else
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ![b (reflectPoint x) 0, -b (reflectPoint x) 1]

def complexPoint (z : ℂ) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![z.re, z.im]
def complexGradient (u : E2 → ℝ) (z : ℂ) : ℂ :=
  (planarGradient u (complexPoint z) 0 : ℂ) -
    Complex.I * (planarGradient u (complexPoint z) 1 : ℂ)
def dbarTest (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ φ z 1 + Complex.I * fderiv ℝ φ z Complex.I)
def vekuaA (b : E2 → E2) (z : ℂ) : ℂ :=
  -(1 / 4 : ℂ) * ((b (complexPoint z) 0 : ℂ) + Complex.I * (b (complexPoint z) 1 : ℂ))
def vekuaB (b : E2 → E2) (z : ℂ) : ℂ :=
  -(1 / 4 : ℂ) * ((b (complexPoint z) 0 : ℂ) - Complex.I * (b (complexPoint z) 1 : ℂ))

def WeakVekuaOn (U : Set ℂ) (w A B : ℂ → ℂ) : Prop :=
  LocallyIntegrableOn w U ∧
  ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    IntegrableOn (fun z => w z * dbarTest φ z) U ∧
    IntegrableOn (fun z => (A z * w z + B z * star (w z)) * φ z) U ∧
    (∫ z in U, w z * dbarTest φ z) =
      -(∫ z in U, (A z * w z + B z * star (w z)) * φ z)

namespace BoundaryIsothermalPatch
variable {D : B1OriginalData g J} {s : Circle} {W : CollarWindow D s}
variable {N : PositiveNormalization W}
def reflectedV (F : BoundaryIsothermalPatch N) : E2 → ℝ := oddReflect F.vhat
def reflectedB (F : BoundaryIsothermalPatch N) : E2 → E2 := driftReflect F.bhat
def w (F : BoundaryIsothermalPatch N) : ℂ → ℂ := complexGradient F.reflectedV
end BoundaryIsothermalPatch

/- Same v=f/h after the same boundary chart, odd extension of v and the
specified even/odd drift. Conormal cancellation is an owed proof, not an input. -/
end SeifertSurfaces.OriginalEndpoints.B1Tangency
