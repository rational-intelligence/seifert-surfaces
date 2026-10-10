import B1InteriorGraphCalculus_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates

/-- Internal coordinate data constructed inside the common actual cylinder.
The compact set records the neighborhood on which ellipticity is estimated. -/
structure NativeInteriorGraphWindow_v475 where
  U : Set E2
  U_open : IsOpen U
  V : Set E3
  V_open : IsOpen V
  metric : CoordinateMetric V
  height : E2 → ℝ
  height_smooth : ContDiffOn ℝ ∞ height U
  compactBase : Set E2
  compactBase_compact : IsCompact compactBase
  U_contains : compactBase ⊆ U
  jets_inside : ∀ x ∈ compactBase, ∀ t ∈ Icc (0 : ℝ) 1,
    jetPoint (x,t*height x,t • planarGradient height x) ∈ V
namespace NativeInteriorGraphWindow_v475
def gram (W : NativeInteriorGraphWindow_v475) (j : Jet) : Mat2 :=
  fun i k => coordinateInner W.metric.tensor (jetPoint j)
    (jetTangent j.2.2 i) (jetTangent j.2.2 k)
def density (W : NativeInteriorGraphWindow_v475) (j : Jet) : ℝ := Real.sqrt (Matrix.det (W.gram j))
def flux (W : NativeInteriorGraphWindow_v475) (j : Jet) : E2 :=
  planarGradient (fun p : E2 => W.density (j.1, j.2.1, p)) j.2.2
def lower (W : NativeInteriorGraphWindow_v475) (j : Jet) : ℝ :=
  -deriv (fun z : ℝ => W.density (j.1, z, j.2.2)) j.2.1
def residual (W : NativeInteriorGraphWindow_v475) (u : E2 → ℝ) (x : E2) : ℝ :=
  (∑ i : Fin 2, fderiv ℝ (fun y : E2 => W.flux (y, u y, planarGradient u y) i) x
    (coordinateVector 2 i)) + W.lower (x, u x, planarGradient u x)

def segmentJet (W : NativeInteriorGraphWindow_v475) (x : E2) (t : ℝ) : Jet :=
  (x,t*W.height x,t • planarGradient W.height x)
def a (W : NativeInteriorGraphWindow_v475) (x : E2) : Mat2 := fun i j =>
  ∫ t in (0 : ℝ)..1, fderiv ℝ
    (fun p : E2 => W.flux (x,(W.segmentJet x t).2.1,p) i)
    (W.segmentJet x t).2.2 (coordinateVector 2 j)
def q (W : NativeInteriorGraphWindow_v475) (x : E2) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm fun i =>
    ∫ t in (0 : ℝ)..1, deriv
      (fun z : ℝ => W.flux (x,z,(W.segmentJet x t).2.2) i) (W.segmentJet x t).2.1
def lowerGradient (W : NativeInteriorGraphWindow_v475) (x : E2) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm fun i =>
    ∫ t in (0 : ℝ)..1, fderiv ℝ
      (fun p : E2 => W.lower (x,(W.segmentJet x t).2.1,p))
      (W.segmentJet x t).2.2 (coordinateVector 2 i)
def lowerHeight (W : NativeInteriorGraphWindow_v475) (x : E2) : ℝ :=
  ∫ t in (0 : ℝ)..1, deriv
    (fun z : ℝ => W.lower (x,z,(W.segmentJet x t).2.2)) (W.segmentJet x t).2.1
def b (W : NativeInteriorGraphWindow_v475) (x : E2) : E2 := W.q x+W.lowerGradient x
def c (W : NativeInteriorGraphWindow_v475) (x : E2) : ℝ :=
  (∑ i : Fin 2, fderiv ℝ (fun y => W.q y i) x (coordinateVector 2 i))+W.lowerHeight x
end NativeInteriorGraphWindow_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
