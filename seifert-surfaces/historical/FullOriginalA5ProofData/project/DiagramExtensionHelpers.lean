import DiagramSamplingHelpers

set_option maxSynthPendingDepth 3
set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.LongitudeProducers
open Foundations MetricFoundations
noncomputable section

def euclideanRectangle (a b : Euc 2) : Set (Euc 2) := {x | ∀ j, a j ≤ x j ∧ x j ≤ b j}

/-- E1 retains each supplied coordinate and its graph on a concrete closed rectangle. -/
structure FiniteCurveExtensionCover {f g : Circle → Euc 3} (H : PiecewiseCurveIsotopy f g) where
  count : ℕ
  lower : Fin count → Euc 2
  upper : Fin count → Euc 2
  nondegenerate : ∀ i j, lower i j < upper i j
  coordinateIndex : Fin count → Fin H.count
  parameter : ∀ i, C(↥(euclideanRectangle (lower i) (upper i)), Time × Time)
  neighborhood : Fin count → Set (Euc 2)
  neighborhood_open : ∀ i, IsOpen (neighborhood i)
  neighborhood_contains : ∀ i, euclideanRectangle (lower i) (upper i) ⊆ neighborhood i
  sourceCoordinates : Fin count → Euc 2 → Euc 2
  targetCoordinates : Fin count → Euc 2 → Euc 4
  source_regular : ∀ i, ContDiffOn ℝ 1 (sourceCoordinates i) (neighborhood i)
  target_regular : ∀ i, ContDiffOn ℝ 1 (targetCoordinates i) (neighborhood i)
  source_time : ∀ i (x : ↥(euclideanRectangle (lower i) (upper i))), sourceCoordinates i x 0 =
    (H.coordinate (coordinateIndex i) (parameter i x)).1
  source_angle : ∀ i (x : ↥(euclideanRectangle (lower i) (upper i))), Circle.exp (sourceCoordinates i x 1) =
    (H.coordinate (coordinateIndex i) (parameter i x)).2
  target_eq : ∀ i (x : ↥(euclideanRectangle (lower i) (upper i))), targetCoordinates i x =
    let p := H.coordinate (coordinateIndex i) (parameter i x)
    !₂[(p.1 : ℝ), H.stage p.1 p.2 0, H.stage p.1 p.2 1, H.stage p.1 p.2 2]
  lowerBound : Fin count → ℝ
  lowerBound_pos : ∀ i, 0 < lowerBound i
  source_minor : ∀ i, ∀ x ∈ euclideanRectangle (lower i) (upper i),
    lowerBound i ≤ |orientedPlaneDet
      (fderiv ℝ (sourceCoordinates i) x (EuclideanSpace.single 0 1))
      (fderiv ℝ (sourceCoordinates i) x (EuclideanSpace.single 1 1))|
  target_lower : ∀ i, ∀ x ∈ euclideanRectangle (lower i) (upper i), ∀ v : Euc 2,
    lowerBound i * ‖v‖ ≤ ‖fderiv ℝ (targetCoordinates i) x v‖
  covers : (⋃ i, Set.range (fun x : ↥(euclideanRectangle (lower i) (upper i)) =>
    ((sourceCoordinates i x 0), Circle.exp (sourceCoordinates i x 1)))) =
      Set.Icc (0 : ℝ) 1 ×ˢ Set.univ

structure SmoothCurveReplacement (f g : Circle → Euc 3) where
  map : ℝ × Circle → Euc 3
  smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, Euc 3) ∞ map
    (Set.Icc 0 1 ×ˢ Set.univ)
  embedding : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, Euc 3) ∞ (fun z => map (t, z))
  initial : ∀ z, map (0, z) = f z
  terminal : ∀ z, map (1, z) = g z

end
end SeifertSurfaces.LongitudeProducers
