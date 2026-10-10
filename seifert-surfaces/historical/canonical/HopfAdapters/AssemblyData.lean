import HopfAdapters.Definitions

noncomputable section
open Set Metric Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.AppendixACoordinates.HopfAdapters

/-- A concrete Hopf input on a tangent ball; the coefficient fields are fixed formulas.
This contains no assumption of the desired nonzero differential. -/
structure GraphHopfBall (g : MetricTensor) (U : Set E2) (p normal : E3)
    (L : E2 →L[ℝ] E3) (w : E2 → ℝ) (r : E3 → ℝ) where
  center : E2
  radius : ℝ
  radiusPositive : 0 < radius
  ballSubset : ball center radius ⊆ interior U
  touching : dist (0 : E2) center = radius
  closedBallSubset : closedBall center radius ⊆ U
  projection : GraphProjection L normal
  bounds : CoefficientBounds (closedBall center radius)
    (inverseGram g (graphMap p L normal w)
      (boundaryGraphLinearization (closedBall center radius) L normal w))
    (graphDrift projection.map
      (tracedChristoffel g (graphMap p L normal w)
        (boundaryGraphLinearization (closedBall center radius) L normal w)
        (inverseGram g (graphMap p L normal w)
          (boundaryGraphLinearization (closedBall center radius) L normal w))))
  symmetric : ∀ x ∈ closedBall center radius, ∀ i j,
    inverseGram g (graphMap p L normal w)
      (boundaryGraphLinearization (closedBall center radius) L normal w) x i j =
    inverseGram g (graphMap p L normal w)
      (boundaryGraphLinearization (closedBall center radius) L normal w) x j i
  scalarSmooth : ContDiffOn ℝ 2 (hopfGraphExtension center radius p L normal w r)
    (ball center radius)
  scalarContinuous : ContinuousOn (hopfGraphExtension center radius p L normal w r)
    (closedBall center radius)
  scalarSubsolution : ∀ x ∈ ball center radius,
    nondivOp
      (inverseGram g (graphMap p L normal w)
        (boundaryGraphLinearization (closedBall center radius) L normal w))
      (fun z i => graphDrift projection.map
        (tracedChristoffel g (graphMap p L normal w)
          (boundaryGraphLinearization (closedBall center radius) L normal w)
          (inverseGram g (graphMap p L normal w)
            (boundaryGraphLinearization (closedBall center radius) L normal w))) z i)
      (fun _ => 0) (hopfGraphExtension center radius p L normal w r) x ≤ 0
  scalarZero : hopfGraphExtension center radius p L normal w r 0 = 0
  scalarNegative : ∀ x ∈ ball center radius,
    hopfGraphExtension center radius p L normal w r x < 0
  scalarDerivative : HasFDerivAt (hopfGraphExtension center radius p L normal w r)
    (-((fderiv ℝ r p).comp L)) 0

end SeifertSurfaces.AppendixACoordinates.HopfAdapters
