import HopfAdapters.AssemblyData
import HopfAdapters.Coefficients
import HopfAdapters.TraceEquation
import HopfAdapters.ScalarWrapper

noncomputable section
open Set Metric Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.AppendixACoordinates.HopfAdapters

/-- All concrete Hopf inputs are produced from the original A.4 assumptions. -/
theorem exists_graph_hopf_ball
    (V : Set E3) (hV : IsOpen V) (g : CoordinateMetric V)
    (U : Set E2) (hU : IsClosed U) (h0 : (0 : E2) ∈ frontier U)
    (hsphere : InteriorSphereAt U 0)
    (p normal : E3) (hp : p ∈ V) (hnormal : normal ≠ 0)
    (L : E2 →L[ℝ] E3) (hL : Function.Injective L)
    (hnormalOrthogonal : ∀ v : E2, coordinateInner g.tensor p (L v) normal = 0)
    (w : E2 → ℝ) (hw₀ : w 0 = 0) (hwC1 : ContDiffOn ℝ 1 w U)
    (hwflat : HasFDerivWithinAt w (0 : E2 →L[ℝ] ℝ) U 0)
    (hgraph : MapsTo (graphMap p L normal w) U V)
    (hminimal : IsMinimalParametrizationOn g.tensor (graphMap p L normal w) (interior U))
    (r : E3 → ℝ) (hrSmooth : ContDiffOn ℝ ∞ r V) (hr₀ : r p = 0)
    (hrNonnegative : ∀ x ∈ U, 0 ≤ r (graphMap p L normal w x))
    (hrPositive : ∀ x ∈ interior U, 0 < r (graphMap p L normal w x))
    (hHess : ∀ x ∈ interior U, ∀ v : E3,
      hessianQuadratic g.tensor r (graphMap p L normal w x) v ≤ 0) :
    Nonempty (GraphHopfBall g.tensor U p normal L w r) := by
  obtain ⟨c, R, hR, hB, hdist, hK, hzero, hcompact, hconvex, hdiff⟩ :=
    exists_closed_tangent_ball U hU hsphere
  obtain ⟨P⟩ := exists_graph_projection V g p normal hp hnormal L hL hnormalOrthogonal
  obtain ⟨ha, hb, hpositive, hsymm, ⟨bounds⟩⟩ :=
    exists_graph_coefficient_bounds V hV g U p normal hp hnormal L hL
      hnormalOrthogonal P w hwC1 hgraph c R hR hK
  obtain ⟨hscalarSmooth, hscalarContinuous⟩ :=
    hopf_graph_extension_regular V hV g U p normal L w hwC1 hgraph hminimal
      r hrSmooth c R hK hB
  obtain ⟨hscalarZero, hscalarNegative⟩ :=
    hopf_graph_extension_values U p normal L w hw₀ r hr₀ hrPositive c R hR hdist hB
  refine ⟨{
    center := c
    radius := R
    radiusPositive := hR
    ballSubset := hB
    touching := hdist
    closedBallSubset := hK
    projection := P
    bounds := bounds
    symmetric := hsymm
    scalarSmooth := hscalarSmooth
    scalarContinuous := hscalarContinuous
    scalarSubsolution := ?_
    scalarZero := hscalarZero
    scalarNegative := hscalarNegative
    scalarDerivative := hopf_graph_extension_boundary_derivative V hV U p normal hp
      L w hw₀ hwflat r hrSmooth c R hK hzero }⟩
  intro x hx
  change nondivOp (fun z i j => inverseGram g.tensor (graphMap p L normal w)
      (boundaryGraphLinearization (closedBall c R) L normal w) z i j)
    (fun z i => graphDrift P.map
      (tracedChristoffel g.tensor (graphMap p L normal w)
        (boundaryGraphLinearization (closedBall c R) L normal w)
        (inverseGram g.tensor (graphMap p L normal w)
          (boundaryGraphLinearization (closedBall c R) L normal w))) z i)
    (fun _ => 0) (affineOutsideExtension (closedBall c R)
    (fun z => -graphHeight r (graphMap p L normal w) z) 0
    (-((fderiv ℝ r p).comp L))) x ≤ 0
  rw [affine_extension_nondivOp_eq
    (fun z i j => inverseGram g.tensor (graphMap p L normal w)
      (boundaryGraphLinearization (closedBall c R) L normal w) z i j)
    (fun z i => graphDrift P.map
      (tracedChristoffel g.tensor (graphMap p L normal w)
        (boundaryGraphLinearization (closedBall c R) L normal w)
        (inverseGram g.tensor (graphMap p L normal w)
          (boundaryGraphLinearization (closedBall c R) L normal w))) z i)
    (fun _ => 0) (closedBall c R)
    (fun z => -graphHeight r (graphMap p L normal w) z) 0
    (-((fderiv ℝ r p).comp L)) x
    (ball_subset_interior_closedBall hx)]
  exact negative_graph_height_subsolution V hV g U p normal hp hnormal L hL
    hnormalOrthogonal P w hwC1 hgraph hminimal r hrSmooth hHess c R hK hB x hx

/-- The fully produced scalar inputs imply the strict outward derivative. -/
theorem graph_hopf_ball_outward_derivative (g : MetricTensor) (U : Set E2)
    (p normal : E3) (L : E2 →L[ℝ] E3) (w : E2 → ℝ) (r : E3 → ℝ)
    (H : GraphHopfBall g U p normal L w r) :
    0 < (-((fderiv ℝ r p).comp L)) ((0 : E2) - H.center) := by
  have hhopf := EllipticPdes.Classical.hopf_lemma_ball (d := 2) (by norm_num)
    H.radiusPositive H.bounds.thetaPositive
    (fun x hx => H.symmetric x (ball_subset_closedBall hx))
    (fun x hx => H.bounds.elliptic x (ball_subset_closedBall hx))
    (fun x hx => H.bounds.secondBounded x (ball_subset_closedBall hx))
    (fun x hx => H.bounds.driftBounded x (ball_subset_closedBall hx))
    (c := fun _ => 0) (C := 0) (by simp) (by simp)
    H.scalarSmooth H.scalarContinuous H.scalarSubsolution H.touching
    (fun x hx => by rw [H.scalarZero]; exact H.scalarNegative x hx)
    (by simp) H.scalarDerivative.differentiableAt
  rwa [H.scalarDerivative.fderiv] at hhopf

/-- A distinct assembly obligation with the original protected A.4 binder list. -/
theorem A4_hopf_coordinate_via_adapters
    (V : Set E3) (hV : IsOpen V) (g : CoordinateMetric V)
    (U : Set E2) (hU : IsClosed U) (h0 : (0 : E2) ∈ frontier U)
    (hsphere : InteriorSphereAt U 0)
    (p normal : E3) (hp : p ∈ V) (hnormal : normal ≠ 0)
    (L : E2 →L[ℝ] E3) (hL : Function.Injective L)
    (hnormalOrthogonal : ∀ v : E2, coordinateInner g.tensor p (L v) normal = 0)
    (w : E2 → ℝ) (hw₀ : w 0 = 0) (hwC1 : ContDiffOn ℝ 1 w U)
    (hwflat : HasFDerivWithinAt w (0 : E2 →L[ℝ] ℝ) U 0)
    (hgraph : MapsTo (graphMap p L normal w) U V)
    (hminimal : IsMinimalParametrizationOn g.tensor (graphMap p L normal w) (interior U))
    (r : E3 → ℝ) (hrSmooth : ContDiffOn ℝ ∞ r V) (hr₀ : r p = 0)
    (hrNonnegative : ∀ x ∈ U, 0 ≤ r (graphMap p L normal w x))
    (hrPositive : ∀ x ∈ interior U, 0 < r (graphMap p L normal w x))
    (hHess : ∀ x ∈ interior U, ∀ v : E3,
      hessianQuadratic g.tensor r (graphMap p L normal w x) v ≤ 0) :
    (fderiv ℝ r p).comp L ≠ 0 := by
  obtain ⟨H⟩ := exists_graph_hopf_ball V hV g U hU h0 hsphere p normal hp hnormal L hL
    hnormalOrthogonal w hw₀ hwC1 hwflat hgraph hminimal r hrSmooth hr₀
    hrNonnegative hrPositive hHess
  exact positive_negative_direction_implies_nonzero _ H.center
    (graph_hopf_ball_outward_derivative g.tensor U p normal L w r H)

end SeifertSurfaces.AppendixACoordinates.HopfAdapters
