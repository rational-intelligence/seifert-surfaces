import HopfAdapters.Assembly

noncomputable section
open Set Metric Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.AppendixACoordinates

theorem A4_hopf_coordinate
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
  exact HopfAdapters.A4_hopf_coordinate_via_adapters V hV g U hU h0 hsphere
    p normal hp hnormal L hL hnormalOrthogonal w hw₀ hwC1 hwflat hgraph hminimal
    r hrSmooth hr₀ hrNonnegative hrPositive hHess

end SeifertSurfaces.AppendixACoordinates
