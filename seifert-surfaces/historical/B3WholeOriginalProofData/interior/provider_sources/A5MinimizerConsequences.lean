import OriginalA25SourceDefinitionsV464
import Mathlib.Analysis.Calculus.DerivativeTest

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology MeasureTheory Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

theorem geometricArea_nonnegative (g : SmoothMetric E.Carrier)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier) :
    0 ≤ geometricArea g F := by
  unfold geometricArea sectorArea sectorPartitionArea
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact integral_nonneg fun y => Real.sqrt_nonneg _

theorem FixedBoundaryImageIsotopic.boundary_image_eq
    {S R : CompactOrientedSurface.{u}}
    {F : GeometricPiecewiseSurface S E.Carrier}
    {G : GeometricPiecewiseSurface R E.Carrier}
    (h : FixedBoundaryImageIsotopic E F G) :
    G.map '' R.boundary = F.map '' S.boundary := by
  obtain ⟨e, stage, _, _, _, hlast, hfixed⟩ := h
  rw [← e.boundary_image, Set.image_image]
  apply Set.image_congr
  intro x hx
  have he := congrArg (fun f : C(S, E.Carrier) => f x) hlast
  exact he.symm.trans (hfixed 1 x hx)

theorem geometric_image_inter_boundary
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier) :
    F.image ∩ (𝓡∂ 3).boundary E.Carrier = F.map '' S.boundary := by
  ext y
  constructor
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, ?_, rfl⟩
    rw [← F.boundary_preimage]
    exact hx
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    rw [← F.boundary_preimage] at hx
    exact hx

theorem FixedBoundaryMinimizer.ambient_boundary_eq
    {g : SmoothMetric E.Carrier} {S R : CompactOrientedSurface.{u}}
    {F : GeometricPiecewiseSurface S E.Carrier}
    {Fprime : GeometricPiecewiseSurface R E.Carrier}
    (h : FixedBoundaryMinimizer E g F Fprime) :
    Fprime.image ∩ (𝓡∂ 3).boundary E.Carrier = F.map '' S.boundary :=
  (geometric_image_inter_boundary Fprime).trans h.in_class.boundary_image_eq

theorem FixedBoundaryMinimizer.area_le
    {g : SmoothMetric E.Carrier} {S R Q : CompactOrientedSurface.{u}}
    {F : GeometricPiecewiseSurface S E.Carrier}
    {Fprime : GeometricPiecewiseSurface R E.Carrier}
    (h : FixedBoundaryMinimizer E g F Fprime)
    (C : GeometricPiecewiseSurface Q E.Carrier)
    (hC : FixedBoundaryImageIsotopic E F C) :
    geometricArea g Fprime ≤ geometricArea g C := by
  rw [h.attainment]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro a ⟨R, C, _, rfl⟩
    exact geometricArea_nonnegative g C
  · exact ⟨Q, C, hC, rfl⟩

/-- The ordinary second-variation inequality at a continuous local minimum. -/
theorem second_deriv_nonnegative_of_local_min {f : ℝ → ℝ} {x : ℝ}
    (h : IsLocalMin f x) (hc : ContinuousAt f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra hn
  have hneg : deriv (deriv f) x < 0 := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hneg h.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [h, hmax] with y hy hy'
    exact le_antisymm hy' hy
  have hz := he.deriv.deriv_eq
  simp at hz
  linarith

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
