import CurveComplexGenusTwo.Foundations.Definitions
import Schoenflies.JordanSchoenflies
import Mathlib.Analysis.Convex.GaugeRescale

/-!
An independent intermediate for the universal-cover route.  The recovery branch
already handles the deck-action and projection-injectivity transfer; this file
only packages relative Schoenflies as an embedded closed-square witness.
-/

namespace CurveComplex

open Topology

private abbrev Plane := Schoenflies.Plane
private abbrev Square := Schoenflies.Plane.closedSquare 0 1
private abbrev UnitDisc := Metric.closedBall (0 : Plane) 1
private def ModelBoundary : Set Square :=
  {x | (x : Plane) ∈ Schoenflies.modelCurve}
private def DiscBoundary : Set UnitDisc :=
  {x | (x : Plane) ∈ Metric.sphere 0 1}

/-- A planar Jordan curve has an embedded closed-square representative whose
boundary is exactly that curve.  The square model is deliberately retained:
the later Euclidean-disc adapter is a separate obligation. -/
theorem exists_embedded_square_disc_of_jordan
    {C : Set Plane} (hC : Schoenflies.IsJordanCurve C) :
    ∃ d : C(Square, Plane),
      IsEmbedding d ∧ d '' ModelBoundary = C := by
  obtain ⟨e⟩ := Schoenflies.IsJordanCurve.modelCurve_homeomorph hC
  obtain ⟨F, hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
    Schoenflies.isJordanCurve_modelCurve hC e
  let d : C(Square, Plane) :=
    ⟨fun x => F x, F.continuous.comp continuous_subtype_val⟩
  refine ⟨d, ?_, ?_⟩
  · exact F.isEmbedding.comp IsEmbedding.subtypeVal
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change F x ∈ C
      rw [hF ⟨x.val, hx⟩]
      exact (e ⟨x.val, hx⟩).property
    · intro hy
      let z : ↥C := ⟨y, hy⟩
      let w : ↥Schoenflies.modelCurve := e.symm z
      let x : Square := ⟨w.val, Schoenflies.modelCurve_subset_closedSquare w.property⟩
      refine ⟨x, w.property, ?_⟩
      change F x = y
      rw [hF w]
      exact congrArg Subtype.val (e.apply_symm_apply z)

private noncomputable def gaugeHomeomorph : Plane ≃ₜ Plane :=
  Classical.choose <|
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (Schoenflies.Plane.convex_closedSquare 0 1)
      (by
        rw [Schoenflies.Plane.interior_closedSquare]
        exact ⟨0, by simp [Schoenflies.Plane.openSquare, Schoenflies.Plane.supNorm]⟩)
      (Schoenflies.Plane.isBounded_closedSquare 0 1)

private theorem gaugeHomeomorph_closed :
    gaugeHomeomorph '' Square = UnitDisc := by
  simpa [gaugeHomeomorph, Schoenflies.Plane.isClosed_closedSquare] using
    (Classical.choose_spec <|
      exists_homeomorph_image_interior_closure_frontier_eq_unitBall
        (Schoenflies.Plane.convex_closedSquare 0 1)
        (by
          rw [Schoenflies.Plane.interior_closedSquare]
          exact ⟨0, by simp [Schoenflies.Plane.openSquare, Schoenflies.Plane.supNorm]⟩)
        (Schoenflies.Plane.isBounded_closedSquare 0 1)).2.1

private theorem gaugeHomeomorph_frontier :
    gaugeHomeomorph '' Schoenflies.modelCurve = Metric.sphere (0 : Plane) 1 := by
  simpa [gaugeHomeomorph, Schoenflies.modelCurve_eq_frontier] using
    (Classical.choose_spec <|
      exists_homeomorph_image_interior_closure_frontier_eq_unitBall
        (Schoenflies.Plane.convex_closedSquare 0 1)
        (by
          rw [Schoenflies.Plane.interior_closedSquare]
          exact ⟨0, by simp [Schoenflies.Plane.openSquare, Schoenflies.Plane.supNorm]⟩)
        (Schoenflies.Plane.isBounded_closedSquare 0 1)).2.2

/-- The gauge-rescaling homeomorphism takes the square's model boundary
exactly to the unit circle. -/
private noncomputable def squareBallHomeomorph : Square ≃ₜ UnitDisc := by
  classical
  let h := gaugeHomeomorph
  have hclosed' : h '' Schoenflies.Plane.closedSquare 0 1 =
      Metric.closedBall (0 : Plane) 1 := gaugeHomeomorph_closed
  apply Homeomorph.sets h
  ext x
  constructor
  · intro hx
    change h x ∈ Metric.closedBall (0 : Plane) 1
    rw [← hclosed']
    exact Set.mem_image_of_mem h hx
  · intro hx
    change h x ∈ UnitDisc at hx
    obtain ⟨y, hy, hxy⟩ : h x ∈ h '' Square := hclosed'.symm ▸ hx
    exact h.injective hxy ▸ hy

private theorem squareBallHomeomorph_boundary :
    squareBallHomeomorph '' ModelBoundary = DiscBoundary := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change gaugeHomeomorph x ∈ Metric.sphere (0 : Plane) 1
    rw [← gaugeHomeomorph_frontier]
    exact ⟨x, hx, rfl⟩
  · intro hy
    change (y : Plane) ∈ Metric.sphere (0 : Plane) 1 at hy
    obtain ⟨x, hx, hxy⟩ := gaugeHomeomorph_frontier.symm ▸ hy
    have hxSquare : x ∈ Square := Schoenflies.modelCurve_subset_closedSquare hx
    refine ⟨⟨x, hxSquare⟩, hx, ?_⟩
    apply Subtype.ext
    exact hxy

/-- Every planar Jordan curve is the boundary of an embedded Euclidean
closed disc, with the exact boundary convention used by `BoundsDisc`. -/
theorem jordan_curve_bounds_disc (c : Curve Plane)
    (hC : Schoenflies.IsJordanCurve c.image) : BoundsDisc c := by
  obtain ⟨dSquare, hEmbedding, hBoundary⟩ :=
    exists_embedded_square_disc_of_jordan hC
  let d : C(UnitDisc, Plane) :=
    ⟨fun x => dSquare (squareBallHomeomorph.symm x),
      dSquare.continuous.comp squareBallHomeomorph.symm.continuous⟩
  refine ⟨d, ?_, ?_⟩
  · exact hEmbedding.comp squareBallHomeomorph.symm.isEmbedding
  · change (dSquare ∘ squareBallHomeomorph.symm) '' DiscBoundary = c.image
    rw [Set.image_comp]
    have hsymm : squareBallHomeomorph.symm '' DiscBoundary = ModelBoundary := by
      rw [← squareBallHomeomorph_boundary]
      exact squareBallHomeomorph.symm_image_image ModelBoundary
    rw [hsymm, hBoundary]

end CurveComplex
