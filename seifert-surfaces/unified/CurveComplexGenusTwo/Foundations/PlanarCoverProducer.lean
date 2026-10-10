import CurveComplexGenusTwo.Foundations.PlanarDiscRecognition
import CurveComplexGenusTwo.Foundations.PlanarJordanNesting
import CurveComplexGenusTwo.Foundations.DeckDiskNoNesting
import CurveComplexGenusTwo.Foundations.PlanarSquareDiscWitness
import CurveComplexGenusTwo.Foundations.SurfaceCoverTransfer

namespace CurveComplex

open Topology

private abbrev Plane := Schoenflies.Plane
private abbrev UnitDisc := Metric.closedBall (0 : Plane) 1
private def DiscBoundary : Set UnitDisc :=
  {x | (x : Plane) ∈ Metric.sphere 0 1}

/-- A planar quotient cover sends the bounded Jordan disc of a lifted circle
homeomorphically to a disc in the base. -/
theorem boundsDisc_of_planar_quotient_cover_disc
    {G S : Type*} [Group G] [MulAction G Plane]
    [TopologicalSpace S] [T2Space S]
    [LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.BrouwerFixedPoint Plane]
    (p : Plane → S) (hp : IsQuotientCoveringMap p G)
    (c : Curve S) (r : C(Circle, Plane))
    (hpr : p ∘ (r : Circle → Plane) = c.map)
    (d : C(UnitDisc, Plane)) (hd : IsEmbedding d)
    (hbd : d '' DiscBoundary = Set.range r)
    (hrJordan : Schoenflies.IsJordanCurve (Set.range r))
    (hBrouwer : ∀ u : C(UnitDisc, UnitDisc), ∃ x, u x = x) :
    BoundsDisc c := by
  have hregion : Set.range d = Schoenflies.inside (Set.range r) ∪ Set.range r :=
    embedded_disc_range_eq_closed_inside d hd (Set.range r) hrJordan hbd
  apply boundsDisc_of_quotient_cover_jordan_disc p hp c r hpr d hd hbd hBrouwer
  intro g hg hboundaryDisjoint
  let t : Plane ≃ₜ Plane := {
    toFun := fun x => g • x
    invFun := fun x => g⁻¹ • x
    left_inv := fun x => by simp
    right_inv := fun x => by simp
    continuous_toFun := hp.continuous_const_smul g
    continuous_invFun := hp.continuous_const_smul g⁻¹
  }
  have hdisj : Disjoint (Set.range r) (t '' Set.range r) := by
    change Disjoint (Set.range r) ((g • ·) '' Set.range r)
    rw [← hbd]
    exact hboundaryDisjoint
  exact planar_disc_translate_disjoint_or_nested d (Set.range r) hrJordan
    hregion t hdisj

/-- Planar Schoenflies supplies the disc witness, while the deck action and
Jordan nesting make its projection embedded. -/
theorem boundsDisc_of_planar_quotient_cover_lift
    {G S : Type*} [Group G] [MulAction G Plane]
    [TopologicalSpace S] [T2Space S]
    [LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.BrouwerFixedPoint Plane]
    (p : Plane → S) (hp : IsQuotientCoveringMap p G)
    (c : Curve S) (r : C(Circle, Plane))
    (hpr : p ∘ (r : Circle → Plane) = c.map)
    (hrJordan : Schoenflies.IsJordanCurve (Set.range r))
    (hBrouwer : ∀ u : C(UnitDisc, UnitDisc), ∃ x, u x = x) :
    BoundsDisc c := by
  have hr : IsEmbedding r := by
    apply IsEmbedding.of_comp r.continuous hp.isCoveringMap.continuous
    rw [hpr]
    exact c.embedded
  let cLift : Curve Plane := ⟨r, hr⟩
  have hcLift : Schoenflies.IsJordanCurve cLift.image := hrJordan
  obtain ⟨d, hd, hbd⟩ := jordan_curve_bounds_disc cLift hcLift
  exact boundsDisc_of_planar_quotient_cover_disc p hp c r hpr d hd hbd
    hrJordan hBrouwer

/-- The nullhomotopy supplies an embedded lift. The only geometric premise
left here identifies an embedded Mathlib circle with a Schoenflies Jordan
curve in the planar cover. -/
theorem boundsDisc_of_nullhomotopic_planar_quotient_cover
    {G S : Type*} [Group G] [MulAction G Plane]
    [TopologicalSpace S] [T2Space S]
    [LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.BrouwerFixedPoint Plane]
    (p : Plane → S) (hp : IsQuotientCoveringMap p G)
    (c : Curve S)
    (hc : (⟨c.map, c.embedded.continuous⟩ : C(Circle, S)).Nullhomotopic)
    (hJordanOfEmbedding : ∀ r : C(Circle, Plane),
      IsEmbedding r → Schoenflies.IsJordanCurve (Set.range r))
    (hBrouwer : ∀ u : C(UnitDisc, UnitDisc), ∃ x, u x = x) :
    BoundsDisc c := by
  obtain ⟨r, hpr, hr, _⟩ :=
    exists_embedded_nullhomotopic_lift_of_covering
      p hp.isCoveringMap hp.surjective c hc
  have hprFun : p ∘ (r : Circle → Plane) = c.map := by
    funext x
    exact congrArg (fun f : C(Circle, S) => f x) hpr
  exact boundsDisc_of_planar_quotient_cover_lift p hp c r hprFun
    (hJordanOfEmbedding r hr) hBrouwer

end CurveComplex
