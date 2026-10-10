import ClassificationOfSurfaces.LeanEval.ChallengeDeps
import CurveComplexGenusTwo.Dictionary.Genus
namespace CurveComplex.Hyperbolic
open Set Topology CategoryTheory
open LeanEval.Topology.ClassificationOfSurfaces

/-- The actual boundary circle in the original closed p-handle quotient. -/
def actualClosedBoundaryPoint (p : ℕ) : C(Circle, Quot (OrientableRel p 0)) :=
  ⟨fun z => Quot.mk (OrientableRel p 0)
    (⟨(z : ℂ), by simpa only [Metric.mem_closedBall, dist_zero_right]
      using (Circle.norm_coe z).le⟩ : Complex.ClosedUnitDisc),
    (continuous_quot_mk (r := OrientableRel p 0)).comp (by fun_prop)⟩

/-- The boundary graph as an actual subspace of the original closed quotient. -/
abbrev ActualClosedOrientableBoundaryGraph (p : ℕ) :=
  Set.range (actualClosedBoundaryPoint p)

/-- The original boundary-circle attaching map, into its actual range. -/
def actualClosedOrientableAttachingMap (p : ℕ) :
    C(Circle, ActualClosedOrientableBoundaryGraph p) :=
  ⟨fun z => ⟨actualClosedBoundaryPoint p z, ⟨z, rfl⟩⟩,
    (actualClosedBoundaryPoint p).continuous.subtype_mk _⟩


end CurveComplex.Hyperbolic
