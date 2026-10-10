import ClassificationOfSurfaces.LeanEval.ChallengeDeps
import CurveComplexGenusTwo.Dictionary.MarkedSphere

namespace CurveComplex.Hyperbolic
open Set Topology CategoryTheory
open LeanEval.Topology.ClassificationOfSurfaces
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The unpaired h-edge of the actual one-boundary orientable representative.
OrientableRel p 1 identifies the a,b handle pairs and the c seam. The h-edge
has angular parameter -(1+t)/(4*p+3), for 0≤t≤1; its quotient image is the
one boundary circle. -/
noncomputable def ActualOneBoundaryOrientableBoundary (p : ℕ) :
    Set (Quot (OrientableRel p 1)) :=
  Set.range (fun t : CurveComplex.Interval =>
    Quot.mk (OrientableRel p 1)
      (Complex.ClosedUnitDisc.bdyPtOfReal (-(1 + (t : ℝ)) / (4 * p + 3))))

/-- The actual interior of the compact one-boundary polygonal representative,
with the quotient/subspace topology, rather than an arbitrary genus witness. -/
abbrev ActualOneBoundaryOrientableOpenModel (p : ℕ) :=
  {z : Quot (OrientableRel p 1) // z ∉ ActualOneBoundaryOrientableBoundary p}


end CurveComplex.Hyperbolic
