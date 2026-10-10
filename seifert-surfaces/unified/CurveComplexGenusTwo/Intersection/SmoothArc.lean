import CurveComplexGenusTwo.Dictionary.MarkedSphere

/-!
The compatible smooth structure and representative convention of §2.4.
The dictionary itself uses topological ambient isotopy classes; this module
supplies the smooth representatives needed for crossings and tangent directions.
-/

namespace CurveComplex
namespace HyperellipticModel

open scoped Manifold ContDiff

variable {E S : Type}
  [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]

/-- The already chosen topological `z ↦ z²` charts are smooth coordinate
charts for the specified atlases, in both directions. -/
structure SmoothSquareBranchChart
    {π : E → S} {w : E} (c : SquareBranchChart E S π w) : Prop where
  upstairs_smooth :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ c.upstairs c.upstairs.source
  upstairs_inverse_smooth :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ c.upstairs.symm c.upstairs.target
  downstairs_smooth :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ c.downstairs c.downstairs.source
  downstairs_inverse_smooth :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ c.downstairs.symm c.downstairs.target

/-- §2.4 chooses compatible smooth atlases: away from ramification π is a
local diffeomorphism, and at ramification its smooth coordinates are `z²`. -/
structure SmoothMarkedSphere (M : HyperellipticModel E S) : Prop where
  sphere_manifold : IsManifold (𝓡 2) ∞ S
  projection_smooth : ContMDiff (𝓡 2) (𝓡 2) ∞ M.cover.projection
  unramified_local_diffeomorph :
    ∀ x : E, x ∉ M.cover.ramification →
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ M.cover.projection x
  branch_square_smooth :
    ∀ w (hw : M.cover.projection w ∈ M.cover.branch),
      SmoothSquareBranchChart (M.cover.branch_chart w hw)

/-- Convention 2.7: the arc is a smooth embedded representative, with nonzero
departure derivatives in the smooth sphere chart at both fixed endpoints. -/
structure SmoothNonLoopArc (M : HyperellipticModel E S) where
  arc : NonLoopArc M
  extension : ℝ → S
  agrees : ∀ t : Interval, extension t.val = arc.val.map t
  smooth : ContMDiff 𝓘(ℝ) (𝓡 2) ∞ extension
  start_immersion :
    fderiv ℝ
      (fun r : ℝ => (extChartAt (𝓡 2) (extension 0)) (extension r)) 0 ≠ 0
  end_immersion :
    fderiv ℝ
      (fun r : ℝ => (extChartAt (𝓡 2) (extension 1)) (extension r)) 1 ≠ 0
  interior_immersion :
    ∀ t : Interval, t ≠ ⟨0, by norm_num⟩ → t ≠ ⟨1, by norm_num⟩ →
      fderiv ℝ
        (fun r : ℝ => (extChartAt (𝓡 2) (arc.val.map t)) (extension r))
        t.val ≠ 0

end HyperellipticModel
end CurveComplex
