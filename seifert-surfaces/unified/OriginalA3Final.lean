import A3Recovery
import A3SharedGraph

noncomputable section
open Set Topology Function
open scoped Manifold ContDiff

namespace SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.Foundations

universe u v
variable {N : Type u}
run_cmd do
  let ctx := Lean.Name.str (Lean.Name.num `OriginalA3 2874678905) "_hygCtx"
  let topo := Lean.mkIdent (Lean.addMacroScope ctx `inst 3)
  let charted := Lean.mkIdent (Lean.addMacroScope ctx `inst 6)
  let manifold := Lean.mkIdent (Lean.addMacroScope ctx `inst 10)
  let n := Lean.mkIdent `N
  Lean.Elab.Command.elabCommand (← `(variable
    [$topo : TopologicalSpace $n]
    [$charted : ChartedSpace E3 $n]
    [$manifold : IsManifold 𝓘(ℝ, E3) ∞ $n]))

/-- Lemma A.3: the literal union of the original two images is, near the
original interior edge point, the image of one actual smooth minimal embedding. -/
theorem A3_original {h : AmbientMetric N} {M : Set N}
    (D : A3OriginalData.{u,v} h M) :
    ∃ V : Set N, IsOpen V ∧ D.edge D.pointParameter ∈ V ∧
    ∃ Ω : Set E2, IsOpen Ω ∧ (0 : E2) ∈ Ω ∧
    ∃ Φ : E2 → N,
      IsEmbedding (fun x : Ω => Φ x) ∧
      IsMinimalPatch h Φ Ω ∧ Φ 0 = D.edge D.pointParameter ∧
      Φ '' Ω = (D.sheetOne.image ∪ D.sheetTwo.image) ∩ V := by
  obtain ⟨G⟩ := A3_same_metric_two_sided_graph D
  obtain ⟨hpoint, hunion⟩ := A3_same_graph_exact_original_union G
  obtain ⟨hembedding, hminimal⟩ := A3_same_graph_minimal_embedding G
  exact ⟨G.neighborhood, G.neighborhood_open, G.point_mem,
    G.disc, Metric.isOpen_ball, Metric.mem_ball_self G.radius_pos,
    G.parameter, hembedding, hminimal, hpoint, hunion⟩

end SeifertSurfaces.OriginalEndpoints
