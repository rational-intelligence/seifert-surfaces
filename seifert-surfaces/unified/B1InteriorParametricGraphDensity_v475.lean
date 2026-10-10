import B1InteriorGraphCalculus_v475
import B1ActualParametricGraphDensity_v475
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The common graph density is the actual induced parametric density of
the same supplied exterior metric and smooth lifted chart. -/
theorem native_interior_parametric_graph_density_v475
    (g : SmoothMetric E.Carrier) (V : Set E3) (hV : IsOpen V)
    (χ : E3 → E.Carrier) (hχ : ContMDiffOn 𝓘(ℝ,E3) (𝓡∂ 3) ∞ χ V)
    (H : CoordinateMetric V) (hH : H.tensor=native_actual_lift_tensor_v475 g χ)
    (u : E2 → ℝ) (x : E2) (hu : DifferentiableAt ℝ u x)
    (hx : jetPoint (x,u x,0) ∈ V) :
    native_parametric_density_v475 g (fun z => χ (jetPoint (z,u z,0))) x =
      native_interior_graph_density_v475 H (x,u x,planarGradient u x) := by
  let y := jetPoint (x,u x,0)
  have hχd : MDifferentiableAt 𝓘(ℝ,E3) (𝓡∂ 3) χ y :=
    (hχ.contMDiffAt (hV.mem_nhds hx)).mdifferentiableAt (by simp)
  have hpoint : DifferentiableAt ℝ (fun z => jetPoint (z,u z,0)) x := by
    unfold jetPoint
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.differentiableAt.comp x
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).differentiableAt
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).differentiableAt
    · exact hu
  have hchain := mfderiv_comp x hχd hpoint.mdifferentiableAt
  rw [mfderiv_eq_fderiv] at hchain
  have heval (i : Fin 2) :
      mfderiv 𝓘(ℝ,E2) (𝓡∂ 3) (fun z => χ (jetPoint (z,u z,0))) x
        ((NormedSpace.fromTangentSpace x).symm (coordinateVector 2 i)) =
      mfderiv 𝓘(ℝ,E3) (𝓡∂ 3) χ y
        ((NormedSpace.fromTangentSpace y).symm (jetTangent (planarGradient u x) i)) := by
    change mfderiv 𝓘(ℝ,E2) (𝓡∂ 3) (χ ∘ (fun z => jetPoint (z,u z,0))) x _ = _
    rw [hchain]
    change mfderiv 𝓘(ℝ,E3) (𝓡∂ 3) χ y
      ((NormedSpace.fromTangentSpace y).symm
        (fderiv ℝ (fun z => jetPoint (z,u z,0)) x (coordinateVector 2 i))) = _
    rw [native_graph_jet_differential_v475 u x hu i]
  unfold native_parametric_density_v475 native_interior_graph_density_v475
  congr 2
  ext i j
  change g.inner (χ y)
    (mfderiv 𝓘(ℝ,E2) (𝓡∂ 3) (fun z => χ (jetPoint (z,u z,0))) x
      ((NormedSpace.fromTangentSpace x).symm (coordinateVector 2 i)))
    (mfderiv 𝓘(ℝ,E2) (𝓡∂ 3) (fun z => χ (jetPoint (z,u z,0))) x
      ((NormedSpace.fromTangentSpace x).symm (coordinateVector 2 j))) = _
  rw [heval,heval]
  unfold native_interior_graph_gram_v475
  rw [hH,native_actual_lift_coordinate_inner_v475]
  rfl

#print axioms native_interior_parametric_graph_density_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
