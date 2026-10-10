import A5NativeProjectionFiber

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- The actual derivative of a smooth ambient chart is a linear equivalence
from the true tangent space to Euclidean coordinates. -/
theorem ambient_chart_tangent_equivalence
    {N : Type*} [TopologicalSpace N] [ChartedSpace (Euc 3) N]
    [IsManifold 𝓘(ℝ, Euc 3) ∞ N]
    (c : SmoothAmbientChart N) (p : N) (hp : p ∈ c.chart.source) :
    ∃ C : TangentSpace 𝓘(ℝ, Euc 3) p ≃L[ℝ] Euc 3,
      ∀ v, C v = (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c.chart p))
        (mfderiv 𝓘(ℝ, Euc 3) 𝓘(ℝ, Euc 3) c.chart p v) := by
  have hd : c.chart.MDifferentiable 𝓘(ℝ, Euc 3) 𝓘(ℝ, Euc 3) :=
    ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
  exact ⟨(hd.mfderiv hp).trans (NormedSpace.fromTangentSpace (c.chart p)), fun _ => rfl⟩

/-- Actual native conormals transport through the ambient chart by the
ordinary within derivative, with the point equality retained explicitly. -/
theorem ambient_chart_within_derivative_transport
    {N : Type*} [TopologicalSpace N] [ChartedSpace (Euc 3) N]
    [IsManifold 𝓘(ℝ, Euc 3) ∞ N]
    (A : Set (Euc 2)) (x : Euc 2) (hu : UniqueDiffWithinAt ℝ A x)
    (G : Euc 2 → N) (hG : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 3) G A x)
    (c : SmoothAmbientChart N) (p : N) (heq : G x = p) (hp : p ∈ c.chart.source)
    (v : Euc 2) :
    fderivWithin ℝ (c.chart ∘ G) A x v =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c.chart p))
        (mfderiv 𝓘(ℝ, Euc 3) 𝓘(ℝ, Euc 3) c.chart p
          (heq ▸ mfderivWithin 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 3) G A x v)) := by
  subst p
  have hc := ((c.smooth _ hp).contMDiffAt (c.chart.open_source.mem_nhds hp)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp_mfderivWithin x hc hG hu.uniqueMDiffWithinAt
  have he := congrArg (fun D => (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c.chart (G x))) (D v)) hd
  rw [mfderivWithin_eq_fderivWithin] at he
  exact he

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
