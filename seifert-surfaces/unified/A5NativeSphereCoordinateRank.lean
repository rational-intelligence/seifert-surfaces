import A5NativeAmbientLift

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- A smooth regular parametrization into the literal exterior remains
smooth and regular in every actual sphere chart containing its image. -/
theorem native_sphere_coordinate_smooth_rank
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (f : Euc 2 → E.Carrier) (U : Set (Euc 2)) (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 3) ∞ f U)
    (hrank : ∀ x ∈ U, Function.Injective (mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 3) f x))
    (c : SmoothAmbientChart ThreeSphere)
    (hchart : MapsTo (E.toSphere ∘ f) U c.chart.source) :
    ContDiffOn ℝ ∞ (c.chart ∘ E.toSphere ∘ f) U ∧
    ∀ x ∈ U, Function.Injective (fderiv ℝ (c.chart ∘ E.toSphere ∘ f) x) := by
  have hinc : Manifold.IsImmersion (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := by
    let : ChartedSpace (EuclideanHalfSpace 3) T.Carrier := E.charted
    let : IsManifold (𝓡∂ 3) ∞ T.Carrier := E.smooth
    exact E.inclusion.isImmersion
  have hs : ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡 3) ∞ (E.toSphere ∘ f) U :=
    hinc.contMDiff.comp_contMDiffOn hf
  refine ⟨(c.smooth.comp hs hchart).contDiffOn, ?_⟩
  intro x hx
  have hfd := (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hsd := (hs.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hcd : c.chart.MDifferentiable (𝓡 3) 𝓘(ℝ, Euc 3) :=
    ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
  have hm : Function.Injective (mfderiv 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 3)
      (c.chart ∘ E.toSphere ∘ f) x) := by
    rw [mfderiv_comp x (hcd.mdifferentiableAt (hchart hx)) hsd,
      mfderiv_comp x (hinc.contMDiff.mdifferentiable (by simp) (f x)) hfd]
    exact (hcd.mfderiv_injective (hchart hx)).comp
      ((hinc.mfderiv_injective (by simp) _).comp (hrank x hx))
  rw [mfderiv_eq_fderiv] at hm
  intro v w hvw
  have he := hm (a₁ := (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm v)
    (a₂ := (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm w) (by simpa using hvw)
  exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm.injective he

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
