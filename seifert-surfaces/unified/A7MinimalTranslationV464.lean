import EndpointGeometry
import Mathlib.Analysis.Calculus.FDeriv.Add
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

theorem graphTangent_translate (Φ : E2 → E3) (a x : E2) (i : Fin 2) :
    graphTangent (fun z => Φ (a + z)) x i = graphTangent Φ (a + x) i := by
  simp only [graphTangent, fderiv_comp_add_left]

theorem tracedAcceleration_translate (g : MetricTensor) (Φ : E2 → E3) (a x : E2) :
    tracedAcceleration g (fun z => Φ (a + z)) x = tracedAcceleration g Φ (a + x) := by
  have hd (i : Fin 2) :
      fderiv ℝ (fun z => graphTangent (fun y => Φ (a + y)) z i) x =
        fderiv ℝ (fun z => graphTangent Φ z i) (a + x) := by
    have he : (fun z => graphTangent (fun y => Φ (a + y)) z i) =
        (fun z => (fun y => graphTangent Φ y i) (a + z)) :=
      funext (fun z => graphTangent_translate Φ a z i)
    rw [he]
    exact fderiv_comp_add_left (f := fun z => graphTangent Φ z i) a
  have hi : inducedMetric g (fun z => Φ (a + z)) x = inducedMetric g Φ (a+x) := by
    ext i j
    simp only [inducedMetric, graphTangent_translate]
  have hc (i j : Fin 2) :
      covariantAcceleration g (fun z => Φ (a+z)) x i j =
      covariantAcceleration g Φ (a+x) i j := by
    unfold covariantAcceleration
    rw [hd]
    simp only [graphTangent_translate]
  simp only [tracedAcceleration, hi, hc]

universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ,E3) ∞ N]

theorem IsMinimalPatch.translate {h : AmbientMetric N} {Φ : E2 → N} {D : Set E2}
    (hΦ : IsMinimalPatch h Φ D) (hD : IsOpen D) (a : E2) :
    IsMinimalPatch h (fun z => Φ (a + z)) ((fun z => a + z) ⁻¹' D) := by
  have ha : ContMDiff 𝓘(ℝ,E2) 𝓘(ℝ,E2) ∞ (fun z : E2 => a + z) :=
    (contDiff_const.add contDiff_id).contMDiff
  refine ⟨hΦ.1.comp ha.contMDiffOn (fun _ hz => hz), ?_, ?_⟩
  · intro x hx
    have hsm : MDifferentiableAt 𝓘(ℝ,E2) 𝓘(ℝ,E3) Φ (a + x) := by
      exact ((hΦ.1 (a+x) hx).contMDiffAt (hD.mem_nhds hx)).mdifferentiableAt (by simp)
    change Function.Injective (mfderiv 𝓘(ℝ,E2) 𝓘(ℝ,E3)
      (Φ ∘ (fun z : E2 => a + z)) x)
    rw [mfderiv_comp x hsm (ha.mdifferentiableAt (by simp))]
    have hd : mfderiv 𝓘(ℝ,E2) 𝓘(ℝ,E2) (fun z : E2 => a + z) x =
        ContinuousLinearMap.id ℝ E2 := by
      rw [mfderiv_eq_fderiv]
      have hfd : fderiv ℝ (fun z : E2 => a+z) x = ContinuousLinearMap.id ℝ E2 := by
        convert (by simpa only [zero_add] using
          ((hasFDerivAt_const (𝕜 := ℝ) a x).add (hasFDerivAt_id x)).fderiv) using 1 <;> rfl
      rw [hfd]
      rfl
    rw [hd]
    intro v w hvw
    exact hΦ.2.1 (a+x) hx hvw
  · intro c
    refine ⟨?_, ?_⟩
    · exact (hΦ.2.2 c).1.comp (contDiff_const.add contDiff_id).contDiffOn
        (fun _ hz => hz)
    · intro x hx
      change tracedAcceleration (actualChartTensor h c) (fun z => c.chart (Φ (a+z))) x ∈ _
      have ht := tracedAcceleration_translate (actualChartTensor h c) (c.chart ∘ Φ) a x
      change tracedAcceleration (actualChartTensor h c)
        (fun z => (c.chart ∘ Φ) (a+z)) x ∈ _
      rw [ht]
      change _ ∈ LinearMap.range (fderiv ℝ (fun z => (c.chart ∘ Φ) (a+z)) x).toLinearMap
      rw [fderiv_comp_add_left (f := c.chart ∘ Φ) a]
      exact (hΦ.2.2 c).2 (a+x) hx

end SeifertSurfaces.OriginalEndpoints.A7Support
