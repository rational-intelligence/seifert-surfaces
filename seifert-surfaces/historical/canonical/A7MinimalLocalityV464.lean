import EndpointGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

theorem tracedAcceleration_eventuallyEq (g : MetricTensor) {Φ Ψ : E2 → E3} {x : E2}
    (he : Φ =ᶠ[𝓝 x] Ψ) : tracedAcceleration g Φ x = tracedAcceleration g Ψ x := by
  have hfd := he.fderiv (𝕜 := ℝ)
  have ht (i : Fin 2) : (fun y => graphTangent Φ y i) =ᶠ[𝓝 x]
      (fun y => graphTangent Ψ y i) := by
    filter_upwards [hfd] with y hy
    exact congrArg (fun L : E2 →L[ℝ] E3 => L (coordinateVector 2 i)) hy
  have hi : inducedMetric g Φ x = inducedMetric g Ψ x := by
    ext i j
    simp only [inducedMetric,graphTangent,he.eq_of_nhds,he.fderiv_eq]
  have hc (i j : Fin 2) : covariantAcceleration g Φ x i j = covariantAcceleration g Ψ x i j := by
    unfold covariantAcceleration
    rw [(ht j).fderiv_eq]
    simp only [graphTangent,he.eq_of_nhds,he.fderiv_eq]
  simp only [tracedAcceleration,hi,hc]

universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ,E3) ∞ N]

theorem IsMinimalPatch.mono {h : AmbientMetric N} {Φ : E2 → N} {D V : Set E2}
    (hΦ : IsMinimalPatch h Φ D) (hVD : V ⊆ D) : IsMinimalPatch h Φ V := by
  refine ⟨hΦ.1.mono hVD,fun x hx => hΦ.2.1 x (hVD hx),?_⟩
  intro c
  exact ⟨(hΦ.2.2 c).1.mono (inter_subset_inter_left _ hVD),
    fun x hx => (hΦ.2.2 c).2 x ⟨hVD hx.1,hx.2⟩⟩

theorem IsMinimalPatch.congr_open {h : AmbientMetric N} {Φ Ψ : E2 → N} {D : Set E2}
    (hΦ : IsMinimalPatch h Φ D) (hD : IsOpen D) (he : EqOn Ψ Φ D) :
    IsMinimalPatch h Ψ D := by
  have heAt (x : E2) (hx : x ∈ D) : Ψ =ᶠ[𝓝 x] Φ :=
    Filter.eventuallyEq_of_mem (hD.mem_nhds hx) he
  refine ⟨hΦ.1.congr he,?_,?_⟩
  · intro x hx
    rw [(heAt x hx).mfderiv_eq]
    exact hΦ.2.1 x hx
  · intro c
    refine ⟨?_,?_⟩
    · apply (hΦ.2.2 c).1.congr_mono
      · intro x hx
        exact congrArg c.chart (he hx.1)
      · intro x hx
        exact ⟨hx.1,by simpa only [Set.mem_preimage,he hx.1] using hx.2⟩
    · intro x hx
      have hce : (c.chart ∘ Ψ) =ᶠ[𝓝 x] (c.chart ∘ Φ) := (heAt x hx.1).fun_comp c.chart
      rw [tracedAcceleration_eventuallyEq _ hce,hce.fderiv_eq]
      exact (hΦ.2.2 c).2 x ⟨hx.1,by simpa only [Set.mem_preimage,he hx.1] using hx.2⟩

end SeifertSurfaces.OriginalEndpoints.A7Support
