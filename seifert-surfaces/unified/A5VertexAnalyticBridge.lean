import AppendixAInteriorRegularity

set_option autoImplicit false
open scoped ContDiff
open Set Topology MeasureTheory Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates

/-- The analytic step at a vertex, once the actual C1 graph has been constructed. -/
theorem smooth_C1_graph_of_punctured_weak_equation
    (Ω : Set E2) (hΩ : IsOpen Ω) (q : E2) (hq : q ∈ Ω)
    (J : Set Jet) (hJ : IsOpen J) (Q : SmoothQuasilinearOperator J)
    (helliptic : UniformlyEllipticOn J Q.flux)
    (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, (x, u x, planarGradient u x) ∈ J)
    (hweak : IsWeakDivergenceSolutionOn (Ω \ {q}) Q.flux Q.lowerOrder u) :
    ContDiffOn ℝ ∞ u Ω := by
  have hgrad : ContinuousOn (planarGradient u) Ω := by
    unfold planarGradient
    apply continuousOn_finsetSum
    intro i hi
    exact ((hC1.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply
      continuousOn_const).smul continuousOn_const
  have hjet : ContinuousOn (fun x => (x, u x, planarGradient u x)) Ω :=
    continuousOn_id.prodMk (hC1.continuousOn.prodMk hgrad)
  have hflux : ContinuousOn (fun x => Q.flux (x, u x, planarGradient u x)) Ω :=
    Q.flux_smooth.continuousOn.comp hjet hjets
  have hlower : ContinuousOn (fun x => Q.lowerOrder (x, u x, planarGradient u x)) Ω :=
    Q.lowerOrder_smooth.continuousOn.comp hjet hjets
  apply smooth_of_C1_weak_uniformlyElliptic Ω hΩ J hJ Q helliptic u hC1 hjets
  apply weak_divergence_extends_over_point Ω hΩ q hq _ _ hflux hlower
  intro φ hφ hcφ hsφ
  have he := hweak φ hφ hcφ hsφ
  unfold weakFluxIdentity at he ⊢
  have hi := (flux_integrand_integrable Ω _ _ φ hflux hlower hφ hcφ
    (hsφ.trans Set.sdiff_subset)).integrableOn (s := Ω)
  rw [setIntegral_sdiff (measurableSet_singleton q) hi (Set.singleton_subset_iff.mpr hq),
    integral_singleton] at he
  simpa [measureReal_def] using he

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
