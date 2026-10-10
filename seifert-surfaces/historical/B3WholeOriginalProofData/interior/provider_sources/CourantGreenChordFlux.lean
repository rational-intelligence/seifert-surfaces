import VM02aDirectMethod
import CourantAnnularBoundaryA
import CourantTranslatedPolar
import CourantAnnularProfiles
set_option autoImplicit false
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod.CourantTraceFluxAssembly
open SeifertSurfaces.AppendixACoordinates

theorem actual_green_chord_flux_ae
    (f : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)
    (hrows : ∀ i, MemLp (d i) 2 (volume.restrict (disc 1)))
    (hgreen : HasGreenBoundaryTrace f d b)
    (hb : Continuous b) (hperiod : Function.Periodic b (2 * Real.pi))
    (s a z : ℝ) (ha : 0 < a) (haz : a < z) (hz : z < 1) :
    let c : ℝ → E2 := unitCircleParameter
    let J : E2 → E2 := fun v => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
    let alpha : ℝ → ℝ := fun r => 2 * Real.arcsin (r / 2)
    let g : ℝ → E2 := fun r => b (s - alpha r) - b (s + alpha r)
    let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
    let F : Fin 2 → ℝ → ℝ := fun i r =>
      r * ∫ t in Ioo (-Real.pi) Real.pi,
        inner ℝ (d0 i (c s + r • c t)) (J (c t))
    ∀ᵐ r ∂volume.restrict (Ioo a z), ∀ i : Fin 2, (g r) i = F i r := by
  classical
  dsimp only
  let c : ℝ → E2 := unitCircleParameter
  let J : E2 → E2 := fun v => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
  let alpha : ℝ → ℝ := fun r => 2 * Real.arcsin (r / 2)
  let g : ℝ → E2 := fun r => b (s - alpha r) - b (s + alpha r)
  let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
  let F : Fin 2 → ℝ → ℝ := fun i r =>
    r * ∫ t in Ioo (-Real.pi) Real.pi, inner ℝ (d0 i (c s + r • c t)) (J (c t))
  change ∀ᵐ r ∂volume.restrict (Ioo a z), ∀ i : Fin 2, (g r) i = F i r
  obtain ⟨_, _, _, _, _, _, _, hF, htests⟩ :=
    CourantAnalyticB.native_translated_polar_rows d
      (fun i => (hrows i).aestronglyMeasurable) hrows (c s) a z ha haz hz
  have cg : Continuous g := by
    have ca : Continuous alpha := by dsimp only [alpha]; fun_prop
    exact (hb.comp (continuous_const.sub ca)).sub (hb.comp (continuous_const.add ca))
  apply ae_all_iff.mpr
  intro i
  have cgi : Continuous (fun r => g r i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp cg
  have hv : LocallyIntegrableOn (fun r => g r i - F i r) (Ioo a z) volume :=
    (cgi.locallyIntegrable.locallyIntegrableOn (Ioo a z)).sub (hF i).2.locallyIntegrableOn
  have hzero : ∀ᵐ r ∂volume.restrict (Ioo a z), g r i - F i r = 0 := by
    apply (CourantAnalyticB.annular_square_radius_tests_detect a z ha haz
      (fun r => g r i - F i r) hv).2
    intro h hh hhc hhs
    let rho2 : E2 → ℝ := fun x => (x 0 - c s 0)^2 + (x 1 - c s 1)^2
    let chi : Fin 2 → E2 → ℝ := fun j x =>
      ![-(x 1 - c s 1) * h (rho2 x), (x 0 - c s 0) * h (rho2 x)] j
    have hfield := CourantAnnularBoundaryA.smooth_squared_radius_rotation_field (c s) h hh
    have hpair := CourantAnnularBoundaryA.native_green_divergence_free_pairing
      f d b hgreen chi hfield.1 hfield.2.1 i
    have hboundary := CourantAnnularBoundaryA.actual_continuous_annular_boundary_substitution
      b hb hperiod s a z ha haz hz h hh hhc hhs i
    have hbulk := htests h hh hhc hhs i
    have hboundaryI : IntegrableOn (fun r => r * h (r ^ 2) * g r i) (Ioo a z) volume :=
      hboundary.2.1
    have hbulkI : IntegrableOn (fun r => r * h (r ^ 2) * F i r) (Ioo a z) volume :=
      hbulk.2.1
    have hmatch : (∫ r in Ioo a z, r * h (r ^ 2) * g r i) =
        ∫ r in Ioo a z, r * h (r ^ 2) * F i r := by
      exact hboundary.2.2.symm.trans (hpair.2.2.symm.trans hbulk.2.2)
    simp_rw [mul_sub]
    rw [integral_sub hboundaryI hbulkI, hmatch, sub_self]
  filter_upwards [hzero] with r hr
  exact sub_eq_zero.mp hr

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod.CourantTraceFluxAssembly
