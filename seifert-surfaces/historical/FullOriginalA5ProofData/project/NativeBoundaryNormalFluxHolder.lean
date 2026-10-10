import NativeBoundaryNeumannRestriction
import NativeBoundaryRoughHolder

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem C1QuasilinearDirichletSolution.local_normal_flux_holder
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ δ : ℝ, ∃ K α : ℝ≥0, 0 < δ ∧ Metric.closedBall c δ ⊆ Metric.ball 0 ρ ∧
      0 < α ∧ α < 1 ∧
      HolderOnWith K α (fun x => Q.flux (firstJetWithin ρ u x) 0)
        (Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}) := by
  obtain ⟨sE, hsE, hballE, hcontE, hmemE, hEqE⟩ :=
    hsolution.local_actual_normal_flux_neumann_equation hρ c hc
  obtain ⟨sC, κ, M, hsC, hκ, hM, hballC, hCb, hCm⟩ :=
    hsolution.local_native_normal_flux_coefficient_bounds hρ c hc
  let r := min sE sC
  have hr : 0 < r := lt_min hsE hsC
  have hrE : r ≤ sE := min_le_left _ _
  have hrC : r ≤ sC := min_le_right _ _
  have hcf : c 0 = 0 := hc.2
  let F : E2 → ℝ := fun x => Q.flux (firstJetWithin ρ u (x + c)) 0
  let C := translateLinearizedCoefficients (nativeNormalFluxCoefficients ρ Q g u) c
  let U := Metric.ball c sC ∩ {x : E2 | 0 < x 0}
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hpre : (fun x : E2 => x + c) ⁻¹' U = openHalfDisc sC :=
    (native_flat_translation_halfDisc c hcf sC).1
  obtain ⟨hCb', hCm'⟩ := native_linear_coefficients_translation U hU.measurableSet c
    (nativeNormalFluxCoefficients ρ Q g u) κ M hCb hCm
  rw [hpre] at hCb' hCm'
  have hsub : openHalfDisc r ⊆ openHalfDisc sC :=
    fun x hx => ⟨Metric.ball_subset_ball hrC hx.1, hx.2⟩
  have hCr : CoefficientBounds (openHalfDisc r) C κ M :=
    ⟨hCb'.1, hCb'.2.1, fun x hx => hCb'.2.2.1 x (hsub hx), fun x hx => hCb'.2.2.2 x (hsub hx)⟩
  have hCmR : CoefficientMeasurableOn (openHalfDisc r) C :=
    ⟨hCm'.1.mono_measure (Measure.restrict_mono_set _ hsub),
      hCm'.2.1.mono_measure (Measure.restrict_mono_set _ hsub),
      hCm'.2.2.1.mono_measure (Measure.restrict_mono_set _ hsub),
      hCm'.2.2.2.1.mono_measure (Measure.restrict_mono_set _ hsub),
      hCm'.2.2.2.2.1.mono_measure (Measure.restrict_mono_set _ hsub),
      hCm'.2.2.2.2.2.mono_measure (Measure.restrict_mono_set _ hsub)⟩
  let hsolE := hmemE.someWitness
  let hsol := hsolE.restrict Metric.isOpen_ball (Metric.ball_subset_ball hrE)
  have hEq : LinearWeakEquation (Metric.ball 0 r) (nativeNeumannCoefficients r κ C)
      (nativeEvenExtension F) hsol.weakGrad :=
    native_neumann_linear_weak_restrict r sE κ hrE C _ hsolE.weakGrad (hEqE κ hsolE)
  have hnb := native_neumann_coefficient_bounds r κ M C hCr
  have hnm := native_neumann_coefficients_measurable r κ C hCmR
  have hcont : ContinuousOn (nativeEvenExtension F) (Metric.ball 0 r) :=
    hcontE.mono (Metric.ball_subset_ball hrE)
  have hmap : MapsTo (fun x : E2 => x + c) (closedHalfDisc r) (closedHalfDisc ρ) := by
    intro x hx
    refine ⟨Metric.ball_subset_closedBall (hballE ?_), ?_⟩
    · have hbr : x + c ∈ Metric.closedBall c r := by
        simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx.1
      exact Metric.closedBall_subset_closedBall hrE hbr
    · simpa only [mem_ofPred_eq, PiLp.add_apply, hcf, add_zero] using hx.2
  obtain ⟨L, hL⟩ := (closedHalfDisc_isCompact ρ).exists_bound_of_continuousOn
    ((EuclideanSpace.proj (0 : Fin 2)).continuous.continuousOn.comp
      (hsolution.continuous_boundary_coefficients hρ).1 (mapsTo_univ _ _))
  have hLplus : 0 ≤ |L| + 1 := by positivity
  have hvalue : ∀ x ∈ Metric.ball 0 r, |nativeEvenExtension F x| ≤ |L| + 1 := by
    intro x hx
    by_cases hp : 0 ≤ x 0
    · have hm := hmap ⟨Metric.ball_subset_closedBall hx, hp⟩
      have hcpt := (hL (x + c) hm).trans (by linarith [le_abs_self L] : L ≤ |L| + 1)
      simpa only [nativeEvenExtension, if_pos hp, F, Function.comp_def, PiLp.proj_apply,
        Real.norm_eq_abs] using hcpt
    · have hxR : normalReflection x ∈ closedHalfDisc r := by
        refine ⟨Metric.ball_subset_closedBall (normalReflection_maps_ball r hx), ?_⟩
        change 0 ≤ normalReflection x 0
        rw [normalReflection_zero]
        linarith [not_le.mp hp]
      have hcpt := (hL (normalReflection x + c) (hmap hxR)).trans
          (by linarith [le_abs_self L] : L ≤ |L| + 1)
      simpa only [nativeEvenExtension, if_neg hp, F, Function.comp_def, PiLp.proj_apply,
        Real.norm_eq_abs] using hcpt
  obtain ⟨δ, K, α, hδ, hδr, hα, hα1, hh⟩ :=
    uniform_holder_native_continuous_sobolev_linear_solutions r κ (M + κ) (|L| + 1)
      hr hκ hnb.2.1 hLplus
  have hholder := hh (nativeNeumannCoefficients r κ C) (nativeEvenExtension F)
    hcont hnb hnm hvalue hsol hEq
  refine ⟨δ, K, α, hδ,
    (Metric.closedBall_subset_closedBall (hδr.le.trans hrE)).trans hballE, hα, hα1, ?_⟩
  intro x hx y hy
  have hx' : x - c ∈ Metric.closedBall (0 : E2) δ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hx.1
  have hy' : y - c ∈ Metric.closedBall (0 : E2) δ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hy.1
  have hxpos : 0 ≤ (x - c) 0 := by
    simpa only [mem_setOf_eq, PiLp.sub_apply, hcf, sub_zero] using hx.2
  have hypos : 0 ≤ (y - c) 0 := by
    simpa only [mem_setOf_eq, PiLp.sub_apply, hcf, sub_zero] using hy.2
  simpa only [nativeEvenExtension, if_pos hxpos, if_pos hypos, F, sub_add_cancel,
    edist_dist, dist_sub_right] using hholder (x - c) hx' (y - c) hy'

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
