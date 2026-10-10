import FirstDerivativeSobolev

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

section Average
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem average_tendsto_at_jet
    (Ω : Set E2) (hΩ : IsOpen Ω) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (J T : Set Jet) (hJ : IsOpen J) (hTJ : closure T ⊆ J)
    (x : E2) (hx : x ∈ Ω) (hjx : firstJet u x ∈ J) (k : Fin 2)
    (hseq : ℕ → ℝ) (hzero : Tendsto hseq atTop (𝓝 0))
    (hseg : ∀ n, ∀ t ∈ Icc (0 : ℝ) 1, jetSegment u k (hseq n) x t ∈ closure T)
    (f : Jet → F) (hf : ContinuousOn f J) (M : ℝ)
    (hbound : ∀ j ∈ closure T, ‖f j‖ ≤ M) :
    Tendsto (fun n => ∫ t in Icc (0 : ℝ) 1, f (jetSegment u k (hseq n) x t))
      atTop (𝓝 (f (firstJet u x))) := by
  have hj : ContinuousAt (firstJet u) x :=
    (continuousOn_id.prodMk (hC1.continuousOn.prodMk
      (SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_continuousOn Ω hΩ u hC1))).continuousAt
        (hΩ.mem_nhds hx)
  have hs : Tendsto (fun n => shift k (hseq n) x) atTop (𝓝 x) := by
    simpa [shift] using (tendsto_const_nhds (x := x)).add (hzero.smul_const (coordinateVector 2 k))
  have hjet := hj.tendsto.comp hs
  have hlim (t : ℝ) : Tendsto (fun n => jetSegment u k (hseq n) x t) atTop (𝓝 (firstJet u x)) := by
    have ht := (tendsto_const_nhds (x := (1 - t) • firstJet u x)).add (hjet.const_smul t)
    simpa only [jetSegment, Function.comp_def, ← add_smul, sub_add_cancel, one_smul] using ht
  have hm (n : ℕ) : AEStronglyMeasurable (fun t => f (jetSegment u k (hseq n) x t))
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (hf.comp (QuotientHelpers.jetSegment_continuous u k (hseq n) x).continuousOn
      (fun t ht => hTJ (hseg n t ht))).aestronglyMeasurable measurableSet_Icc
  have hb (n : ℕ) : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ‖f (jetSegment u k (hseq n) x t)‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hbound _ (hseg n t ht)
  have hp : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      Tendsto (fun n => f (jetSegment u k (hseq n) x t)) atTop (𝓝 (f (firstJet u x))) :=
    ae_of_all _ fun t => ((hf.continuousAt (hJ.mem_nhds hjx)).tendsto.comp (hlim t))
  have hh := tendsto_integral_of_dominated_convergence (fun _ : ℝ => M) hm
    (integrableOn_const isCompact_Icc.measure_ne_top) hb hp
  simpa [integral_const, Measure.real, Real.volume_Icc] using hh
end Average

theorem differentiated_coefficients_bounds
    (J : Set Jet) (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (x₀ : E2)
    (r κ M : ℝ) (hr : 0 < r) (T : Set Jet)
    (hjetsT : ∀ x ∈ Metric.closedBall x₀ (4 * r), firstJet u x ∈ T)
    (hbound : JetTubeBounds Q u x₀ r κ M T) (k : Fin 2) :
    CoefficientBounds (Metric.ball x₀ r) (differentiatedCoefficients Q u k) κ M := by
  refine ⟨hbound.1, hbound.2.1, ?_, ?_⟩
  · intro x hx X
    exact hbound.2.2.2.2.2 _ (subset_closure (hjetsT x
      ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))) hx))) X
  · intro x hx
    have hj := subset_closure (hjetsT x
      ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))) hx))
    have hb := hbound.2.2.2.1 _ hj
    have hd := (fluxDx Q (firstJet u x)).le_opNorm (coordinateVector 2 k)
    have hf := (lowerDx Q (firstJet u x)).le_opNorm (coordinateVector 2 k)
    simp only [QuotientHelpers.coordinate_norm, mul_one] at hd hf
    exact ⟨hb.2.2.2.2.1, hb.2.2.2.1, hd.trans hb.2.2.1,
      hb.2.2.2.2.2.2.2, hb.2.2.2.2.2.2.1, hf.trans hb.2.2.2.2.2.1⟩

theorem differentiated_coefficients_continuous
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J) (k : Fin 2) :
    coefficientsContinuousOn Ω (differentiatedCoefficients Q u k) := by
  have hj : ContinuousOn (firstJet u) Ω := continuousOn_id.prodMk
    (hC1.continuousOn.prodMk (SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_continuousOn Ω hΩ u hC1))
  exact ⟨(QuotientHelpers.p_partial_continuousOn J hJ Q.flux Q.flux_smooth).comp hj hjets,
    (QuotientHelpers.z_partial_continuousOn J hJ Q.flux Q.flux_smooth).comp hj hjets,
    ((QuotientHelpers.x_partial_continuousOn J hJ Q.flux Q.flux_smooth).clm_apply continuousOn_const).comp hj hjets,
    (QuotientHelpers.p_partial_continuousOn J hJ Q.lowerOrder Q.lowerOrder_smooth).comp hj hjets,
    (QuotientHelpers.z_partial_continuousOn J hJ Q.lowerOrder Q.lowerOrder_smooth).comp hj hjets,
    ((QuotientHelpers.x_partial_continuousOn J hJ Q.lowerOrder Q.lowerOrder_smooth).clm_apply continuousOn_const).comp hj hjets⟩

end SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers

namespace SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

set_option synthInstance.maxHeartbeats 100000 in
theorem averaged_coefficients_tendsto
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (x₀ : E2) (r κ M : ℝ) (hr : 0 < r) (T : Set Jet)
    (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω)
    (hT : Convex ℝ T) (hTJ : closure T ⊆ J)
    (hjetsT : ∀ x ∈ Metric.closedBall x₀ (4 * r), firstJet u x ∈ T)
    (hbound : JetTubeBounds Q u x₀ r κ M T) (k : Fin 2)
    (hseq : ℕ → ℝ) (hzero : Tendsto hseq atTop (𝓝 0)) (hsmall : ∀ n, |hseq n| < r)
    (x : E2) (hx : x ∈ Metric.ball x₀ r) :
    Tendsto (fun n => (averagedCoefficients Q u k (hseq n)).a x) atTop
      (𝓝 ((differentiatedCoefficients Q u k).a x)) ∧
    Tendsto (fun n => (averagedCoefficients Q u k (hseq n)).c x) atTop
      (𝓝 ((differentiatedCoefficients Q u k).c x)) ∧
    Tendsto (fun n => (averagedCoefficients Q u k (hseq n)).d x) atTop
      (𝓝 ((differentiatedCoefficients Q u k).d x)) ∧
    Tendsto (fun n => (averagedCoefficients Q u k (hseq n)).b x) atTop
      (𝓝 ((differentiatedCoefficients Q u k).b x)) ∧
    Tendsto (fun n => (averagedCoefficients Q u k (hseq n)).q x) atTop
      (𝓝 ((differentiatedCoefficients Q u k).q x)) ∧
    Tendsto (fun n => (averagedCoefficients Q u k (hseq n)).f x) atTop
      (𝓝 ((differentiatedCoefficients Q u k).f x)) := by
  have hx3 : x ∈ Metric.closedBall x₀ (3 * r) :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))) hx
  have hxΩ : x ∈ Ω := hball (Metric.closedBall_subset_closedBall (by linarith) hx3)
  have hs (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      jetSegment u k (hseq n) x t ∈ closure T :=
    subset_closure (QuotientHelpers.jetSegment_mem u x₀ r hr T hT hjetsT k (hseq n) (hsmall n) x hx3 t ht)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact average_tendsto_at_jet Ω hΩ u hC1 J T hJ hTJ x hxΩ (hjets x hxΩ) k hseq hzero hs
      (fluxDp Q) (QuotientHelpers.p_partial_continuousOn J hJ Q.flux Q.flux_smooth) M
      (fun j hj => (hbound.2.2.2.1 j hj).2.2.2.2.1)
  · exact average_tendsto_at_jet Ω hΩ u hC1 J T hJ hTJ x hxΩ (hjets x hxΩ) k hseq hzero hs
      (fluxDz Q) (QuotientHelpers.z_partial_continuousOn J hJ Q.flux Q.flux_smooth) M
      (fun j hj => (hbound.2.2.2.1 j hj).2.2.2.1)
  · apply average_tendsto_at_jet Ω hΩ u hC1 J T hJ hTJ x hxΩ (hjets x hxΩ) k hseq hzero hs
      (fun j => fluxDx Q j (coordinateVector 2 k))
      ((QuotientHelpers.x_partial_continuousOn J hJ Q.flux Q.flux_smooth).clm_apply continuousOn_const) M
    intro j hj
    exact ((fluxDx Q j).le_opNorm _).trans (by simpa only [QuotientHelpers.coordinate_norm, mul_one]
      using (hbound.2.2.2.1 j hj).2.2.1)
  · exact average_tendsto_at_jet Ω hΩ u hC1 J T hJ hTJ x hxΩ (hjets x hxΩ) k hseq hzero hs
      (lowerDp Q) (QuotientHelpers.p_partial_continuousOn J hJ Q.lowerOrder Q.lowerOrder_smooth) M
      (fun j hj => (hbound.2.2.2.1 j hj).2.2.2.2.2.2.2)
  · exact average_tendsto_at_jet Ω hΩ u hC1 J T hJ hTJ x hxΩ (hjets x hxΩ) k hseq hzero hs
      (lowerDz Q) (QuotientHelpers.z_partial_continuousOn J hJ Q.lowerOrder Q.lowerOrder_smooth) M
      (fun j hj => (hbound.2.2.2.1 j hj).2.2.2.2.2.2.1)
  · apply average_tendsto_at_jet Ω hΩ u hC1 J T hJ hTJ x hxΩ (hjets x hxΩ) k hseq hzero hs
      (fun j => lowerDx Q j (coordinateVector 2 k))
      ((QuotientHelpers.x_partial_continuousOn J hJ Q.lowerOrder Q.lowerOrder_smooth).clm_apply continuousOn_const) M
    intro j hj
    exact ((lowerDx Q j).le_opNorm _).trans (by simpa only [QuotientHelpers.coordinate_norm, mul_one]
      using (hbound.2.2.2.1 j hj).2.2.2.2.2.1)

end SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
