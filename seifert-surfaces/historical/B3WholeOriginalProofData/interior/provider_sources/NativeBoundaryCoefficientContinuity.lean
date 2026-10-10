import NativeBoundaryLinearization

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_jetSegment_joint_continuousOn
    (Ω B : Set E2) (hΩ : IsOpen Ω) (u : E2 → ℝ)
    (hC1 : ContDiffOn ℝ 1 u Ω) (hBΩ : B ⊆ Ω)
    (k : Fin 2) (h : ℝ) (hshiftΩ : MapsTo (shift k h) B Ω) :
    ContinuousOn (fun z : E2 × ℝ => jetSegment u k h z.1 z.2) (B ×ˢ Icc (0 : ℝ) 1) := by
  have hj : ContinuousOn (firstJet u) Ω :=
    continuousOn_id.prodMk
      (hC1.continuousOn.prodMk (Helpers.gradient_continuousOn Ω hΩ u hC1))
  have hs : Continuous (shift k h) := by unfold shift; fun_prop
  have hfst : ContinuousOn (fun z : E2 × ℝ => firstJet u z.1) (B ×ˢ Icc (0 : ℝ) 1) :=
    hj.comp continuous_fst.continuousOn (fun z hz => hBΩ hz.1)
  have hshift : ContinuousOn (fun z : E2 × ℝ => firstJet u (shift k h z.1))
      (B ×ˢ Icc (0 : ℝ) 1) :=
    hj.comp (hs.comp continuous_fst).continuousOn (fun z hz => hshiftΩ hz.1)
  exact (continuousOn_const.sub continuous_snd.continuousOn).smul hfst |>.add
    (continuous_snd.continuousOn.smul hshift)

section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem native_integral_continuousOn_open
    (B : Set E2) (hB : IsOpen B) (f : E2 → ℝ → F)
    (hf : ContinuousOn f.uncurry (B ×ˢ Icc (0 : ℝ) 1))
    (M : ℝ) (hbound : ∀ x ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, ‖f x t‖ ≤ M) :
    ContinuousOn (fun x => ∫ t in Icc (0 : ℝ) 1, f x t) B := by
  intro x hx
  have hn : B ∈ 𝓝 x := hB.mem_nhds hx
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_of_dominated (bound := fun _ : ℝ => M)
  · filter_upwards [hn] with y hy
    exact ((hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hy, ht⟩)).integrableOn_compact isCompact_Icc).aestronglyMeasurable
  · filter_upwards [hn] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hbound y hy t ht
  · exact integrableOn_const isCompact_Icc.measure_ne_top
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun y hy => ⟨hy, ht⟩)).continuousAt hn

theorem native_jet_average_continuousOn
    (Ω B : Set E2) (hΩ : IsOpen Ω) (hB : IsOpen B) (u : E2 → ℝ)
    (hC1 : ContDiffOn ℝ 1 u Ω) (hBΩ : B ⊆ Ω)
    (k : Fin 2) (h : ℝ) (hshiftΩ : MapsTo (shift k h) B Ω)
    (J : Set Jet) (hsegments : ∀ x ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, jetSegment u k h x t ∈ J)
    (f : Jet → F) (hf : ContinuousOn f J) (M : ℝ)
    (hbound : ∀ x ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, ‖f (jetSegment u k h x t)‖ ≤ M) :
    ContinuousOn (fun x => ∫ t in Icc (0 : ℝ) 1, f (jetSegment u k h x t)) B := by
  apply native_integral_continuousOn_open B hB _ _ M hbound
  exact hf.comp (native_jetSegment_joint_continuousOn Ω B hΩ u hC1 hBΩ k h hshiftΩ)
    (fun z hz => hsegments z.1 hz.1 z.2 hz.2)

end

theorem native_averaged_coefficients_continuousOn
    (Ω B : Set E2) (hΩ : IsOpen Ω) (hB : IsOpen B)
    (J : Set Jet) (hJ : IsOpen J) (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω) (hBΩ : B ⊆ Ω)
    (k : Fin 2) (h : ℝ) (hshiftΩ : MapsTo (shift k h) B Ω)
    (T : Set Jet) (hTJ : closure T ⊆ J)
    (hsegments : ∀ x ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, jetSegment u k h x t ∈ closure T)
    (M : ℝ)
    (hcoefficients : ∀ j ∈ closure T, ‖Q.flux j‖ ≤ M ∧ |Q.lowerOrder j| ≤ M ∧
      ‖fluxDx Q j‖ ≤ M ∧ ‖fluxDz Q j‖ ≤ M ∧ ‖fluxDp Q j‖ ≤ M ∧
      ‖lowerDx Q j‖ ≤ M ∧ |lowerDz Q j| ≤ M ∧ ‖lowerDp Q j‖ ≤ M) :
    coefficientsContinuousOn B (averagedCoefficients Q u k h) ∧
      CoefficientMeasurableOn B (averagedCoefficients Q u k h) := by
  have hsJ := fun x hx t ht => hTJ (hsegments x hx t ht)
  have hc := fun x hx t ht => hcoefficients (jetSegment u k h x t) (hsegments x hx t ht)
  have hxA : ∀ x ∈ B, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fluxDx Q (jetSegment u k h x t) (coordinateVector 2 k)‖ ≤ M := by
    intro x hx t ht
    calc
      _ ≤ ‖fluxDx Q (jetSegment u k h x t)‖ * ‖coordinateVector 2 k‖ :=
        (fluxDx Q (jetSegment u k h x t)).le_opNorm _
      _ ≤ M := by simpa [QuotientHelpers.coordinate_norm] using (hc x hx t ht).2.2.1
  have hxB : ∀ x ∈ B, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖lowerDx Q (jetSegment u k h x t) (coordinateVector 2 k)‖ ≤ M := by
    intro x hx t ht
    calc
      _ ≤ ‖lowerDx Q (jetSegment u k h x t)‖ * ‖coordinateVector 2 k‖ :=
        (lowerDx Q (jetSegment u k h x t)).le_opNorm _
      _ ≤ M := by simpa [QuotientHelpers.coordinate_norm] using (hc x hx t ht).2.2.2.2.2.1
  have ha := native_jet_average_continuousOn Ω B hΩ hB u hC1 hBΩ k h hshiftΩ J hsJ
    (fluxDp Q) (QuotientHelpers.p_partial_continuousOn J hJ Q.flux Q.flux_smooth) M
    (fun x hx t ht => (hc x hx t ht).2.2.2.2.1)
  have hcv := native_jet_average_continuousOn Ω B hΩ hB u hC1 hBΩ k h hshiftΩ J hsJ
    (fluxDz Q) (QuotientHelpers.z_partial_continuousOn J hJ Q.flux Q.flux_smooth) M
    (fun x hx t ht => (hc x hx t ht).2.2.2.1)
  have hd := native_jet_average_continuousOn Ω B hΩ hB u hC1 hBΩ k h hshiftΩ J hsJ
    (fun j => fluxDx Q j (coordinateVector 2 k))
    ((QuotientHelpers.x_partial_continuousOn J hJ Q.flux Q.flux_smooth).clm_apply continuousOn_const)
    M hxA
  have hb := native_jet_average_continuousOn Ω B hΩ hB u hC1 hBΩ k h hshiftΩ J hsJ
    (lowerDp Q) (QuotientHelpers.p_partial_continuousOn J hJ Q.lowerOrder Q.lowerOrder_smooth) M
    (fun x hx t ht => (hc x hx t ht).2.2.2.2.2.2.2)
  have hq := native_jet_average_continuousOn Ω B hΩ hB u hC1 hBΩ k h hshiftΩ J hsJ
    (lowerDz Q) (QuotientHelpers.z_partial_continuousOn J hJ Q.lowerOrder Q.lowerOrder_smooth) M
    (fun x hx t ht => by simpa only [Real.norm_eq_abs] using (hc x hx t ht).2.2.2.2.2.2.1)
  have hf := native_jet_average_continuousOn Ω B hΩ hB u hC1 hBΩ k h hshiftΩ J hsJ
    (fun j => lowerDx Q j (coordinateVector 2 k))
    ((QuotientHelpers.x_partial_continuousOn J hJ Q.lowerOrder Q.lowerOrder_smooth).clm_apply continuousOn_const)
    M hxB
  exact ⟨⟨ha, hcv, hd, hb, hq, hf⟩,
    ha.aestronglyMeasurable hB.measurableSet, hcv.aestronglyMeasurable hB.measurableSet,
    hd.aestronglyMeasurable hB.measurableSet, hb.aestronglyMeasurable hB.measurableSet,
    hq.aestronglyMeasurable hB.measurableSet, hf.aestronglyMeasurable hB.measurableSet⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
