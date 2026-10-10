import NativeBoundaryTangentialSchauderWeak
import OddH1LocalTrace
import NativeH1SubsetRestriction

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak


open BoundaryContinuation BoundarySupport
open SeifertSurfaces.QuasilinearProviderBridge

private theorem witness_native_h1 (U : Set E2) (u : E2 → ℝ)
    (hw : DeGiorgi.MemW1pWitness 2 u U) : H1On U u hw.weakGrad := by
  have hg := hw.weakGrad_memLp
  refine ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict
      (hw.memLp.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hg.locallyIntegrable (by norm_num)), ?_⟩,
    hw.memLp, hg⟩
  intro ψ hs hc ht i
  simpa only [coordinateVector] using hw.isWeakGrad i ψ hs hc ht

private theorem native_h10_congr_ae (U : Set E2) (u v : E2 → ℝ) (du dv : E2 → E2)
    (hu : H10On U u du) (he : u =ᵐ[volume.restrict U] v)
    (hde : du =ᵐ[volume.restrict U] dv) : H10On U v dv := by
  have hm : MemLp v 2 (volume.restrict U) := (memLp_congr_ae he).mp hu.1.2.1
  have hdm : MemLp dv 2 (volume.restrict U) := (memLp_congr_ae hde).mp hu.1.2.2
  refine ⟨⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hm.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hdm.locallyIntegrable (by norm_num)), ?_⟩,
    hm, hdm⟩, ?_⟩
  · intro ψ hs hc ht i
    have hi := hu.1.1.2.2 ψ hs hc ht i
    have hf : (∫ x in U, v x * fderiv ℝ ψ x (coordinateVector 2 i)) =
        ∫ x in U, u x * fderiv ℝ ψ x (coordinateVector 2 i) :=
      integral_congr_ae (he.symm.mul EventuallyEq.rfl)
    have hg : (∫ x in U, dv x i * ψ x) = ∫ x in U, du x i * ψ x := by
      apply integral_congr_ae
      filter_upwards [hde] with x hx
      rw [hx]
    rw [hf, hg]
    exact hi
  · intro ε hε
    obtain ⟨ψ, hs, hc, ht, herr⟩ := hu.2 ε hε
    refine ⟨ψ, hs, hc, ht, ?_⟩
    have hi : (∫ x in U, |v x - ψ x| ^ 2 + ‖dv x - planarGradient ψ x‖ ^ 2) =
        ∫ x in U, |u x - ψ x| ^ 2 + ‖du x - planarGradient ψ x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [he, hde] with x hx hdx
      rw [hx, hdx]
    rw [hi]
    exact herr

private theorem swap_ball (R : ℝ) :
    coordinateSwap.toContinuousLinearEquiv ⁻¹' Metric.ball (0 : E2) R = Metric.ball 0 R := by
  ext x
  simp only [mem_preimage, Metric.mem_ball, dist_zero_right]
  change (‖coordinateSwap x‖ < R) ↔ (‖x‖ < R)
  rw [coordinateSwap.norm_map]

private theorem swap_half_disc (R : ℝ) :
    coordinateSwap.toContinuousLinearEquiv ⁻¹' halfDisc R = openHalfDisc R := by
  ext x
  simp only [mem_preimage, halfDisc, disc, openHalfDisc, mem_setOf_eq,
    mem_inter_iff, Metric.mem_ball, dist_zero_right]
  change (‖coordinateSwap x‖ < R ∧ 0 < coordinateSwap x 1) ↔
    (‖x‖ < R ∧ 0 < x 0)
  rw [coordinateSwap.norm_map, coordinateSwap_one]

private theorem swap_reflect (x : E2) :
    coordinateSwap (reflect x) = normalReflection (coordinateSwap x) := by
  ext i
  fin_cases i <;> simp [coordinateSwap, reflect, normalReflection]

private theorem swap_gradient_at (v : E2 → ℝ) (x : E2)
    (hd : DifferentiableAt ℝ v (coordinateSwap x)) :
    planarGradient (fun y => v (coordinateSwap y)) x =
      coordinateSwap (planarGradient v (coordinateSwap x)) := by
  apply ext_inner_right ℝ
  intro q
  rw [planar_gradient_pairing, ← coordinateSwap_adjoint,
    ContinuousLinearMap.adjoint_inner_left, planar_gradient_pairing]
  have ht := hd.hasFDerivAt.comp x coordinateSwap.toContinuousLinearEquiv.hasFDerivAt
  simp only [Function.comp_def] at ht
  rw [ht.fderiv]
  rfl

/-- Frozen standalone Sobolev trace bridge requested from an independent
owner. Coordinate 0 is normal, all derivatives in the output are the actual
ordinary interior gradients. This is not a premise added to the A5 target. -/
theorem native_flat_zero_trace_of_odd_H1_holder
    (r : ℝ) (hr : 0 < r) (v : E2 → ℝ) (C α : ℝ≥0)
    (hα : 0 < α) (hα1 : α < 1)
    (hv : ContDiffOn ℝ 1 v (openHalfDisc (2 * r)))
    (hholder : HolderOnWith C α v (closedHalfDisc (2 * r)))
    (hzero : ∀ x ∈ flatBoundary (2 * r), v x = 0)
    (hodd : DeGiorgi.MemW1p 2 (nativeOddExtension v) (Metric.ball 0 (2 * r))) :
    (∀ χ : E2 → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Metric.ball 0 r →
      H10On (openHalfDisc r) (fun x => χ x * v x)
        (fun x => χ x • planarGradient v x + v x • planarGradient χ x)) ∧
    FlatZeroTrace r (fun y => v (coordinateSwap y))
      (fun y => coordinateSwap (planarGradient v (coordinateSwap y))) := by
  classical
  let P := coordinateSwap.toContinuousLinearEquiv
  let w := nativeOddExtension v
  let hw := hodd.someWitness.restrict (Metric.isOpen_ball)
    (Metric.ball_subset_ball (by linarith : r ≤ 2 * r))
  have hH := linear_h1_pullback (Metric.ball 0 r) P w hw.weakGrad
    (witness_native_h1 _ _ hw)
  rw [swap_ball] at hH
  let ws : E2 → ℝ := fun y => w (coordinateSwap y)
  let ds : E2 → E2 := fun y => coordinateSwap (hw.weakGrad (coordinateSwap y))
  have hHs : H1On (Metric.ball 0 r) ws ds := by
    change H1On (Metric.ball 0 r) (fun y => w (coordinateSwap y)) (fun y => coordinateSwap (hw.weakGrad (coordinateSwap y)))
    simpa only [P, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      coordinateSwap_adjoint] using hH
  have hodds : (fun y => ws (reflect y)) =ᵐ[volume.restrict (Metric.ball 0 r)]
      (fun y => -ws y) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hb : coordinateSwap y ∈ Metric.ball 0 (2 * r) := by
      have hy' := Metric.ball_subset_ball (by linarith : r ≤ 2 * r) hy
      simpa only [Metric.mem_ball, dist_zero_right, coordinateSwap.norm_map] using hy'
    dsimp only [ws, w]
    rw [swap_reflect]
    by_cases hp : 0 < coordinateSwap y 0
    · simp only [nativeOddExtension, normalReflection_zero, if_pos hp.le,
        if_neg (by linarith : ¬ 0 ≤ -(coordinateSwap y 0)), normalReflection_involutive]
    · by_cases hn : coordinateSwap y 0 < 0
      · simp only [nativeOddExtension, normalReflection_zero,
          if_neg (by linarith : ¬ 0 ≤ coordinateSwap y 0),
          if_pos (by linarith : 0 ≤ -(coordinateSwap y 0)), neg_neg]
      · have hz : coordinateSwap y 0 = 0 := by linarith
        have hvz := hzero _ ⟨hb, hz⟩
        simp [nativeOddExtension, normalReflection_zero, hz, normalReflection_flat hz, hvz]
  have hhalf : IsOpen (halfDisc r) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hsub : halfDisc r ⊆ Metric.ball 0 r := fun x hx => hx.1
  let vs : E2 → ℝ := fun y => v (coordinateSwap y)
  let gs : E2 → E2 := fun y => coordinateSwap (planarGradient v (coordinateSwap y))
  have hmap : MapsTo coordinateSwap (halfDisc r) (openHalfDisc (2 * r)) := by
    intro y hy
    refine ⟨?_, ?_⟩
    · have hh := Metric.ball_subset_ball (by linarith : r ≤ 2 * r) hy.1
      simpa only [Metric.mem_ball, dist_zero_right, coordinateSwap.norm_map] using hh
    · change 0 < coordinateSwap y 0
      simpa only [coordinateSwap_zero] using hy.2
  have hvsc : ContDiffOn ℝ 1 vs (halfDisc r) :=
    hv.comp P.contDiff.contDiffOn hmap
  have heq : EqOn ws vs (halfDisc r) := by
    intro y hy
    exact if_pos (hmap hy).2.le
  have h1s := h1_restrict_subset _ _ hsub ws ds hHs
  let hws : DeGiorgi.MemW1pWitness 2 ws (halfDisc r) :=
    { memLp := h1s.2.1
      weakGrad := ds
      weakGrad_component_memLp := fun i => h1s.2.2.eval_piLp i
      isWeakGrad := by
        intro i ψ hs hc ht
        simpa only [coordinateVector] using h1s.1.2.2 ψ hs hc ht i }
  have hgws := R1_classical_weak_gradient_agrees _ hhalf ws
    (hvsc.congr (fun y hy => heq hy)) hws
  have hgrad : ds =ᵐ[volume.restrict (halfDisc r)] gs := by
    filter_upwards [hgws, ae_restrict_mem hhalf.measurableSet] with y hg hy
    have he : ws =ᶠ[𝓝 y] vs := by
      filter_upwards [hhalf.mem_nhds hy] with z hz
      exact heq hz
    have hd := (hv.contDiffAt ((openHalfDisc_isOpen (2 * r)).mem_nhds (hmap hy))).differentiableAt one_ne_zero
    change ds y = gs y
    change ds y = planarGradient ws y at hg
    rw [hg]
    simp only [planarGradient, he.fderiv_eq]
    exact swap_gradient_at v y hd
  have htrace : FlatZeroTrace r vs gs := by
    intro χ hχ hc ht
    have hh := (HemisphereQ.odd_H1_cutoff_H10_native_approximation r hr ws ds hHs hodds χ hχ hc ht).1
    apply native_h10_congr_ae _ _ _ _ _ hh
    · filter_upwards [ae_restrict_mem hhalf.measurableSet] with y hy
      rw [heq hy]
    · filter_upwards [hgrad, ae_restrict_mem hhalf.measurableSet] with y hg hy
      simp only [cutoffGradient, hg, heq hy]
  refine ⟨?_, htrace⟩
  intro χ hχ hc ht
  let χs : E2 → ℝ := fun y => χ (coordinateSwap y)
  have hχs : ContDiff ℝ ∞ χs := hχ.comp P.contDiff
  have hcs : HasCompactSupport χs := hc.comp_homeomorph P.toHomeomorph
  have hts : tsupport χs ⊆ disc r := by
    rw [show χs = χ ∘ P.toHomeomorph from rfl, tsupport_comp_eq_preimage]
    intro y hy
    have hh := ht hy
    change coordinateSwap y ∈ Metric.ball 0 r at hh
    simpa only [disc, Metric.mem_ball, dist_zero_right, coordinateSwap.norm_map] using hh
  have hh := linear_h10_pullback (halfDisc r) P _ _ (htrace χs hχs hcs hts)
  rw [swap_half_disc] at hh
  have hf : (fun y => χs (P y) * vs (P y)) = (fun y => χ y * v y) := by
    funext y
    simp only [χs, vs, P, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      coordinateSwap_involutive]
  have hg : (fun y => P.toContinuousLinearMap.adjoint (cutoffGradient χs vs gs (P y))) =
      (fun y => χ y • planarGradient v y + v y • planarGradient χ y) := by
    funext y
    simp only [cutoffGradient, coordinateSwap_adjoint, map_add, map_smul,
      χs, vs, gs, P, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      coordinateSwap_involutive]
    rw [coordinateSwap_gradient χ hχ, coordinateSwap_involutive,
      coordinateSwap_involutive]
  rw [hf, hg] at hh
  exact hh


end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
