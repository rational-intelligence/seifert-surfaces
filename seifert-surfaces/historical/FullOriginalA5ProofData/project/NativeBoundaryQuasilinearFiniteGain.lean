import NativeBoundaryLinearFiniteBootstrap
import NativeBoundaryFiniteHolderNormal

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation

/-- The actual original solution gains one finite boundary Holder order.
The linear equation is its own zero-trace tangential equation. -/
theorem C1QuasilinearDirichletSolution.local_finite_holder_successor
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ)
    (r0 : ℝ) (hr0 : 0 < r0) (hball0 : Metric.closedBall c r0 ⊆ Metric.ball 0 ρ)
    (α : ℝ≥0) (hα : 0 < α) (hα1 : α < 1) (n : ℕ)
    (hu0 : NativeCapHolder (nativeClosedBoundaryCap c r0) α (n + 2) u) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.closedBall c δ ⊆ Metric.ball 0 ρ ∧
      NativeCapHolder (nativeClosedBoundaryCap c δ) α (n + 3) u := by
  obtain ⟨rt, κ, M, T, hrt, _, hTc, hTcompact, hTJ, hTube, hκ, hM, _, hbound, _, hell⟩ :=
    hsolution.local_boundary_jet_tube hρ c (flatBoundary_subset_closedHalfDisc ρ hc)
  obtain ⟨rw, hrw, hwball, hvSob, _, hweak⟩ :=
    hsolution.local_actual_tangential_schauder_weak hρ c hc
  let r := min r0 (min rw (4 * rt))
  have hr : 0 < r := lt_min hr0 (lt_min hrw (by positivity))
  have hrr0 : r ≤ r0 := min_le_left _ _
  have hrrw : r ≤ rw := (min_le_right _ _).trans (min_le_left _ _)
  have hrrt : r ≤ 4 * rt := (min_le_right _ _).trans (min_le_right _ _)
  have hball : Metric.closedBall c r ⊆ Metric.ball 0 ρ :=
    (Metric.closedBall_subset_closedBall hrr0).trans hball0
  let K := nativeClosedBoundaryCap c r
  let V := Metric.ball c r ∩ {x : E2 | 0 < x 0}
  let W := Metric.ball c rw ∩ {x : E2 | 0 < x 0}
  let C := nativeTangentialSchauderCoefficients ρ Q g u
  let t := fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1)
  let z := fun x : E2 => deriv g.value (x 1)
  let v := fun x => t x - z x
  have hcf : c 0 = 0 := hc.2
  have hKD := nativeClosedBoundaryCap_uniqueDiffOn c r hr hcf
  have hKρ : K ⊆ closedHalfDisc ρ := fun x hx =>
    ⟨Metric.ball_subset_closedBall (hball hx.1), hx.2⟩
  have hsub0 : K ⊆ nativeClosedBoundaryCap c r0 := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall hrr0 hx.1, hx.2⟩
  have hu : NativeCapHolder K α (n + 2) u := hu0.restrict hsub0 hKD
  have hmap : MapsTo (firstJetWithin ρ u) K (closure T) := fun x hx =>
    subset_closure (hTube x ⟨Metric.closedBall_subset_closedBall hrrt hx.1, hKρ hx⟩)
  have hjet := hsolution.firstJetWithin_capHolder c hcf r hr hball α hα1.le (n + 1) hu
  have ha : NativeCapHolder K α (n + 1) C.a :=
    hjet.comp_smooth c r hr hcf hα hα1.le J (closure T) hsolution.jet_domain_open
      hTcompact hTc.closure hTJ (fluxDp Q)
      (native_jet_p_partial_smooth J hsolution.jet_domain_open Q.flux Q.flux_smooth) _ hmap
  have hF : NativeCapHolder K α (n + 1)
      (fun x => nativeTangentialForcingJet Q (firstJetWithin ρ u x)) :=
    hjet.comp_smooth c r hr hcf hα hα1.le J (closure T) hsolution.jet_domain_open
      hTcompact hTc.closure hTJ (nativeTangentialForcingJet Q)
      (native_tangential_forcing_jet_smooth J hsolution.jet_domain_open Q) _ hmap
  have hzSmooth : ContDiffOn ℝ ∞ z K :=
    g.smooth_deriv_extension_on_ball.mono (fun x hx => hball hx.1)
  have hzH : NativeCapHolder K α (n + 1) z :=
    NativeCapHolder.of_contDiffOn_succ c r hr hcf hα1.le (hzSmooth.of_le (by simp))
  have hg2 : NativeCapHolder K α (n + 1)
      (fun x : E2 => deriv (deriv g.value) (x 1) • coordinateVector 2 1) :=
    (NativeCapHolder.of_contDiffOn_succ c r hr hcf hα1.le
      ((g.smooth_second_deriv_extension_on_ball.mono (fun x hx => hball hx.1)).of_le (by simp))).smul_const
      hKD (coordinateVector 2 1)
  have hd : NativeCapHolder K α (n + 1) C.d :=
    hF.add hKD (ha.clm_apply c r hr hcf hα hα1.le hg2)
  have ht : NativeCapHolder K α (n + 1) t := by
    apply (hu.2 1).congr
    intro x hx
    change fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1) =
      fderivWithin ℝ u K x (coordinateVector 2 1)
    rw [fderivWithin_subset hKρ (hKD x hx)
      (hsolution.c1.differentiableOn (by norm_num) x (hKρ hx))]
  have hv : NativeCapHolder K α (n + 1) v := ht.sub hKD hzH
  have hVO : V ⊆ openHalfDisc ρ := fun x hx =>
    ⟨hball (Metric.ball_subset_closedBall hx.1), hx.2⟩
  have hvSmooth : ContDiffOn ℝ ∞ v V :=
    ((hsolution.smooth_partial_on_openHalfDisc 1).mono hVO).sub
      (g.smooth_deriv_extension_on_ball.mono (fun x hx => (hVO hx).1))
  have hWO : W ⊆ openHalfDisc ρ := fun x hx =>
    ⟨hwball (Metric.ball_subset_closedBall hx.1), hx.2⟩
  have hW : IsOpen W := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hvWC1 : ContDiffOn ℝ 1 v W :=
    (((hsolution.smooth_partial_on_openHalfDisc 1).mono hWO).sub
      (g.smooth_deriv_extension_on_ball.mono (fun x hx => (hWO hx).1))).of_le (by simp)
  obtain ⟨hV, hVEq⟩ := native_memW1pWitness_actual_classical_gradient W hW v hvWC1 hvSob.someWitness
  have hw0 : LinearWeakEquation W C v (planarGradient v) := by
    have hh := hweak hV
    rwa [hVEq] at hh
  have hVopen : IsOpen V := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hw : LinearWeakEquation V C v (planarGradient v) :=
    native_linear_weak_restrict W V hVopen (fun x hx =>
      ⟨Metric.ball_subset_ball hrrw hx.1, hx.2⟩) C v _ hw0
  have hprincipal : ∀ x ∈ K,
      (∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤ inner ℝ (C.a x ξ) ξ) ∧ ‖C.a x‖ ≤ M :=
    fun x hx => ⟨hell _ (hmap hx), (hbound _ (hmap hx)).2.2.2.2.1⟩
  let D := translateLinearizedCoefficients C c
  let w := fun x => v (x + c)
  have hpre := native_flat_translation_halfDisc c hcf r
  have hKmap : MapsTo (fun x : E2 => x + c) (closedHalfDisc r) K := fun x hx =>
    (Set.ext_iff.mp hpre.2 x).mpr hx
  have hVmap : MapsTo (fun x : E2 => x + c) (openHalfDisc r) V := fun x hx =>
    (Set.ext_iff.mp hpre.1 x).mpr hx
  have hwSmooth : ContDiffOn ℝ ∞ w (openHalfDisc r) :=
    hvSmooth.comp (contDiff_id.add contDiff_const).contDiffOn hVmap
  have hwz : ∀ x ∈ flatBoundary r, w x = 0 := by
    intro x hx
    have hxc : x + c ∈ flatBoundary ρ := by
      refine ⟨hball (hKmap (flatBoundary_subset_closedHalfDisc r hx)).1, ?_⟩
      change (x + c) 0 = 0
      simp only [PiLp.add_apply, hcf, add_zero]
      exact hx.2
    exact sub_eq_zero.mpr (hsolution.tangential_derivative_trace hρ hxc)
  have hww : LinearWeakEquation (openHalfDisc r) D w (planarGradient w) := by
    have hh := native_linear_weak_translation V hVopen.measurableSet c C v _ hw
    rw [hpre.1] at hh
    have he : (fun x => planarGradient v (x + c)) = planarGradient w := by
      funext x
      exact (planar_gradient_translation v c x).symm
    rwa [he] at hh
  obtain ⟨s, hs, hsr, hgain⟩ := native_linear_finite_holder_gain n r κ M hr hκ
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hM) D w α hα hα1
    (hv.translate c hcf r hr) (ha.translate c hcf r hr) (hd.translate c hcf r hr)
    hwSmooth hwz rfl rfl rfl rfl (fun x hx => hprincipal _ (hKmap hx)) hww
  have hback : NativeCapHolder (nativeClosedBoundaryCap c s) α (n + 2) v :=
    hgain.translate_back c hcf s hs
  have hsmall : nativeClosedBoundaryCap c s ⊆ K := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall hsr.le hx.1, hx.2⟩
  have hsd := nativeClosedBoundaryCap_uniqueDiffOn c s hs hcf
  have hbs : Metric.closedBall c s ⊆ Metric.ball 0 ρ :=
    (Metric.closedBall_subset_closedBall hsr.le).trans hball
  have hzGain : NativeCapHolder (nativeClosedBoundaryCap c s) α (n + 2) z :=
    NativeCapHolder.of_contDiffOn_succ c s hs hcf hα1.le ((hzSmooth.mono hsmall).of_le (by simp))
  have htGain : NativeCapHolder (nativeClosedBoundaryCap c s) α (n + 2) t := by
    apply (hback.add hsd hzGain).congr
    intro x _
    dsimp only [v]
    exact (sub_add_cancel _ _).symm
  have hnGain := hsolution.finite_holder_normal_derivative_from_tangential hρ c hc s hs hbs
    α hα hα1.le (n + 1) (closure T) hTcompact hTc.closure hTJ (fun x hx => hmap (hsmall hx))
    (hu.restrict hsmall hsd) htGain
  have hs2 : 0 < s / 2 := by positivity
  have hsmall2 : nativeClosedBoundaryCap c (s / 2) ⊆ nativeClosedBoundaryCap c s := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall (by linarith) hx.1, hx.2⟩
  have hbs2 : Metric.closedBall c (s / 2) ⊆ Metric.ball 0 ρ :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hbs
  refine ⟨s / 2, hs2, hbs2, ?_⟩
  apply native_capHolder_of_partials c hcf (s / 2) hs2 (closedHalfDisc ρ)
    (fun x hx => ⟨Metric.ball_subset_closedBall (hbs2 hx.1), hx.2⟩) u
    (hsolution.c1.differentiableOn (by norm_num)) α hα (n + 2)
  intro i
  fin_cases i
  · simpa [Nat.add_assoc, coordinateVector] using hnGain
  · exact htGain.restrict hsmall2 (nativeClosedBoundaryCap_uniqueDiffOn c (s / 2) hs2 hcf)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
