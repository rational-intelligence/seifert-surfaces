import NativeBoundaryCenteredFluxReflection
import NativeBoundaryDirichletLinearization

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

def normalReflectionCLM : E2 →L[ℝ] E2 :=
  normalReflection.toContinuousLinearEquiv.toContinuousLinearMap

def nativeOddGradient (G : E2 → E2) (x : E2) : E2 :=
  if 0 ≤ x 0 then G x else -normalReflection (G (normalReflection x))

def reflectLinearizedCoefficients (C : LinearizedCoefficients) (κ : ℝ) : LinearizedCoefficients where
  a x := if 0 < x 0 then C.a x else if x 0 < 0 then
    normalReflectionCLM.comp ((C.a (normalReflection x)).comp normalReflectionCLM)
    else κ • ContinuousLinearMap.id ℝ E2
  c x := if 0 < x 0 then C.c x else if x 0 < 0 then normalReflection (C.c (normalReflection x)) else 0
  d x := if 0 < x 0 then C.d x else if x 0 < 0 then -normalReflection (C.d (normalReflection x)) else 0
  b x := if 0 < x 0 then C.b x else if x 0 < 0 then (C.b (normalReflection x)).comp normalReflectionCLM else 0
  q x := if 0 < x 0 then C.q x else if x 0 < 0 then C.q (normalReflection x) else 0
  f x := if 0 < x 0 then C.f x else if x 0 < 0 then -C.f (normalReflection x) else 0

theorem normalReflection_maps_centered_ball {c : E2} (hc : c 0 = 0) (ρ : ℝ) :
    MapsTo normalReflection (Metric.ball c ρ) (Metric.ball c ρ) := by
  intro x hx
  change dist (normalReflection x) c < ρ
  rw [← normalReflection_flat hc, normalReflection.dist_map]
  exact hx

theorem reflected_linearized_flux_off_flat
    (c : E2) (hc : c 0 = 0) (ρ κ : ℝ) (C : LinearizedCoefficients)
    (v : E2 → ℝ) (G : E2 → E2) (x : E2) (hx : x ∈ Metric.ball c ρ) (hn : x 0 ≠ 0) :
    linearizedFlux (reflectLinearizedCoefficients C κ) (nativeOddExtension v)
      (nativeOddGradient G) x = nativeCenteredReflectedFlux c ρ (linearizedFlux C v G) x := by
  classical
  have hRx := normalReflection_maps_centered_ball hc ρ hx
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hxU : x ∉ Metric.ball c ρ ∩ {x : E2 | 0 < x 0} := fun hh =>
      (not_lt_of_ge hneg.le) hh.2
    have hRxU : normalReflection x ∈ Metric.ball c ρ ∩ {x : E2 | 0 < x 0} := by
      refine ⟨hRx, ?_⟩
      change 0 < normalReflection x 0
      rw [normalReflection_zero]
      linarith
    simp only [linearizedFlux, reflectLinearizedCoefficients, ite_eq_right (not_lt.mpr hneg.le),
      ite_eq_left hneg, nativeOddExtension, ite_eq_right (not_le.mpr hneg),
      nativeOddGradient, nativeCenteredReflectedFlux, indicator_of_notMem hxU,
      indicator_of_mem hRxU, zero_sub]
    change normalReflection ((C.a (normalReflection x)) (normalReflection (-normalReflection (G (normalReflection x))))) +
      -v (normalReflection x) • normalReflection (C.c (normalReflection x)) -
        normalReflection (C.d (normalReflection x)) = _
    rw [map_neg, normalReflection_involutive]
    simp only [map_neg, map_add, map_smul, neg_smul, neg_add_rev]
    module
  · have hxU : x ∈ Metric.ball c ρ ∩ {x : E2 | 0 < x 0} := ⟨hx, hpos⟩
    have hRxU : normalReflection x ∉ Metric.ball c ρ ∩ {x : E2 | 0 < x 0} := by
      intro hh
      have hnorm : 0 < normalReflection x 0 := hh.2
      rw [normalReflection_zero] at hnorm
      linarith
    simp only [linearizedFlux, reflectLinearizedCoefficients, ite_eq_left hpos,
      nativeOddExtension, ite_eq_left hpos.le, nativeOddGradient, nativeCenteredReflectedFlux,
      indicator_of_mem hxU, indicator_of_notMem hRxU, map_zero, sub_zero]

theorem reflected_linearized_source_off_flat
    (c : E2) (hc : c 0 = 0) (ρ κ : ℝ) (C : LinearizedCoefficients)
    (v : E2 → ℝ) (G : E2 → E2) (x : E2) (hx : x ∈ Metric.ball c ρ) (hn : x 0 ≠ 0) :
    linearizedSource (reflectLinearizedCoefficients C κ) (nativeOddExtension v)
      (nativeOddGradient G) x = nativeCenteredReflectedSource c ρ (linearizedSource C v G) x := by
  classical
  have hRx := normalReflection_maps_centered_ball hc ρ hx
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hxU : x ∉ Metric.ball c ρ ∩ {x : E2 | 0 < x 0} := fun hh =>
      (not_lt_of_ge hneg.le) hh.2
    have hRxU : normalReflection x ∈ Metric.ball c ρ ∩ {x : E2 | 0 < x 0} := by
      refine ⟨hRx, ?_⟩
      change 0 < normalReflection x 0
      rw [normalReflection_zero]
      linarith
    simp only [linearizedSource, reflectLinearizedCoefficients, ite_eq_right (not_lt.mpr hneg.le),
      ite_eq_left hneg, nativeOddExtension, ite_eq_right (not_le.mpr hneg),
      nativeOddGradient, nativeCenteredReflectedSource, indicator_of_notMem hxU,
      indicator_of_mem hRxU, zero_sub]
    change (C.b (normalReflection x)) (normalReflection (-normalReflection (G (normalReflection x)))) +
      C.q (normalReflection x) * -v (normalReflection x) + -C.f (normalReflection x) = _
    rw [map_neg, normalReflection_involutive, map_neg]
    ring
  · have hxU : x ∈ Metric.ball c ρ ∩ {x : E2 | 0 < x 0} := ⟨hx, hpos⟩
    have hRxU : normalReflection x ∉ Metric.ball c ρ ∩ {x : E2 | 0 < x 0} := by
      intro hh
      have hnorm : 0 < normalReflection x 0 := hh.2
      rw [normalReflection_zero] at hnorm
      linarith
    simp only [linearizedSource, reflectLinearizedCoefficients, ite_eq_left hpos,
      nativeOddExtension, ite_eq_left hpos.le, nativeOddGradient, nativeCenteredReflectedSource,
      indicator_of_mem hxU, indicator_of_notMem hRxU, sub_zero]

theorem native_flat_plane_null : volume {x : E2 | x 0 = 0} = 0 := by
  have hm := PiLp.volume_preserving_ofLp (Fin 2)
  calc
    volume {x : E2 | x 0 = 0} = volume {x : Fin 2 → ℝ | x 0 = 0} :=
      hm.measure_preimage (s := {x : Fin 2 → ℝ | x 0 = 0})
        ((isClosed_eq (continuous_apply 0) continuous_const).measurableSet.nullMeasurableSet)
    _ = 0 := Measure.pi_hyperplane (fun _ : Fin 2 => volume (α := ℝ)) 0 0

theorem normalReflection_conjugate_norm_le
    (A : E2 →L[ℝ] E2) (M : ℝ) (hM : 0 ≤ M) (hA : ‖A‖ ≤ M) :
    ‖normalReflectionCLM.comp (A.comp normalReflectionCLM)‖ ≤ M := by
  apply (normalReflectionCLM.comp (A.comp normalReflectionCLM)).opNorm_le_bound hM
  intro ξ
  change ‖normalReflection (A (normalReflection ξ))‖ ≤ M * ‖ξ‖
  rw [normalReflection.norm_map]
  exact (A.le_opNorm _).trans (by rw [normalReflection.norm_map]; gcongr)

theorem normalReflection_scalar_comp_norm_le
    (b : E2 →L[ℝ] ℝ) (M : ℝ) (hM : 0 ≤ M) (hb : ‖b‖ ≤ M) :
    ‖b.comp normalReflectionCLM‖ ≤ M := by
  apply (b.comp normalReflectionCLM).opNorm_le_bound hM
  intro ξ
  change ‖b (normalReflection ξ)‖ ≤ M * ‖ξ‖
  exact (b.le_opNorm _).trans (by rw [normalReflection.norm_map]; gcongr)

theorem native_reflected_coefficient_bounds
    (c : E2) (hc : c 0 = 0) (ρ κ M : ℝ) (C : LinearizedCoefficients)
    (hb : CoefficientBounds (Metric.ball c ρ ∩ {x : E2 | 0 < x 0}) C κ M) :
    CoefficientBounds (Metric.ball c ρ) (reflectLinearizedCoefficients C κ) κ (M + κ) := by
  have hM : 0 ≤ M := by linarith [hb.2.1]
  have hMM : M ≤ M + κ := le_add_of_nonneg_right hb.1.le
  refine ⟨hb.1, hb.2.1.trans hMM, ?_, ?_⟩
  · intro x hx ξ
    rcases lt_trichotomy 0 (x 0) with hp | hz | hn
    · dsimp only [reflectLinearizedCoefficients]
      rw [ite_eq_left hp]
      exact hb.2.2.1 x ⟨hx, hp⟩ ξ
    · have hxz : x 0 = 0 := hz.symm
      simp [reflectLinearizedCoefficients, hxz,
        smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
    · have hRx : normalReflection x ∈ Metric.ball c ρ ∩ {x : E2 | 0 < x 0} := by
        refine ⟨normalReflection_maps_centered_ball hc ρ hx, ?_⟩
        change 0 < normalReflection x 0
        rw [normalReflection_zero]
        linarith
      change κ * ‖ξ‖ ^ 2 ≤ inner ℝ ((if 0 < x 0 then C.a x else
        if x 0 < 0 then normalReflectionCLM.comp ((C.a (normalReflection x)).comp normalReflectionCLM)
          else κ • ContinuousLinearMap.id ℝ E2) ξ) ξ
      rw [ite_eq_right (not_lt.mpr hn.le), ite_eq_left hn]
      change κ * ‖ξ‖ ^ 2 ≤ inner ℝ (normalReflection (C.a (normalReflection x) (normalReflection ξ))) ξ
      rw [← normalReflection_adjoint, ContinuousLinearMap.adjoint_inner_left]
      change κ * ‖ξ‖ ^ 2 ≤ inner ℝ (C.a (normalReflection x) (normalReflection ξ)) (normalReflection ξ)
      simpa only [normalReflection.norm_map] using hb.2.2.1 _ hRx (normalReflection ξ)
  · intro x hx
    rcases lt_trichotomy 0 (x 0) with hp | hz | hn
    · simpa only [reflectLinearizedCoefficients, ite_eq_left hp] using
        (show ‖C.a x‖ ≤ M + κ ∧ ‖C.c x‖ ≤ M + κ ∧ ‖C.d x‖ ≤ M + κ ∧
          ‖C.b x‖ ≤ M + κ ∧ |C.q x| ≤ M + κ ∧ |C.f x| ≤ M + κ from
          let H := hb.2.2.2 x ⟨hx, hp⟩
          ⟨H.1.trans hMM, H.2.1.trans hMM, H.2.2.1.trans hMM,
            H.2.2.2.1.trans hMM, H.2.2.2.2.1.trans hMM, H.2.2.2.2.2.trans hMM⟩)
    · have hxz : x 0 = 0 := hz.symm
      simp only [reflectLinearizedCoefficients, hxz, lt_self_iff_false, ite_false,
        norm_smul, Real.norm_eq_abs, abs_of_pos hb.1, ContinuousLinearMap.norm_id,
        mul_one, norm_zero, abs_zero]
      have hMK : 0 ≤ M + κ := add_nonneg hM hb.1.le
      exact ⟨le_add_of_nonneg_left hM, hMK, hMK, hMK, hMK, hMK⟩
    · have hRx : normalReflection x ∈ Metric.ball c ρ ∩ {x : E2 | 0 < x 0} := by
        refine ⟨normalReflection_maps_centered_ball hc ρ hx, ?_⟩
        change 0 < normalReflection x 0
        rw [normalReflection_zero]
        linarith
      obtain ⟨ha, hc', hd, hb', hq, hf⟩ := hb.2.2.2 _ hRx
      simp only [reflectLinearizedCoefficients, ite_eq_right (not_lt.mpr hn.le), ite_eq_left hn,
        norm_neg, normalReflection.norm_map, abs_neg]
      exact ⟨(normalReflection_conjugate_norm_le _ M hM ha).trans hMM,
        hc'.trans hMM, hd.trans hMM,
        (normalReflection_scalar_comp_norm_le _ M hM hb').trans hMM,
        hq.trans hMM, hf.trans hMM⟩

theorem native_linearized_equation_odd_reflection
    (c : E2) (hc : c 0 = 0) (ρ κ : ℝ) (C : LinearizedCoefficients)
    (v : E2 → ℝ) (G : E2 → E2)
    (hF : MemLp (linearizedFlux C v G) 2
      (volume.restrict (Metric.ball c ρ ∩ {x : E2 | 0 < x 0})))
    (hS : MemLp (linearizedSource C v G) 2
      (volume.restrict (Metric.ball c ρ ∩ {x : E2 | 0 < x 0})))
    (hw : LinearWeakEquation (Metric.ball c ρ ∩ {x : E2 | 0 < x 0}) C v G) :
    LinearWeakEquation (Metric.ball c ρ) (reflectLinearizedCoefficients C κ)
      (nativeOddExtension v) (nativeOddGradient G) := by
  obtain ⟨_, _, heq⟩ := native_centered_flux_source_reflected_weak_identity c hc ρ
    (linearizedFlux C v G) (linearizedSource C v G) hF hS
    (fun φ hs hc' ht => (hw φ hs hc' ht).2.2)
  have hne : ∀ᵐ x : E2 ∂volume, x 0 ≠ 0 := by
    simpa only [ae_iff, not_not] using native_flat_plane_null
  intro φ hs hc' ht
  obtain ⟨hiF, hiS, hzero⟩ := heq φ hs hc' ht
  have hFae : (fun x => inner ℝ
      (linearizedFlux (reflectLinearizedCoefficients C κ) (nativeOddExtension v) (nativeOddGradient G) x)
      (planarGradient φ x)) =ᵐ[volume.restrict (Metric.ball c ρ)]
      (fun x => inner ℝ (nativeCenteredReflectedFlux c ρ (linearizedFlux C v G) x) (planarGradient φ x)) := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet, hne.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hn
    rw [reflected_linearized_flux_off_flat c hc ρ κ C v G x hx hn]
  have hSae : (fun x => linearizedSource (reflectLinearizedCoefficients C κ) (nativeOddExtension v) (nativeOddGradient G) x * φ x)
      =ᵐ[volume.restrict (Metric.ball c ρ)]
      (fun x => nativeCenteredReflectedSource c ρ (linearizedSource C v G) x * φ x) := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet, hne.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hn
    rw [reflected_linearized_source_off_flat c hc ρ κ C v G x hx hn]
  refine ⟨hiF.integrableOn.congr hFae.symm, hiS.integrableOn.congr hSae.symm, ?_⟩
  have hiAe : (fun x => inner ℝ
      (linearizedFlux (reflectLinearizedCoefficients C κ) (nativeOddExtension v) (nativeOddGradient G) x)
      (planarGradient φ x) -
      linearizedSource (reflectLinearizedCoefficients C κ) (nativeOddExtension v) (nativeOddGradient G) x * φ x)
      =ᵐ[volume.restrict (Metric.ball c ρ)]
      (fun x => inner ℝ (nativeCenteredReflectedFlux c ρ (linearizedFlux C v G) x) (planarGradient φ x) -
        nativeCenteredReflectedSource c ρ (linearizedSource C v G) x * φ x) := by
    filter_upwards [hFae, hSae] with x hf hs'
    rw [hf, hs']
  rw [integral_congr_ae hiAe]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hzero
  · intro x hx
    have hx' : x ∉ tsupport φ := fun hh => hx (ht hh)
    simp [Helpers.gradient_zero_off_tsupport φ hx', image_eq_zero_of_notMem_tsupport hx']

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
