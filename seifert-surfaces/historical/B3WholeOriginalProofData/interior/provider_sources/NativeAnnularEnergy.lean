import NativeCutoffMinimum
import NativeHoleFilling

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent
set_option autoImplicit false
set_option maxHeartbeats 0

private theorem native_compact_gradient_square_bound
    (u c : E2) (d : Fin 2 → E2) (eta D : ℝ) (g : E2)
    (h01 : 0 ≤ eta ∧ eta ≤ 1) (hD : 0 ≤ D) (hg : ‖g‖ ≤ D) :
    (∑ i, ‖(1 - eta) • d i - (u i - c i) • g‖ ^ 2) ≤
      2 * (∑ i, ‖d i‖ ^ 2) + 2 * D ^ 2 * ‖u - c‖ ^ 2 := by
  have hp (i : Fin 2) : ‖(1 - eta) • d i - (u i - c i) • g‖ ^ 2 ≤
      2 * ‖d i‖ ^ 2 + 2 * D ^ 2 * (u i - c i)^2 := by
    have hn := norm_sub_le ((1 - eta) • d i) ((u i - c i) • g)
    have h1 : ‖(1 - eta) • d i‖ ≤ ‖d i‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h01.2)]
      nlinarith [norm_nonneg (d i)]
    have h2 : ‖(u i - c i) • g‖ ≤ |u i - c i| * D := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hg (abs_nonneg _)
    have hwhole : ‖(1 - eta) • d i - (u i - c i) • g‖ ≤ ‖d i‖ + |u i - c i| * D :=
      hn.trans (add_le_add h1 h2)
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hwhole
    nlinarith [sq_nonneg (‖d i‖ - |u i - c i| * D), sq_abs (u i - c i)]
  have hsum := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin 2))) => hp i)
  have hnorm : ‖u - c‖ ^ 2 = ∑ i : Fin 2, (u i - c i)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [PiLp.sub_apply]
  rw [hnorm]
  calc
    _ ≤ ∑ i : Fin 2, (2 * ‖d i‖ ^ 2 + 2 * D ^ 2 * (u i - c i)^2) := hsum
    _ = _ := by
      simp only [Fin.sum_univ_two]
      ring

private theorem native_annular_competitor_integral_bound
    (u : E2 → E2) (d : Fin 2 → E2 → E2) (a : E2) (s t D : ℝ)
    (hs : 0 < s) (hst : s < t) (hD : 0 ≤ D)
    (hsub : Metric.ball a t ⊆ disc 1)
    (hH1 : ∀ i, H1On (disc 1) (fun z => u z i) (d i))
    (chi : E2 → ℝ) (hc : ContDiff ℝ ∞ chi) (c : E2)
    (h01 : ∀ z, 0 ≤ chi z ∧ chi z ≤ 1)
    (hone : ∀ z ∈ Metric.ball a s, chi z = 1 ∧ planarGradient chi z = 0)
    (hg : ∀ z, ‖planarGradient chi z‖ ≤ D / (t - s))
    (hseam : ∀ i, H10On (Metric.ball a t)
      (fun z => (u z - chi z • (u z - c)) i - u z i)
      (fun z => ((1 - chi z) • d i z - (u z i - c i) • planarGradient chi z) - d i z)) :
    (∫ z in Metric.ball a t,
      euclideanJetDensity (fun i z => (1 - chi z) • d i z -
        (u z i - c i) • planarGradient chi z) z) ≤
      2 * ((∫ z in Metric.ball a t, euclideanJetDensity d z) -
        ∫ z in Metric.ball a s, euclideanJetDensity d z) +
      2 * (D / (t - s)) ^ 2 * ∫ z in Metric.ball a t, ‖u z - c‖ ^ 2 := by
  classical
  let U := Metric.ball a t
  let V := Metric.ball a s
  let dh : Fin 2 → E2 → E2 := fun i z => (1 - chi z) • d i z -
    (u z i - c i) • planarGradient chi z
  have hVU : V ⊆ U := Metric.ball_subset_ball hst.le
  have hjet (i : Fin 2) : MemLp (dh i) 2 (volume.restrict U) := by
    have hi := ((hH1 i).2.2.mono_measure (Measure.restrict_mono hsub le_rfl)).add
      (hseam i).1.2.2
    convert hi using 1
    funext z
    dsimp [dh]
    abel
  have he : IntegrableOn (euclideanJetDensity d) U :=
    integrable_finsetSum _ (fun i _ =>
      ((hH1 i).2.2.mono_measure (Measure.restrict_mono hsub le_rfl)).norm.integrable_sq)
  have hd : IntegrableOn (euclideanJetDensity dh) U :=
    integrable_finsetSum _ (fun i _ => (hjet i).norm.integrable_sq)
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hu : MemLp u 2 (volume.restrict U) :=
    memLp_piLp_iff.mpr (fun i =>
      (hH1 i).2.1.mono_measure (Measure.restrict_mono hsub le_rfl))
  have hv : IntegrableOn (fun z => ‖u z - c‖ ^ 2) U :=
    (hu.sub (memLp_const c)).norm.integrable_sq
  have hDn : 0 ≤ D / (t - s) := div_nonneg hD (sub_pos.mpr hst).le
  have hpoint : ∀ z, euclideanJetDensity dh z ≤
      2 * euclideanJetDensity d z + 2 * (D / (t - s)) ^ 2 * ‖u z - c‖ ^ 2 :=
    fun z => native_compact_gradient_square_bound (u z) c (fun i => d i z)
      (chi z) (D / (t - s)) (planarGradient chi z) (h01 z) hDn (hg z)
  have hzero : ∀ z ∈ V, euclideanJetDensity dh z = 0 := by
    intro z hz
    obtain ⟨hchi, hgrad⟩ := hone z hz
    simp [euclideanJetDensity, dh, hchi, hgrad]
  have hlocal : (∫ z in U, euclideanJetDensity dh z) =
      ∫ z in U \ V, euclideanJetDensity dh z := by
    rw [setIntegral_sdiff Metric.isOpen_ball.measurableSet hd hVU]
    have hz : (∫ z in V, euclideanJetDensity dh z) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero hzero
    rw [hz, sub_zero]
  rw [hlocal]
  have hsum : IntegrableOn (fun z => 2 * euclideanJetDensity d z +
      2 * (D / (t - s)) ^ 2 * ‖u z - c‖ ^ 2) U :=
    (he.const_mul 2).add (hv.const_mul (2 * (D / (t - s)) ^ 2))
  have hbound := integral_mono_ae (μ := volume.restrict (U \ V)) (hd.mono_set sdiff_subset)
    (hsum.mono_set sdiff_subset)
    (Filter.Eventually.of_forall hpoint)
  calc
    _ ≤ ∫ z in U \ V, (2 * euclideanJetDensity d z +
        2 * (D / (t - s)) ^ 2 * ‖u z - c‖ ^ 2) := hbound
    _ = 2 * (∫ z in U \ V, euclideanJetDensity d z) +
        2 * (D / (t - s)) ^ 2 * ∫ z in U \ V, ‖u z - c‖ ^ 2 := by
      rw [integral_add ((he.mono_set sdiff_subset).const_mul 2)
        ((hv.mono_set sdiff_subset).const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ 2 * ((∫ z in U, euclideanJetDensity d z) -
        ∫ z in V, euclideanJetDensity d z) +
        2 * (D / (t - s)) ^ 2 * ∫ z in U, ‖u z - c‖ ^ 2 := by
      rw [setIntegral_sdiff Metric.isOpen_ball.measurableSet he hVU]
      have hm : (∫ z in U \ V, ‖u z - c‖ ^ 2) ≤ ∫ z in U, ‖u z - c‖ ^ 2 :=
        setIntegral_mono_set hv (Filter.Eventually.of_forall fun z => sq_nonneg ‖u z - c‖)
          sdiff_subset.eventuallyLE
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hm (by positivity))

#print axioms native_compact_gradient_square_bound
#print axioms native_annular_competitor_integral_bound
