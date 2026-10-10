import B1L1IndependentLower
import B1ScalarCapPoincare
set_option autoImplicit false
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.AnalyticLower
open SeifertSurfaces.AppendixACoordinates L1Independent
theorem native_H1_moving_cap_poincare (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => f x i) (d i)) :
    ∃ P : ℝ, 0 ≤ P ∧
      ∀ x ∈ closedDisc 1, ∀ r : ℝ, 0 < r → r ≤ 1 →
        capExcess (fun z i _j => f z i) x r ≤
          P * r ^ 2 * ∫ z in planarCap x r, euclideanJetDensity d z := by
  have scalar_caps := fun i : Fin 2 =>
    scalar_native_H1_moving_cap_poincare (fun z => f z i) (d i) (hH1 i)
  obtain ⟨C0, hC0, hp0⟩ := scalar_caps 0
  obtain ⟨C1, hC1, hp1⟩ := scalar_caps 1
  refine ⟨2 * (C0 + C1), by positivity, ?_⟩
  intro x hx r hr hr1
  let U := planarCap x r
  let F : E2 → Mat2 := fun z i j => f z i
  let m : Fin 2 → ℝ := fun i => (capVolume x r)⁻¹ * ∫ z in U, f z i
  have hsub : U ⊆ disc 1 := inter_subset_left
  let : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hsub).trans_lt measure_ball_lt_top).ne
  have hLp (i : Fin 2) : MemLp (fun z => f z i) 2 (volume.restrict U) :=
    MemLp.mono_measure (Measure.restrict_mono hsub le_rfl) (hH1 i).2.1
  have hi (i : Fin 2) : IntegrableOn (fun z => (f z i - m i) ^ 2) U :=
    ((hLp i).sub (memLp_const (m i))).integrable_sq
  have hd (i : Fin 2) : IntegrableOn (fun z => ‖d i z‖ ^ 2) U := by
    have hi : IntegrableOn (fun z => ‖d i z‖ ^ 2) (disc 1) :=
      (hH1 i).2.2.norm.integrable_sq
    exact hi.mono_set hsub
  have hpoint (z : E2) :
      frobeniusSquared (F z - capMean F x r) =
        2 * (f z 0 - m 0) ^ 2 + 2 * (f z 1 - m 1) ^ 2 := by
    delta frobeniusSquared
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    change ((f z 0 - m 0) ^ 2 + (f z 0 - m 0) ^ 2) +
      ((f z 1 - m 1) ^ 2 + (f z 1 - m 1) ^ 2) = _
    ring
  have hexc : capExcess (fun z i _j => f z i) x r =
      2 * (∫ z in U, (f z 0 - m 0) ^ 2) +
        2 * (∫ z in U, (f z 1 - m 1) ^ 2) := by
    change ∫ z in U, frobeniusSquared (F z - capMean F x r) = _
    calc
      _ = ∫ z in U, 2 * (f z 0 - m 0) ^ 2 + 2 * (f z 1 - m 1) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with z
        exact hpoint z
      _ = _ := by
        rw [integral_add ((hi 0).const_mul 2) ((hi 1).const_mul 2),
          integral_const_mul, integral_const_mul]
  have henergy : (∫ z in U, euclideanJetDensity d z) =
      (∫ z in U, ‖d 0 z‖ ^ 2) + ∫ z in U, ‖d 1 z‖ ^ 2 := by
    calc
      _ = ∫ z in U, ‖d 0 z‖ ^ 2 + ‖d 1 z‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with z
        exact Fin.sum_univ_two _
      _ = _ := integral_add (hd 0) (hd 1)
  have he0 : 0 ≤ ∫ z in U, ‖d 0 z‖ ^ 2 := integral_nonneg (fun z => sq_nonneg _)
  have he1 : 0 ≤ ∫ z in U, ‖d 1 z‖ ^ 2 := integral_nonneg (fun z => sq_nonneg _)
  have hb0 := hp0 x hx r hr hr1
  have hb1 := hp1 x hx r hr hr1
  change (∫ z in U, (f z 0 - m 0) ^ 2) ≤ C0 * r ^ 2 * ∫ z in U, ‖d 0 z‖ ^ 2 at hb0
  change (∫ z in U, (f z 1 - m 1) ^ 2) ≤ C1 * r ^ 2 * ∫ z in U, ‖d 1 z‖ ^ 2 at hb1
  change capExcess F x r ≤ _
  rw [hexc]
  change _ ≤ 2 * (C0 + C1) * r ^ 2 * ∫ z in U, euclideanJetDensity d z
  rw [henergy]
  have hcross0 := mul_nonneg (mul_nonneg hC0 (sq_nonneg r)) he1
  have hcross1 := mul_nonneg (mul_nonneg hC1 (sq_nonneg r)) he0
  nlinarith [hb0, hb1]
end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.AnalyticLower
