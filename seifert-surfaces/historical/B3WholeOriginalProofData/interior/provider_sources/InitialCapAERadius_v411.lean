import VM02aDirectMethod
import B1L1IndependentLower
import Mathlib.MeasureTheory.Integral.Average

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

/- Internal selector retaining every additionally established almost-everywhere
radius property. This is used to retain the ACTUAL f-slices and Green chord flux
at the same radius as the original shell-energy budget. -/
private theorem original_cap_good_polar_radius_with_ae_v411
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (x : E2) (r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (P : ℝ → Prop) (hP : ∀ᵐ q ∂volume.restrict (Ioo (r / 2) r), P q) :
    let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
    let angles : Set ℝ := Ioo (-Real.pi) Real.pi
    let annulus : Set E2 := {z | z ∈ disc 1 ∧ r / 2 < ‖z - x‖ ∧ ‖z - x‖ < r}
    ∃ s ∈ Ioo (r / 2) r, P s ∧
      (∀ i, MemLp (fun t => d0 i (x + s • unitCircleParameter t)) 2
        (volume.restrict angles)) ∧
      s * (∫ t in angles, euclideanJetDensity d0 (x + s • unitCircleParameter t)) ≤
        (2 / r) * ∫ z in annulus, euclideanJetDensity d z := by
  classical
  dsimp only
  let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
  let angles : Set ℝ := Ioo (-Real.pi) Real.pi
  let U : Set ℝ := Ioo (r / 2) r
  let annulus : Set E2 := {z | z ∈ disc 1 ∧ r / 2 < ‖z - x‖ ∧ ‖z - x‖ < r}
  let Q : (Fin 2 → E2 → E2) → E2 → ℝ := fun rows z =>
    ‖rows 0 z‖ ^ 2 + ‖rows 1 z‖ ^ 2
  let e : ℝ → ℝ := fun s => s * ∫ t in angles, Q d0 (x + s • unitCircleParameter t)
  let good : ℝ → Prop := fun s => ∀ i,
    MemLp (fun t => d0 i (x + s • unitCircleParameter t)) 2 (volume.restrict angles)
  have hpolar := CourantAnalyticB.native_translated_polar_rows d
    (fun i => (minimum.admissible.1 i).2.2.aestronglyMeasurable)
    (fun i => (minimum.admissible.1 i).2.2) x (r / 2) r
    (by positivity) (by linarith) (by linarith)
  dsimp only at hpolar
  rcases hpolar with ⟨_, _, hslices, _, hint, _, hidentity, _, _⟩
  have he : IntegrableOn e U := hint
  have hgood : ∀ᵐ s ∂volume.restrict U, s ∈ U ∧ P s ∧ good s := by
    filter_upwards [hslices, hP, ae_restrict_mem measurableSet_Ioo] with s hs hp hsu
    exact ⟨hsu, hp, fun i => (hs.1 i).2.1⟩
  let μ : Measure ℝ := volume.restrict U
  have hvolume : volume U = ENNReal.ofReal (r / 2) := by
    dsimp only [U]
    rw [Real.volume_Ioo]
    congr 1
    ring
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by rw [hvolume]; simp)
  have hμ : μ ≠ 0 := by
    apply Measure.measure_univ_ne_zero.mp
    rw [Measure.restrict_apply_univ, hvolume]
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  let N : Set ℝ := {s | ¬(s ∈ U ∧ P s ∧ good s)}
  have hN : μ N = 0 := by
    exact ae_iff.mp hgood
  obtain ⟨s, hsN, hsavg⟩ := exists_notMem_null_le_average hμ he hN
  have hs : s ∈ U ∧ P s ∧ good s := Classical.not_not.mp hsN
  have havg : (⨍ a, e a ∂μ) = (2 / r) * ∫ z in annulus, Q d z := by
    rw [average_eq, Measure.real]
    dsimp only [μ]
    rw [Measure.restrict_apply_univ, hvolume,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    change (r / 2)⁻¹ * (∫ a in U, e a) = _
    have hident : (∫ a in U, e a) = ∫ z in annulus, Q d z := hidentity
    rw [hident]
    congr 1
    field_simp
  have hQ (rows : Fin 2 → E2 → E2) : euclideanJetDensity rows = Q rows := by
    funext z
    exact Fin.sum_univ_two _
  refine ⟨s, hs.1, hs.2.1, hs.2.2, ?_⟩
  rw [hQ d0, hQ d]
  exact hsavg.trans_eq havg

private theorem original_cap_good_shell_radius_with_ae_v411
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (x : E2) (r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (P : ℝ → Prop) (hP : ∀ᵐ q ∂volume.restrict (Ioo (r / 2) r), P q) :
    let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
    let angles : Set ℝ := Ioo (-Real.pi) Real.pi
    ∃ s ∈ Ioo (r / 2) r, P s ∧
      (∀ i, MemLp (fun t => d0 i (x + s • unitCircleParameter t)) 2
        (volume.restrict angles)) ∧
      s ^ 2 * (∫ t in angles, euclideanJetDensity d0 (x + s • unitCircleParameter t)) ≤
        2 * ((∫ z in planarCap x r, euclideanJetDensity d z) -
          (∫ z in planarCap x (r / 2), euclideanJetDensity d z)) := by
  classical
  dsimp only
  obtain ⟨s, hs, hp, hslice, hbound⟩ := original_cap_good_polar_radius_with_ae_v411 minimum x r hr hrhalf P hP
  let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
  let angles : Set ℝ := Ioo (-Real.pi) Real.pi
  let annulus : Set E2 := {z | z ∈ disc 1 ∧ r / 2 < ‖z - x‖ ∧ ‖z - x‖ < r}
  have hi : IntegrableOn (euclideanJetDensity d) (disc 1) := by
    apply integrable_finsetSum
    intro i _
    exact (minimum.admissible.1 i).2.2.norm.integrable_sq
  have hdiff : planarCap x (r / 2) ⊆ planarCap x r :=
    inter_subset_inter_right _ (Metric.ball_subset_ball (by linarith))
  have hsub : annulus ⊆ planarCap x r \ planarCap x (r / 2) := by
    intro z hz
    refine ⟨⟨hz.1, ?_⟩, ?_⟩
    · simpa only [Metric.mem_ball, dist_eq_norm] using hz.2.2
    · intro hzinner
      have hnorm : ‖z - x‖ < r / 2 := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hzinner.2
      exact (not_lt_of_ge hz.2.1.le) hnorm
  have hshell : (∫ z in annulus, euclideanJetDensity d z) ≤
      (∫ z in planarCap x r, euclideanJetDensity d z) -
        (∫ z in planarCap x (r / 2), euclideanJetDensity d z) := by
    have hm := setIntegral_mono_set
      ((hi.mono_set inter_subset_left).mono_set sdiff_subset)
      (Eventually.of_forall fun z => Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Eventually.of_forall fun z hz => hsub hz)
    change (∫ z in annulus, euclideanJetDensity d z) ≤
      ∫ z in planarCap x r \ planarCap x (r / 2), euclideanJetDensity d z at hm
    have heq : (∫ z in planarCap x r \ planarCap x (r / 2), euclideanJetDensity d z) =
        (∫ z in planarCap x r, euclideanJetDensity d z) -
          (∫ z in planarCap x (r / 2), euclideanJetDensity d z) :=
      setIntegral_sdiff (measurableSet_ball.inter measurableSet_ball)
        (hi.mono_set inter_subset_left) hdiff
    exact hm.trans_eq heq
  have henergy : 0 ≤ ∫ t in angles,
      euclideanJetDensity d0 (x + s • unitCircleParameter t) :=
    integral_nonneg (fun t => Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hspos : 0 < s := lt_trans (by positivity) hs.1
  have hmult := mul_le_mul_of_nonneg_left hbound hr.le
  have heq : r * ((2 / r) * ∫ z in annulus, euclideanJetDensity d z) =
      2 * ∫ z in annulus, euclideanJetDensity d z := by field_simp
  rw [heq] at hmult
  refine ⟨s, hs, hp, hslice, ?_⟩
  have hscale : s ^ 2 ≤ r * s := by nlinarith [hs.2, hspos]
  calc
    _ ≤ (r * s) * ∫ t in angles,
        euclideanJetDensity d0 (x + s • unitCircleParameter t) :=
      mul_le_mul_of_nonneg_right hscale henergy
    _ = r * (s * ∫ t in angles,
        euclideanJetDensity d0 (x + s • unitCircleParameter t)) := by ring
    _ ≤ 2 * ∫ z in annulus, euclideanJetDensity d z := hmult
    _ ≤ _ := mul_le_mul_of_nonneg_left hshell (by norm_num)

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
