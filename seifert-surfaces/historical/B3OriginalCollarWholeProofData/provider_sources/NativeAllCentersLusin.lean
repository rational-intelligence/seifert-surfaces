import NativeMorreyBall
import Mathlib.MeasureTheory.Measure.RegularityCompacts
noncomputable section
open Set Topology Function MeasureTheory Filter Metric
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem all_centers_image_null {u : E2 → E2} {U : Set E2}
    (hU : IsOpen U) (μ : Measure E2) [IsFiniteMeasure μ]
    {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hball : ∀ a r, 0 < r → closedBall a r ⊆ U →
      volume (u '' ball a r) ≤ K * μ (ball a r))
    {E : Set E2} (hEU : E ⊆ U) (hE : μ E = 0) :
    volume (u '' E) = 0 := by
  classical
  obtain ⟨N,τ,hτ,hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := E2)
  have hcoverbound (O : Set E2) (hEO : E ⊆ O) (hO : IsOpen O) :
      volume (u '' E) ≤ K * (N : ℝ≥0∞) * μ O := by
    have hex (x : E) : ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ closedBall (x : E2) r ⊆ O ∩ U := by
      obtain ⟨δ,hδ,hsub⟩ := Metric.isOpen_iff.mp (hO.inter hU) x ⟨hEO x.property,hEU x.property⟩
      refine ⟨min (δ/2) 1,lt_min (by linarith) zero_lt_one,min_le_right _ _,?_⟩
      intro y hy
      apply hsub
      exact mem_ball.mpr ((mem_closedBall.mp hy).trans_lt (lt_of_le_of_lt (min_le_left _ _) (by linarith)))
    choose r hr hr1 hrO using hex
    let q : Besicovitch.BallPackage E E2 := {
      c := Subtype.val
      r := r
      rpos := hr
      r_bound := 1
      r_le := hr1 }
    obtain ⟨s,hsdisj,hscover⟩ := Besicovitch.exist_disjoint_covering_families hτ hN q
    have hsct (i : Fin N) : (s i).Countable :=
      (hsdisj i).countable_of_nonempty_interior (fun x _ =>
        ⟨q.c x,ball_subset_interior_closedBall (mem_ball_self (q.rpos x))⟩)
    have hEcover : E ⊆ ⋃ i : Fin N, ⋃ x : s i, ball (q.c x) (q.r x) := by
      intro x hx
      have hh := hscover (mem_range.mpr ⟨⟨x,hx⟩,rfl⟩)
      simpa only [biUnion_eq_iUnion] using hh
    have hsum (i : Fin N) :
        (∑' x : s i, volume (u '' ball (q.c x) (q.r x))) ≤ K * μ O := by
      letI : Countable (s i) := (hsct i).to_subtype
      have hd : Pairwise (Function.onFun Disjoint (fun x : s i => ball (q.c x) (q.r x))) := by
        intro x y hxy
        exact (hsdisj i x.property y.property (Subtype.coe_ne_coe.mpr hxy)).mono ball_subset_closedBall ball_subset_closedBall
      have hBO : (⋃ x : s i, ball (q.c x) (q.r x)) ⊆ O := by
        intro y hy
        obtain ⟨x,hx⟩ := mem_iUnion.mp hy
        exact (hrO x) (ball_subset_closedBall hx) |>.1
      calc
        _ ≤ ∑' x : s i, K * μ (ball (q.c x) (q.r x)) := ENNReal.tsum_le_tsum (fun x =>
          hball (q.c x) (q.r x) (q.rpos x) (fun y hy => (hrO x hy).2))
        _ = K * ∑' x : s i, μ (ball (q.c x) (q.r x)) := ENNReal.tsum_mul_left
        _ = K * μ (⋃ x : s i, ball (q.c x) (q.r x)) := by rw [measure_iUnion hd (fun _ => isOpen_ball.measurableSet)]
        _ ≤ K * μ O := by gcongr
    calc
      volume (u '' E) ≤ volume (u '' (⋃ i : Fin N, ⋃ x : s i, ball (q.c x) (q.r x))) := measure_mono (image_mono hEcover)
      _ = volume (⋃ i : Fin N, ⋃ x : s i, u '' ball (q.c x) (q.r x)) := by simp only [image_iUnion]
      _ ≤ ∑' i : Fin N, volume (⋃ x : s i, u '' ball (q.c x) (q.r x)) := measure_iUnion_le _
      _ ≤ ∑' i : Fin N, K * μ O := ENNReal.tsum_le_tsum (fun i => by
        letI : Countable (s i) := (hsct i).to_subtype
        exact (measure_iUnion_le _).trans (hsum i))
      _ = K * (N : ℝ≥0∞) * μ O := by simp [tsum_fintype,mul_assoc,mul_comm,mul_left_comm]
  have hfin : K * (N : ℝ≥0∞) ≠ ⊤ := ENNReal.mul_ne_top hK (by simp)
  by_cases hK0 : K*(N : ℝ≥0∞) = 0
  · have hh := hcoverbound U hEU hU
    simpa only [hK0,zero_mul,nonpos_iff_eq_zero] using hh
  have hh : volume (u '' E) ≤ (K * (N : ℝ≥0∞)) * μ E := by
    rw [E.measure_eq_iInf_isOpen μ]
    simp_rw [ENNReal.mul_iInf_of_ne hK0 hfin]
    exact le_iInf (fun O => le_iInf (fun hEO => le_iInf (fun hO => hcoverbound O hEO hO)))
  simpa [hE] using hh
#print axioms all_centers_image_null
