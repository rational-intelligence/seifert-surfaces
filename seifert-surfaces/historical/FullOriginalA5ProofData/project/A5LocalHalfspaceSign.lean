import A5SmoothBoundaryStraightener
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates

/-- The first component of a C1 coordinate change with positive inward
derivative and zero flat trace has the exact half-space sign locally.
The conclusion controls both sides of the flat boundary. -/
theorem local_halfspace_sign_of_C1_flat_trace
    (p : E2 → ℝ) (U : Set E2) (hU : IsOpen U) (hzero : (0 : E2) ∈ U)
    (hp : ContDiffOn ℝ 1 p U)
    (htrace : ∀ s : ℝ, s • coordinateVector 2 1 ∈ U →
      p (s • coordinateVector 2 1) = 0)
    (hder : 0 < fderiv ℝ p 0 (coordinateVector 2 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t s : ℝ, |t| < ε → |s| < ε →
      t • coordinateVector 2 0 + s • coordinateVector 2 1 ∈ U ∧
      (0 ≤ p (t • coordinateVector 2 0 + s • coordinateVector 2 1) ↔ 0 ≤ t) ∧
      (p (t • coordinateVector 2 0 + s • coordinateVector 2 1) = 0 ↔ t = 0) := by
  let q : ℝ → ℝ → E2 := fun t s =>
    t • coordinateVector 2 0 + s • coordinateVector 2 1
  have hc : ContinuousOn (fun z => fderiv ℝ p z (coordinateVector 2 0)) U :=
    (hp.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  let V := U ∩ {z | 0 < fderiv ℝ p z (coordinateVector 2 0)}
  have hV : IsOpen V := hc.isOpen_inter_preimage hU isOpen_Ioi
  obtain ⟨δ,hδ,hδV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds ⟨hzero,hder⟩)
  let ε := δ / 3
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hn (t s : ℝ) : ‖q t s‖ ≤ |t| + |s| := by
    calc
      ‖q t s‖ ≤ ‖t • coordinateVector 2 0‖ + ‖s • coordinateVector 2 1‖ := norm_add_le _ _
      _ = |t| + |s| := by simp [norm_smul,coordinateVector,EuclideanSpace.single]
  have hq (t s : ℝ) (ht : |t| < ε) (hs : |s| < ε) : q t s ∈ V := by
    apply hδV
    rw [Metric.mem_ball,dist_zero_right]
    have hh := hn t s
    dsimp [ε] at ht hs
    linarith
  refine ⟨ε,hε,?_⟩
  intro t s ht hs
  have htI : t ∈ Ioo (-ε) ε := abs_lt.mp ht
  have hzI : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε,hε⟩
  have hqzero : p (q 0 s) = 0 := by
    have hh := htrace s (by simpa only [q,zero_smul,zero_add] using (hq 0 s (by simpa using hε) hs).1)
    simpa only [q,zero_smul,zero_add] using hh
  have hqt : Continuous (fun a : ℝ => q a s) := by dsimp [q]; fun_prop
  have hmono : StrictMonoOn (fun a : ℝ => p (q a s)) (Ioo (-ε) ε) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · exact hp.continuousOn.comp hqt.continuousOn (fun a ha => (hq a s (abs_lt.mpr ha) hs).1)
    · intro a ha
      have haI : a ∈ Ioo (-ε) ε := interior_subset ha
      have haV := hq a s (abs_lt.mpr haI) hs
      have hpd := (hp.contDiffAt (hU.mem_nhds haV.1)).differentiableAt (by simp)
      have hqd : HasDerivAt (fun b : ℝ => q b s) (coordinateVector 2 0) a := by
        convert!
          ((hasDerivAt_id a).smul_const (coordinateVector 2 0)).add_const
            (s • coordinateVector 2 1) using 1 <;> simp only [q,id_eq,one_smul]
      change 0 < deriv (p ∘ fun b => q b s) a
      rw [(hpd.hasFDerivAt.comp_hasDerivAt a hqd).deriv]
      exact haV.2
  have hpos : 0 < t → 0 < p (q t s) := by
    intro h
    simpa only [hqzero] using hmono hzI htI h
  have hneg : t < 0 → p (q t s) < 0 := by
    intro h
    simpa only [hqzero] using hmono htI hzI h
  refine ⟨(hq t s ht hs).1,?_,?_⟩
  · constructor
    · intro h
      exact le_of_not_gt (fun htneg => (not_lt_of_ge h) (hneg htneg))
    · intro h
      rcases lt_or_eq_of_le h with h|h
      · exact (hpos h).le
      · simpa only [← h] using hqzero.ge
  · constructor
    · intro h
      exact hmono.injOn htI hzI (h.trans hqzero.symm)
    · intro h
      simpa only [h] using hqzero

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
