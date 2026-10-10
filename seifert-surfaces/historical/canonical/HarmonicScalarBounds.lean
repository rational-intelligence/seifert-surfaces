import WeakSmoothRepresentative
import DifferentialGeometry.External.DeGiorgi.ScaledBallEstimates

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace SeifertSurfaces.WeakSchauder

def identityCoeff (Ω : Set V) : DeGiorgi.NormalizedEllipticCoeff 3 Ω :=
  ⟨{ a := fun _ => 1
     lam := 1
     Λ := 1
     measurable_comp := fun _ _ => measurable_const
     hlam := zero_lt_one
     hΛ := le_rfl
     coercive := Eventually.of_forall fun _ v => by
       simp [DeGiorgi.matMulE, real_inner_self_eq_norm_sq]
     coercive_inv := Eventually.of_forall fun _ v => by
       simp [DeGiorgi.matMulE, real_inner_self_eq_norm_sq] }, rfl⟩

theorem leOn_of_ae_le (Ω : Set V) (hΩ : IsOpen Ω) (f : V → ℝ) (C : ℝ)
    (hf : ContinuousOn f Ω) (hae : ∀ᵐ x ∂volume.restrict Ω, f x ≤ C) :
    ∀ x ∈ Ω, f x ≤ C := by
  have he : (fun x => min (f x) C) =ᵐ[volume.restrict Ω] f :=
    hae.mono fun x hx => min_eq_left hx
  have hp := Measure.eqOn_open_of_ae_eq he hΩ (hf.inf continuousOn_const) hf
  intro x hx
  exact min_eq_left_iff.mp (hp hx)

/-- Uniform dimension-three local scalar bound for the fixed identity coefficients. -/
theorem identity_solution_sq_bound (c : V) (R : ℝ) (hR : 0 < R)
    (u : V → ℝ) (hu : H1Witness u (Metric.ball c R))
    (hc : ContinuousOn u (Metric.ball c R))
    (hs : DeGiorgi.IsSolution (identityCoeff (Metric.ball c R)).1 u) :
    ∀ x ∈ Metric.ball c (R / 2),
      |u x| ^ 2 ≤ (8 * DeGiorgi.CMoser 3) * (R ^ (3 : ℕ))⁻¹ *
        ∫ y in Metric.ball c R, |u y| ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball c R)) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  have hp : MemLp (fun x => max (u x) 0) 2 (volume.restrict (Metric.ball c R)) :=
    hu.memLp.sup (MemLp.zero)
  have hn : MemLp (fun x => max (-u x) 0) 2 (volume.restrict (Metric.ball c R)) :=
    hu.memLp.neg.sup (MemLp.zero)
  have hi : IntegrableOn (fun x => |u x| ^ 2) (Metric.ball c R) := by
    simpa only [sq_abs, IntegrableOn] using hu.memLp.integrable_sq
  have hip : IntegrableOn (fun x => |max (u x) 0| ^ 2) (Metric.ball c R) := by
    simpa only [sq_abs, IntegrableOn] using hp.integrable_sq
  have hin : IntegrableOn (fun x => |max (-u x) 0| ^ 2) (Metric.ball c R) := by
    simpa only [sq_abs, IntegrableOn] using hn.integrable_sq
  have bp := DeGiorgi.linfty_subsolution_Moser_on_ball (d := 3) (by norm_num) hR
    (identityCoeff (Metric.ball c R)) (p₀ := 2) (by norm_num) hs.1
    (by simpa only [Real.rpow_two] using hip)
  have bn := DeGiorgi.linfty_subsolution_Moser_on_ball (d := 3) (by norm_num) hR
    (identityCoeff (Metric.ball c R)) (p₀ := 2) (by norm_num)
    (hs.neg_ball hR).1 (by simpa only [Real.rpow_two] using hin)
  have hC : 0 ≤ 8 * DeGiorgi.CMoser 3 * (R ^ (3 : ℕ))⁻¹ := by
    have h := DeGiorgi.one_le_C_Moser (d := 3)
    positivity
  have posbound (t : ℝ) : |max t 0| ^ 2 ≤ |t| ^ 2 := by
    by_cases ht : 0 ≤ t
    · simp [max_eq_left ht]
    · simp [max_eq_right (le_of_not_ge ht), sq_nonneg]
  have ip := integral_mono hip hi (fun x => posbound (u x))
  have ineg := integral_mono hin hi (fun x => by simpa using posbound (-u x))
  apply leOn_of_ae_le _ Metric.isOpen_ball _ _
    ((hc.mono (Metric.ball_subset_ball (by linarith))).abs.pow 2)
  filter_upwards [bp, bn] with x hxp hxn
  norm_num [identityCoeff, Real.rpow_natCast] at hxp hxn
  have hpp := mul_le_mul_of_nonneg_left ip hC
  have hnn := mul_le_mul_of_nonneg_left ineg hC
  simp only [Pi.pow_apply, sq_abs] at hpp hnn ⊢
  by_cases hx : 0 ≤ u x
  · rw [max_eq_left hx] at hxp
    calc
      _ ≤ 8 * DeGiorgi.CMoser 3 * (R ^ 3)⁻¹ * ∫ y in Metric.ball c R, max (u y) 0 ^ 2 := by
        convert hxp using 1 <;> ring
      _ ≤ _ := hpp
  · rw [max_eq_left (by linarith : 0 ≤ -u x)] at hxn
    calc
      _ ≤ 8 * DeGiorgi.CMoser 3 * (R ^ 3)⁻¹ * ∫ y in Metric.ball c R, max (-u y) 0 ^ 2 := by
        simpa only [neg_sq, mul_assoc, mul_comm, mul_left_comm] using hxn
      _ ≤ _ := hnn

end SeifertSurfaces.WeakSchauder
