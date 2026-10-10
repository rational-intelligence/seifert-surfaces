import NativeH10CutoffReuse
import NativeH1SubsetRestriction
set_option maxHeartbeats 3000000
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open SeifertSurfaces.AppendixACoordinates

theorem h10_cutoff_localization (U V : Set E2) (hVU : V ⊆ U)
    (chi : E2 → ℝ) (hs : ContDiff ℝ ∞ chi) (hc : HasCompactSupport chi)
    (hlocal : tsupport chi ∩ U ⊆ V) (u : E2 → ℝ) (du : E2 → E2) (hu : H10On U u du) :
    H10On V (fun y => chi y*u y) (cutoffGradient chi u du) := by
  have hcut := h10_cutoff U chi hs hc u du hu
  have hH1 := h1_restrict_subset U V hVU _ _ hcut.1
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hs.continuous
  have hgcompact : HasCompactSupport (planarGradient chi) := by
    apply hc.mono'
    intro y hy
    by_contra hn
    exact hy (planarGradient_eq_zero_off_support chi hn)
  obtain ⟨K,hK⟩ := hgcompact.exists_bound_of_continuous (continuous_planarGradient hs)
  let B0 := max B 0
  let K0 := max K 0
  have hB0 : 0 ≤ B0 := le_max_right _ _
  have hK0 : 0 ≤ K0 := le_max_right _ _
  have hBc (y : E2) : |chi y| ≤ B0 := by
    have hh : |chi y| ≤ B := by simpa only [Real.norm_eq_abs] using hB y
    exact hh.trans (le_max_left _ _)
  have hKc (y : E2) : ‖planarGradient chi y‖ ≤ K0 := (hK y).trans (le_max_left _ _)
  have smoothLp (phi : E2 → ℝ) (hp : ContDiff ℝ ∞ phi) (hpc : HasCompactSupport phi) :
      MemLp phi 2 (volume.restrict U) ∧ MemLp (planarGradient phi) 2 (volume.restrict U) := by
    have hg : HasCompactSupport (planarGradient phi) := by
      apply hpc.mono'
      intro y hy
      by_contra hn
      exact hy (planarGradient_eq_zero_off_support phi hn)
    exact ⟨(hp.continuous.memLp_of_hasCompactSupport hpc).restrict U,
      ((continuous_planarGradient hp).memLp_of_hasCompactSupport hg).restrict U⟩
  refine ⟨hH1,?_⟩
  intro eps heps
  let A := 2*B0^2+2*K0^2+1
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨phi,hps,hpc,hpt,herr⟩ := hu.2 (eps/A) (div_pos heps hA)
  let psi : E2 → ℝ := fun y => chi y*phi y
  have hpsis : ContDiff ℝ ∞ psi := hs.mul hps
  have hpsic : HasCompactSupport psi := hc.mul_right
  have hpsit : tsupport psi ⊆ V := fun y hy => hlocal ⟨tsupport_mul_subset_left hy,hpt (tsupport_mul_subset_right hy)⟩
  have hgprod (y : E2) : planarGradient psi y =
      chi y • planarGradient phi y+phi y • planarGradient chi y := by
    unfold planarGradient
    rw [fderiv_fun_mul (hs.differentiable (by simp) y) (hps.differentiable (by simp) y)]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
      add_smul,Finset.sum_add_distrib,Finset.smul_sum,smul_smul]
  have hpoint (y : E2) : |chi y*u y-psi y|^2 + ‖cutoffGradient chi u du y-planarGradient psi y‖^2 ≤
      A*(|u y-phi y|^2+‖du y-planarGradient phi y‖^2) := by
    have hv : |chi y*u y-psi y| ≤ B0*|u y-phi y| := by
      change |chi y*u y-chi y*phi y| ≤ _
      rw [← mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_right (hBc y) (abs_nonneg _)
    have hd : cutoffGradient chi u du y-planarGradient psi y =
        chi y • (du y-planarGradient phi y)+(u y-phi y) • planarGradient chi y := by
      unfold cutoffGradient
      rw [hgprod,smul_sub,sub_smul]
      exact add_sub_add_comm _ _ _ _
    have hn : ‖cutoffGradient chi u du y-planarGradient psi y‖ ≤
        B0*‖du y-planarGradient phi y‖+K0*|u y-phi y| := by
      rw [hd]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_right (hBc y) (norm_nonneg _))
        ((mul_le_mul_of_nonneg_left (hKc y) (abs_nonneg _)).trans_eq (mul_comm _ _))
    have hv2 := pow_le_pow_left₀ (abs_nonneg _) hv 2
    have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    dsimp only [A]
    nlinarith [sq_nonneg (B0*‖du y-planarGradient phi y‖-K0*|u y-phi y|),
      sq_nonneg (u y-phi y),sq_nonneg ‖du y-planarGradient phi y‖,sq_abs (u y-phi y)]
  obtain ⟨hpL,hgL⟩ := smoothLp phi hps hpc
  obtain ⟨hpsiL,hgpsiL⟩ := smoothLp psi hpsis hpsic
  have hvi : IntegrableOn (fun y => |u y-phi y|^2) U := by
    change Integrable (fun y => |u y-phi y|^2) (volume.restrict U)
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using (hu.1.2.1.sub hpL).norm.integrable_sq
  have hdi : IntegrableOn (fun y => ‖du y-planarGradient phi y‖^2) U := (hu.1.2.2.sub hgL).norm.integrable_sq
  have herror : IntegrableOn (fun y => |u y-phi y|^2+‖du y-planarGradient phi y‖^2) U := hvi.add hdi
  have hvi' : IntegrableOn (fun y => |chi y*u y-psi y|^2) U := by
    change Integrable (fun y => |chi y*u y-psi y|^2) (volume.restrict U)
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using (hcut.1.2.1.sub hpsiL).norm.integrable_sq
  have hdi' : IntegrableOn (fun y => ‖cutoffGradient chi u du y-planarGradient psi y‖^2) U :=
    (hcut.1.2.2.sub hgpsiL).norm.integrable_sq
  have herror' : IntegrableOn (fun y => |chi y*u y-psi y|^2+‖cutoffGradient chi u du y-planarGradient psi y‖^2) V :=
    (hvi'.add hdi').mono_set hVU
  have hm := integral_mono herror' ((herror.mono_set hVU).const_mul A) hpoint
  rw [integral_const_mul] at hm
  have hnest := setIntegral_mono_set herror
    (Eventually.of_forall fun y => add_nonneg (sq_nonneg _) (sq_nonneg _)) (Eventually.of_forall fun _ hh => hVU hh)
  refine ⟨psi,hpsis,hpsic,hpsit,?_⟩
  calc
    _ ≤ A*(∫ y in V, |u y-phi y|^2+‖du y-planarGradient phi y‖^2) := hm
    _ ≤ A*(∫ y in U, |u y-phi y|^2+‖du y-planarGradient phi y‖^2) := mul_le_mul_of_nonneg_left hnest hA.le
    _ < eps := (mul_lt_mul_of_pos_left herr hA).trans_eq (mul_div_cancel₀ eps hA.ne')

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
