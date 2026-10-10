import NativeH10CutoffLocalization
import PlanarGradientLinearComp
set_option maxHeartbeats 3000000
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open SeifertSurfaces.AppendixACoordinates

theorem flat_trace_linear_pullback (r rho : ℝ) (hrho : 0 < rho)
    (T : E2 ≃L[ℝ] E2) (t : ℝ) (ht : 0 < t) (hT1 : ∀ y : E2, T y 1 = t*y 1)
    (hmap : MapsTo T (disc rho) (disc r))
    (v : E2 → ℝ) (dv : E2 → E2) (htrace : FlatZeroTrace r v dv) :
    FlatZeroTrace rho (fun y => v (T y)) (fun y => T.toContinuousLinearMap.adjoint (dv (T y))) := by
  intro chi hs hc hsupport
  let psi : E2 → ℝ := fun x => chi (T.symm x)
  have hpsis : ContDiff ℝ ∞ psi := hs.comp T.symm.contDiff
  have hpsic : HasCompactSupport psi := hc.comp_homeomorph T.symm.toHomeomorph
  have hpsit : tsupport psi ⊆ disc r := by
    rw [show psi = chi ∘ T.symm.toHomeomorph from rfl,tsupport_comp_eq_preimage]
    intro x hx
    have hh := hmap (hsupport hx)
    change T (T.symm x) ∈ disc r at hh
    rwa [T.apply_symm_apply] at hh
  have hpull := linear_h10_pullback (halfDisc r) T (fun x => psi x*v x) (cutoffGradient psi v dv)
    (htrace psi hpsis hpsic hpsit)
  let u : E2 → ℝ := fun y => chi y*v (T y)
  let du : E2 → E2 := cutoffGradient chi (fun y => v (T y)) (fun y => T.toContinuousLinearMap.adjoint (dv (T y)))
  have hpsi (y : E2) : psi (T y) = chi y := by dsimp [psi]; rw [T.symm_apply_apply]
  have hgrad (y : E2) : T.toContinuousLinearMap.adjoint (planarGradient psi (T y)) = planarGradient chi y := by
    have heq : (fun z => psi (T z)) = chi := funext hpsi
    rw [← planar_gradient_linear_comp T psi hpsis y,heq]
  have heqv : (fun y => psi (T y)*v (T y)) = u := by funext y; rw [hpsi]
  have heqd : (fun y => T.toContinuousLinearMap.adjoint (cutoffGradient psi v dv (T y))) = du := by
    funext y
    dsimp only [du]
    unfold cutoffGradient
    rw [map_add,map_smul,map_smul,hgrad,hpsi]
  rw [heqv,heqd] at hpull
  let U : Set E2 := T ⁻¹' halfDisc r
  let V : Set E2 := halfDisc rho
  have hVU : V ⊆ U := by
    intro y hy
    refine ⟨hmap hy.1,?_⟩
    rw [hT1]
    exact mul_pos ht hy.2
  obtain ⟨ri,⟨hri,hriR⟩,hKi⟩ := exists_pos_lt_subset_ball hrho (isClosed_tsupport chi) hsupport
  obtain ⟨ro,hiro,hor⟩ := exists_between hriR
  let eta : ContDiffBump (0 : E2) := ⟨ri,ro,hri,hiro⟩
  have heta : tsupport (eta : E2 → ℝ) ∩ U ⊆ V := by
    intro y hy
    constructor
    · have hh := hy.1
      rw [eta.tsupport_eq] at hh
      exact (Metric.closedBall_subset_ball hor) hh
    · have hh : 0 < (T y) 1 := hy.2.2
      rw [hT1] at hh
      exact (mul_pos_iff_of_pos_left ht).mp hh
  have heid (y : E2) : eta y*u y = u y ∧ cutoffGradient (eta : E2 → ℝ) u du y = du y := by
    by_cases hy : y ∈ tsupport chi
    · have heta1 : eta y = 1 := eta.one_of_mem_closedBall (Metric.ball_subset_closedBall (hKi hy))
      have hetag : planarGradient (eta : E2 → ℝ) y = 0 := by
        unfold planarGradient
        rw [(eta.eventuallyEq_one_of_mem_ball (hKi hy)).fderiv_eq]
        simp
      constructor
      · rw [heta1,one_mul]
      · unfold cutoffGradient
        rw [heta1,hetag,one_smul,smul_zero,add_zero]
    · have hu0 : u y = 0 := by dsimp [u]; rw [image_eq_zero_of_notMem_tsupport hy,zero_mul]
      have hdu0 : du y = 0 := by
        dsimp only [du]
        unfold cutoffGradient
        rw [image_eq_zero_of_notMem_tsupport hy,planarGradient_eq_zero_off_support chi hy,
          zero_smul,smul_zero,add_zero]
      constructor
      · rw [hu0,mul_zero]
      · unfold cutoffGradient
        rw [hu0,hdu0,smul_zero,zero_smul,add_zero]
  have hloc := h10_cutoff_localization U V hVU (eta : E2 → ℝ) eta.contDiff eta.hasCompactSupport heta u du hpull
  rw [show (fun y => eta y*u y) = u from funext (fun y => (heid y).1),
    show cutoffGradient (eta : E2 → ℝ) u du = du from funext (fun y => (heid y).2)] at hloc
  exact hloc

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
