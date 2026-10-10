import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

/-- A continuous lift through a C1 immersion is C1 on its actual closed domain.
No ambient extension of the immersion, nor smoothness of the auxiliary lift,
is assumed. -/
theorem C1_lift_through_relative_immersion
    {V E W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (S : Set E) (T : Set V) (hS : UniqueDiffOn ℝ S) (hT : UniqueDiffOn ℝ T)
    (G : E → W) (g : V → W) (q : V → E)
    (hG : ContDiffOn ℝ 1 G S) (hg : ContDiffOn ℝ 1 g T)
    (hGc : ∀ x ∈ S, Function.Injective (fderivWithin ℝ G S x))
    (hq : ContinuousOn q T) (hmaps : MapsTo q T S)
    (heq : ∀ x ∈ T, G (q x) = g x) :
    ContDiffOn ℝ 1 q T ∧
      ∀ x ∈ T, (fderivWithin ℝ G S (q x)).comp (fderivWithin ℝ q T x) =
        fderivWithin ℝ g T x := by
  have hGd := hG.differentiableOn (by norm_num)
  have hgd := hg.differentiableOn (by norm_num)
  have hqd : DifferentiableOn ℝ q T := by
    intro x hx
    let D := fderivWithin ℝ G S (q x)
    obtain ⟨L, hL⟩ := D.toLinearMap.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (hGc (q x) (hmaps hx)))
    let Lc : W →L[ℝ] E := L.toContinuousLinearMap
    have hinv : Function.LeftInverse Lc D := by
      intro v
      exact congrArg (fun A : E →ₗ[ℝ] E => A v) hL
    exact (HasFDerivWithinAt.of_comp_of_leftInverse
      ((hq x hx).tendsto_nhdsWithin hmaps)
      (hGd (q x) (hmaps hx)).hasFDerivWithinAt
      (hgd x hx).hasFDerivWithinAt
      (Set.EqOn.eventuallyEq_nhdsWithin heq) hinv hx).differentiableWithinAt
  have hchain (x : V) (hx : x ∈ T) :
      (fderivWithin ℝ G S (q x)).comp (fderivWithin ℝ q T x) =
        fderivWithin ℝ g T x := by
    rw [← fderivWithin_comp x (hGd (q x) (hmaps hx)) (hqd x hx) hmaps (hT x hx)]
    exact fderivWithin_congr' heq hx
  have hqc : ContinuousOn (fderivWithin ℝ q T) T := by
    intro x hx
    let D : V → E →L[ℝ] W := fun y => fderivWithin ℝ G S (q y)
    obtain ⟨L, hL⟩ := (D x).toLinearMap.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (hGc (q x) (hmaps hx)))
    let Lc : W →L[ℝ] E := L.toContinuousLinearMap
    have hLc : Lc.comp (D x) = 1 := by
      ext v
      exact congrArg (fun A : E →ₗ[ℝ] E => A v) hL
    let B : V → E →L[ℝ] E := fun y => Lc.comp (D y)
    have hDc : ContinuousOn D T := (hG.continuousOn_fderivWithin hS le_rfl).comp hq hmaps
    have hBc : ContinuousWithinAt B T x := continuousWithinAt_const.clm_comp (hDc x hx)
    have hBx : B x = 1 := hLc
    have hi : ContDiffAt ℝ 0 Ring.inverse (B x) := by
      rw [hBx]
      exact contDiffAt_ringInverse ℝ (1 : (E →L[ℝ] E)ˣ)
    let dq : V → V →L[ℝ] E := fun y =>
      (Ring.inverse (B y)).comp (Lc.comp (fderivWithin ℝ g T y))
    have hdqc : ContinuousWithinAt dq T x :=
      (hi.continuousAt.comp_continuousWithinAt hBc).clm_comp
        (continuousWithinAt_const.clm_comp ((hg.continuousOn_fderivWithin hT le_rfl) x hx))
    have hform (y : V) (hy : y ∈ T) (hyunit : IsUnit (B y)) :
        fderivWithin ℝ q T y = dq y := by
      dsimp only [dq]
      rw [← hchain y hy, ← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc]
      change _ = (Ring.inverse (B y) * B y).comp (fderivWithin ℝ q T y)
      rw [Ring.inverse_mul_cancel _ hyunit]
      rfl
    have hu : ∀ᶠ y in 𝓝[T] x, IsUnit (B y) := hBc.tendsto.eventually
      (Units.isOpen.mem_nhds (show IsUnit (B x) by rw [hBx]; exact isUnit_one))
    apply hdqc.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin, hu] with y hy hyu
      exact hform y hy hyu
    · exact hform x hx (by rw [hBx]; exact isUnit_one)
  refine ⟨?_, hchain⟩
  simpa only [zero_add] using
    (contDiffOn_succ_iff_fderivWithin (n := 0) hT).mpr
      ⟨hqd, by simp, contDiffOn_zero.mpr hqc⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
