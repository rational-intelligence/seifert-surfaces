import HalfStripGlueProbe
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

def seamFrameMap (e m : Euc 2) : (ℝ × ℝ) →L[ℝ] Euc 2 :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight e +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight m

theorem seamFrameMap_apply (e m : Euc 2) (z : ℝ × ℝ) :
    seamFrameMap e m z = z.1 • e + z.2 • m := rfl

theorem seamFrameMap_bijective (e m : Euc 2)
    (he : ‖e‖ = 1) (hm : ‖m‖ = 1) (hem : inner ℝ e m = 0) :
    Function.Bijective (seamFrameMap e m) := by
  have hme : inner ℝ m e = 0 := by rw [real_inner_comm, hem]
  have hinj : Function.Injective (seamFrameMap e m) := by
    intro z w hzw
    have h1 := congrArg (fun y => inner ℝ e y) hzw
    have h2 := congrArg (fun y => inner ℝ m y) hzw
    simp only [seamFrameMap_apply, inner_add_right, inner_smul_right,
      real_inner_self_eq_norm_sq, he, hm, hem, hme, one_pow, mul_one,
      mul_zero, add_zero, zero_add] at h1 h2
    exact Prod.ext h1 h2
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ (Euc 2) by simp [Euc])).mp hinj⟩

def affineSeamCoordinates (o e m : Euc 2) (clock : ℝ → ℝ) (z : ℝ × ℝ) : Euc 2 :=
  o + clock z.1 • e + z.2 • m

/-- A regular C1 boundary clock in an orthonormal straight sector frame
gives the literal affine halfstrip's C1 regularity and full planar rank. -/
theorem affineSeamCoordinates_c1_rank
    (o e m : Euc 2) (clock : ℝ → ℝ) (h : ℝ)
    (he : ‖e‖ = 1) (hm : ‖m‖ = 1) (hem : inner ℝ e m = 0)
    (hc : ContDiffOn ℝ 1 clock (Ioo (-1 : ℝ) 1))
    (hr : ∀ t ∈ Ioo (-1 : ℝ) 1, deriv clock t ≠ 0) :
    ContDiffOn ℝ 1 (affineSeamCoordinates o e m clock) (seamHalfstrip h) ∧
      ∀ z ∈ seamHalfstrip h,
        Function.Injective (fderiv ℝ (affineSeamCoordinates o e m clock) z) := by
  have hcont : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => clock z.1) (seamHalfstrip h) :=
    hc.comp contDiff_fst.contDiffOn (fun _ hz => hz.1)
  refine ⟨(contDiffOn_const.add (hcont.smul contDiffOn_const)).add
    (contDiff_snd.contDiffOn.smul contDiffOn_const), ?_⟩
  intro z hz
  have hca := (hc z.1 hz.1).contDiffAt (isOpen_Ioo.mem_nhds hz.1)
  have hclock : HasFDerivAt (fun z : ℝ × ℝ => clock z.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv clock z.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) z := by
    exact (hca.differentiableAt (by norm_num)).hasDerivAt.hasFDerivAt.comp z
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hd := ((hasFDerivAt_const o z).add (hclock.smul_const e)).add
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.smul_const m)
  have hd' : HasFDerivAt (affineSeamCoordinates o e m clock)
      (0 + ((ContinuousLinearMap.toSpanSingleton ℝ (deriv clock z.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)).smulRight e +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight m) z := hd
  have hD (v : ℝ × ℝ) : fderiv ℝ (affineSeamCoordinates o e m clock) z v =
      seamFrameMap e m (deriv clock z.1 * v.1, v.2) := by
    rw [hd'.fderiv]
    simp [seamFrameMap_apply, ContinuousLinearMap.smulRight_apply, mul_comm]
  intro v w hvw
  rw [hD, hD] at hvw
  have hab := (seamFrameMap_bijective e m he hm hem).1 hvw
  have h1 := congrArg Prod.fst hab
  have h2 := congrArg Prod.snd hab
  exact Prod.ext (mul_left_cancel₀ (hr z.1 hz.1) h1) h2

/-- The same literal affine halfstrip is a topological embedding whenever
its original boundary clock is one. No derivative hypothesis replaces this
global injectivity requirement. -/
theorem affineSeamCoordinates_embedding
    (o e m : Euc 2) (clock : ℝ → ℝ) (h : ℝ)
    (he : ‖e‖ = 1) (hm : ‖m‖ = 1) (hem : inner ℝ e m = 0)
    (hc : IsEmbedding (fun t : Ioo (-1 : ℝ) 1 => clock t)) :
    IsEmbedding (fun z : seamHalfstrip h => affineSeamCoordinates o e m clock z) := by
  let D := seamFrameMap e m
  have hbij := seamFrameMap_bijective e m he hm hem
  let L : (ℝ × ℝ) ≃L[ℝ] Euc 2 := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  let A : (ℝ × ℝ) ≃ₜ Euc 2 := L.toHomeomorph.trans (Homeomorph.addLeft o)
  have hprod := (hc.prodMap (IsEmbedding.subtypeVal (p := fun b : ℝ => b ∈ Ico (0 : ℝ) h))).comp
    (Homeomorph.Set.prod (Ioo (-1 : ℝ) 1) (Ico (0 : ℝ) h)).isEmbedding
  have heq : (fun z : seamHalfstrip h => affineSeamCoordinates o e m clock z) =
      A ∘ (fun z : seamHalfstrip h => (clock z.val.1, z.val.2)) := by
    funext z
    change o + clock z.val.1 • e + z.val.2 • m =
      o + seamFrameMap e m (clock z.val.1, z.val.2)
    rw [seamFrameMap_apply]
    exact add_assoc _ _ _
  rw [heq]
  exact A.isEmbedding.comp hprod

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
