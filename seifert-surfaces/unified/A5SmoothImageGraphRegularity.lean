import A5NativeGraphOpenSides

set_option autoImplicit false
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates

/-- A C¹ projection section whose image lies in a smooth regular patch is
smooth. The continuous image-coordinate lift is first proved C¹ using a
local retraction, after which the original projection has a smooth inverse. -/
theorem smooth_projection_section_of_smooth_embedded_image
    (f Φ : E2 → E3) (κ : E2 → E2) (P : E3 →L[ℝ] E2)
    (U Ω : Set E2) (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ 1 f U) (hΦ : ContDiffOn ℝ ∞ Φ Ω)
    (hΦrank : ∀ z ∈ Ω, Function.Injective (fderiv ℝ Φ z))
    (hκ : ContinuousOn κ U) (hκΩ : MapsTo κ U Ω)
    (heq : ∀ y ∈ U, Φ (κ y) = f y)
    (hsection : ∀ y ∈ U, P (f y) = y) : ContDiffOn ℝ ∞ f U := by
  intro x hx
  have hcκ : ContinuousAt κ x := hκ.continuousAt (hU.mem_nhds hx)
  have hΦat := hΦ.contDiffAt (hΩ.mem_nhds (hκΩ hx))
  have hfat := hf.contDiffAt (hU.mem_nhds hx)
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (hΦrank _ (hκΩ hx))
  have hLD : HasFDerivAt (L ∘ Φ)
      (ContinuousLinearEquiv.refl ℝ E2 : E2 →L[ℝ] E2) (κ x) := by
    have hd := L.hasFDerivAt.comp (κ x) (hΦat.differentiableAt (by simp)).hasFDerivAt
    have he : L.comp (fderiv ℝ Φ (κ x)) =
        (ContinuousLinearEquiv.refl ℝ E2 : E2 →L[ℝ] E2) := by
      apply ContinuousLinearMap.ext
      intro v
      exact hL v
    simpa only [he] using hd
  have hLat : ContDiffAt ℝ ∞ (L ∘ Φ) (κ x) := L.contDiff.contDiffAt.comp _ hΦat
  let e := hLat.toOpenPartialHomeomorph (L ∘ Φ) hLD (by simp)
  have hκe : κ x ∈ e.source := hLat.mem_toOpenPartialHomeomorph_source hLD (by simp)
  have hreverse : κ =ᶠ[𝓝 x] e.symm ∘ L ∘ f := by
    filter_upwards [hU.mem_nhds hx, hcκ.preimage_mem_nhds (e.open_source.mem_nhds hκe)] with y hy hye
    have hr := e.left_inv hye
    change e.symm (L (Φ (κ y))) = κ y at hr
    rw [heq y hy] at hr
    exact hr.symm
  have hκC1 : ContDiffAt ℝ 1 κ x := by
    have hinv : ContDiffAt ℝ 1 e.symm (L (f x)) := by
      rw [← heq x hx]
      exact (hLat.to_localInverse hLD (by simp)).of_le (by simp)
    exact (hinv.comp x (L.contDiff.contDiffAt.comp x hfat)).congr_of_eventuallyEq hreverse
  let Q := P ∘ Φ
  have hQat : ContDiffAt ℝ ∞ Q (κ x) := P.contDiff.contDiffAt.comp _ hΦat
  have hQκ : Q ∘ κ =ᶠ[𝓝 x] id := by
    filter_upwards [hU.mem_nhds hx] with y hy
    change P (Φ (κ y)) = y
    rw [heq y hy, hsection y hy]
  have hchain : (fderiv ℝ Q (κ x)).comp (fderiv ℝ κ x) = ContinuousLinearMap.id ℝ E2 := by
    rw [← fderiv_comp x (hQat.differentiableAt (by simp))
      (hκC1.differentiableAt (by norm_num)), hQκ.fderiv_eq, fderiv_id]
  have hsurj : Function.Surjective (fderiv ℝ Q (κ x)) := by
    intro v
    refine ⟨fderiv ℝ κ x v, ?_⟩
    exact congrArg (fun D : E2 →L[ℝ] E2 => D v) hchain
  let A := ContinuousLinearEquiv.ofBijective (fderiv ℝ Q (κ x))
    (LinearMap.ker_eq_bot.mpr (LinearMap.injective_iff_surjective.mpr hsurj))
    (LinearMap.range_eq_top.mpr hsurj)
  have hQD : HasFDerivAt Q (A : E2 →L[ℝ] E2) (κ x) :=
    (hQat.differentiableAt (by simp)).hasFDerivAt
  let d := hQat.toOpenPartialHomeomorph Q hQD (by simp)
  have hκd : κ x ∈ d.source := hQat.mem_toOpenPartialHomeomorph_source hQD (by simp)
  have hκeq : κ =ᶠ[𝓝 x] d.symm := by
    filter_upwards [hU.mem_nhds hx, hcκ.preimage_mem_nhds (d.open_source.mem_nhds hκd)] with y hy hyd
    have hr := d.left_inv hyd
    change d.symm (Q (κ y)) = κ y at hr
    have hQy : Q (κ y) = y := by change P (Φ (κ y)) = y; rw [heq y hy, hsection y hy]
    rw [hQy] at hr
    exact hr.symm
  have hκsmooth : ContDiffAt ℝ ∞ κ x := by
    have hinv : ContDiffAt ℝ ∞ d.symm x := by
      have hQx : Q (κ x) = x := hQκ.self_of_nhds
      rw [← hQx]
      exact hQat.to_localInverse hQD (by simp)
    exact hinv.congr_of_eventuallyEq hκeq
  have hgerm : f =ᶠ[𝓝 x] Φ ∘ κ := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (heq y hy).symm
  exact ((hΦat.comp x hκsmooth).congr_of_eventuallyEq hgerm).contDiffWithinAt

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
