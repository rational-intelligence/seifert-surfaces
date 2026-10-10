import A5SmoothImageGraphRegularity

set_option autoImplicit false
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

/-- A continuous coordinate lift between two smooth regular surface
parametrizations is smooth and has invertible derivative. -/
theorem smooth_regular_image_coordinate_lift
    (f Φ : E2 → E3) (κ : E2 → E2) (U Ω : Set E2)
    (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ ∞ f U) (hΦ : ContDiffOn ℝ ∞ Φ Ω)
    (hfrank : ∀ x ∈ U, Function.Injective (fderiv ℝ f x))
    (hΦrank : ∀ z ∈ Ω, Function.Injective (fderiv ℝ Φ z))
    (hκ : ContinuousOn κ U) (hκΩ : MapsTo κ U Ω)
    (heq : ∀ x ∈ U, Φ (κ x) = f x) :
    ContDiffOn ℝ ∞ κ U ∧ ∀ x ∈ U, Function.Bijective (fderiv ℝ κ x) := by
  have hs (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ κ x := by
    have hcκ : ContinuousAt κ x := hκ.continuousAt (hU.mem_nhds hx)
    have hΦat := hΦ.contDiffAt (hΩ.mem_nhds (hκΩ hx))
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
    have hinv : ContDiffAt ℝ ∞ e.symm (L (f x)) := by
      rw [← heq x hx]
      exact hLat.to_localInverse hLD (by simp)
    exact (hinv.comp x (L.contDiff.contDiffAt.comp x
      (hf.contDiffAt (hU.mem_nhds hx)))).congr_of_eventuallyEq hreverse
  refine ⟨fun x hx => (hs x hx).contDiffWithinAt, ?_⟩
  intro x hx
  have he : Φ ∘ κ =ᶠ[𝓝 x] f := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact heq y hy
  have hd : (fderiv ℝ Φ (κ x)).comp (fderiv ℝ κ x) = fderiv ℝ f x := by
    rw [← fderiv_comp x ((hΦ.contDiffAt (hΩ.mem_nhds (hκΩ hx))).differentiableAt (by simp))
      ((hs x hx).differentiableAt (by simp)), he.fderiv_eq]
  have hi : Function.Injective (fderiv ℝ κ x) := by
    apply Function.Injective.of_comp (f := fderiv ℝ Φ (κ x))
    change Function.Injective ((fderiv ℝ Φ (κ x)).comp (fderiv ℝ κ x))
    rw [hd]
    exact hfrank x hx
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- Minimality transfers through a merely continuous same-image lift;
all differential properties of that lift are derived from regularity. -/
theorem coordinate_minimality_of_continuous_image_lift
    (V : Set E3) (hV : IsOpen V) (g : CoordinateMetric V)
    (U Ω : Set E2) (hU : IsOpen U) (hΩ : IsOpen Ω)
    (f Φ : E2 → E3) (κ : E2 → E2)
    (hf : ContDiffOn ℝ ∞ f U)
    (hminimal : IsMinimalParametrizationOn g.tensor Φ Ω)
    (hΦimage : MapsTo Φ Ω V)
    (hfrank : ∀ x ∈ U, Function.Injective (fderiv ℝ f x))
    (hΦrank : ∀ z ∈ Ω, Function.Injective (fderiv ℝ Φ z))
    (hκ : ContinuousOn κ U) (hκΩ : MapsTo κ U Ω)
    (heq : ∀ x ∈ U, Φ (κ x) = f x) :
    IsMinimalParametrizationOn g.tensor f U := by
  obtain ⟨hs, hr⟩ := smooth_regular_image_coordinate_lift f Φ κ U Ω hU hΩ hf
    hminimal.1 hfrank hΦrank hκ hκΩ heq
  exact coordinate_minimality_congr g.tensor (Φ ∘ κ) f U hU
    (coordinate_minimality_reparametrization V hV g Ω U hΩ hU Φ hminimal hΦimage
      hΦrank κ hs hκΩ hr) (fun x hx => (heq x hx).symm)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
