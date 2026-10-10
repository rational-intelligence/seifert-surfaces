import NativeBoundaryEvenContinuous

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.QuasilinearProviderBridge

theorem native_gradient_normal_comp_on_lower
    (ρ : ℝ) (f : E2 → ℝ) (hf : ContDiffOn ℝ 1 f (openHalfDisc ρ))
    (x : E2) (hx : x ∈ Metric.ball 0 ρ) (hn : x 0 < 0) :
    planarGradient (fun y => f (normalReflection y)) x =
      normalReflection (planarGradient f (normalReflection x)) := by
  have hR : normalReflection x ∈ openHalfDisc ρ :=
    ⟨normalReflection_maps_ball ρ hx, by change 0 < normalReflection x 0; rw [normalReflection_zero]; linarith⟩
  have hd := (hf.contDiffAt ((openHalfDisc_isOpen ρ).mem_nhds hR)).differentiableAt (by norm_num)
  have hder := hd.hasFDerivAt.comp x normalReflection.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  have hD : fderiv ℝ (fun y => f (normalReflection y)) x =
      (fderiv ℝ f (normalReflection x)).comp normalReflection.toContinuousLinearEquiv.toContinuousLinearMap :=
    hder.fderiv
  ext i
  fin_cases i
  · change planarGradient (fun y => f (normalReflection y)) x 0 =
      normalReflection (planarGradient f (normalReflection x)) 0
    simp only [Helpers.gradient_apply, hD, ContinuousLinearMap.comp_apply]
    change fderiv ℝ f (normalReflection x) (normalReflection (coordinateVector 2 0)) = _
    rw [normalReflection_basis_zero, map_neg]
    rw [normalReflection_zero, Helpers.gradient_apply]
  · change planarGradient (fun y => f (normalReflection y)) x 1 =
      normalReflection (planarGradient f (normalReflection x)) 1
    simp only [Helpers.gradient_apply, hD, ContinuousLinearMap.comp_apply]
    change fderiv ℝ f (normalReflection x) (normalReflection (coordinateVector 2 1)) = _
    rw [normalReflection_basis_one, normalReflection_one, Helpers.gradient_apply]

/-- Weak derivatives of an actual Sobolev parity extension agree with its
ordinary reflected gradients away from the null flat plane. -/
theorem native_parity_weak_gradient_agrees
    (ρ ε : ℝ) (f F : E2 → ℝ)
    (hf : ContDiffOn ℝ 1 f (openHalfDisc ρ))
    (hw : DeGiorgi.MemW1pWitness 2 F (Metric.ball 0 ρ))
    (hupper : EqOn F f (openHalfDisc ρ))
    (hlower : EqOn F (fun x => ε * f (normalReflection x))
      (Metric.ball 0 ρ ∩ {x : E2 | x 0 < 0})) :
    hw.weakGrad =ᵐ[volume.restrict (Metric.ball 0 ρ)]
      (fun x => if 0 < x 0 then planarGradient f x
        else ε • normalReflection (planarGradient f (normalReflection x))) := by
  let U := openHalfDisc ρ
  let V := Metric.ball (0 : E2) ρ ∩ {x : E2 | x 0 < 0}
  have hU := openHalfDisc_isOpen ρ
  have hV : IsOpen V := Metric.isOpen_ball.inter
    (isOpen_lt (EuclideanSpace.proj (0 : Fin 2)).continuous continuous_const)
  have hUb : U ⊆ Metric.ball (0 : E2) ρ := fun x hx => hx.1
  have hVb : V ⊆ Metric.ball (0 : E2) ρ := fun x hx => hx.1
  have hFU : ContDiffOn ℝ 1 F U := hf.congr (fun x hx => hupper hx)
  have hmap : MapsTo normalReflection V U := by
    intro x hx
    refine ⟨normalReflection_maps_ball ρ hx.1, ?_⟩
    change 0 < normalReflection x 0
    rw [normalReflection_zero]
    have hn : x 0 < 0 := hx.2
    linarith
  have hFR : ContDiffOn ℝ 1 (fun x => ε * f (normalReflection x)) V := by
    have hRc : ContDiffOn ℝ 1 (fun y => f (normalReflection y)) V :=
      hf.comp normalReflection.toContinuousLinearEquiv.contDiff.contDiffOn hmap
    exact contDiffOn_const.mul hRc
  have hFV : ContDiffOn ℝ 1 F V := hFR.congr (fun x hx => hlower hx)
  have hEqU := R1_classical_weak_gradient_agrees U hU F hFU (hw.restrict hU hUb)
  have hEqV := R1_classical_weak_gradient_agrees V hV F hFV (hw.restrict hV hVb)
  have hgU : EqOn (planarGradient F) (planarGradient f) U := by
    intro x hx
    have he : F =ᶠ[𝓝 x] f := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hupper hy
    simp only [planarGradient, he.fderiv_eq]
  have hgV : EqOn (planarGradient F)
      (fun x => ε • normalReflection (planarGradient f (normalReflection x))) V := by
    intro x hx
    have he : F =ᶠ[𝓝 x] (fun y => ε * f (normalReflection y)) := by
      filter_upwards [hV.mem_nhds hx] with y hy
      exact hlower hy
    have hRc : ContDiffOn ℝ 1 (fun y => f (normalReflection y)) V :=
      hf.comp normalReflection.toContinuousLinearEquiv.contDiff.contDiffOn hmap
    have hRd := (hRc.contDiffAt (hV.mem_nhds hx)).differentiableAt (by norm_num)
    unfold planarGradient
    rw [he.fderiv_eq, fderiv_const_mul hRd]
    simp only [ContinuousLinearMap.smul_apply, smul_assoc, ← Finset.smul_sum]
    exact congrArg (fun y : E2 => ε • y)
      (native_gradient_normal_comp_on_lower ρ f hf x hx.1 hx.2)
  have hwholeU : ∀ᵐ x : E2 ∂volume, x ∈ U → hw.weakGrad x = planarGradient f x := by
    have he : hw.weakGrad =ᵐ[volume.restrict U] planarGradient f := by
      filter_upwards [hEqU, ae_restrict_mem hU.measurableSet] with x hx hxU
      exact hx.trans (hgU hxU)
    exact (ae_restrict_iff' hU.measurableSet).mp he
  have hwholeV : ∀ᵐ x : E2 ∂volume, x ∈ V →
      hw.weakGrad x = ε • normalReflection (planarGradient f (normalReflection x)) := by
    have he : hw.weakGrad =ᵐ[volume.restrict V]
        (fun x => ε • normalReflection (planarGradient f (normalReflection x))) := by
      filter_upwards [hEqV, ae_restrict_mem hV.measurableSet] with x hx hxV
      exact hx.trans (hgV hxV)
    exact (ae_restrict_iff' hV.measurableSet).mp he
  have hflat : ∀ᵐ x : E2 ∂volume, x 0 ≠ 0 := by
    simpa only [ae_iff, not_not] using native_flat_plane_null
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet,
    ae_restrict_of_ae hwholeU, ae_restrict_of_ae hwholeV, ae_restrict_of_ae hflat] with x hx hxu hxv hn
  by_cases hp : 0 < x 0
  · rw [if_pos hp]
    exact hxu ⟨hx, hp⟩
  · rw [if_neg hp]
    exact hxv ⟨hx, lt_of_le_of_ne (not_lt.mp hp) hn⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
