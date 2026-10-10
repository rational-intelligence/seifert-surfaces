import NativeBoundaryFluxReflection

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal
namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

def nativeEvenReflectedFlux (ρ : ℝ) (F : E2 → E2) (x : E2) : E2 :=
  (openHalfDisc ρ).indicator F x + normalReflection ((openHalfDisc ρ).indicator F (normalReflection x))

def nativeEvenReflectedSource (ρ : ℝ) (S : E2 → ℝ) (x : E2) : ℝ :=
  (openHalfDisc ρ).indicator S x + (openHalfDisc ρ).indicator S (normalReflection x)

/-- Even reflection of an actual native Neumann weak identity.
Smooth tests may reach the flat edge; all flux and source fields are L2. -/
theorem native_even_flux_source_reflected_weak_identity
    (ρ : ℝ) (F : E2 → E2) (S : E2 → ℝ)
    (hF : MemLp F 2 (volume.restrict (openHalfDisc ρ)))
    (hS : MemLp S 2 (volume.restrict (openHalfDisc ρ)))
    (hweak : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball 0 ρ →
        (∫ x in openHalfDisc ρ, inner ℝ (F x) (planarGradient φ x) - S x * φ x) = 0) :
    MemLp (nativeEvenReflectedFlux ρ F) 2 volume ∧
      MemLp (nativeEvenReflectedSource ρ S) 2 volume ∧
      ∀ ψ : E2 → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball 0 ρ →
          Integrable (fun x => inner ℝ (nativeEvenReflectedFlux ρ F x) (planarGradient ψ x)) ∧
          Integrable (fun x => nativeEvenReflectedSource ρ S x * ψ x) ∧
          (∫ x, inner ℝ (nativeEvenReflectedFlux ρ F x) (planarGradient ψ x) -
            nativeEvenReflectedSource ρ S x * ψ x) = 0 := by
  classical
  let U := openHalfDisc ρ
  let D : E2 → E2 := U.indicator F
  let E : E2 → ℝ := U.indicator S
  have hUm : MeasurableSet U := (openHalfDisc_isOpen ρ).measurableSet
  have hD : MemLp D 2 volume := (memLp_indicator_iff_restrict hUm.nullMeasurableSet).mpr hF
  have hE : MemLp E 2 volume := (memLp_indicator_iff_restrict hUm.nullMeasurableSet).mpr hS
  have hmp : MeasurePreserving normalReflection volume volume := normalReflection.measurePreserving
  have hemb := normalReflection.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hRD : MemLp (fun x => normalReflection (D (normalReflection x))) 2 volume :=
    (hD.comp_measurePreserving hmp).continuousLinearMap_comp
      normalReflection.toContinuousLinearEquiv.toContinuousLinearMap
  have hRE : MemLp (fun x => E (normalReflection x)) 2 volume := hE.comp_measurePreserving hmp
  refine ⟨hD.add hRD, hE.add hRE, ?_⟩
  intro ψ hψ hc ht
  let ψR : E2 → ℝ := fun x => ψ (normalReflection x)
  have hψR : ContDiff ℝ ∞ ψR := hψ.comp normalReflection.toContinuousLinearEquiv.contDiff
  have hcR : HasCompactSupport ψR := hc.comp_homeomorph
    normalReflection.toContinuousLinearEquiv.toHomeomorph
  have htR : tsupport ψR ⊆ Metric.ball 0 ρ := by
    rw [show ψR = ψ ∘ normalReflection.toContinuousLinearEquiv.toHomeomorph from rfl,
      tsupport_comp_eq_preimage]
    intro x hx
    have hh := ht hx
    change normalReflection x ∈ Metric.ball 0 ρ at hh
    simpa only [Metric.mem_ball, dist_zero_right, normalReflection.norm_map] using hh
  let φ : E2 → ℝ := ψ + ψR
  have hφ : ContDiff ℝ ∞ φ := hψ.add hψR
  have hcφ : HasCompactSupport φ := hc.add hcR
  have htφ : tsupport φ ⊆ Metric.ball 0 ρ := (tsupport_add _ _).trans (union_subset ht htR)
  have hφgrad (x : E2) : planarGradient φ x =
      planarGradient ψ x + normalReflection (planarGradient ψ (normalReflection x)) := by
    unfold φ planarGradient
    rw [fderiv_add (hψ.differentiable (by simp) x) (hψR.differentiable (by simp) x)]
    simp only [add_apply, add_smul, Finset.sum_add_distrib]
    exact congrArg (fun G => planarGradient ψ x + G) (normalReflection_gradient ψ hψ x)
  have hgc : HasCompactSupport (planarGradient ψ) := by
    apply hc.mono'
    intro x hx
    by_contra hn
    exact hx (Helpers.gradient_zero_off_tsupport ψ hn)
  have hg : MemLp (planarGradient ψ) 2 volume :=
    (Helpers.gradient_continuous ψ hψ).memLp_of_hasCompactSupport hgc
  have hψLp : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hc
  have hgR : MemLp (fun x => normalReflection (planarGradient ψ (normalReflection x))) 2 volume :=
    (hg.comp_measurePreserving hmp).continuousLinearMap_comp
      normalReflection.toContinuousLinearEquiv.toContinuousLinearMap
  have hψRLp : MemLp ψR 2 volume := hψLp.comp_measurePreserving hmp
  have pair (f g : E2 → E2) (hf : MemLp f 2 volume) (hg' : MemLp g 2 volume) :
      Integrable (fun x => inner ℝ (f x) (g x)) := by
    have hi (i : Fin 2) := (hf.eval_piLp i).integrable_mul (hg'.eval_piLp i)
    convert (hi 0).add (hi 1) using 1
    funext x
    simp [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, mul_comm]
  have hiD := pair _ _ hD hg
  have hiRD := pair _ _ hRD hg
  have hiDR := pair _ _ hD hgR
  have hiE : Integrable (fun x => E x * ψ x) := hE.integrable_mul hψLp
  have hiRE : Integrable (fun x => E (normalReflection x) * ψ x) := hRE.integrable_mul hψLp
  have hiER : Integrable (fun x => E x * ψR x) := hE.integrable_mul hψRLp
  have hrefF : (∫ x, inner ℝ (normalReflection (D (normalReflection x))) (planarGradient ψ x)) =
      ∫ x, inner ℝ (D x) (normalReflection (planarGradient ψ (normalReflection x))) := by
    have heq (x : E2) : inner ℝ (normalReflection (D (normalReflection (normalReflection x))))
        (planarGradient ψ (normalReflection x)) =
        inner ℝ (D x) (normalReflection (planarGradient ψ (normalReflection x))) := by
      rw [normalReflection_involutive, ← normalReflection_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
      rfl
    exact (hmp.integral_comp hemb _).symm.trans (integral_congr_ae (.of_forall heq))
  have hrefS : (∫ x, E (normalReflection x) * ψ x) = ∫ x, E x * ψR x := by
    have heq (x : E2) : E (normalReflection (normalReflection x)) * ψ (normalReflection x) =
        E x * ψR x := by rw [normalReflection_involutive]
    exact (hmp.integral_comp hemb _).symm.trans (integral_congr_ae (.of_forall heq))
  have hfluxInt : Integrable (fun x => inner ℝ (nativeEvenReflectedFlux ρ F x) (planarGradient ψ x)) := by
    unfold nativeEvenReflectedFlux
    simp_rw [inner_add_left]
    convert hiD.add hiRD using 1
  have hsourceInt : Integrable (fun x => nativeEvenReflectedSource ρ S x * ψ x) := by
    unfold nativeEvenReflectedSource
    simp_rw [add_mul]
    convert hiE.add hiRE using 1
  refine ⟨hfluxInt, hsourceInt, ?_⟩
  rw [integral_sub hfluxInt hsourceInt]
  simp only [nativeEvenReflectedFlux, nativeEvenReflectedSource, inner_add_left, add_mul]
  change (∫ x, inner ℝ (D x) (planarGradient ψ x) +
    inner ℝ (normalReflection (D (normalReflection x))) (planarGradient ψ x)) -
      (∫ x, E x * ψ x + E (normalReflection x) * ψ x) = 0
  rw [integral_add hiD hiRD, integral_add hiE hiRE, hrefF, hrefS]
  have hgφ : MemLp (planarGradient φ) 2 volume :=
    (Helpers.gradient_continuous φ hφ).memLp_of_hasCompactSupport (by
      apply hcφ.mono'
      intro x hx
      by_contra hn
      exact hx (Helpers.gradient_zero_off_tsupport φ hn))
  have hφLp : MemLp φ 2 volume := by
    simpa only [φ, Pi.add_apply] using hψLp.add hψRLp
  have hiφD : Integrable (fun x => inner ℝ (D x) (planarGradient φ x)) :=
    pair D (planarGradient φ) hD hgφ
  have hiφE : Integrable (fun x => E x * φ x) := hE.integrable_mul hφLp
  have hzero : (∫ x, inner ℝ (D x) (planarGradient φ x) - E x * φ x) = 0 := by
    have hind (x : E2) : inner ℝ (D x) (planarGradient φ x) - E x * φ x =
        U.indicator (fun y => inner ℝ (F y) (planarGradient φ y) - S y * φ y) x := by
      by_cases hx : x ∈ U <;> simp [D, E, hx]
    simp_rw [hind]
    rw [integral_indicator hUm]
    exact hweak φ hφ hcφ htφ
  rw [integral_sub hiφD hiφE] at hzero
  rw [← hzero]
  simp only [hφgrad, inner_add_right, φ, Pi.add_apply, mul_add]
  rw [integral_add hiD hiDR, integral_add hiE hiER]

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
