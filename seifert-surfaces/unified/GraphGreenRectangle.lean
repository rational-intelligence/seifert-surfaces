import GraphGreenFlux

set_option autoImplicit false
open Set MeasureTheory
open scoped ContDiff

namespace SeifertSurfaces.GraphGreenTransport
noncomputable section

def weightedDivergence (L U : ℝ → ℝ) (f g : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  (U z.2 - L z.2) *
    (fderiv ℝ f (transport L U z) (1, 0) + fderiv ℝ g (transport L U z) (0, 1))

def withinFlux (a b : ℝ) (H : ℝ → ℝ) (f g : ℝ × ℝ → ℝ) (y : ℝ) : ℝ :=
  f (H y, y) - derivWithin H (Icc a b) y * g (H y, y)

theorem rectangle_ae (a b : ℝ) :
    Ioo (0 : ℝ) 1 ×ˢ Ioo a b =ᵐ[volume] Icc (0 : ℝ) 1 ×ˢ Icc a b :=
  Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc

theorem cont_weightedDivergence {a b : ℝ} {L U : ℝ → ℝ}
    (hL : ContDiffOn ℝ 2 L (Icc a b)) (hU : ContDiffOn ℝ 2 U (Icc a b))
    {f g : ℝ × ℝ → ℝ} {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hm : MapsTo (transport L U) (Icc (0 : ℝ) 1 ×ˢ Icc a b) Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω) :
    ContinuousOn (weightedDivergence L U f g) (Icc (0 : ℝ) 1 ×ˢ Icc a b) := by
  have hT := (contDiffOn_transport hL hU).continuousOn
  have hF := (hf.continuousOn_fderiv_of_isOpen hΩ (by simp)).comp hT hm
  have hG := (hg.continuousOn_fderiv_of_isOpen hΩ (by simp)).comp hT hm
  have hs : MapsTo (fun z : ℝ × ℝ => z.2) (Icc (0 : ℝ) 1 ×ˢ Icc a b) (Icc a b) :=
    fun _ hz => hz.2
  exact ((hU.continuousOn.sub hL.continuousOn).comp continuousOn_snd hs).mul
    ((hF.clm_apply continuousOn_const).add (hG.clm_apply continuousOn_const))

theorem rectangle_green {a b : ℝ} (hab : a < b) {L U : ℝ → ℝ}
    (hL : ContDiffOn ℝ 2 L (Icc a b)) (hU : ContDiffOn ℝ 2 U (Icc a b))
    (ha : L a = U a) (hb : L b = U b)
    {f g : ℝ × ℝ → ℝ} {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hm : MapsTo (transport L U) (Icc (0 : ℝ) 1 ×ˢ Icc a b) Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω) :
    IntegrableOn (weightedDivergence L U f g) (Icc (0 : ℝ) 1 ×ˢ Icc a b) ∧
      IntegrableOn (withinFlux a b U f g) (Icc a b) ∧
      IntegrableOn (withinFlux a b L f g) (Icc a b) ∧
      (∫ z in Icc (0 : ℝ) 1 ×ˢ Icc a b, weightedDivergence L U f g z) =
        ∫ y in Icc a b, withinFlux a b U f g y - withinFlux a b L f g y := by
  let Q := Icc (0 : ℝ) 1 ×ˢ Icc a b
  let Qo := Ioo (0 : ℝ) 1 ×ˢ Ioo a b
  have hsub : Qo ⊆ Q := Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hCd := contDiffOn_pulls hab hL hU hm hf hg
  have hAf (z : ℝ × ℝ) (hz : z ∈ Qo) : DifferentiableAt ℝ (pullF a b L U f g) z :=
    (hCd.1.differentiableOn (by norm_num) z (hsub hz)).differentiableAt
      (prod_mem_nhds (Icc_mem_nhds hz.1.1 hz.1.2) (Icc_mem_nhds hz.2.1 hz.2.2))
  have hBf (z : ℝ × ℝ) (hz : z ∈ Qo) : DifferentiableAt ℝ (pullG L U g) z :=
    (hCd.2.differentiableOn (by norm_num) z (hsub hz)).differentiableAt
      (prod_mem_nhds (Icc_mem_nhds hz.1.1 hz.1.2) (Icc_mem_nhds hz.2.1 hz.2.2))
  have hEq (z : ℝ × ℝ) (hz : z ∈ Qo) :
      fderiv ℝ (pullF a b L U f g) z (1, 0) + fderiv ℝ (pullG L U g) z (0, 1) =
        weightedDivergence L U f g z := by
    exact pull_divergence hL hU hz.2
      ((hf.differentiableOn (by simp) _ (hm (hsub hz))).differentiableAt (hΩ.mem_nhds (hm (hsub hz))))
      ((hg.differentiableOn (by simp) _ (hm (hsub hz))).differentiableAt (hΩ.mem_nhds (hm (hsub hz))))
      (hAf z hz) (hBf z hz)
  have hAE : ∀ᵐ z ∂volume.restrict Q, z ∈ Qo := by
    have hh := ae_restrict_mem (μ := (volume : Measure (ℝ × ℝ)))
      (measurableSet_Ioo.prod measurableSet_Ioo : MeasurableSet Qo)
    rwa [Measure.restrict_congr_set (rectangle_ae a b)] at hh
  have heqAE : (fun z => fderiv ℝ (pullF a b L U f g) z (1, 0) +
      fderiv ℝ (pullG L U g) z (0, 1)) =ᵐ[volume.restrict Q]
      weightedDivergence L U f g := by
    filter_upwards [hAE] with z hz using hEq z hz
  have hInt : IntegrableOn (weightedDivergence L U f g) Q volume :=
    (cont_weightedDivergence hL hU hΩ hm hf hg).integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)
  have hId : IntegrableOn (fun z => fderiv ℝ (pullF a b L U f g) z (1, 0) +
      fderiv ℝ (pullG L U g) z (0, 1)) Q := hInt.congr_fun_ae heqAE.symm
  have hh := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (pullF a b L U f g) (pullG L U g)
    (fderiv ℝ (pullF a b L U f g)) (fderiv ℝ (pullG L U g))
    (0, a) (1, b) ⟨by norm_num, hab.le⟩
    (by simpa only [← Icc_prod_Icc] using hCd.1.continuousOn)
    (by simpa only [← Icc_prod_Icc] using hCd.2.continuousOn)
    (fun z hz => (hAf z hz).hasFDerivAt) (fun z hz => (hBf z hz).hasFDerivAt)
    (by simpa only [← Icc_prod_Icc] using hId)
  have hOne : ContinuousOn (fun y => pullF a b L U f g (1, y)) (Icc a b) :=
    hCd.1.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun _ hy => ⟨⟨by norm_num, le_rfl⟩, hy⟩)
  have hZero : ContinuousOn (fun y => pullF a b L U f g (0, y)) (Icc a b) :=
    hCd.1.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun _ hy => ⟨⟨le_rfl, by norm_num⟩, hy⟩)
  have hUflux : (fun y => pullF a b L U f g (1, y)) = withinFlux a b U f g := by
    funext y; simp [pullF, transport, slope, withinFlux]
  have hLflux : (fun y => pullF a b L U f g (0, y)) = withinFlux a b L f g := by
    funext y; simp [pullF, transport, slope, withinFlux]
  have hUI : IntegrableOn (withinFlux a b U f g) (Icc a b) := by
    rw [← hUflux]; exact hOne.integrableOn_compact isCompact_Icc
  have hLI : IntegrableOn (withinFlux a b L f g) (Icc a b) := by
    rw [← hLflux]; exact hZero.integrableOn_compact isCompact_Icc
  refine ⟨hInt, hUI, hLI, ?_⟩
  rw [← Icc_prod_Icc] at hh
  rw [integral_congr_ae heqAE] at hh
  have hTop : (fun x => pullG L U g (x, b)) = 0 := by ext; simp [pullG, hb]
  have hBot : (fun x => pullG L U g (x, a)) = 0 := by ext; simp [pullG, ha]
  rw [hTop, hBot, hUflux, hLflux] at hh
  simp only [sub_self, zero_add] at hh
  rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le,
    setIntegral_congr_set (Ioc_ae_eq_Icc (μ := volume)),
    setIntegral_congr_set (Ioc_ae_eq_Icc (μ := volume))] at hh
  exact hh.trans (integral_sub hUI hLI).symm

end
end SeifertSurfaces.GraphGreenTransport
