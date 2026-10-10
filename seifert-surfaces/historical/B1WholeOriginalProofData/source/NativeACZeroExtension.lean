import NativeBallH1Extension
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem ac_zero_extension_primitive (a b A D : ℝ) (hab : a < b)
    (hAa : A ≤ a) (hbD : b ≤ D) (f : ℝ → ℝ)
    (hf : AbsolutelyContinuousOnInterval f a b) (hfa : f a = 0) (hfb : f b = 0) :
    ∀ t ∈ Icc A D,
      (∫ u in A..t, (Icc a b).indicator (deriv f) u) = (Icc a b).indicator f t := by
  intro t ht
  rw [intervalIntegral.integral_of_le ht.1,
    setIntegral_congr_set Ioc_ae_eq_Icc, setIntegral_indicator measurableSet_Icc]
  by_cases hat : a ≤ t
  · by_cases htb : t ≤ b
    · have hi : Icc A t ∩ Icc a b = Icc a t := by
        ext u
        constructor
        · intro h; exact ⟨h.2.1, h.1.2⟩
        · intro h; exact ⟨⟨hAa.trans h.1, h.2⟩, ⟨h.1, h.2.trans htb⟩⟩
      rw [hi, indicator_of_mem (show t ∈ Icc a b from ⟨hat, htb⟩)]
      have hac := hf.mono (show uIcc a t ⊆ uIcc a b by
        rw [uIcc_of_le hat, uIcc_of_le hab.le]
        exact Icc_subset_Icc le_rfl htb)
      have he := hac.integral_deriv_eq_sub
      rw [hfa, sub_zero, intervalIntegral.integral_of_le hat,
        setIntegral_congr_set Ioc_ae_eq_Icc] at he
      exact he
    · have hi : Icc A t ∩ Icc a b = Icc a b := by
        exact inter_eq_right.mpr (Icc_subset_Icc hAa (le_of_not_ge htb))
      rw [hi, indicator_of_notMem (by simpa only [mem_Icc, not_and] using fun _ => htb)]
      have he := hf.integral_deriv_eq_sub
      simpa only [hfa, hfb, sub_self, intervalIntegral.integral_of_le hab.le,
        setIntegral_congr_set Ioc_ae_eq_Icc] using he
  · have hi : Icc A t ∩ Icc a b = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact hat (hu.2.1.trans hu.1.2)
    rw [hi, setIntegral_empty, indicator_of_notMem (by intro h; exact hat h.1)]

theorem ac_zero_extension (a b A D : ℝ) (hab : a < b)
    (hAa : A ≤ a) (hbD : b ≤ D) (f : ℝ → ℝ)
    (hf : AbsolutelyContinuousOnInterval f a b) (hfa : f a = 0) (hfb : f b = 0) :
    AbsolutelyContinuousOnInterval ((Icc a b).indicator f) A D := by
  have hAD : A ≤ D := hAa.trans (hab.le.trans hbD)
  have hfd : IntegrableOn (deriv f) (Icc a b) :=
    hf.intervalIntegrable_deriv.1.congr_set_ae Ioc_ae_eq_Icc.symm
  have hi : Integrable ((Icc a b).indicator (deriv f)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hfd
  apply (hi.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    (show A ∈ uIcc A D by simp [uIcc_of_le hAD, hAD])).congr
  intro t ht
  exact ac_zero_extension_primitive a b A D hab hAa hbD f hf hfa hfb t
    (by simpa [uIcc_of_le hAD] using ht)

theorem periodic_zero_extension (a b : ℝ) (ha : -Real.pi < a) (hab : a < b)
    (hb : b < Real.pi) (f : ℝ → ℝ)
    (hf : AbsolutelyContinuousOnInterval f a b) (hfa : f a = 0) (hfb : f b = 0)
    (hfd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) :
    ∃ g : ℝ → ℝ,
      Continuous g ∧ Periodic g (2 * Real.pi) ∧
      AbsolutelyContinuousOnInterval g (-Real.pi) Real.pi ∧
      MemLp (deriv g) 2 (volume.restrict (Icc (-Real.pi) Real.pi)) ∧
      (∀ t ∈ Icc (-Real.pi) Real.pi, g t = (Icc a b).indicator f t) ∧
      (deriv g =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
        (Icc a b).indicator (deriv f)) ∧
      (∫ t in Icc (-Real.pi) Real.pi, g t ^ 2) = ∫ t in Icc a b, f t ^ 2 ∧
      (∫ t in Icc (-Real.pi) Real.pi, deriv g t ^ 2) =
        ∫ t in Icc a b, deriv f t ^ 2 := by
  classical
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let u : ℝ → ℝ := (Icc a b).indicator f
  let v : ℝ → ℝ := (Icc a b).indicator (deriv f)
  let g : ℝ → ℝ := fun t => AddCircle.liftIco (2 * Real.pi) (-Real.pi) u
    (t : AddCircle (2 * Real.pi))
  have hup : u (-Real.pi) = u Real.pi := by
    simp only [u, indicator_of_notMem (show -Real.pi ∉ Icc a b by intro h; linarith [h.1]),
      indicator_of_notMem (show Real.pi ∉ Icc a b by intro h; linarith [h.2])]
  have huAC := ac_zero_extension a b (-Real.pi) Real.pi hab ha.le hb.le f hf hfa hfb
  have hug : ∀ t ∈ Icc (-Real.pi) Real.pi, g t = u t := by
    intro t ht
    by_cases htp : t = Real.pi
    · subst t
      have hc : (Real.pi : AddCircle (2 * Real.pi)) = (-Real.pi : ℝ) := by
        calc
          _ = ((-Real.pi + 2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) := by congr 1; ring
          _ = _ := AddCircle.coe_add_period _ _
      dsimp [g]
      rw [hc, AddCircle.liftIco_coe_apply (by constructor <;> linarith [Real.pi_pos])]
      exact hup
    · exact AddCircle.liftIco_coe_apply (by constructor <;> linarith [ht.1, lt_of_le_of_ne ht.2 htp])
  have hgc : Continuous g := by
    have heq : u (-Real.pi) = u (-Real.pi + 2 * Real.pi) := by
      convert hup using 1 <;> congr 1 <;> ring
    have huc : ContinuousOn u (Icc (-Real.pi) (-Real.pi + 2 * Real.pi)) := by
      simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring,
        uIcc_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos])] using huAC.continuousOn
    exact (AddCircle.liftIco_continuous heq huc).comp (AddCircle.continuous_mk' (2 * Real.pi))
  have hgp : Periodic g (2 * Real.pi) := by
    intro t
    dsimp [g]
    simp only [AddCircle.coe_period, add_zero]
  have hga : AbsolutelyContinuousOnInterval g (-Real.pi) Real.pi := by
    apply huAC.congr
    intro t ht
    exact (hug t (by simpa only [uIcc_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos])] using ht)).symm
  have hvi : Integrable v := (integrable_indicator_iff measurableSet_Icc).mpr
    (hf.intervalIntegrable_deriv.1.congr_set_ae Ioc_ae_eq_Icc.symm)
  have hiv : ∀ᵐ t ∂volume.restrict (Icc (-Real.pi) Real.pi),
      t ∈ Ioo (-Real.pi) Real.pi := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hderiv_integral := _root_.LocallyIntegrable.ae_hasDerivAt_integral hvi.locallyIntegrable
  have hgd : deriv g =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)] v := by
    filter_upwards [ae_restrict_of_ae hderiv_integral, hiv] with t hd ht
    have he : g =ᶠ[𝓝 t] (fun t => ∫ u in (-Real.pi)..t, v u) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with z hz
      rw [hug z (Ioo_subset_Icc_self hz)]
      exact (ac_zero_extension_primitive a b (-Real.pi) Real.pi hab ha.le hb.le f hf hfa hfb z
        (Ioo_subset_Icc_self hz)).symm
    exact he.deriv_eq.trans (hd (-Real.pi)).deriv
  have hvLp : MemLp v 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).mpr hfd
  have hge : MemLp (deriv g) 2 (volume.restrict (Icc (-Real.pi) Real.pi)) :=
    (hvLp.restrict _).ae_eq hgd.symm
  refine ⟨g, hgc, hgp, hga, hge, hug, hgd, ?_, ?_⟩
  · calc
      _ = ∫ t in Icc (-Real.pi) Real.pi, (Icc a b).indicator (fun t => f t ^ 2) t := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        change g t ^ 2 = _
        rw [hug t ht]
        by_cases ht' : t ∈ Icc a b <;> simp [u, ht']
      _ = _ := by
        rw [setIntegral_indicator measurableSet_Icc,
          inter_eq_right.mpr (Icc_subset_Icc ha.le hb.le)]
  · calc
      _ = ∫ t in Icc (-Real.pi) Real.pi, (Icc a b).indicator (fun t => deriv f t ^ 2) t := by
        apply integral_congr_ae
        filter_upwards [hgd] with t ht
        rw [ht]
        by_cases ht' : t ∈ Icc a b <;> simp [v, ht']
      _ = _ := by
        rw [setIntegral_indicator measurableSet_Icc,
          inter_eq_right.mpr (Icc_subset_Icc ha.le hb.le)]

theorem deriv_zero_of_zero_interval (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ∀ t ∈ Icc a b, f t = 0) (t : ℝ) (ht : t ∈ Icc a b) : deriv f t = 0 := by
  by_cases hd : DifferentiableAt ℝ f t
  · have hz : HasDerivWithinAt f 0 (Icc a b) t := by
      apply (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt.congr
      · intro y hy
        exact hf y hy
      · exact hf t ht
    have hu := uniqueDiffOn_Icc hab t ht
    exact (hd.hasDerivAt.hasDerivWithinAt.derivWithin hu).symm.trans (hz.derivWithin hu)
  · exact deriv_zero_of_not_differentiableAt hd

theorem zero_extension_deriv_off (a b : ℝ) (ha : -Real.pi < a) (hab : a < b)
    (hb : b < Real.pi) (f g : ℝ → ℝ) (hfa : f a = 0) (hfb : f b = 0)
    (hgf : ∀ t ∈ Icc (-Real.pi) Real.pi, g t = (Icc a b).indicator f t)
    (t : ℝ) (ht : t ∈ Icc (-Real.pi) Real.pi) (htab : t ∉ Icc a b) :
    g t = 0 ∧ deriv g t = 0 := by
  refine ⟨by rw [hgf t ht, indicator_of_notMem htab], ?_⟩
  by_cases hat : t < a
  · apply deriv_zero_of_zero_interval g t a hat _ t ⟨le_rfl, hat.le⟩
    intro z hz
    rw [hgf z ⟨ht.1.trans hz.1, hz.2.trans (hab.le.trans hb.le)⟩]
    by_cases hza : z = a
    · simp [hza, hfa]
    · exact indicator_of_notMem (by intro h; exact hza (le_antisymm hz.2 h.1)) _
  · have hbt : b < t := by
      by_contra hn
      exact htab ⟨le_of_not_gt hat, le_of_not_gt hn⟩
    apply deriv_zero_of_zero_interval g b t hbt _ t ⟨hbt.le, le_rfl⟩
    intro z hz
    rw [hgf z ⟨ha.le.trans (hab.le.trans hz.1), hz.2.trans ht.2⟩]
    by_cases hzb : z = b
    · simp [hzb, hfb]
    · exact indicator_of_notMem (by intro h; exact hzb (le_antisymm h.2 hz.1)) _

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
