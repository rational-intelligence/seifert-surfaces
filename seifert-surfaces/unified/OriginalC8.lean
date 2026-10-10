import OriginalC7
import C9Compatibility
import Mathlib.Analysis.Complex.Convex

noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace SeifertSurfaces.AppendixC.Original

universe u
variable (X : Type u) [TopologicalSpace X] [ChartedSpace Plane X]
  [IsManifold (𝓡 2) ∞ X]

/-- Holomorphic and real-analytic chart and inverse in the SAME given
Riemann-surface atlas; the atlas carries the analytic structure of X. -/
structure HolomorphicChartIn (a : ComplexConformalAtlas (𝓡 2) X)
    (u : OpenPartialHomeomorph X ℂ) : Prop where
  smooth : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ u u.source
  smooth_inverse : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ u.symm u.target
  holomorphic : ∀ q, DifferentiableOn ℂ (u ∘ (a.chart q).symm)
    ((a.chart q).target ∩ (a.chart q).symm ⁻¹' u.source)
  inverse_holomorphic : ∀ q, DifferentiableOn ℂ ((a.chart q) ∘ u.symm)
    (u.target ∩ u.symm ⁻¹' (a.chart q).source)
  analytic : ∀ q, AnalyticOnNhd ℝ (u ∘ (a.chart q).symm)
    ((a.chart q).target ∩ (a.chart q).symm ⁻¹' u.source)
  inverse_analytic : ∀ q, AnalyticOnNhd ℝ ((a.chart q) ∘ u.symm)
    (u.target ∩ u.symm ⁻¹' (a.chart q).source)

/-- A normal-form chart at a fixed point. Its fixed-set image is an open
real interval, which is the local dimension-one analytic submanifold
condition. Its complement has exactly the two connected open half-disks. -/
structure DiskReflectionChart (a : ComplexConformalAtlas (𝓡 2) X)
    (ι : X → X) (p : X) where
  chart : OpenPartialHomeomorph X ℂ
  radius : ℝ
  positive_radius : 0 < radius
  mem_source : p ∈ chart.source
  centered : chart p = 0
  disk_target : chart.target = Metric.ball 0 radius
  holomorphic_chart : HolomorphicChartIn X a chart
  invariant : ι '' chart.source = chart.source
  reflection : ∀ q ∈ chart.source, chart (ι q) = star (chart q)
  fixed_iff : ∀ q ∈ chart.source, ι q = q ↔ (chart q).im = 0
  fixed_interval : chart '' {q ∈ chart.source | ι q = q} =
    Complex.ofReal '' Set.Ioo (-radius) radius
  complement : chart.source \ {q | ι q = q} =
    {q ∈ chart.source | 0 < (chart q).im} ∪
    {q ∈ chart.source | (chart q).im < 0}
  upper_connected : IsConnected {q ∈ chart.source | 0 < (chart q).im}
  lower_connected : IsConnected {q ∈ chart.source | (chart q).im < 0}
  upper_image : chart '' {q ∈ chart.source | 0 < (chart q).im} =
    {z ∈ Metric.ball 0 radius | 0 < z.im}
  lower_image : chart '' {q ∈ chart.source | (chart q).im < 0} =
    {z ∈ Metric.ball 0 radius | z.im < 0}
  exchange_upper : ι '' {q ∈ chart.source | 0 < (chart q).im} =
    {q ∈ chart.source | (chart q).im < 0}
  exchange_lower : ι '' {q ∈ chart.source | (chart q).im < 0} =
    {q ∈ chart.source | 0 < (chart q).im}

/-- The residual interface restricts already-proved same-atlas reflection
charts to disks. No new antiholomorphic normal-form argument is requested. -/
theorem reflection_charts_disk_interface
    (a : ComplexConformalAtlas (𝓡 2) X) (ι : X ≃ₜ X)
    (hinvolution : Function.Involutive ι)
    (r : ReflectionCharts (𝓡 2) X a ι)
    (p : X) (hp : ι p = p) :
    Nonempty (DiskReflectionChart X a ι p) := by
  classical
  let e := r.chart p hp
  have hep : p ∈ e.source := r.fixed_mem p hp
  have he0 : e p = 0 := r.centered p hp
  have ht0 : (0 : ℂ) ∈ e.target := he0 ▸ e.map_source hep
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp e.open_target 0 ht0
  let d := e.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0 : ℂ) R) Metric.isOpen_ball)
  have ds : d.source = e.source ∩ e ⁻¹' Metric.ball 0 R := rfl
  have dt : d.target = Metric.ball 0 R := by
    ext z
    change (z ∈ Metric.ball 0 R ∧ z ∈ e.target) ↔ z ∈ Metric.ball 0 R
    exact ⟨And.left, fun hz => ⟨hz, hball hz⟩⟩
  have dv (q : X) : d q = e q := rfl
  have di (z : ℂ) : d.symm z = e.symm z := rfl
  have hsub : d.source ⊆ e.source := by rw [ds]; exact Set.inter_subset_left
  have drefl (q : X) (hq : q ∈ d.source) : d (ι q) = star (d q) :=
    r.reflection p hp q (hsub hq)
  have stable : Set.MapsTo ι d.source d.source := by
    intro q hq
    rw [ds] at hq ⊢
    refine ⟨?_, ?_⟩
    · rw [← r.invariant p hp]
      exact ⟨q, hq.1, rfl⟩
    · change e (ι q) ∈ Metric.ball 0 R
      rw [r.reflection p hp q hq.1]
      simpa only [Metric.mem_ball, dist_zero_right, norm_star, Set.mem_preimage] using hq.2
  have fix (q : X) (hq : q ∈ d.source) : ι q = q ↔ (d q).im = 0 :=
    r.fixed_curve p hp q (hsub hq)
  have upper_image : d '' {q ∈ d.source | 0 < (d q).im} =
      {z ∈ Metric.ball 0 R | 0 < z.im} := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨dt ▸ d.map_source hq.1, hq.2⟩
    · intro hz
      refine ⟨d.symm z, ⟨d.map_target (dt.symm ▸ hz.1), ?_⟩, d.right_inv (dt.symm ▸ hz.1)⟩
      simpa only [d.right_inv (dt.symm ▸ hz.1)] using hz.2
  have lower_image : d '' {q ∈ d.source | (d q).im < 0} =
      {z ∈ Metric.ball 0 R | z.im < 0} := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨dt ▸ d.map_source hq.1, hq.2⟩
    · intro hz
      refine ⟨d.symm z, ⟨d.map_target (dt.symm ▸ hz.1), ?_⟩, d.right_inv (dt.symm ▸ hz.1)⟩
      simpa only [d.right_inv (dt.symm ▸ hz.1)] using hz.2
  have upper_pullback : {q ∈ d.source | 0 < (d q).im} =
      d.symm '' {z ∈ Metric.ball 0 R | 0 < z.im} := by
    ext q
    constructor
    · intro hq
      exact ⟨d q, ⟨dt ▸ d.map_source hq.1, hq.2⟩, d.left_inv hq.1⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨d.map_target (dt.symm ▸ hz.1), ?_⟩
      simpa only [d.right_inv (dt.symm ▸ hz.1)] using hz.2
  have lower_pullback : {q ∈ d.source | (d q).im < 0} =
      d.symm '' {z ∈ Metric.ball 0 R | z.im < 0} := by
    ext q
    constructor
    · intro hq
      exact ⟨d q, ⟨dt ▸ d.map_source hq.1, hq.2⟩, d.left_inv hq.1⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨d.map_target (dt.symm ▸ hz.1), ?_⟩
      simpa only [d.right_inv (dt.symm ▸ hz.1)] using hz.2
  have hupper : IsConnected {z ∈ Metric.ball (0 : ℂ) R | 0 < z.im} := by
    apply ((convex_ball (0 : ℂ) R).inter (convex_halfSpace_im_gt 0)).isConnected
    refine ⟨(R / 2 : ℝ) * Complex.I, ?_, ?_⟩
    · simp only [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity : 0 < R / 2), Complex.norm_I, mul_one]
      linarith
    · change 0 < (((R / 2 : ℝ) : ℂ) * Complex.I).im
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
      positivity
  have hlower : IsConnected {z ∈ Metric.ball (0 : ℂ) R | z.im < 0} := by
    apply ((convex_ball (0 : ℂ) R).inter (convex_halfSpace_im_lt 0)).isConnected
    refine ⟨(-R / 2 : ℝ) * Complex.I, ?_, ?_⟩
    · simp only [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_neg (by linarith : -R / 2 < 0), Complex.norm_I, mul_one]
      linarith
    · change (((-R / 2 : ℝ) : ℂ) * Complex.I).im < 0
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
      linarith
  have hhol : HolomorphicChartIn X a d := by
    refine ⟨(r.smooth p hp).mono hsub, ?_, ?_, ?_, ?_, ?_⟩
    · exact (r.smooth_inverse p hp).mono (by rw [dt]; exact hball)
    · intro q
      exact (r.holomorphic_in_atlas p q hp).mono (fun z hz => ⟨hz.1, hsub hz.2⟩)
    · intro q
      exact (r.inverse_holomorphic_in_atlas p q hp).mono
        (fun z hz => ⟨hball (dt ▸ hz.1), hz.2⟩)
    · intro q
      have hopen := (a.chart q).continuousOn_symm.isOpen_inter_preimage
        (a.chart q).open_target d.open_source
      exact ((r.holomorphic_in_atlas p q hp).mono
        (fun z hz => ⟨hz.1, hsub hz.2⟩)).analyticOnNhd hopen |>.restrictScalars
    · intro q
      have hopen := d.continuousOn_symm.isOpen_inter_preimage
        d.open_target (a.chart q).open_source
      exact ((r.inverse_holomorphic_in_atlas p q hp).mono
        (fun z hz => ⟨hball (dt ▸ hz.1), hz.2⟩)).analyticOnNhd hopen |>.restrictScalars
  refine ⟨{
    chart := d
    radius := R
    positive_radius := hR
    mem_source := ?_
    centered := he0
    disk_target := dt
    holomorphic_chart := hhol
    invariant := ?_
    reflection := drefl
    fixed_iff := fix
    fixed_interval := ?_
    complement := ?_
    upper_connected := ?_
    lower_connected := ?_
    upper_image := upper_image
    lower_image := lower_image
    exchange_upper := ?_
    exchange_lower := ?_ }⟩
  · rw [ds]
    exact ⟨hep, by change e p ∈ Metric.ball 0 R; rw [he0]; exact Metric.mem_ball_self hR⟩
  · apply Set.Subset.antisymm
    · exact Set.image_subset_iff.mpr stable
    · intro q hq
      exact ⟨ι q, stable hq, hinvolution q⟩
  · ext z
    constructor
    · rintro ⟨q, ⟨hq, hfix⟩, rfl⟩
      have him := (fix q hq).mp hfix
      have heq : d q = Complex.ofReal (d q).re := by
        apply Complex.ext <;> simp [him]
      have hb : |(d q).re| < R := by
        have hh := dt ▸ d.map_source hq
        rw [Metric.mem_ball, dist_zero_right, heq, Complex.norm_real, Real.norm_eq_abs] at hh
        exact hh
      exact ⟨(d q).re, abs_lt.mp hb, heq.symm⟩
    · rintro ⟨x, hx, rfl⟩
      have hz : (x : ℂ) ∈ d.target := by
        rw [dt]
        simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real,
          Real.norm_eq_abs] using abs_lt.mpr hx
      refine ⟨d.symm x, ⟨d.map_target hz, ?_⟩, d.right_inv hz⟩
      apply (fix _ (d.map_target hz)).mpr
      rw [d.right_inv hz]
      exact Complex.ofReal_im x
  · ext q
    simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro hq
      have hn : (d q).im ≠ 0 := fun hz => hq.2 ((fix q hq.1).mpr hz)
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact Or.inr ⟨hq.1, hn⟩
      · exact Or.inl ⟨hq.1, hn⟩
    · rintro (⟨hq, hpos⟩ | ⟨hq, hneg⟩)
      · exact ⟨hq, fun hfix => (ne_of_gt hpos) ((fix q hq).mp hfix)⟩
      · exact ⟨hq, fun hfix => (ne_of_lt hneg) ((fix q hq).mp hfix)⟩
  · rw [upper_pullback]
    exact hupper.image d.symm (d.continuousOn_symm.mono (by rw [dt]; exact Set.inter_subset_left))
  · rw [lower_pullback]
    exact hlower.image d.symm (d.continuousOn_symm.mono (by rw [dt]; exact Set.inter_subset_left))
  · ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨stable hz.1, ?_⟩
      rw [drefl z hz.1]
      simpa only [Complex.star_def, Complex.conj_im] using neg_neg_of_pos hz.2
    · intro hq
      refine ⟨ι q, ⟨stable hq.1, ?_⟩, hinvolution q⟩
      rw [drefl q hq.1]
      simpa only [Complex.star_def, Complex.conj_im] using neg_pos.mpr hq.2
  · ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨stable hz.1, ?_⟩
      rw [drefl z hz.1]
      simpa only [Complex.star_def, Complex.conj_im] using neg_pos.mpr hz.2
    · intro hq
      refine ⟨ι q, ⟨stable hq.1, ?_⟩, hinvolution q⟩
      rw [drefl q hq.1]
      simpa only [Complex.star_def, Complex.conj_im] using neg_neg_of_pos hq.2

/-- The full original Lemma C.8, for a Riemann surface with its actual atlas.
At every fixed point the same local chart gives normal form, analytic
fixed curve and the two exchanged half-disks. -/
theorem paper_C8 [T2Space X] [SecondCountableTopology X]
    (a : ComplexConformalAtlas (𝓡 2) X) (ι : X ≃ₜ X)
    (hinvolution : Function.Involutive ι)
    (hanti : AntiholomorphicInAtlas (𝓡 2) X a ι) :
    ∀ p : X, ι p = p → Nonempty (DiskReflectionChart X a ι p) := by
  obtain ⟨r⟩ := c8_reflection_charts_from_involution (𝓡 2) X a ι hinvolution hanti
  intro p hp
  exact reflection_charts_disk_interface X a ι hinvolution r p hp

end SeifertSurfaces.AppendixC.Original
