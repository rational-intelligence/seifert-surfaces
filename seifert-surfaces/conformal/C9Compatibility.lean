import C7Conformal
import C8NormalForm

/-!
# Appendix C.9: the two compatibility clauses, as hypotheses

Source: `references/seifert-surfaces.txt`, lines 2169–2217.
Neither compatibility structure is asserted to exist. Constructing one from
the cited moduli-space limit is precisely the outstanding source debt.
-/

noncomputable section
open Bundle
open scoped Manifold ContDiff
namespace SeifertSurfaces.AppendixC

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace ℝ EH]
    [FiniteDimensional ℝ EH]
    {HH : Type*} [TopologicalSpace HH] (IH : ModelWithCorners ℝ EH HH)
    (S : Type*) [TopologicalSpace S] [ChartedSpace H S] [IsManifold I ∞ S]
    (D : Type*) [TopologicalSpace D] [ChartedSpace HH D] [IsManifold IH ∞ D]

/-- L2′, expressed through the actual inclusion into the closed double and a
smooth representative of its conformal structure (provided by C.7).
This is a hypothesis bundle, never a theorem asserting its existence. -/
structure L2PrimeCompatibility
    (t : InteriorConformalField I S) (j : S → D) where
  double_compact : IsCompact (Set.univ : Set D)
  double_boundaryless : BoundarylessManifold IH D
  double_metric : ContMDiffRiemannianMetric IH ∞ EH
    (fun p : D => TangentSpace IH p)
  preserving_diffeomorph : Diffeomorph IH IH D D ∞
  preserves_subsurface : preserving_diffeomorph '' Set.range j = Set.range j
  inclusion_smooth : ContMDiff I IH ∞ j
  inclusion_immersion : ∀ p, Function.Injective (mfderiv I IH j p)
  pullback_conformal : ∀ p ∈ I.interior S, ∃ c : ℝ, 0 < c ∧ ∀ v w,
    double_metric.inner (preserving_diffeomorph (j p))
      (mfderiv IH IH preserving_diffeomorph (j p) (mfderiv I IH j p v))
      (mfderiv IH IH preserving_diffeomorph (j p) (mfderiv I IH j p w)) =
      c * t.representative p v w

/-- A genuine holomorphic atlas, compatible with the given real smooth
structure. It expresses the closed double's conformal structure using complex
coordinates and holomorphic transitions. -/
structure ComplexConformalAtlas where
  chart : D → OpenPartialHomeomorph D ℂ
  mem_source : ∀ p : D, p ∈ (chart p).source
  smooth : ∀ p : D, ContMDiffOn IH 𝓘(ℝ, ℂ) ∞ (chart p) (chart p).source
  smooth_inverse : ∀ p : D,
    ContMDiffOn 𝓘(ℝ, ℂ) IH ∞ (chart p).symm (chart p).target
  holomorphic_transition : ∀ p q : D,
    DifferentiableOn ℂ ((chart q) ∘ (chart p).symm)
      ((chart p).target ∩ (chart p).symm ⁻¹' (chart q).source)

def AntiholomorphicInAtlas (a : ComplexConformalAtlas IH D) (ι : D → D) : Prop :=
  ∀ p : D, AntiholomorphicOn ((a.chart (ι p)) ∘ ι ∘ (a.chart p).symm)
    ((a.chart p).target ∩ (a.chart p).symm ⁻¹' (ι ⁻¹' (a.chart (ι p)).source))

/-- A concrete reflection-chart property. It expresses the local analytic
fixed curve and the two sides in C.8 without an uninterpreted predicate. -/
structure ReflectionCharts (a : ComplexConformalAtlas IH D) (ι : D → D) where
  chart : ∀ p : D, ι p = p → OpenPartialHomeomorph D ℂ
  fixed_mem : ∀ (p : D) (hp : ι p = p), p ∈ (chart p hp).source
  centered : ∀ (p : D) (hp : ι p = p), chart p hp p = 0
  reflection : ∀ (p : D) (hp : ι p = p) (z : D),
    z ∈ (chart p hp).source → chart p hp (ι z) = star (chart p hp z)
  fixed_curve : ∀ (p : D) (hp : ι p = p) (z : D),
    z ∈ (chart p hp).source → (ι z = z ↔ (chart p hp z).im = 0)
  invariant : ∀ (p : D) (hp : ι p = p),
    ι '' (chart p hp).source = (chart p hp).source
  smooth : ∀ (p : D) (hp : ι p = p),
    ContMDiffOn IH 𝓘(ℝ, ℂ) ∞ (chart p hp) (chart p hp).source
  smooth_inverse : ∀ (p : D) (hp : ι p = p),
    ContMDiffOn 𝓘(ℝ, ℂ) IH ∞ (chart p hp).symm (chart p hp).target
  holomorphic_in_atlas : ∀ (p q : D) (hp : ι p = p),
    DifferentiableOn ℂ ((chart p hp) ∘ (a.chart q).symm)
      ((a.chart q).target ∩ (a.chart q).symm ⁻¹' (chart p hp).source)
  inverse_holomorphic_in_atlas : ∀ (p q : D) (hp : ι p = p),
    DifferentiableOn ℂ ((a.chart q) ∘ (chart p hp).symm)
      ((chart p hp).target ∩ (chart p hp).symm ⁻¹' (a.chart q).source)

lemma conjugate_differentiable_antiholomorphic
    (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hh : DifferentiableOn ℂ (fun z => star (F z)) U) : AntiholomorphicOn F U := by
  intro z hz
  have h := (hh.differentiableAt (hU.mem_nhds hz)).star_star
  simpa [Function.comp_def] using h.differentiableWithinAt

lemma local_reflection_chart
    (a : ComplexConformalAtlas IH D) (ι : D ≃ₜ D)
    (hinvolution : Function.Involutive ι)
    (hanti : AntiholomorphicInAtlas IH D a ι) (p : D) (hp : ι p = p) :
    ∃ d : OpenPartialHomeomorph D ℂ,
      p ∈ d.source ∧ d p = 0 ∧
      (∀ z ∈ d.source, d (ι z) = star (d z)) ∧
      (∀ z ∈ d.source, ι z = z ↔ (d z).im = 0) ∧
      ι '' d.source = d.source ∧
      ContMDiffOn IH 𝓘(ℝ, ℂ) ∞ d d.source ∧
      ContMDiffOn 𝓘(ℝ, ℂ) IH ∞ d.symm d.target ∧
      (∀ q : D, DifferentiableOn ℂ (d ∘ (a.chart q).symm)
        ((a.chart q).target ∩ (a.chart q).symm ⁻¹' d.source)) ∧
      (∀ q : D, DifferentiableOn ℂ ((a.chart q) ∘ d.symm)
        (d.target ∩ d.symm ⁻¹' (a.chart q).source)) := by
  classical
  let b := a.chart p
  let c := b p
  let e := b.trans (Homeomorph.subRight c).toOpenPartialHomeomorph
  have es : e.source = b.source := by simp [e]
  have et : e.target = {z | z + c ∈ b.target} := by ext z; simp [e, Homeomorph.subRight]
  have etm (z : ℂ) : z ∈ e.target ↔ z + c ∈ b.target := by rw [et]; rfl
  have ev (z : D) : e z = b z - c := rfl
  have ei (z : ℂ) : e.symm z = b.symm (z + c) := rfl
  have ep : p ∈ e.source := es ▸ a.mem_source p
  have ep0 : e p = 0 := by simp [ev, c]
  let F := fun z : ℂ => e (ι (e.symm z))
  let U := e.target ∩ e.symm ⁻¹' (ι ⁻¹' e.source)
  have hU : IsOpen U :=
    (ι.continuous.comp_continuousOn e.continuousOn_symm).isOpen_inter_preimage
      e.open_target e.open_source
  have hzU : (0 : ℂ) ∈ U := by
    refine ⟨?_, ?_⟩
    · simpa only [ep0] using e.map_source ep
    · change ι (e.symm 0) ∈ e.source
      rw [← ep0, e.left_inv ep, hp]
      exact ep
  have hF0 : F 0 = 0 := by
    dsimp [F]
    rw [← ep0, e.left_inv ep, hp, ep0]
  have hFU : Set.MapsTo F U U := by
    intro z hz
    have his : ι (e.symm z) ∈ e.source := hz.2
    refine ⟨e.map_source his, ?_⟩
    change ι (e.symm (e (ι (e.symm z)))) ∈ e.source
    rw [e.left_inv his, hinvolution]
    exact e.map_target hz.1
  have hFF : ∀ z ∈ U, F (F z) = z := by
    intro z hz
    dsimp [F]
    rw [e.left_inv hz.2, hinvolution, e.right_inv hz.1]
  have hFcont : ContinuousOn F U :=
    e.continuousOn.comp (ι.continuous.comp_continuousOn (e.continuousOn_symm.mono
      Set.inter_subset_left)) (fun z hz => hz.2)
  let U0 := b.target ∩ b.symm ⁻¹' (ι ⁻¹' b.source)
  let F0 := fun z : ℂ => b (ι (b.symm z))
  have hU0 : IsOpen U0 :=
    (ι.continuous.comp_continuousOn b.continuousOn_symm).isOpen_inter_preimage
      b.open_target b.open_source
  have hanti0 : AntiholomorphicOn F0 U0 := by
    simpa only [hp, Function.comp_def] using hanti p
  have hhol0 := antiholomorphic_conjugate_differentiable F0 U0 hU0 hanti0
  have hshift : Set.MapsTo (fun z : ℂ => z + c) U U0 := by
    intro z hz
    refine ⟨(etm z).mp hz.1, ?_⟩
    change ι (b.symm (z + c)) ∈ b.source
    have hh : ι (e.symm z) ∈ e.source := hz.2
    simpa only [ei, es] using hh
  have hantiF : AntiholomorphicOn F U := by
    apply conjugate_differentiable_antiholomorphic F U hU
    have hh := (hhol0.comp (differentiableOn_id.add_const c) hshift).sub_const (star c)
    simpa [F, F0, ev, ei, Function.comp_def, star_sub] using hh
  obtain ⟨u, R, hR, huU, hu0, hu0', hut, huhol, huihol, huan, huian,
      huinv, hurefl, hufix, _, _⟩ :=
    c8_antiholomorphic_involution_normal_form F U hU hzU hantiF hFcont hFU hFF hF0
  let d := e.trans u
  have ds : d.source = e.source ∩ e ⁻¹' u.source := rfl
  have dt : d.target = u.target := by
    ext z
    change (z ∈ u.target ∧ u.symm z ∈ e.target) ↔ z ∈ u.target
    exact ⟨And.left, fun hz => ⟨hz, (huU (u.map_target hz)).1⟩⟩
  have dv (z : D) : d z = u (e z) := rfl
  have di (z : ℂ) : d.symm z = e.symm (u.symm z) := rfl
  have dstable : Set.MapsTo ι d.source d.source := by
    intro z hz
    rw [ds] at hz ⊢
    have hzU := huU hz.2
    have hi : ι z ∈ e.source := by
      have hh : ι (e.symm (e z)) ∈ e.source := hzU.2
      rwa [e.left_inv hz.1] at hh
    refine ⟨hi, ?_⟩
    change e (ι z) ∈ u.source
    have hs : F (e z) ∈ u.source := by rw [← huinv]; exact ⟨e z, hz.2, rfl⟩
    simpa only [F, e.left_inv hz.1] using hs
  have drefl : ∀ z ∈ d.source, d (ι z) = star (d z) := by
    intro z hz
    rw [ds] at hz
    simpa only [dv, F, e.left_inv hz.1] using hurefl (e z) hz.2
  have dsm : ContMDiffOn IH 𝓘(ℝ, ℂ) ∞ d d.source := by
    have hs : ContMDiffOn IH 𝓘(ℝ, ℂ) ∞ e e.source := by
      have hadd : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z : ℂ => z - c) :=
        (contDiff_id.sub contDiff_const).contMDiff
      exact hadd.comp_contMDiffOn ((a.smooth p).mono (by rw [es]))
    exact (huan.contDiffOn u.open_source.uniqueDiffOn).contMDiffOn.comp
      (hs.mono Set.inter_subset_left) (fun z hz => hz.2)
  have dism : ContMDiffOn 𝓘(ℝ, ℂ) IH ∞ d.symm d.target := by
    have hs : ContMDiffOn 𝓘(ℝ, ℂ) IH ∞ e.symm e.target := by
      have hadd : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z : ℂ => z + c) :=
        (contDiff_id.add contDiff_const).contMDiff
      exact (a.smooth_inverse p).comp hadd.contMDiffOn (fun z hz => (etm z).mp hz)
    exact hs.comp ((huian.contDiffOn u.open_target.uniqueDiffOn).contMDiffOn.mono
      (by rw [dt])) (fun z hz => (huU (u.map_target (dt ▸ hz))).1)
  have dpm : p ∈ d.source := by
    rw [ds]
    refine ⟨ep, ?_⟩
    change e p ∈ u.source
    rw [ep0]
    exact hu0
  refine ⟨d, dpm, ?_, drefl, ?_, ?_, dsm, dism, ?_, ?_⟩
  · simpa only [dv, ep0] using hu0'
  · intro z hz
    constructor
    · intro hfixz
      apply Complex.conj_eq_iff_im.mp
      change star (d z) = d z
      simpa only [hfixz] using (drefl z hz).symm
    · intro him
      apply d.injOn (dstable hz) hz
      rw [drefl z hz]
      exact Complex.conj_eq_iff_im.mpr him
  · apply Set.Subset.antisymm
    · exact Set.image_subset_iff.mpr dstable
    · intro z hz
      exact ⟨ι z, dstable hz, hinvolution z⟩
  · intro q
    let T := (a.chart q).target ∩ (a.chart q).symm ⁻¹' d.source
    have hsub : T ⊆ (a.chart q).target ∩ (a.chart q).symm ⁻¹' b.source := by
      intro z hz
      exact ⟨hz.1, es ▸ hz.2.1⟩
    have hh := ((a.holomorphic_transition q p).mono hsub).sub_const c
    have hh' : DifferentiableOn ℂ (e ∘ (a.chart q).symm) T := hh
    exact huhol.comp hh' (fun z hz => hz.2.2)
  · intro q
    let T := d.target ∩ d.symm ⁻¹' (a.chart q).source
    have hh : DifferentiableOn ℂ (fun z : ℂ => u.symm z + c) T :=
      (huihol.mono (fun z hz => dt ▸ hz.1)).add_const c
    have hmaps : Set.MapsTo (fun z : ℂ => u.symm z + c) T
        (b.target ∩ b.symm ⁻¹' (a.chart q).source) := by
      intro z hz
      refine ⟨?_, hz.2⟩
      exact (etm (u.symm z)).mp (huU (u.map_target (dt ▸ hz.1))).1
    exact (a.holomorphic_transition p q).comp hh hmaps

/-- Manifold/chart bridge for C.8. The raw L2″ hypothesis below does not
assume the reflection charts that C.8 is supposed to produce. -/
theorem c8_reflection_charts_from_involution
    (a : ComplexConformalAtlas IH D) (ι : D ≃ₜ D)
    (hinvolution : Function.Involutive ι)
    (hanti : AntiholomorphicInAtlas IH D a ι) :
    Nonempty (ReflectionCharts IH D a ι) := by
  classical
  let chosen := fun p hp => Classical.choose (local_reflection_chart IH D a ι
    hinvolution hanti p hp)
  have hc := fun p hp => Classical.choose_spec (local_reflection_chart IH D a ι
    hinvolution hanti p hp)
  exact ⟨{
    chart := chosen
    fixed_mem := fun p hp => (hc p hp).1
    centered := fun p hp => (hc p hp).2.1
    reflection := fun p hp => (hc p hp).2.2.1
    fixed_curve := fun p hp => (hc p hp).2.2.2.1
    invariant := fun p hp => (hc p hp).2.2.2.2.1
    smooth := fun p hp => (hc p hp).2.2.2.2.2.1
    smooth_inverse := fun p hp => (hc p hp).2.2.2.2.2.2.1
    holomorphic_in_atlas := fun p q hp => (hc p hp).2.2.2.2.2.2.2.1 q
    inverse_holomorphic_in_atlas := fun p q hp => (hc p hp).2.2.2.2.2.2.2.2 q }⟩

/-- L2″, after C.7 and the C.8 bridge: the real double involution and its
conjugacy, one connected component, its closure and the pullback metric.
The given map is a smooth parametrisation with an injective differential and
a homeomorphism onto that closure. The smooth inverse into the subsurface
requires the induced subsurface manifold structure (an explicit bridge). -/
structure L2DoublePrimeCompatibility
    (t : InteriorConformalField I S) (swap : D ≃ₜ D) where
  double_compact : IsCompact (Set.univ : Set D)
  double_boundaryless : BoundarylessManifold IH D
  double_metric : ContMDiffRiemannianMetric IH ∞ EH
    (fun p : D => TangentSpace IH p)
  conformal_atlas : ComplexConformalAtlas IH D
  metric_in_atlas : ∀ p q : D, q ∈ (conformal_atlas.chart p).source →
    ∃ c : ℝ, 0 < c ∧ ∀ v w,
      double_metric.inner q v w = c * inner ℝ
        (mfderiv IH 𝓘(ℝ, ℂ) (conformal_atlas.chart p) q v)
        (mfderiv IH 𝓘(ℝ, ℂ) (conformal_atlas.chart p) q w)
  involution : D ≃ₜ D
  involutive : Function.Involutive involution
  anti_conformal : AntiholomorphicInAtlas IH D conformal_atlas involution
  conjugacy : D ≃ₜ D
  conjugate_swap : ∀ p, involution (conjugacy p) = conjugacy (swap p)
  component : Set D
  component_open : IsOpen component
  component_connected : IsConnected component
  component_maximal : ∀ C : Set D,
    IsPreconnected C → C ⊆ {p | involution p ≠ p} →
      (C ∩ component).Nonempty → C ⊆ component
  component_avoids_fixed : component ⊆ {p | involution p ≠ p}
  exchanges_components : involution '' component =
    {p | involution p ≠ p} \ component
  parametrization : S ≃ₜ closure component
  inclusion_smooth : ContMDiff I IH ∞
    (fun p => (parametrization p : D))
  inclusion_immersion : ∀ p, Function.Injective
    (mfderiv I IH (fun p => (parametrization p : D)) p)
  boundary_fixed : ∀ p, I.IsBoundaryPoint p ↔
    involution (parametrization p : D) = (parametrization p : D)
  pullback_conformal : ∀ p ∈ I.interior S, ∃ c : ℝ, 0 < c ∧ ∀ v w,
    double_metric.inner (parametrization p : D)
      (mfderiv I IH (fun p => (parametrization p : D)) p v)
      (mfderiv I IH (fun p => (parametrization p : D)) p w) =
      c * t.representative p v w

/-- C.9, L2′ branch: it produces a smooth boundary metric conditionally on
the subsurface-preserving compatibility data, without supplying that data. -/
theorem c9_metric_from_L2prime
    (t : InteriorConformalField I S) (j : S → D)
    (hcompat : L2PrimeCompatibility I IH S D t j) :
    ∃ g : ContMDiffRiemannianMetric I ∞ E (fun p : S => TangentSpace I p),
      ConformalOnInterior I S g.inner t.representative := by
  let Φ := hcompat.preserving_diffeomorph
  have hj : ContMDiff I IH ∞ (Φ ∘ j) := Φ.contMDiff.comp hcompat.inclusion_smooth
  have hΦ : ∀ q, Function.Injective (mfderiv IH IH Φ q) := by
    intro q
    have hi : Function.Injective (mfderiv IH IH (Φ.symm ∘ Φ) q) := by
      have heq : (Φ.symm ∘ Φ : D → D) = id := by
        funext x
        exact Φ.symm_apply_apply x
      rw [heq, mfderiv_id]
      exact Function.injective_id
    rw [mfderiv_comp q (Φ.symm.contMDiff.mdifferentiableAt (by simp))
      (Φ.contMDiff.mdifferentiableAt (by simp))] at hi
    exact Function.Injective.of_comp hi
  have him : ∀ p, Function.Injective (mfderiv I IH (Φ ∘ j) p) := by
    intro p
    rw [mfderiv_comp p (Φ.contMDiff.mdifferentiableAt (by simp))
      (hcompat.inclusion_smooth.mdifferentiableAt (by simp))]
    exact (hΦ (j p)).comp (hcompat.inclusion_immersion p)
  obtain ⟨g, hg⟩ := c7_restrict_metric_smooth_up_to_boundary IH D I S (Φ ∘ j) hj him
    hcompat.double_metric
  refine ⟨g, ?_⟩
  intro p hp
  obtain ⟨c, hc, heq⟩ := hcompat.pullback_conformal p hp
  refine ⟨c, hc, ?_⟩
  intro v w
  rw [hg]
  simpa only [Function.comp_apply, mfderiv_comp p
    (Φ.contMDiff.mdifferentiableAt (by simp))
    (hcompat.inclusion_smooth.mdifferentiableAt (by simp)), ContinuousLinearMap.comp_apply]
    using heq v w

/-- C.9, L2″ branch. The returned reflection-chart bundle retains its actual
chart, inverse, and holomorphic transitions to the SAME conformal atlas.
By `boundary_fixed`, every image boundary point has such a chart, and its
boundary is the real axis by `fixed_curve`. -/
theorem c9_metric_from_L2doubleprime
    (t : InteriorConformalField I S) (swap : D ≃ₜ D)
    (hcompat : L2DoublePrimeCompatibility I IH S D t swap) :
    (∃ g : ContMDiffRiemannianMetric I ∞ E (fun p : S => TangentSpace I p),
      ConformalOnInterior I S g.inner t.representative) ∧
      Nonempty (ReflectionCharts IH D hcompat.conformal_atlas hcompat.involution) := by
  constructor
  · obtain ⟨g, hg⟩ := c7_restrict_metric_smooth_up_to_boundary IH D I S
      (fun p => (hcompat.parametrization p : D)) hcompat.inclusion_smooth
      hcompat.inclusion_immersion hcompat.double_metric
    refine ⟨g, ?_⟩
    intro p hp
    obtain ⟨c, hc, heq⟩ := hcompat.pullback_conformal p hp
    refine ⟨c, hc, ?_⟩
    intro v w
    rw [hg]
    exact heq v w
  · exact c8_reflection_charts_from_involution IH D hcompat.conformal_atlas
      hcompat.involution hcompat.involutive hcompat.anti_conformal

end SeifertSurfaces.AppendixC
