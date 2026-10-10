import Mathlib

/-!
# Appendix C.8: local antiholomorphic involution normal form

Source: `references/seifert-surfaces.txt`, lines 2145–2168.
This is the coordinate-plane normal-form obligation. Moving it to a Riemann
surface needs a holomorphic chart and its restriction, explicitly recorded in
the source map. The chart is a genuine partial homeomorphism with holomorphic
coordinate map and inverse.
-/

noncomputable section
namespace SeifertSurfaces.AppendixC

/-- Antiholomorphic on an open set means the conjugated map is holomorphic. -/
def AntiholomorphicOn (F : ℂ → ℂ) (U : Set ℂ) : Prop :=
  DifferentiableOn ℂ (fun z => F (star z)) ((fun z : ℂ => star z) ⁻¹' U)

lemma antiholomorphic_conjugate_differentiable
    (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hanti : AntiholomorphicOn F U) :
    DifferentiableOn ℂ (fun z => star (F z)) U := by
  intro z hz
  have hh : DifferentiableAt ℂ (fun z => F (star z)) (star z) :=
    hanti.differentiableAt
      ((hU.preimage continuous_star).mem_nhds (by simpa using hz))
  simpa [Function.comp_def] using hh.star_star.differentiableWithinAt

lemma equivariant_holomorphic_coordinate
    (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hzero : (0 : ℂ) ∈ U)
    (hanti : AntiholomorphicOn F U)
    (hinvolution : ∀ z ∈ U, F (F z) = z) (hfix : F 0 = 0) :
    ∃ h : ℂ → ℂ, h 0 = 0 ∧ DifferentiableOn ℂ h U ∧ deriv h 0 ≠ 0 ∧
      ∀ z ∈ U, h (F z) = star (h z) := by
  let G := fun z => star (F z)
  have hG := antiholomorphic_conjugate_differentiable F U hU hanti
  have hG0 : DifferentiableAt ℂ G 0 := hG.differentiableAt (hU.mem_nhds hzero)
  let b := deriv G 0
  have hb : 1 + b ≠ 0 ∨ Complex.I - Complex.I * b ≠ 0 := by
    by_cases h : 1 + b = 0
    · right
      have hb' : b = -1 := by linear_combination h
      simp [hb', Complex.I_ne_zero]
    · exact Or.inl h
  rcases hb with hb | hb
  · refine ⟨fun z => z + G z, ?_, ?_, ?_, ?_⟩
    · simp [G, hfix]
    · exact differentiableOn_id.add hG
    · have he := (hasDerivAt_id (0 : ℂ)).add hG0.hasDerivAt
      change deriv (id + G) 0 ≠ 0
      rw [he.deriv]
      exact hb
    · intro z hz
      simp [G, hinvolution z hz, map_add]
      ring
  · refine ⟨fun z => Complex.I * z - Complex.I * G z, ?_, ?_, ?_, ?_⟩
    · simp [G, hfix]
    · exact (differentiableOn_id.const_mul _).sub (hG.const_mul _)
    · have he := ((hasDerivAt_id (0 : ℂ)).const_mul Complex.I).sub
        (hG0.hasDerivAt.const_mul Complex.I)
      change deriv ((fun z => Complex.I * id z) - fun z => Complex.I * G z) 0 ≠ 0
      rw [he.deriv]
      simpa [b] using hb
    · intro z hz
      simp [G, hinvolution z hz, map_sub, map_mul]
      ring

/-- C.8's normalized chart and reflection formula, including the invariant
domain and full disk image. -/
theorem c8_antiholomorphic_involution_normal_form
    (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hzero : (0 : ℂ) ∈ U)
    (hanti : AntiholomorphicOn F U) (hcont : ContinuousOn F U)
    (hstable : Set.MapsTo F U U) (hinvolution : ∀ z ∈ U, F (F z) = z)
    (hfix : F 0 = 0) :
    ∃ (u : OpenPartialHomeomorph ℂ ℂ) (R : ℝ),
      0 < R ∧ u.source ⊆ U ∧ (0 : ℂ) ∈ u.source ∧ u 0 = 0 ∧
      u.target = Metric.ball 0 R ∧
      DifferentiableOn ℂ u u.source ∧ DifferentiableOn ℂ u.symm u.target ∧
      AnalyticOnNhd ℝ u u.source ∧ AnalyticOnNhd ℝ u.symm u.target ∧
      F '' u.source = u.source ∧
      (∀ z ∈ u.source, u (F z) = star (u z)) ∧
      (∀ z ∈ u.source, F z = z ↔ (u z).im = 0) ∧
      F '' {z ∈ u.source | 0 < (u z).im} = {z ∈ u.source | (u z).im < 0} ∧
      F '' {z ∈ u.source | (u z).im < 0} = {z ∈ u.source | 0 < (u z).im} := by
  classical
  obtain ⟨h, hh0, hhol, hd, heq⟩ :=
    equivariant_holomorphic_coordinate F U hU hzero hanti hinvolution hfix
  have ha : AnalyticAt ℂ h 0 := (hhol.analyticOnNhd hU) 0 hzero
  let hfd := ha.hasStrictDerivAt.hasStrictFDerivAt_equiv hd
  let v := hfd.toOpenPartialHomeomorph h
  have hv0 : (0 : ℂ) ∈ v.source := hfd.mem_toOpenPartialHomeomorph_source
  have hv : (v : ℂ → ℂ) = h := rfl
  have hv_inv : AnalyticAt ℂ v.symm 0 := by
    simpa [v, hfd, hh0, HasStrictDerivAt.localInverse,
      HasStrictFDerivAt.localInverse] using ha.analyticAt_localInverse hd
  let W := U ∩ F ⁻¹' v.source
  have hW : IsOpen W := hcont.isOpen_inter_preimage hU v.open_source
  let w := v.restrOpen W hW
  have hw0 : (0 : ℂ) ∈ w.source := ⟨hv0, hzero, by simpa [hfix] using hv0⟩
  have hw : (w : ℂ → ℂ) = h := rfl
  have hw0' : (0 : ℂ) ∈ w.target := by
    simpa [w, hv, hh0] using w.map_source hw0
  have hnh : w.target ∩ {y | AnalyticAt ℂ v.symm y} ∈ nhds (0 : ℂ) :=
    (w.open_target.inter (isOpen_analyticAt ℂ v.symm)).mem_nhds ⟨hw0', hv_inv⟩
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hnh
  let u := w.trans (OpenPartialHomeomorph.ofSet (Metric.ball 0 R) Metric.isOpen_ball)
  have hu : (u : ℂ → ℂ) = h := rfl
  have hui : (u.symm : ℂ → ℂ) = v.symm := rfl
  have hus : u.source = {z | z ∈ v.source ∧ z ∈ U ∧ F z ∈ v.source ∧ h z ∈ Metric.ball 0 R} := by
    ext z
    simp [u, w, W, hv, and_assoc]
    tauto
  have hut : u.target = Metric.ball 0 R := by
    ext z
    simp only [u, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.ofSet_target,
      OpenPartialHomeomorph.ofSet_symm, OpenPartialHomeomorph.ofSet_apply,
      Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨And.left, fun hz => ⟨hz, (hball hz).1⟩⟩
  have husU : u.source ⊆ U := by intro z hz; exact (hus ▸ hz).2.1
  have hustable : Set.MapsTo F u.source u.source := by
    intro z hz
    rw [hus] at hz ⊢
    refine ⟨hz.2.2.1, hstable hz.2.1, ?_, ?_⟩
    · simpa [hinvolution z hz.2.1] using hz.1
    · rw [heq z hz.2.1]
      simpa using hz.2.2.2
  have hreflect : ∀ z ∈ u.source, u (F z) = star (u z) := by
    intro z hz
    exact heq z (husU hz)
  refine ⟨u, R, hR, husU, ?_, ?_, hut, ?_, ?_, ?_, ?_, ?_, hreflect, ?_, ?_, ?_⟩
  · rw [hus]
    refine ⟨hv0, hzero, ?_, ?_⟩
    · simpa only [hfix] using hv0
    · simpa only [hh0] using (Metric.mem_ball_self (x := (0 : ℂ)) hR)
  · exact hh0
  · exact hhol.mono husU
  · intro z hz
    have haz := (hball (hut ▸ hz)).2
    exact haz.differentiableAt.differentiableWithinAt
  · exact ((hhol.analyticOnNhd hU).mono husU).restrictScalars
  · intro z hz
    exact ((hball (hut ▸ hz)).2).restrictScalars
  · apply Set.Subset.antisymm
    · exact Set.image_subset_iff.mpr hustable
    · intro z hz
      exact ⟨F z, hustable hz, hinvolution z (husU hz)⟩
  · intro z hz
    constructor
    · intro hfixz
      have hh := hreflect z hz
      rw [hfixz] at hh
      exact Complex.conj_eq_iff_im.mp hh.symm
    · intro him
      apply u.injOn (hustable hz) hz
      rw [hreflect z hz]
      exact Complex.conj_eq_iff_im.mpr him
  · ext z
    constructor
    · rintro ⟨x, ⟨hx, hxpos⟩, rfl⟩
      exact ⟨hustable hx, by simpa [hreflect x hx] using hxpos⟩
    · rintro ⟨hz, hzneg⟩
      refine ⟨F z, ⟨hustable hz, ?_⟩, hinvolution z (husU hz)⟩
      simpa [hreflect z hz] using hzneg
  · ext z
    constructor
    · rintro ⟨x, ⟨hx, hxneg⟩, rfl⟩
      exact ⟨hustable hx, by simpa [hreflect x hx] using hxneg⟩
    · rintro ⟨hz, hzpos⟩
      refine ⟨F z, ⟨hustable hz, ?_⟩, hinvolution z (husU hz)⟩
      simpa [hreflect z hz] using hzpos

end SeifertSurfaces.AppendixC
