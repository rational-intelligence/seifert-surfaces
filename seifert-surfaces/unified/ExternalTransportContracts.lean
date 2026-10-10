import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option maxSynthPendingDepth 3

/-! Exact public-source contracts staged as proof obligations, not imported
proofs. Four source modules at qinz1yang/differential-geometry commit
777299070a5529e96345e0033979706fd00c7e62 are preserved in external_source.
The two explicitly new bridges are inverse smoothness and analytic model
transport. Their statements are not attributed to the public smooth theorem. -/
open scoped Manifold ContDiff
open Set Topology
open OpenPartialHomeomorph Manifold IsManifold
namespace SeifertSurfaces.LongitudeProducers.Transport
noncomputable section

section Homeomorphism
variable {𝕜 V H X Y : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [TopologicalSpace H] [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace H X] (I : ModelWithCorners 𝕜 V H) (n : ℕ∞ω)

theorem homeomorph_atlas_manifold (e : X ≃ₜ Y) [IsManifold I n X] :
    @IsManifold 𝕜 _ V _ _ H _ I n Y _ e.chartedSpace := by
  let e₀ := e
  refine @isManifold_of_contDiffOn 𝕜 _ V _ _ H _ I n Y _ (e₀.chartedSpace) ?_
  intro e e' he he'
  change e ∈ Set.range (@chartAt H _ Y _ e₀.chartedSpace) at he
  change e' ∈ Set.range (@chartAt H _ Y _ e₀.chartedSpace) at he'
  obtain ⟨q, rfl⟩ := he
  obtain ⟨q', rfl⟩ := he'
  change ContDiffOn 𝕜 n (I ∘ (((e₀.isLocalHomeomorph.localInverseAt (e₀.surjective.hasRightInverse.choose q)).trans (chartAt H (e₀.surjective.hasRightInverse.choose q))).symm.trans ((e₀.isLocalHomeomorph.localInverseAt (e₀.surjective.hasRightInverse.choose q')).trans (chartAt H (e₀.surjective.hasRightInverse.choose q')))) ∘ I.symm) _
  set g := e₀.surjective.hasRightInverse.choose with hgdef
  set A := e₀.isLocalHomeomorph.localInverseAt (g q) with hA
  set A' := e₀.isLocalHomeomorph.localInverseAt (g q') with hA'
  set c := chartAt H (g q) with hc
  set c' := chartAt H (g q') with hc'
  have hAs : ⇑(A.symm) = (e₀ : X → Y) := by
    rw [hA]; exact IsLocalHomeomorph.localInverseAt_symm e₀.isLocalHomeomorph (g q)
  have hA's : ⇑(A'.symm) = (e₀ : X → Y) := by
    rw [hA']; exact IsLocalHomeomorph.localInverseAt_symm e₀.isLocalHomeomorph (g q')
  have hB : ∀ y, y ∈ (A.symm ≫ₕ A').source → A' (A.symm y) = y := by
    intro y hy
    rw [OpenPartialHomeomorph.trans_source] at hy
    have hy2 : e₀ y ∈ A'.source := by rw [← hAs]; exact hy.2
    rw [hAs]
    refine e₀.injective ?_
    have h := A'.left_inv hy2
    rwa [hA's] at h
  have hsrc : ∀ w, w ∈ ((A ≫ₕ c).symm ≫ₕ (A' ≫ₕ c')).source →
      w ∈ c.symm.source ∧ c.symm w ∈ A.symm.source ∧
        A.symm (c.symm w) ∈ A'.source ∧ A' (A.symm (c.symm w)) ∈ c'.source := by
    intro w hw
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] at hw
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hw
    simp only [coe_trans, Function.comp_apply, Set.mem_inter_iff, Set.mem_preimage] at hw
    exact ⟨hw.1.1, hw.1.2, hw.2.1, hw.2.2⟩
  have hsub : ((A ≫ₕ c).symm ≫ₕ (A' ≫ₕ c')).source ⊆ (c.symm ≫ₕ c').source := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hsrc w hw
    have hmem : c.symm w ∈ (A.symm ≫ₕ A').source := by
      rw [OpenPartialHomeomorph.trans_source]; exact ⟨h2, h3⟩
    have hb := hB (c.symm w) hmem
    rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨h1, by rw [← hb]; exact h4⟩
  have heq : ∀ w ∈ ((A ≫ₕ c).symm ≫ₕ (A' ≫ₕ c')).source,
      ((A ≫ₕ c).symm ≫ₕ (A' ≫ₕ c')) w = (c.symm ≫ₕ c') w := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hsrc w hw
    have hmem : c.symm w ∈ (A.symm ≫ₕ A').source := by
      rw [OpenPartialHomeomorph.trans_source]; exact ⟨h2, h3⟩
    have hb := hB (c.symm w) hmem
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    simp only [OpenPartialHomeomorph.trans_apply]
    rw [hb]
  have hY : (c.symm ≫ₕ c') ∈ contDiffGroupoid n I :=
    StructureGroupoid.compatible (contDiffGroupoid n I)
      (chart_mem_atlas H (g q)) (chart_mem_atlas H (g q'))
  refine (mem_groupoid_of_pregroupoid.mp hY).1.congr_mono (fun z hz => ?_) (fun z hz => ?_)
  · simp only [Function.comp_apply]
    exact congrArg (⇑I) (heq _ hz.1)
  · exact ⟨hsub hz.1, hz.2⟩

theorem homeomorph_atlas_forward (e : X ≃ₜ Y) [IsManifold I n X] :
    @ContMDiff 𝕜 _ V _ _ H _ I X _ _ V _ _ H _ I Y _ e.chartedSpace n e := by
  let e₀ := e
  let _ := (e₀.chartedSpace : ChartedSpace H Y)
  letI := homeomorph_atlas_manifold I n e₀
  let g' := e₀.surjective.hasRightInverse.choose
  have hg' : Function.RightInverse g' e₀ := e₀.surjective.hasRightInverse.choose_spec
  have hchart : ∀ y, chartAt H y =
      (e₀.isLocalHomeomorph.localInverseAt (g' y)).trans (chartAt H (g' y)) := fun y => rfl
  rw [contMDiff_iff_target]
  refine ⟨e₀.continuous, fun y => ?_⟩
  have hinv : ∀ x, e₀ x ∈ (e₀.isLocalHomeomorph.localInverseAt (g' y)).source →
      (e₀.isLocalHomeomorph.localInverseAt (g' y)) (e₀ x) = x := fun x hx =>
    e₀.injective (e₀.isLocalHomeomorph.apply_localInverseAt_of_mem hx)
  have hsrc : ∀ x, x ∈ e₀ ⁻¹' (extChartAt I y).source →
      e₀ x ∈ (e₀.isLocalHomeomorph.localInverseAt (g' y)).source ∧
        (e₀.isLocalHomeomorph.localInverseAt (g' y)) (e₀ x) ∈ (chartAt H (g' y)).source := by
    intro x hx
    rw [mem_preimage, extChartAt_source, hchart y, OpenPartialHomeomorph.trans_source,
      mem_inter_iff, mem_preimage] at hx
    exact hx
  have hsub : e₀ ⁻¹' (extChartAt I y).source ⊆ (chartAt H (g' y)).source := fun x hx => by
    obtain ⟨h1, h2⟩ := hsrc x hx
    rw [← hinv x h1]
    exact h2
  refine (contMDiffOn_extChartAt (I := I) (x := g' y)).mono hsub |>.congr fun x hx => ?_
  rw [Function.comp_apply, extChartAt_coe, extChartAt_coe, Function.comp_apply, hchart y,
    OpenPartialHomeomorph.coe_trans, Function.comp_apply, hinv x (hsrc x hx).1]
  rfl

/-- New obligation: the inverse uses the ORIGINAL X atlas. -/
theorem homeomorph_atlas_inverse (e : X ≃ₜ Y) [IsManifold I n X] :
    @ContMDiff 𝕜 _ V _ _ H _ I Y _ e.chartedSpace V _ _ H _ I X _ _ n e.symm := by
  letI : ChartedSpace H Y := e.chartedSpace
  letI := homeomorph_atlas_manifold I n e
  intro y
  let g := e.surjective.hasRightInverse.choose
  have hg : e (g y) = y := e.surjective.hasRightInverse.choose_spec y
  have hchart : chartAt H y =
      (e.isLocalHomeomorph.localInverseAt (g y)).trans (chartAt H (g y)) := rfl
  have hinvs : ⇑(e.isLocalHomeomorph.localInverseAt (g y)).symm = (e : X → Y) :=
    IsLocalHomeomorph.localInverseAt_symm e.isLocalHomeomorph (g y)
  have heq : (e.symm ∘ (extChartAt I y).symm : V → X) =
      (extChartAt I (g y)).symm := by
    funext z
    rw [Function.comp_apply, extChartAt_coe_symm, extChartAt_coe_symm,
      Function.comp_apply, Function.comp_apply, hchart,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.coe_trans, Function.comp_apply, hinvs]
    exact e.symm_apply_apply _
  have hpoint : extChartAt I y y = extChartAt I (g y) (g y) := by
    rw [extChartAt_coe, extChartAt_coe, Function.comp_apply, Function.comp_apply,
      hchart, OpenPartialHomeomorph.trans_apply]
    congr 2
    apply e.injective
    exact (e.isLocalHomeomorph.apply_localInverseAt_of_mem
      ((mem_chart_source H y).1)).trans hg.symm
  rw [contMDiffAt_iff_source]
  rw [heq, hpoint]
  exact contMDiffWithinAt_extChartAt_symm_range_self (I := I) (g y)

theorem homeomorph_atlas_chart (e : X ≃ₜ Y) (q : Y) :
    @chartAt H _ Y _ e.chartedSpace q =
      (e.isLocalHomeomorph.localInverseAt (e.surjective.hasRightInverse.choose q)).trans
        (chartAt H (e.surjective.hasRightInverse.choose q)) := by
  rfl
end Homeomorphism

section ModelChange
variable {𝕜 V W H H' X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace X] [ChartedSpace H X]

/-- Literal ChartedSpace.comp construction from the inspected ModelTransport. -/
def modelChangedAtlas (e : H ≃ₜ H') : ChartedSpace H' X :=
  letI : ChartedSpace H' H := e.toOpenPartialHomeomorph.singletonChartedSpace
    e.toOpenPartialHomeomorph_source
  ChartedSpace.comp H' H X

theorem modelChangedAtlas_chart (e : H ≃ₜ H') (x : X) :
    @chartAt H' _ X _ (modelChangedAtlas e) x =
      (chartAt H x).trans e.toOpenPartialHomeomorph := by
  rfl

variable (I : ModelWithCorners 𝕜 V H) (J : ModelWithCorners 𝕜 W H')
  (e : H ≃ₜ H') (L : V ≃L[𝕜] W) (hc : ∀ y, J (e y) = L (I y))

include hc

theorem modelChangedAtlas_smooth [IsManifold I ∞ X] :
    @IsManifold 𝕜 _ W _ _ H' _ J ∞ X _ (modelChangedAtlas e) := by
  let _ := modelChangedAtlas (X := X) e
  have hInv (x : W) (hx : x ∈ range J) : I.symm (L.symm x) = e.symm (J.symm x) := by
    obtain ⟨y, rfl⟩ := hx
    have hy : J y = L (I (e.symm y)) := by rw [← hc, e.apply_symm_apply]
    rw [hy, L.symm_apply_apply, I.left_inv]
    rw [← hy, J.left_inv]
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨f, hf, u, hu, rfl⟩ ⟨g, hg, v, hv, rfl⟩
  have hu' : u = e.toOpenPartialHomeomorph := hu
  have hv' : v = e.toOpenPartialHomeomorph := hv
  subst u v
  have hfg := (StructureGroupoid.compatible (G := contDiffGroupoid ∞ I) hf hg).1
  let s := J.symm ⁻¹' ((f.trans e.toOpenPartialHomeomorph).symm.trans
    (g.trans e.toOpenPartialHomeomorph)).source ∩ range J
  have hmaps : MapsTo L.symm s (I.symm ⁻¹' (f.symm.trans g).source ∩ range I) := by
    intro x hx
    have he := hInv x hx.2
    refine ⟨?_, ?_⟩
    · change I.symm (L.symm x) ∈ (f.symm.trans g).source
      rw [he]
      simpa only [s, mfld_simps] using hx.1
    · obtain ⟨y, hy⟩ := hx.2
      refine ⟨e.symm y, ?_⟩
      apply L.injective
      rw [L.apply_symm_apply, ← hc, e.apply_symm_apply, hy]
  have hs := L.contDiff.comp_contDiffOn (hfg.comp L.symm.contDiff.contDiffOn hmaps)
  apply hs.congr
  intro x hx
  have he := hInv x hx.2
  change J (e (g (f.symm (e.symm (J.symm x))))) =
    L (I (g (f.symm (I.symm (L.symm x)))))
  rw [he, hc]

/-- New analytic-order strengthening, separate from the public ∞ theorem. -/
theorem modelChangedAtlas_analytic [IsManifold I ω X] :
    @IsManifold 𝕜 _ W _ _ H' _ J ω X _ (modelChangedAtlas e) := by
  let _ := modelChangedAtlas (X := X) e
  have hInv (x : W) (hx : x ∈ range J) : I.symm (L.symm x) = e.symm (J.symm x) := by
    obtain ⟨y, rfl⟩ := hx
    have hy : J y = L (I (e.symm y)) := by rw [← hc, e.apply_symm_apply]
    rw [hy, L.symm_apply_apply, I.left_inv]
    rw [← hy, J.left_inv]
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨f, hf, u, hu, rfl⟩ ⟨g, hg, v, hv, rfl⟩
  have hu' : u = e.toOpenPartialHomeomorph := hu
  have hv' : v = e.toOpenPartialHomeomorph := hv
  subst u v
  have hfg := (StructureGroupoid.compatible (G := contDiffGroupoid ω I) hf hg).1
  let s := J.symm ⁻¹' ((f.trans e.toOpenPartialHomeomorph).symm.trans
    (g.trans e.toOpenPartialHomeomorph)).source ∩ range J
  have hmaps : MapsTo L.symm s (I.symm ⁻¹' (f.symm.trans g).source ∩ range I) := by
    intro x hx
    have he := hInv x hx.2
    refine ⟨?_, ?_⟩
    · change I.symm (L.symm x) ∈ (f.symm.trans g).source
      rw [he]
      simpa only [s, mfld_simps] using hx.1
    · obtain ⟨y, hy⟩ := hx.2
      refine ⟨e.symm y, ?_⟩
      apply L.injective
      rw [L.apply_symm_apply, ← hc, e.apply_symm_apply, hy]
  have hs := L.contDiff.comp_contDiffOn (hfg.comp L.symm.contDiff.contDiffOn hmaps)
  apply hs.congr
  intro x hx
  have he := hInv x hx.2
  change J (e (g (f.symm (e.symm (J.symm x))))) =
    L (I (g (f.symm (I.symm (L.symm x)))))
  rw [he, hc]

theorem modelChangedAtlas_extChart (x : X) :
    (@extChartAt 𝕜 W X H' _ _ _ _ _ J (modelChangedAtlas e) x : X → W) =
      L ∘ (extChartAt I x : X → V) := by
  let _ := modelChangedAtlas (X := X) e
  funext y
  rw [Function.comp_apply, extChartAt_coe, extChartAt_coe, Function.comp_apply,
    modelChangedAtlas_chart, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  exact hc _

variable {V₀ H₀ N : Type*} [NormedAddCommGroup V₀] [NormedSpace 𝕜 V₀]
  [TopologicalSpace H₀] [TopologicalSpace N] [ChartedSpace H₀ N]
  (I₀ : ModelWithCorners 𝕜 V₀ H₀) (n : ℕ∞ω)

theorem modelChangedAtlas_contMDiff_iff (f : N → X) :
    @ContMDiff 𝕜 _ V₀ _ _ H₀ _ I₀ N _ _ W _ _ H' _ J X _
      (modelChangedAtlas e) n f ↔ ContMDiff I₀ I n f := by
  letI := modelChangedAtlas (X := X) e
  constructor
  · intro h x
    have hp := h x
    change ContMDiffWithinAt I₀ J n f univ x at hp
    change ContMDiffWithinAt I₀ I n f univ x
    rw [contMDiffWithinAt_iff] at hp ⊢
    refine ⟨hp.1, ?_⟩
    rw [modelChangedAtlas_extChart I J e L hc (f x), ← Function.comp_assoc] at hp
    exact L.comp_contDiffWithinAt_iff.mp hp.2
  · intro h x
    have hp := h x
    change ContMDiffWithinAt I₀ I n f univ x at hp
    change ContMDiffWithinAt I₀ J n f univ x
    rw [contMDiffWithinAt_iff] at hp ⊢
    refine ⟨hp.1, ?_⟩
    rw [modelChangedAtlas_extChart I J e L hc (f x), ← Function.comp_assoc]
    exact L.comp_contDiffWithinAt_iff.mpr hp.2

theorem modelChangedAtlas_contMDiffOn_iff (f : N → X) (s : Set N) :
    @ContMDiffOn 𝕜 _ V₀ _ _ H₀ _ I₀ N _ _ W _ _ H' _ J X _
      (modelChangedAtlas e) n f s ↔ ContMDiffOn I₀ I n f s := by
  letI := modelChangedAtlas (X := X) e
  constructor
  · intro h x hx
    have hp := h x hx
    rw [contMDiffWithinAt_iff] at hp ⊢
    refine ⟨hp.1, ?_⟩
    rw [modelChangedAtlas_extChart I J e L hc (f x), ← Function.comp_assoc] at hp
    exact L.comp_contDiffWithinAt_iff.mp hp.2
  · intro h x hx
    have hp := h x hx
    rw [contMDiffWithinAt_iff] at hp ⊢
    refine ⟨hp.1, ?_⟩
    rw [modelChangedAtlas_extChart I J e L hc (f x), ← Function.comp_assoc]
    exact L.comp_contDiffWithinAt_iff.mpr hp.2
end ModelChange

section EmbeddingTransport
variable {V W H H' X Y Z : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace H] [TopologicalSpace H']
  (I : ModelWithCorners ℝ V H) (J : ModelWithCorners ℝ W H')
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace H' Y]

theorem smoothEmbedding_diffeomorph_comp
    [TopologicalSpace Z] [ChartedSpace H' Z] [IsManifold J ∞ Z]
    (f : X → Y) (hf : Manifold.IsSmoothEmbedding I J ∞ f)
    (D : Diffeomorph J J Y Z ∞) :
    Manifold.IsSmoothEmbedding I J ∞ (D ∘ f) := by
  refine ⟨?_, D.toHomeomorph.isEmbedding.comp hf.isEmbedding⟩
  obtain ⟨C, hC, hC', hImm⟩ := hf.isImmersion
  let := hC
  let := hC'
  refine ⟨C, hC, hC', ?_⟩
  intro x
  let h := hImm x
  let c := D.symm.toHomeomorph.toOpenPartialHomeomorph.trans h.codChart
  have hc : c ∈ maximalAtlas J ∞ Z := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        D.symm.contMDiff.contMDiffOn (fun _ hy => hy.2)
    · exact D.contMDiff.comp_contMDiffOn
        ((contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mono (fun _ hy => hy.1))
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    ((D.contMDiff.comp hf.contMDiff).continuous.continuousAt) h.equiv h.domChart c
    h.mem_domChart_source (by exact ⟨mem_univ _, by simpa using h.mem_codChart_source⟩)
    h.domChart_mem_maximalAtlas hc
  intro z hz
  change J (h.codChart (D.symm (D (f ((h.domChart.extend I).symm z))))) = h.equiv (z, 0)
  rw [D.symm_apply_apply]
  exact h.writtenInCharts hz

theorem smoothEmbedding_diffeomorph_precomp
    [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
    (f : X → Y) (hf : Manifold.IsSmoothEmbedding I J ∞ f)
    (D : Diffeomorph I I Z X ∞) :
    Manifold.IsSmoothEmbedding I J ∞ (f ∘ D) := by
  refine ⟨?_, hf.isEmbedding.comp D.toHomeomorph.isEmbedding⟩
  obtain ⟨C, hC, hC', hImm⟩ := hf.isImmersion
  let := hC
  let := hC'
  refine ⟨C, hC, hC', ?_⟩
  intro x
  let h := hImm (D x)
  let c := D.toHomeomorph.toOpenPartialHomeomorph.trans h.domChart
  have hc : c ∈ maximalAtlas I ∞ Z := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).comp
        D.contMDiff.contMDiffOn (fun _ hy => hy.2)
    · exact D.symm.contMDiff.comp_contMDiffOn
        ((contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mono
          (fun _ hy => hy.1))
  have hxc : x ∈ c.source := by
    refine ⟨mem_univ _, ?_⟩
    simpa using h.mem_domChart_source
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    ((hf.contMDiff.comp D.contMDiff).continuous.continuousAt) h.equiv c h.codChart
    hxc h.mem_codChart_source hc h.codChart_mem_maximalAtlas
  intro z hz
  change J (h.codChart (f (D ((c.extend I).symm z)))) = h.equiv (z, 0)
  have hy : (c.extend I).symm z ∈ c.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (c.extend I).map_target hz
  have hcval : c ((c.extend I).symm z) = h.domChart (D ((c.extend I).symm z)) := rfl
  have hval : (h.domChart.extend I) (D ((c.extend I).symm z)) = z := by
    have h2 : (c.extend I) ((c.extend I).symm z) = z := (c.extend I).right_inv hz
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply] at h2
    rwa [hcval] at h2
  have hdom : D ((c.extend I).symm z) ∈ h.domChart.source := by
    have h := hy.2
    simp only [c, Set.mem_preimage, OpenPartialHomeomorph.symm_symm,
      Homeomorph.toOpenPartialHomeomorph_apply, Diffeomorph.coe_toHomeomorph] at h
    exact h
  have hzt : z ∈ (h.domChart.extend I).target := by
    rw [OpenPartialHomeomorph.extend_target_eq_image_source]
    exact ⟨D ((c.extend I).symm z), hdom, hval⟩
  have hsymm : D ((c.extend I).symm z) = (h.domChart.extend I).symm z :=
    (PartialEquiv.eq_symm_apply _ (by rwa [OpenPartialHomeomorph.extend_source]) hzt).mpr hval
  rw [hsymm]
  exact h.writtenInCharts hzt
end EmbeddingTransport
end
end SeifertSurfaces.LongitudeProducers.Transport
