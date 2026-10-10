import PiecewiseCompetitors
import Mathlib

open scoped Manifold ContDiff
open IsManifold Manifold
open Set Topology WithLp
noncomputable section
namespace SeifertSurfaces.MetricFoundations
open Foundations
universe u v w
set_option maxSynthPendingDepth 3

@[instance_reducible]
def chartedSpaceChangeModel {H : Type*} {H' : Type*} {X : Type*}
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace X]
    [ChartedSpace H X] (h : H ≃ₜ H') : ChartedSpace H' X where
  atlas := (fun e : OpenPartialHomeomorph X H => e.trans h.toOpenPartialHomeomorph) '' atlas H X
  chartAt x := (chartAt H x).trans h.toOpenPartialHomeomorph
  mem_chart_source x := by simp [mfld_simps]
  chart_mem_atlas x := ⟨chartAt H x, chart_mem_atlas H x, rfl⟩

theorem isManifold_changeModel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (h : H ≃ₜ H') (L : E ≃L[ℝ] E')
    (hI : ∀ z, I' (h z) = L (I z))
    (hinv : ∀ y, I.symm (L.symm y) = h.symm (I'.symm y))
    (n : ℕ∞ω) [IsManifold I n X] :
    @IsManifold ℝ _ E' _ _ H' _ I' n X _ (chartedSpaceChangeModel h) := by
  letI : ChartedSpace H' X := chartedSpaceChangeModel h
  apply isManifold_of_contDiffOn
  rintro e e' ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  have hold := (contDiffGroupoid n I).compatible ha hb
  have hc : ContDiffOn ℝ n (I ∘ a.symm.trans b ∘ I.symm)
      (I.symm ⁻¹' (a.symm.trans b).source ∩ range I) := hold.1
  have heq : (I' ∘ (a.trans h.toOpenPartialHomeomorph).symm.trans
        (b.trans h.toOpenPartialHomeomorph) ∘ I'.symm) =
      L ∘ (I ∘ a.symm.trans b ∘ I.symm) ∘ L.symm := by
    funext y
    change I' (h (b (a.symm (h.symm (I'.symm y))))) =
      L (I (b (a.symm (I.symm (L.symm y)))))
    rw [← hinv, hI]
  rw [heq]
  apply L.contDiff.comp_contDiffOn
    (hc.comp L.symm.contDiff.contDiffOn ?_)
  intro y hy
  constructor
  · simpa [mfld_simps, hinv] using hy.1
  · rcases hy.2 with ⟨z, rfl⟩
    refine ⟨h.symm z, ?_⟩
    have he := hI (h.symm z)
    simpa using congrArg L.symm he.symm

theorem contMDiff_changeModel_source
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
    {K : Type*} [TopologicalSpace K]
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace K Y]
    (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (J : ModelWithCorners ℝ F K) (h : H ≃ₜ H') (L : E ≃L[ℝ] E')
    (hI : ∀ z, I' (h z) = L (I z))
    (hinv : ∀ y, I.symm (L.symm y) = h.symm (I'.symm y))
    (n : ℕ∞ω) [IsManifold I n X] [IsManifold J n Y]
    (f : X → Y) (hf : ContMDiff I J n f) :
    (letI : ChartedSpace H' X := chartedSpaceChangeModel h;
      ContMDiff I' J n f) := by
  obtain ⟨hfc, hfd⟩ := contMDiff_iff.mp hf
  letI : ChartedSpace H' X := chartedSpaceChangeModel h
  letI : IsManifold I' n X := isManifold_changeModel I I' h L hI hinv n
  rw [contMDiff_iff]
  refine ⟨hfc, ?_⟩
  intro x y
  have hc := (hfd x y).comp L.symm.contDiff.contDiffOn
    (s := (extChartAt I' x).target ∩
      (extChartAt I' x).symm ⁻¹' f ⁻¹' (extChartAt J y).source) ?_
  · convert hc using 1
    funext z
    change J ((chartAt K y) (f ((chartAt H x).symm (h.symm (I'.symm z))))) =
      J ((chartAt K y) (f ((chartAt H x).symm (I.symm (L.symm z)))))
    rw [hinv]
  · intro z hz
    simp only [extChartAt_target, extChartAt_source, mem_inter_iff, mem_preimage] at hz ⊢
    change (I'.symm z ∈ ((chartAt H x).trans h.toOpenPartialHomeomorph).target ∧
      z ∈ range I') ∧
      f ((chartAt H x).symm (h.symm (I'.symm z))) ∈ (chartAt K y).source at hz
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [mfld_simps, hinv] using hz.1.1
    · rcases hz.1.2 with ⟨w, hw⟩
      refine ⟨h.symm w, ?_⟩
      have he := hI (h.symm w)
      simpa [hw] using congrArg L.symm he.symm
    · simpa [extChartAt, mfld_simps, hinv] using hz.2

theorem mfderiv_injective_changeModel_source
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
    {K : Type*} [TopologicalSpace K]
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace K Y]
    (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (J : ModelWithCorners ℝ F K) (h : H ≃ₜ H') (L : E ≃L[ℝ] E')
    (hI : ∀ z, I' (h z) = L (I z))
    (hinv : ∀ y, I.symm (L.symm y) = h.symm (I'.symm y))
    [IsManifold I 1 X] [IsManifold J 1 Y]
    (f : X → Y) (hf : ContMDiff I J 1 f) (x : X)
    (hrank : Function.Injective (mfderiv I J f x)) :
    (letI : ChartedSpace H' X := chartedSpaceChangeModel h;
      Function.Injective (mfderiv I' J f x)) := by
  have hdiff := (hf x).mdifferentiableAt (by simp)
  have hraw : Function.Injective (fderivWithin ℝ (writtenInExtChartAt I J x f)
      (range I) (extChartAt I x x)) := by
    intro a b hab
    have ht : (tangentSpaceCastModel I x).symm a =
        (tangentSpaceCastModel I x).symm b := by
      apply hrank
      simp only [mfderiv, if_pos hdiff, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
      exact congrArg (tangentSpaceCastModel J (f x)).symm hab
    simpa using congrArg (tangentSpaceCastModel I x) ht
  letI : ChartedSpace H' X := chartedSpaceChangeModel h
  letI : IsManifold I' 1 X := isManifold_changeModel I I' h L hI hinv 1
  have hnew := contMDiff_changeModel_source I I' J h L hI hinv 1 f hf
  have hnewdiff := (hnew x).mdifferentiableAt (by simp)
  have hcoord : writtenInExtChartAt I' J x f =
      writtenInExtChartAt I J x f ∘ L.symm := by
    funext z
    change J ((chartAt K (f x)) (f ((chartAt H x).symm (h.symm (I'.symm z))))) =
      J ((chartAt K (f x)) (f ((chartAt H x).symm (I.symm (L.symm z)))))
    rw [hinv]
  have hpoint : extChartAt I' x x = L (extChartAt I x x) := by
    change I' (h ((chartAt H x) x)) = L (I ((chartAt H x) x))
    exact hI _
  have hmaps : MapsTo L.symm (range I') (range I) := by
    rintro z ⟨w, rfl⟩
    refine ⟨h.symm w, ?_⟩
    have he := hI (h.symm w)
    simpa using congrArg L.symm he.symm
  have hder : fderivWithin ℝ (writtenInExtChartAt I' J x f) (range I')
      (extChartAt I' x x) =
      (fderivWithin ℝ (writtenInExtChartAt I J x f) (range I)
        (extChartAt I x x)).comp L.symm.toContinuousLinearMap := by
    rw [hcoord, hpoint]
    have hu : UniqueDiffWithinAt ℝ (range I') (L (extChartAt I x x)) := by
      rw [← hpoint]
      exact I'.uniqueDiffWithinAt_image
    have holdiff : DifferentiableWithinAt ℝ (writtenInExtChartAt I J x f)
        (range I) (L.symm (L (extChartAt I x x))) := by
      simpa using hdiff.differentiableWithinAt_writtenInExtChartAt
    rw [fderivWithin_comp _ holdiff
      L.symm.differentiableAt.differentiableWithinAt hmaps hu,
      L.symm.fderivWithin hu]
    simp
  intro a b hab
  apply (tangentSpaceCastModel I' x).injective
  apply L.symm.injective
  apply hraw
  apply (tangentSpaceCastModel J (f x)).symm.injective
  simpa only [mfderiv, if_pos hnewdiff, hder, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe] using hab

def quadrantProductLinear : (Euc 1 × Euc 1) ≃L[ℝ] Euc 2 :=
  (ContinuousLinearEquiv.prodCongr
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ))
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ))).trans
    ((LinearEquiv.finTwoArrow ℝ ℝ).symm.toContinuousLinearEquiv.trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm)

def quadrantProductHomeomorph :
    EuclideanHalfSpace 1 × EuclideanHalfSpace 1 ≃ₜ EuclideanQuadrant 2 where
  toFun p := ⟨toLp 2 ![p.1.val 0, p.2.val 0], by
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, PiLp.toLp_apply]
    · exact p.1.property
    · exact p.2.property⟩
  invFun q := (⟨toLp 2 (fun _ : Fin 1 => q.val 0), q.property 0⟩,
    ⟨toLp 2 (fun _ : Fin 1 => q.val 1), q.property 1⟩)
  left_inv p := by
    apply Prod.ext <;> apply Subtype.ext <;> apply PiLp.ext
    all_goals intro i; fin_cases i; rfl
  right_inv q := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem quadrantProduct_model_compatible (p : EuclideanHalfSpace 1 × EuclideanHalfSpace 1) :
    CornerModel (quadrantProductHomeomorph p) =
      quadrantProductLinear (((𝓡∂ 1).prod (𝓡∂ 1)) p) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [quadrantProductHomeomorph, quadrantProductLinear, LinearEquiv.finTwoArrow,
      modelWithCornersEuclideanHalfSpace_apply, ModelWithCorners.prod]

theorem quadrantProduct_model_inverse (y : Euc 2) :
    ((𝓡∂ 1).prod (𝓡∂ 1)).symm (quadrantProductLinear.symm y) =
      quadrantProductHomeomorph.symm (CornerModel.symm y) := by
  apply Prod.ext <;> apply Subtype.ext <;> apply PiLp.ext
  all_goals
    intro i
    fin_cases i
    simp [quadrantProductHomeomorph, quadrantProductLinear, LinearEquiv.finTwoArrow,
      modelWithCornersEuclideanHalfSpace_symm_apply,
      modelWithCornersEuclideanQuadrant_symm_apply, ModelWithCorners.prod]

abbrev CornerSquare := Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1

@[instance_reducible]
def cornerSquareCharted : ChartedSpace (EuclideanQuadrant 2) CornerSquare := by
  letI : ChartedSpace (EuclideanHalfSpace 1 × EuclideanHalfSpace 1) CornerSquare :=
    prodChartedSpace (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1)
      (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1)
  exact chartedSpaceChangeModel quadrantProductHomeomorph

theorem cornerSquare_isManifold :
    @IsManifold ℝ _ (Euc 2) _ _ (EuclideanQuadrant 2) _ CornerModel ∞
      CornerSquare _ cornerSquareCharted := by
  letI : ChartedSpace (EuclideanHalfSpace 1 × EuclideanHalfSpace 1) CornerSquare :=
    prodChartedSpace (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1)
      (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1)
  exact isManifold_changeModel ((𝓡∂ 1).prod (𝓡∂ 1)) CornerModel
    quadrantProductHomeomorph quadrantProductLinear
    quadrantProduct_model_compatible quadrantProduct_model_inverse ∞

def compactCornerSquare : CompactCornerPiece.{0} where
  carrier := CornerSquare
  charted := cornerSquareCharted
  smooth := cornerSquare_isManifold

def cornerSquareCoordinates (x : CornerSquare) : Euc 2 :=
  toLp 2 ![(x.1 : ℝ), (x.2 : ℝ)]

theorem cornerSquareCoordinates_contMDiff :
    (letI : ChartedSpace (EuclideanQuadrant 2) CornerSquare := cornerSquareCharted;
      ContMDiff CornerModel 𝓘(ℝ, Euc 2) ∞ cornerSquareCoordinates) := by
  letI : ChartedSpace (EuclideanHalfSpace 1 × EuclideanHalfSpace 1) CornerSquare :=
    prodChartedSpace (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1)
      (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1)
  have hfst : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun x : CornerSquare => (x.1 : ℝ)) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_fst
  have hsnd : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun x : CornerSquare => (x.2 : ℝ)) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_snd
  have hpair := hfst.prodMk_space hsnd
  let A : (ℝ × ℝ) ≃L[ℝ] Euc 2 :=
    (LinearEquiv.finTwoArrow ℝ ℝ).symm.toContinuousLinearEquiv.trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm
  have hcoord : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, Euc 2) ∞
      cornerSquareCoordinates := by
    convert A.contDiff.contMDiff.comp hpair using 1
    ext z i
    fin_cases i <;> rfl
  exact contMDiff_changeModel_source ((𝓡∂ 1).prod (𝓡∂ 1)) CornerModel
    𝓘(ℝ, Euc 2) quadrantProductHomeomorph quadrantProductLinear
    quadrantProduct_model_compatible quadrantProduct_model_inverse ∞
    cornerSquareCoordinates hcoord

theorem cornerSquareCoordinates_mfderiv_injective (x : CornerSquare) :
    (letI : ChartedSpace (EuclideanQuadrant 2) CornerSquare := cornerSquareCharted;
      Function.Injective (mfderiv CornerModel 𝓘(ℝ, Euc 2) cornerSquareCoordinates x)) := by
  letI : ChartedSpace (EuclideanHalfSpace 1 × EuclideanHalfSpace 1) CornerSquare :=
    prodChartedSpace (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1)
      (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1)
  have hval : IsImmersion (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞
      (Subtype.val : Icc (0 : ℝ) 1 → ℝ) :=
    isImmersionOfComplement_subtypeVal_Icc.isImmersion
  have hpair := hval.prodMap hval
  have hpairc : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun z : CornerSquare => ((z.1 : ℝ), (z.2 : ℝ))) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hpair.contMDiff
  have hpairinj : Function.Injective (mfderiv ((𝓡∂ 1).prod (𝓡∂ 1))
      𝓘(ℝ, ℝ × ℝ) (fun z : CornerSquare => ((z.1 : ℝ), (z.2 : ℝ))) x) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hpair.mfderiv_injective (by simp) x
  let A : (ℝ × ℝ) ≃L[ℝ] Euc 2 :=
    (LinearEquiv.finTwoArrow ℝ ℝ).symm.toContinuousLinearEquiv.trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm
  have heq : cornerSquareCoordinates = A ∘
      (fun z : CornerSquare => ((z.1 : ℝ), (z.2 : ℝ))) := by
    ext z i
    fin_cases i <;> rfl
  have hcoord : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, Euc 2) 1
      cornerSquareCoordinates := by
    rw [heq]
    exact A.contDiff.contMDiff.comp (hpairc.of_le (by simp))
  have hrank : Function.Injective
      (mfderiv ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, Euc 2) cornerSquareCoordinates x) := by
    rw [heq]
    rw [mfderiv_comp x A.isDiffImmersionAt.mdifferentiableAt
      ((hpairc x).mdifferentiableAt (by simp))]
    exact A.isDiffImmersionAt.mfderiv_injective.comp hpairinj
  exact mfderiv_injective_changeModel_source ((𝓡∂ 1).prod (𝓡∂ 1)) CornerModel
    𝓘(ℝ, Euc 2) quadrantProductHomeomorph quadrantProductLinear
    quadrantProduct_model_compatible quadrantProduct_model_inverse
    cornerSquareCoordinates hcoord x hrank

@[instance_reducible]
def chartedSpacePullback {H : Type*} {X : Type*} {Y : Type*}
    [TopologicalSpace H] [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace H X] (h : Y ≃ₜ X) : ChartedSpace H Y where
  atlas := (fun e : OpenPartialHomeomorph X H =>
    h.toOpenPartialHomeomorph.trans e) '' atlas H X
  chartAt y := h.toOpenPartialHomeomorph.trans (chartAt H (h y))
  mem_chart_source y := by simp [mfld_simps]
  chart_mem_atlas y := ⟨chartAt H (h y), chart_mem_atlas H (h y), rfl⟩

theorem isManifold_pullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X]
    (I : ModelWithCorners ℝ E H) (h : Y ≃ₜ X)
    (n : ℕ∞ω) [IsManifold I n X] :
    @IsManifold ℝ _ E _ _ H _ I n Y _ (chartedSpacePullback h) := by
  letI : ChartedSpace H Y := chartedSpacePullback h
  apply isManifold_of_contDiffOn
  rintro e e' ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  have hold := (contDiffGroupoid n I).compatible ha hb
  have hc : ContDiffOn ℝ n (I ∘ a.symm.trans b ∘ I.symm)
      (I.symm ⁻¹' (a.symm.trans b).source ∩ range I) := hold.1
  convert hc using 1
  · funext y
    simp [mfld_simps]
  · ext y
    simp [mfld_simps]

def liftedCompactCornerSquare : CompactCornerPiece.{u} := by
  letI : ChartedSpace (EuclideanQuadrant 2) CornerSquare := cornerSquareCharted
  letI : IsManifold CornerModel ∞ CornerSquare := cornerSquare_isManifold
  exact {
    carrier := ULift.{u} CornerSquare
    charted := chartedSpacePullback Homeomorph.ulift
    smooth := isManifold_pullback CornerModel Homeomorph.ulift ∞ }

end SeifertSurfaces.MetricFoundations
