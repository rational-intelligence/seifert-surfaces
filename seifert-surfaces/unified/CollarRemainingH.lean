import CollarRemainingC
import SuppliedChartHelpers
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option maxSynthPendingDepth 3
set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.LongitudeProducers.CollarCutHelpers.Remaining
open Foundations MetricFoundations
noncomputable section
section HalfCollar
variable {K : OrientedKnot} {T : TubularNeighborhood K} {F : SphereSpanningSurface.{0} K}
  {R : FramedRibbon T F} (C : CutSurface R)

structure HalfCollarTopology where
  map : Circle × Time → C.surface
  equation : ∀ p, C.inclusion (map p)=R.collar (p.1,affineHalfTime p.2)
  unique : ∀ p x, C.inclusion x=R.collar (p.1,affineHalfTime p.2) ↔ x=map p
  boundary : ∀ z, map (z,0)=C.boundary.toFun z
  continuous : Continuous map
  embedding : IsEmbedding map
  image : TopologicalSpace.Opens C.surface
  image_eq : (image : Set C.surface)=map '' {p : Circle × Time | (p.2:ℝ)<1}
  coordinates : (openTimeStrip 1) ≃ₜ image
  coordinates_eq : ∀ p, (coordinates p:C.surface)=map p.val

theorem H1_unique_half_collar : Nonempty (HalfCollarTopology C) := by
  classical
  have hex (p : Circle × Time) : ∃ x : C.surface, C.inclusion x=R.collar (p.1,affineHalfTime p.2) := by
    obtain ⟨x,hx,_⟩ := (cut_boundary_exact_level C).2.2.2 p.1 (affineHalfTime p.2)
      (by change (1/2:ℝ)≤1/2+(p.2:ℝ)/4; linarith [p.2.property.1])
    exact ⟨x,hx⟩
  let f : Circle × Time → C.surface := fun p => (hex p).choose
  have heq (p : Circle × Time) : C.inclusion (f p)=R.collar (p.1,affineHalfTime p.2) :=
    (hex p).choose_spec
  have huniq (p : Circle × Time) (x : C.surface) :
      C.inclusion x=R.collar (p.1,affineHalfTime p.2) ↔ x=f p := by
    constructor
    · intro hx
      exact C.embedding.injective (hx.trans (heq p).symm)
    · rintro rfl
      exact heq p
  have hboundary (z : Circle) : f (z,0)=C.boundary.toFun z := by
    apply (cut_boundary_exact_level C).1 _ z |>.mp
    have ht : affineHalfTime 0=halfTime := by
      apply Subtype.ext
      norm_num [affineHalfTime,halfTime]
    rw [←ht]
    exact heq (z,0)
  have htime : Continuous affineHalfTime := by
    apply Continuous.subtype_mk
    exact continuous_const.add (continuous_subtype_val.div_const 4)
  have hcont : Continuous f := by
    apply C.embedding.continuous_iff.mpr
    have hh : (C.inclusion ∘ f : Circle × Time → F.surface)=
        (fun p => R.collar (p.1,affineHalfTime p.2)) := funext heq
    rw [hh]
    exact R.collar_embedding.isEmbedding.continuous.comp
      (continuous_fst.prodMk (htime.comp continuous_snd))
  have hinj : Function.Injective f := by
    intro p q hpq
    have hh : (p.1,affineHalfTime p.2)=(q.1,affineHalfTime q.2) :=
      R.collar_embedding.isEmbedding.injective ((heq p).symm.trans
        ((congrArg C.inclusion hpq).trans (heq q)))
    have hz := congrArg (@Prod.fst Circle Time) hh
    refine Prod.ext hz ?_
    apply Subtype.ext
    have ht := congrArg (fun a : Circle × Time => (a.2:ℝ)) hh
    change 1/2+(p.2:ℝ)/4=1/2+(q.2:ℝ)/4 at ht
    linarith
  have hemb : IsEmbedding f := (hcont.isClosedEmbedding hinj).isEmbedding
  obtain ⟨U,hU,_⟩ := C1_open_substrip (ribbonSourceCollar R) (3/4) (7/8)
    (by norm_num) (by norm_num) (by norm_num)
  let V := C.inclusion ⁻¹' (U : Set F.surface)
  have hopen : IsOpen V := U.isOpen.preimage C.inclusion.continuous
  have himage : V=f '' {p : Circle × Time | (p.2:ℝ)<1} := by
    ext x
    constructor
    · intro hx
      change C.inclusion x ∈ (U : Set F.surface) at hx
      rw [hU] at hx
      obtain ⟨⟨z,t⟩,ht,hxt⟩ := hx
      change (t:ℝ)<3/4 at ht
      change R.collar (z,t)=C.inclusion x at hxt
      have htlo : (1/2:ℝ)≤(t:ℝ) := by
        by_contra h
        have hxcut : C.inclusion x ∈ cutSet R := by rw [←C.image_eq]; exact mem_range_self x
        exact hxcut ⟨(z,t),lt_of_not_ge h,hxt⟩
      let u : Time := ⟨4*((t:ℝ)-1/2),by constructor <;> linarith⟩
      have hu : (u:ℝ)<1 := by dsimp [u]; linarith
      have htimeeq : affineHalfTime u=t := by
        apply Subtype.ext
        change 1/2+(4*((t:ℝ)-1/2))/4=(t:ℝ)
        ring
      refine ⟨(z,u),hu,?_⟩
      apply Eq.symm
      apply (huniq (z,u) x).mp
      rw [htimeeq]
      exact hxt.symm
    · rintro ⟨⟨z,t⟩,ht,rfl⟩
      change C.inclusion (f (z,t)) ∈ (U : Set F.surface)
      rw [hU,heq]
      refine ⟨(z,affineHalfTime t),?_,rfl⟩
      change 1/2+(t:ℝ)/4<3/4
      change (t:ℝ)<1 at ht
      linarith
  let image : TopologicalSpace.Opens C.surface := ⟨V,hopen⟩
  let f1 : openTimeStrip 1 → C.surface := fun p => f p.val
  have he1 : IsEmbedding f1 := hemb.comp IsEmbedding.subtypeVal
  have hr : Set.range f1=(image : Set C.surface) := by
    change Set.range f1=V
    rw [himage]
    ext x
    constructor
    · rintro ⟨p,rfl⟩
      exact ⟨p.val,p.property,rfl⟩
    · rintro ⟨p,hp,rfl⟩
      exact ⟨⟨p,hp⟩,rfl⟩
  let e := he1.toHomeomorph.trans (Homeomorph.setCongr hr)
  exact ⟨{ map := f
           equation := heq
           unique := huniq
           boundary := hboundary
           continuous := hcont
           embedding := hemb
           image := image
           image_eq := himage
           coordinates := e
           coordinates_eq := fun _ => rfl }⟩


theorem H2_half_collar_smooth_inverse (A : HalfCollarTopology C) :
    ContMDiff CollarModel (𝓡∂ 2) ∞ A.map ∧
      ContMDiff CollarModel (𝓡∂ 2) ∞ A.coordinates ∧
      ContMDiff (𝓡∂ 2) CollarModel ∞ A.coordinates.symm := by
  have ht : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ affineHalfTime := by
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    refine ⟨?_,?_⟩
    · exact (continuous_const.add (continuous_subtype_val.div_const 4)).subtype_mk _
    · exact contMDiff_const.add (contMDiff_subtypeVal_Icc.div_const 4)
  have hmap : ContMDiff CollarModel (𝓡∂ 2) ∞ A.map := by
    apply (ContMDiff.iff_comp_isImmersion C.smooth_embedding.isImmersion).mpr
    refine ⟨A.continuous,?_⟩
    have heq : C.inclusion ∘ A.map=(fun p => R.collar (p.1,affineHalfTime p.2)) :=
      funext A.equation
    rw [heq]
    exact R.collar_embedding.contMDiff.comp
      (contMDiff_fst.prodMk (ht.comp contMDiff_snd))
  have hf : ContMDiff CollarModel (𝓡∂ 2) ∞ A.coordinates := by
    apply (ContMDiff.subtypeVal_comp_iff A.image A.coordinates).mp
    have he : (Subtype.val ∘ A.coordinates : openTimeStrip 1 → C.surface)=A.map ∘ Subtype.val :=
      funext A.coordinates_eq
    rw [he]
    exact hmap.comp contMDiff_subtype_val
  have he : A.map ∘ (Subtype.val ∘ A.coordinates.symm)=(Subtype.val : A.image → C.surface) := by
    funext y
    rw [Function.comp_apply,Function.comp_apply,←A.coordinates_eq,A.coordinates.apply_symm_apply]
  let u : A.image → Circle × Time := fun y =>
    ((A.coordinates.symm y).val.1,affineHalfTime (A.coordinates.symm y).val.2)
  have hu : ContMDiff (𝓡∂ 2) CollarModel ∞ u := by
    apply (ContMDiff.iff_comp_isImmersion R.collar_embedding.isImmersion).mpr
    refine ⟨?_,?_⟩
    · exact (continuous_fst.comp (continuous_subtype_val.comp A.coordinates.symm.continuous)).prodMk
        ((continuous_const.add (continuous_subtype_val.div_const 4)).subtype_mk _ |>.comp
          (continuous_snd.comp (continuous_subtype_val.comp A.coordinates.symm.continuous)))
    · have hcomp : (R.collar ∘ u : A.image → F.surface)=C.inclusion ∘ Subtype.val := by
        funext y
        change R.collar ((A.coordinates.symm y).val.1,affineHalfTime (A.coordinates.symm y).val.2)=C.inclusion y.val
        rw [←A.equation]
        have h := congrFun he y
        exact congrArg C.inclusion h
      rw [hcomp]
      exact C.smooth_embedding.contMDiff.comp contMDiff_subtype_val
  have hinv : ContMDiff (𝓡∂ 2) CollarModel ∞ A.coordinates.symm := by
    apply (ContMDiff.subtypeVal_comp_iff (openTimeStrip 1) A.coordinates.symm).mp
    have hf1 : ContMDiff (𝓡∂ 2) (𝓡 1) ∞ (fun y : A.image => (A.coordinates.symm y).val.1) := by
      change ContMDiff (𝓡∂ 2) (𝓡 1) ∞ (Prod.fst ∘ u)
      exact contMDiff_fst.comp hu
    have hf2 : ContMDiff (𝓡∂ 2) (𝓡∂ 1) ∞ (fun y : A.image => (A.coordinates.symm y).val.2) := by
      apply contMDiff_iff_comp_subtypeVal_Icc.mpr
      refine ⟨continuous_snd.comp (continuous_subtype_val.comp A.coordinates.symm.continuous),?_⟩
      have hs : ContMDiff (𝓡∂ 2) 𝓘(ℝ,ℝ) ∞ (fun y : A.image => 4*((u y).2:ℝ)-2) :=
        (contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp (contMDiff_snd.comp hu))).sub contMDiff_const
      have hh : (fun y : A.image => 4*((u y).2:ℝ)-2)=
          (fun y : A.image => ((A.coordinates.symm y).val.2:ℝ)) := by
        funext y
        change 4*(1/2+((A.coordinates.symm y).val.2:ℝ)/4)-2=_
        ring
      rw [hh] at hs
      exact hs
    exact hf1.prodMk hf2
  exact ⟨hmap,hf,hinv⟩


theorem H3_full_half_collar (A : HalfCollarTopology C) :
    Manifold.IsSmoothEmbedding CollarModel (𝓡∂ 2) ∞ A.map ∧
    (∀ p (w : TangentSpace CollarModel p),
      mfderiv (𝓡∂ 2) (𝓡∂ 2) C.inclusion (A.map p)
        (mfderiv CollarModel (𝓡∂ 2) A.map p w) =
      mfderiv CollarModel (𝓡∂ 2) (fun q => R.collar (q.1,affineHalfTime q.2)) p w) ∧
    (∀ z, 0 < inwardCoordinate (C.boundary.toFun z)
      (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => A.map (z,t)) 0 timeUnit)) ∧
    ∃ k : GivenCutHalfCollar C, k.map=A.map ∧ k.image=A.image ∧
      HEq k.coordinates.toHomeomorph A.coordinates := by
  have hlower {K : OrientedKnot} {T : TubularNeighborhood K} {F : SphereSpanningSurface.{0} K}
      {R : FramedRibbon T F} (C : CutSurface R) (A : HalfCollarTopology C)
      (p : Circle × Time) (hp : (p.2:ℝ)<1) :
      Manifold.IsImmersionAtOfComplement (Euc 0) CollarModel (𝓡∂ 2) ∞ A.map p := by
    have hbridge (B : CollarModelBridge) :
        ContMDiff CollarModel (𝓡∂ 2) ∞ B.homeo ∧
          ContMDiff (𝓡∂ 2) CollarModel ∞ B.homeo.symm := by
      have hf : (fun p => (𝓡∂ 2).symm (B.linear (CollarModel p)))=B.homeo := by
        funext p
        rw [←B.compatible p]
        exact (𝓡∂ 2).left_inv _
      have hi : (fun p => CollarModel.symm (B.linear.symm ((𝓡∂ 2) p)))=B.homeo.symm := by
        funext p
        have he := B.compatible (B.homeo.symm p)
        rw [B.homeo.apply_symm_apply] at he
        rw [he,B.linear.symm_apply_apply]
        exact CollarModel.left_inv _
      have hc : ContMDiff CollarModel 𝓘(ℝ,Euc 1 × Euc 1) ∞
          (fun p : Euc 1 × EuclideanHalfSpace 1 => (p.1,(𝓡∂ 1) p.2)) := by
        rw [modelWithCornersSelf_prod,←chartedSpaceSelf_prod]
        exact contMDiff_fst.prodMk ((𝓡∂ 1).contMDiff.comp contMDiff_snd)
      constructor
      · rw [←hf]
        apply (𝓡∂ 2).contMDiffOn_symm.comp_contMDiff
          (B.linear.contDiff.contMDiff.comp hc)
        intro p
        change B.linear (CollarModel p) ∈ range (𝓡∂ 2)
        rw [←B.compatible p]
        exact mem_range_self _
      · rw [←hi]
        have hh := B.linear.symm.contDiff.contMDiff.comp (𝓡∂ 2).contMDiff (n:=∞)
        rw [modelWithCornersSelf_prod,←chartedSpaceSelf_prod] at hh
        exact hh.fst.prodMk ((𝓡∂ 1).contMDiffOn_symm.comp_contMDiff hh.snd (by
          intro p
          have he := B.compatible (B.homeo.symm p)
          rw [B.homeo.apply_symm_apply] at he
          rw [he,B.linear.symm_apply_apply]
          exact mem_range_self _))
    have hinc {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
        {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
        {M : Type} [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] (U : TopologicalSpace.Opens M) (hne : Nonempty U) :
        ∃ d : PartialDiffeomorph I I U M ∞,
          (∀ x, d x=x.val) ∧ d.source=univ ∧ d.target=(U:Set M) := by
      let e := U.openPartialHomeomorphSubtypeCoe hne
      have hi : ContMDiffOn I I ∞ e.symm e.target := by
        intro x hx
        apply (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target x).mp
        have heq : EqOn (Subtype.val ∘ e.symm) id e.target :=
          fun y hy => e.right_inv hy
        exact (contMDiffOn_id.congr (fun y hy => heq hy)) x hx
      exact ⟨{ toPartialEquiv := e.toPartialEquiv
               open_source := e.open_source
               open_target := e.open_target
               contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
               contMDiffOn_invFun := hi },fun _ => rfl,rfl,
        U.openPartialHomeomorphSubtypeCoe_target hne⟩
    let l₂ : (Euc 1 × Euc 1) ≃ₗ[ℝ] Euc 2 :=
      { toFun := fun p => !₂[p.2 0, p.1 0]
        invFun := fun w => (!₂[w 1], !₂[w 0])
        left_inv := by
          intro p
          apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
        right_inv := by intro w; ext i; fin_cases i <;> rfl
        map_add' := by intro p q; ext i; fin_cases i <;> rfl
        map_smul' := by intro r p; ext i; fin_cases i <;> rfl }
    let L₂ := l₂.toContinuousLinearEquiv
    let e₂ : (Euc 1 × EuclideanHalfSpace 1) ≃ EuclideanHalfSpace 2 :=
      { toFun := fun p => ⟨L₂ (p.1, p.2.val), p.2.property⟩
        invFun := fun w => ((L₂.symm w.val).1, ⟨(L₂.symm w.val).2, w.property⟩)
        left_inv := by
          intro p
          refine Prod.ext ?_ ?_
          · ext i; fin_cases i; rfl
          · apply Subtype.ext; ext i; fin_cases i; rfl
        right_inv := by
          intro w
          apply Subtype.ext
          exact L₂.apply_symm_apply w.val }
    let h₂ : (Euc 1 × EuclideanHalfSpace 1) ≃ₜ EuclideanHalfSpace 2 :=
      { toEquiv := e₂
        continuous_toFun := (L₂.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
        continuous_invFun :=
          ((continuous_fst.comp (L₂.symm.continuous.comp continuous_subtype_val)).prodMk
            ((continuous_snd.comp (L₂.symm.continuous.comp continuous_subtype_val)).subtype_mk _)) }
    let B : CollarModelBridge :=
      { homeo := h₂
        linear := L₂
        formula := fun _ => rfl
        linear_formula := fun _ => rfl
        compatible := fun _ => rfl }
    let ps : openTimeStrip 1 := ⟨p,hp⟩
    obtain ⟨incA,hincA,hincAs,hincAt⟩ := hinc (I:=𝓡∂ 2) A.image ⟨A.coordinates ps⟩
    obtain ⟨incS,hincS,hincSs,hincSt⟩ := hinc (I:=CollarModel) (openTimeStrip 1) ⟨ps⟩
    let dc : Diffeomorph CollarModel (𝓡∂ 2) (openTimeStrip 1) A.image ∞ :=
      ⟨A.coordinates.toEquiv,(H2_half_collar_smooth_inverse C A).2.1,(H2_half_collar_smooth_inverse C A).2.2⟩
    let cc := chartAt (Euc 1) p.1
    have hcc : cc∈IsManifold.maximalAtlas (𝓡 1) ∞ Circle := IsManifold.chart_mem_maximalAtlas _
    have hct : IccLeftChart 0 1∈IsManifold.maximalAtlas (𝓡∂ 1) ∞ Time := by
      rw [←Icc_chartedSpaceChartAt_of_le_top (z:=(0:Time)) (by norm_num)]
      exact IsManifold.chart_mem_maximalAtlas _
    let dom := cc.prod (IccLeftChart 0 1)
    have hdom : dom∈IsManifold.maximalAtlas CollarModel ∞ (Circle × Time) :=
      IsManifold.mem_maximalAtlas_prod hcc hct
    let cd : PartialDiffeomorph CollarModel CollarModel (Circle × Time) (Euc 1 × EuclideanHalfSpace 1) ∞ :=
      { toPartialEquiv := dom.toPartialEquiv
        open_source := dom.open_source
        open_target := dom.open_target
        contMDiffOn_toFun := by
          have h := contMDiffOn_of_mem_maximalAtlas hdom
          simp_rw +instances [ModelProd,←chartedSpaceSelf_prod] at h
          exact h
        contMDiffOn_invFun := by
          have h := contMDiffOn_symm_of_mem_maximalAtlas hdom
          simp_rw +instances [ModelProd,←chartedSpaceSelf_prod] at h
          exact h }
    let db : Diffeomorph CollarModel (𝓡∂ 2) (Euc 1 × EuclideanHalfSpace 1) (EuclideanHalfSpace 2) ∞ :=
      ⟨B.homeo.toEquiv,(hbridge B).1,(hbridge B).2⟩
    let codD := (((incA.symm.trans dc.symm.toPartialDiffeomorph).trans incS).trans cd).trans db.toPartialDiffeomorph
    let cod := codD.toOpenPartialHomeomorph
    have hcod : cod∈IsManifold.maximalAtlas (𝓡∂ 2) ∞ C.surface :=
      cod.mem_maximalAtlas_of_contMDiffOn codD.contMDiffOn_toFun codD.contMDiffOn_invFun
    have hmem (q : Circle × Time) (hq : q∈dom.source) :
        A.map q∈cod.source ∧ cod (A.map q)=B.homeo (dom q) := by
      let qs : openTimeStrip 1 := ⟨q,hq.2⟩
      have he : incA (dc qs)=A.map q := (hincA _).trans (A.coordinates_eq qs)
      have hin : dc qs∈incA.source := by rw [hincAs]; trivial
      have hi : incA.symm (A.map q)=dc qs := by rw [←he]; exact incA.toOpenPartialHomeomorph.left_inv hin
      have hc : dc.symm (incA.symm (A.map q))=qs := by rw [hi,dc.symm_apply_apply]
      have hv : incS (dc.symm (incA.symm (A.map q)))=q := by rw [hc,hincS]
      constructor
      · change ((((A.map q∈incA.target ∧ incA.symm (A.map q)∈univ) ∧
          dc.symm (incA.symm (A.map q))∈incS.source) ∧
          incS (dc.symm (incA.symm (A.map q)))∈cd.source) ∧
          cd (incS (dc.symm (incA.symm (A.map q))))∈univ)
        rw [hincAt,hincSs,hv]
        exact ⟨⟨⟨⟨by rw [←he,hincA]; exact (dc qs).property,mem_univ _⟩,mem_univ _⟩,hq⟩,mem_univ _⟩
      · change B.homeo (dom (incS (dc.symm (incA.symm (A.map q)))))=_
        rw [hv]
    let L := (ContinuousLinearEquiv.prodUnique ℝ (Euc 1 × Euc 1) (Euc 0)).trans B.linear
    have hpdom : p∈dom.source := ⟨mem_chart_source _ _,hp⟩
    apply Manifold.IsImmersionAtOfComplement.mk_of_charts (I:=CollarModel) (J:=𝓡∂ 2) L dom cod hpdom (hmem p hpdom).1 hdom hcod
    · exact fun q hq => (hmem q hq).1
    · intro u hu
      let q := (dom.extend CollarModel).symm u
      have hq : q∈dom.source := by simpa only [OpenPartialHomeomorph.extend_source] using (dom.extend CollarModel).map_target hu
      change (𝓡∂ 2) (cod (A.map q))=L (u,0)
      rw [(hmem q hq).2,B.compatible]
      change B.linear ((dom.extend CollarModel) q)=B.linear u
      rw [(dom.extend CollarModel).right_inv hu]
  have hinclusion {K : OrientedKnot} {T : TubularNeighborhood K} {F : SphereSpanningSurface.{0} K}
      {R : FramedRibbon T F} (C : CutSurface R) (x : C.surface)
      (hx : (𝓡∂ 2).IsInteriorPoint x) (hix : (𝓡∂ 2).IsInteriorPoint (C.inclusion x)) :
      IsLocalDiffeomorphAt (𝓡∂ 2) (𝓡∂ 2) ∞ C.inclusion x := by
    have hflat (n : ℕ) [NeZero n] :
        ∃ j : OpenPartialHomeomorph (Euc n) (EuclideanHalfSpace n),
          j.source={u | 0<u 0} ∧ j.target={u | 0<(Subtype.val u) 0} ∧
          (∀ u, j u=(𝓡∂ n).symm u) ∧ (∀ u, j.symm u=(𝓡∂ n) u) ∧
          ContMDiffOn (𝓡 n) (𝓡∂ n) ∞ j j.source ∧
          ContMDiffOn (𝓡∂ n) (𝓡 n) ∞ j.symm j.target := by
      let S : Set (Euc n) := {u | 0<u 0}
      let V : Set (EuclideanHalfSpace n) := {u | 0<(Subtype.val u) 0}
      have hS : S ⊆ range (𝓡∂ n) := by
        intro u hu
        change 0<u 0 at hu
        rw [range_modelWithCornersEuclideanHalfSpace]
        exact hu.le
      let j : OpenPartialHomeomorph (Euc n) (EuclideanHalfSpace n) :=
        { toFun := (𝓡∂ n).symm
          invFun := (𝓡∂ n)
          source := S
          target := V
          map_source' := by
            intro u hu
            change 0<(𝓡∂ n) ((𝓡∂ n).symm u) 0
            rw [(𝓡∂ n).right_inv (hS hu)]
            exact hu
          map_target' := by intro u hu; exact hu
          left_inv' := fun u hu => (𝓡∂ n).right_inv (hS hu)
          right_inv' := fun u _ => (𝓡∂ n).left_inv u
          open_source := isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous
          open_target := isOpen_lt continuous_const ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val)
          continuousOn_toFun := (𝓡∂ n).continuous_symm.continuousOn
          continuousOn_invFun := (𝓡∂ n).continuous.continuousOn }
      exact ⟨j,rfl,rfl,fun _ => rfl,fun _ => rfl,
        (𝓡∂ n).contMDiffOn_symm.mono hS,(𝓡∂ n).contMDiff.contMDiffOn⟩
    
    let h := C.smooth_embedding.isImmersion.isImmersionAt x
    let a := h.domChart
    let b := h.codChart
    let L : Euc 2 →L[ℝ] Euc 2 := h.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Euc 2) h.complement)
    have hLinj : Function.Injective L := by
      intro u v huv
      exact congrArg Prod.fst (h.equiv.injective huv)
    have hLsurj : Function.Surjective L :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rfl) (f:=L.toLinearMap)).mp hLinj
    let le : Euc 2 ≃L[ℝ] Euc 2 := (LinearEquiv.ofBijective L.toLinearMap ⟨hLinj,hLsurj⟩).toContinuousLinearEquiv
    let dl : Diffeomorph (𝓡 2) (𝓡 2) (Euc 2) (Euc 2) ∞ :=
      ⟨le.toEquiv,le.contDiff.contMDiff,le.symm.contDiff.contMDiff⟩
    let ac : PartialDiffeomorph (𝓡∂ 2) (𝓡∂ 2) C.surface (EuclideanHalfSpace 2) ∞ :=
      { toPartialEquiv := a.toPartialEquiv
        open_source := a.open_source
        open_target := a.open_target
        contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
        contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas }
    let bc : PartialDiffeomorph (𝓡∂ 2) (𝓡∂ 2) F.surface (EuclideanHalfSpace 2) ∞ :=
      { toPartialEquiv := b.toPartialEquiv
        open_source := b.open_source
        open_target := b.open_target
        contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
        contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas }
    obtain ⟨j,hjs,hjt,hj,hji,hjdiff,hjidiff⟩ := hflat 2
    let jd : PartialDiffeomorph (𝓡 2) (𝓡∂ 2) (Euc 2) (EuclideanHalfSpace 2) ∞ :=
      { toPartialEquiv := j.toPartialEquiv
        open_source := j.open_source
        open_target := j.open_target
        contMDiffOn_toFun := hjdiff
        contMDiffOn_invFun := hjidiff }
    let df := (((ac.trans jd.symm).trans dl.toPartialDiffeomorph).trans jd).trans bc.symm
    have hcoord (y : C.surface) (hy : y∈a.source) : (𝓡∂ 2) (b (C.inclusion y))=L ((𝓡∂ 2) (a y)) := by
      have hu := (a.extend (𝓡∂ 2)).map_source (by simpa only [OpenPartialHomeomorph.extend_source] using hy)
      have hh := h.writtenInCharts hu
      change (b.extend (𝓡∂ 2)) (C.inclusion ((a.extend (𝓡∂ 2)).symm ((a.extend (𝓡∂ 2)) y)))=
        h.equiv ((a.extend (𝓡∂ 2)) y,0) at hh
      rw [(a.extend (𝓡∂ 2)).left_inv (by simpa only [OpenPartialHomeomorph.extend_source] using hy)] at hh
      exact hh
    have haj (y : C.surface) (hy : y∈a.source) : j (le (j.symm (a y)))=b (C.inclusion y) := by
      rw [hji,hj]
      change (𝓡∂ 2).symm (L ((𝓡∂ 2) (a y)))=b (C.inclusion y)
      rw [←hcoord y hy]
      exact (𝓡∂ 2).left_inv _
    have haPos : 0<(a x).val 0 := by
      have hd : IsLocalDiffeomorphAt (𝓡∂ 2) (𝓡∂ 2) ∞ a x := ⟨ac,h.mem_domChart_source,fun _ _ => rfl⟩
      have hh := (hd.isInteriorPoint_iff (by simp)).mp hx
      simpa [ModelWithCorners.IsInteriorPoint,extChartAt,interior_range_modelWithCornersEuclideanHalfSpace] using hh
    have hbPos : 0<(b (C.inclusion x)).val 0 := by
      have hd : IsLocalDiffeomorphAt (𝓡∂ 2) (𝓡∂ 2) ∞ b (C.inclusion x) := ⟨bc,h.mem_codChart_source,fun _ _ => rfl⟩
      have hh := (hd.isInteriorPoint_iff (by simp)).mp hix
      simpa [ModelWithCorners.IsInteriorPoint,extChartAt,interior_range_modelWithCornersEuclideanHalfSpace] using hh
    have hdp : x∈df.source := by
      change ((((x∈a.source ∧ a x∈j.target) ∧ j.symm (a x)∈univ) ∧ le (j.symm (a x))∈j.source) ∧
        j (le (j.symm (a x)))∈b.target)
      refine ⟨⟨⟨⟨h.mem_domChart_source,?_⟩,mem_univ _⟩,?_⟩,?_⟩
      · rw [hjt]; exact haPos
      · rw [hjs,hji]
        change 0<L ((𝓡∂ 2) (a x)) 0
        rw [←hcoord x h.mem_domChart_source]
        exact hbPos
      · rw [haj x h.mem_domChart_source]
        exact b.map_source h.mem_codChart_source
    refine ⟨df,hdp,?_⟩
    intro y hy
    have hya : y∈a.source := hy.1.1.1.1
    change C.inclusion y=b.symm (j (le (j.symm (a y))))
    rw [haj y hya]
    exact (b.left_inv (h.isImmersionAtOfComplement_complement.mapsto_domChart_source_codChart_source hya)).symm
  have hupper {K : OrientedKnot} {T : TubularNeighborhood K} {F : SphereSpanningSurface.{0} K}
      (R : FramedRibbon T F) (p : Circle × Time) (hp : (p.2:ℝ)=1) :
      Manifold.IsImmersionAtOfComplement (Euc 0) CollarModel (𝓡∂ 2) ∞
        (fun q : Circle × Time => R.collar (q.1,affineHalfTime q.2)) p := by
    let c := ribbonSourceCollar R
    let a : ℝ := 1/4
    have ha : 0<a := by norm_num [a]
    have ha1 : a<1 := by norm_num [a]
    have hflat (n : ℕ) [NeZero n] :
        ∃ j : OpenPartialHomeomorph (Euc n) (EuclideanHalfSpace n),
          j.source={u | 0<u 0} ∧ j.target={u | 0<(Subtype.val u) 0} ∧
          (∀ u, j u=(𝓡∂ n).symm u) ∧ (∀ u, j.symm u=(𝓡∂ n) u) ∧
          ContMDiffOn (𝓡 n) (𝓡∂ n) ∞ j j.source ∧
          ContMDiffOn (𝓡∂ n) (𝓡 n) ∞ j.symm j.target := by
      let S : Set (Euc n) := {u | 0<u 0}
      let V : Set (EuclideanHalfSpace n) := {u | 0<(Subtype.val u) 0}
      have hS : S ⊆ range (𝓡∂ n) := by
        intro u hu
        change 0<u 0 at hu
        rw [range_modelWithCornersEuclideanHalfSpace]
        exact hu.le
      let j : OpenPartialHomeomorph (Euc n) (EuclideanHalfSpace n) :=
        { toFun := (𝓡∂ n).symm
          invFun := (𝓡∂ n)
          source := S
          target := V
          map_source' := by
            intro u hu
            change 0<(𝓡∂ n) ((𝓡∂ n).symm u) 0
            rw [(𝓡∂ n).right_inv (hS hu)]
            exact hu
          map_target' := by intro u hu; exact hu
          left_inv' := fun u hu => (𝓡∂ n).right_inv (hS hu)
          right_inv' := fun u _ => (𝓡∂ n).left_inv u
          open_source := isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous
          open_target := isOpen_lt continuous_const ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val)
          continuousOn_toFun := (𝓡∂ n).continuous_symm.continuousOn
          continuousOn_invFun := (𝓡∂ n).continuous.continuousOn }
      exact ⟨j,rfl,rfl,fun _ => rfl,fun _ => rfl,
        (𝓡∂ n).contMDiffOn_symm.mono hS,(𝓡∂ n).contMDiff.contMDiffOn⟩
    
    have hinc {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
        {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
        {M : Type} [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] (U : TopologicalSpace.Opens M) (hne : Nonempty U) :
        ∃ d : PartialDiffeomorph I I U M ∞,
          (∀ x, d x=x.val) ∧ d.source=univ ∧ d.target=(U:Set M) := by
      let e := U.openPartialHomeomorphSubtypeCoe hne
      have hi : ContMDiffOn I I ∞ e.symm e.target := by
        intro x hx
        apply (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target x).mp
        have heq : EqOn (Subtype.val ∘ e.symm) id e.target :=
          fun y hy => e.right_inv hy
        exact (contMDiffOn_id.congr (fun y hy => heq hy)) x hx
      exact ⟨{ toPartialEquiv := e.toPartialEquiv
               open_source := e.open_source
               open_target := e.open_target
               contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
               contMDiffOn_invFun := hi },fun _ => rfl,rfl,
        U.openPartialHomeomorphSubtypeCoe_target hne⟩
    obtain ⟨j1,hj1s,hj1t,hj1,hj1inv,hj1smooth,hj1invsmooth⟩ := hflat 1
    obtain ⟨j2,hj2s,hj2t,hj2,hj2inv,hj2smooth,hj2invsmooth⟩ := hflat 2
    let jd1 : PartialDiffeomorph (𝓡 1) (𝓡∂ 1) (Euc 1) (EuclideanHalfSpace 1) ∞ :=
      { toPartialEquiv := j1.toPartialEquiv
        open_source := j1.open_source
        open_target := j1.open_target
        contMDiffOn_toFun := hj1smooth
        contMDiffOn_invFun := hj1invsmooth }
    let jd2 : PartialDiffeomorph (𝓡 2) (𝓡∂ 2) (Euc 2) (EuclideanHalfSpace 2) ∞ :=
      { toPartialEquiv := j2.toPartialEquiv
        open_source := j2.open_source
        open_target := j2.open_target
        contMDiffOn_toFun := hj2smooth
        contMDiffOn_invFun := hj2invsmooth }
    have hleft : IccLeftChart 0 1 ∈ IsManifold.maximalAtlas (𝓡∂ 1) ∞ Time := by
      rw [←Icc_chartedSpaceChartAt_of_le_top (z:=(0:Time)) (by norm_num)]
      exact IsManifold.chart_mem_maximalAtlas _
    have hright : IccRightChart 0 1 ∈ IsManifold.maximalAtlas (𝓡∂ 1) ∞ Time := by
      rw [←Icc_chartedSpaceChartAt_of_top_le (z:=(1:Time)) (by norm_num)]
      exact IsManifold.chart_mem_maximalAtlas _
    let td : PartialDiffeomorph (𝓡∂ 1) (𝓡∂ 1) Time (EuclideanHalfSpace 1) ∞ :=
      { toPartialEquiv := (IccLeftChart 0 1).toPartialEquiv
        open_source := (IccLeftChart 0 1).open_source
        open_target := (IccLeftChart 0 1).open_target
        contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hleft
        contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hleft }
    let tf := td.trans jd1.symm
    let cc := chartAt (Euc 1) p.1
    let v : Euc 1 := !₂[1-(cc p.1) 0]
    let dc : Diffeomorph (𝓡 1) (𝓡 1) (Euc 1) (Euc 1) ∞ :=
      ⟨(Homeomorph.addLeft v).toEquiv,contMDiff_const.add contMDiff_id,contMDiff_const.add contMDiff_id⟩
    let cs := cc.trans dc.toHomeomorph.toOpenPartialHomeomorph
    have hcs : cs ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle := by
      apply cs.mem_maximalAtlas_of_contMDiffOn
      · exact dc.contMDiff.comp_contMDiffOn
          ((contMDiffOn_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p.1)).mono inter_subset_left)
      · exact (contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p.1)).comp
          dc.symm.contMDiff.contMDiffOn (fun _ h => h.2)
    let O : Set Circle := cs.source ∩ cs ⁻¹' {u : Euc 1 | 0<u 0}
    have hO : IsOpen O := cs.isOpen_inter_preimage (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous)
    let cp := cs.restr O
    have hcpSource : cp.source=O := by
      simp only [cp,OpenPartialHomeomorph.restr_source,hO.interior_eq]
      exact inter_eq_right.mpr inter_subset_left
    have hcp : cp ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle := restr_mem_maximalAtlas _ hcs hO
    have hpcc : p.1 ∈ cp.source := by
      rw [hcpSource]
      refine ⟨⟨mem_chart_source _ _,mem_univ _⟩,?_⟩
      change 0 < (v + cc p.1) 0
      change 0 < 1-(cc p.1) 0+(cc p.1) 0
      linarith
    let dom := cp.prod (IccRightChart 0 1)
    have hdom : dom ∈ IsManifold.maximalAtlas CollarModel ∞ (Circle × Time) :=
      IsManifold.mem_maximalAtlas_prod hcp hright
    let cd : PartialDiffeomorph CollarModel ((𝓡 1).prod (𝓡 1)) (Circle × Time) (Euc 1 × Euc 1) ∞ :=
      { toPartialEquiv := (cp.prod tf.toOpenPartialHomeomorph).toPartialEquiv
        open_source := (cp.prod tf.toOpenPartialHomeomorph).open_source
        open_target := (cp.prod tf.toOpenPartialHomeomorph).open_target
        contMDiffOn_toFun := by
          exact ((contMDiffOn_of_mem_maximalAtlas hcp).comp contMDiff_fst.contMDiffOn (fun _ h => h.1)).prodMk
            (tf.contMDiffOn_toFun.comp contMDiff_snd.contMDiffOn (fun _ h => h.2))
        contMDiffOn_invFun := by
          exact ((contMDiffOn_symm_of_mem_maximalAtlas hcp).comp contMDiff_fst.contMDiffOn (fun _ h => h.1)).prodMk
            (tf.contMDiffOn_invFun.comp contMDiff_snd.contMDiffOn (fun _ h => h.2)) }
    let ell : (Euc 1 × Euc 1) ≃ₗ[ℝ] Euc 2 :=
      { toFun := fun u => !₂[u.1 0,-a⁻¹*u.2 0]
        invFun := fun w => (!₂[w 0],!₂[-a*w 1])
        left_inv := by
          intro u
          apply Prod.ext <;> ext i <;> fin_cases i
          · rfl
          · change -a*(-a⁻¹*u.2 0)=u.2 0
            field_simp [ne_of_gt ha]
        right_inv := by
          intro w
          ext i
          fin_cases i
          · rfl
          · change -a⁻¹*(-a*w 1)=w 1
            field_simp [ne_of_gt ha]
        map_add' := by intro u w; ext i; fin_cases i <;> simp <;> ring
        map_smul' := by intro r u; ext i; fin_cases i <;> simp <;> ring }
    let el := ell.toContinuousLinearEquiv
    let dl : Diffeomorph ((𝓡 1).prod (𝓡 1)) (𝓡 2) (Euc 1 × Euc 1) (Euc 2) ∞ :=
      ⟨el.toEquiv,by
        rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod]
        exact el.contDiff.contMDiff,by
        rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod]
        exact el.symm.contDiff.contMDiff⟩
    let dt : Diffeomorph (𝓡 2) (𝓡 2) (Euc 2) (Euc 2) ∞ :=
      ⟨(Homeomorph.addLeft (!₂[0,3]:Euc 2)).toEquiv,
        contMDiff_const.add contMDiff_id,contMDiff_const.add contMDiff_id⟩
    let dx := dl.trans dt
    have hdx (u : Euc 1 × Euc 1) : dx u = !₂[u.1 0,3-a⁻¹*u.2 0] := by
      ext i
      fin_cases i
      · change 0 + u.1 0=u.1 0
        simp
      · change 3 + -a⁻¹*u.2 0=3-a⁻¹*u.2 0
        ring
    let b : ℝ := 7/8
    let b' : ℝ := 15/16
    have hb : (3/4:ℝ)<b := by norm_num [b]
    have hbpos : 0<b := by norm_num [b]
    have hbb' : b<b' := by norm_num [b,b']
    have hb' : b'<1 := by norm_num [b']
    obtain ⟨A⟩ := source_collar_substrip_coordinates c b b' hbpos hbb' hb'
    let ps : openTimeStrip b := ⟨(p.1,0),by change (0:ℝ)<b; exact hbpos⟩
    obtain ⟨incA,hincA,hincAs,hincAt⟩ := hinc (I:=𝓡∂ 2) A.image ⟨A.coordinates ps⟩
    obtain ⟨incS,hincS,hincSs,hincSt⟩ := hinc (I:=CollarModel) (openTimeStrip b) ⟨ps⟩
    let codD := ((((incA.symm.trans A.coordinates.symm.toPartialDiffeomorph).trans incS).trans cd).trans
      dx.toPartialDiffeomorph).trans jd2
    let cod := codD.toOpenPartialHomeomorph
    have hcod : cod ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ F.surface :=
      cod.mem_maximalAtlas_of_contMDiffOn codD.contMDiffOn_toFun codD.contMDiffOn_invFun
    let f : Circle × Time → F.surface := fun q => c.toFun (q.1,affineHalfTime q.2)
    have hsmem (q : Circle × Time) : (affineHalfTime q.2:ℝ)<b := by
      change 1/2+(q.2:ℝ)/4<b
      linarith [q.2.property.2]
    have htime (q : Circle × Time) (hq : q ∈ dom.source) :
        affineHalfTime q.2 ∈ tf.source := by
      change (affineHalfTime q.2:ℝ)<1 ∧ IccLeftChart 0 1 (affineHalfTime q.2) ∈ j1.target
      refine ⟨(hsmem q).trans (hbb'.trans hb'),?_⟩
      rw [hj1t]
      change 0<(1/2+(q.2:ℝ)/4)-0
      linarith [q.2.property.1]
    have hxsource (q : Circle × Time) (hq : q ∈ dom.source) :
        dx (cp q.1,tf (affineHalfTime q.2)) ∈ j2.source := by
      rw [hj2s]
      rw [hdx]
      change 0<(cp q.1) 0
      exact (hcpSource ▸ hq.1).2
    have hmem (q : Circle × Time) (hq : q ∈ dom.source) :
        f q ∈ cod.source ∧
        (𝓡∂ 2) (cod (f q))= !₂[(cp q.1) 0,1-(q.2:ℝ)] := by
      let q' : openTimeStrip b := ⟨(q.1,affineHalfTime q.2),hsmem q⟩
      have hfq : incA (A.coordinates q')=f q := (hincA _).trans (A.equation q')
      have hqin : A.coordinates q' ∈ incA.source := by rw [hincAs]; trivial
      have hinv : incA.symm (f q)=A.coordinates q' := by
        rw [←hfq]
        exact incA.toOpenPartialHomeomorph.left_inv hqin
      have hcomp : A.coordinates.symm (incA.symm (f q))=q' := by rw [hinv,A.coordinates.symm_apply_apply]
      have hval : incS (A.coordinates.symm (incA.symm (f q)))=q'.val := by rw [hcomp,hincS]
      have hqd : q'.val ∈ cd.source := ⟨hq.1,htime q hq⟩
      constructor
      · change (((((f q ∈ incA.target ∧ incA.symm (f q) ∈ univ) ∧
          A.coordinates.symm (incA.symm (f q)) ∈ incS.source) ∧
          incS (A.coordinates.symm (incA.symm (f q))) ∈ cd.source) ∧
          cd (incS (A.coordinates.symm (incA.symm (f q)))) ∈ univ) ∧
          dx (cd (incS (A.coordinates.symm (incA.symm (f q))))) ∈ j2.source)
        refine ⟨⟨⟨⟨⟨?_,mem_univ _⟩,?_⟩,?_⟩,mem_univ _⟩,?_⟩
        · rw [hincAt,←hfq,hincA]; exact (A.coordinates q').property
        · rw [hincSs]; trivial
        · rw [hval]; exact hqd
        · rw [hval]; exact hxsource q hq
      · change (𝓡∂ 2) (j2 (dx (cd (incS (A.coordinates.symm (incA.symm (f q)))))))=_
        rw [hval]
        rw [hj2]
        rw [(𝓡∂ 2).right_inv (by
          rw [range_modelWithCornersEuclideanHalfSpace]
          have hx := hxsource q hq
          rw [hj2s] at hx
          exact (show 0<(dx (cp q.1,tf (affineHalfTime q.2))) 0 from hx).le)]
        change dx (cp q.1,j1.symm (IccLeftChart 0 1 (affineHalfTime q.2)))=_
        rw [hj1inv,hdx]
        ext i
        fin_cases i
        · rfl
        · change 3-a⁻¹*((1/2+(q.2:ℝ)/4)-0)=1-(q.2:ℝ)
          norm_num [a]
          ring
    have hpdom : p ∈ dom.source := ⟨hpcc,by change (0:ℝ)<(p.2:ℝ); rw [hp]; norm_num⟩
    let lin : (Euc 1 × Euc 1) ≃ₗ[ℝ] Euc 2 :=
      { toFun := fun u => !₂[u.1 0,u.2 0]
        invFun := fun w => (!₂[w 0],!₂[w 1])
        left_inv := by intro u; apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
        right_inv := by intro w; ext i; fin_cases i <;> rfl
        map_add' := by intro u w; ext i; fin_cases i <;> rfl
        map_smul' := by intro r u; ext i; fin_cases i <;> rfl }
    let L := (ContinuousLinearEquiv.prodUnique ℝ (Euc 1 × Euc 1) (Euc 0)).trans lin.toContinuousLinearEquiv
    apply Manifold.IsImmersionAtOfComplement.mk_of_charts (I:=CollarModel) (J:=𝓡∂ 2) L dom cod hpdom (hmem p hpdom).1 hdom hcod
    · exact fun q hq => (hmem q hq).1
    · intro u hu
      let q := (dom.extend CollarModel).symm u
      have hq : q ∈ dom.source := by simpa only [OpenPartialHomeomorph.extend_source] using (dom.extend CollarModel).map_target hu
      change (𝓡∂ 2) (cod (f q))=L (u,0)
      rw [(hmem q hq).2]
      have heq := (dom.extend CollarModel).right_inv hu
      change (cp q.1,(𝓡∂ 1) (IccRightChart 0 1 q.2))=u at heq
      rw [←heq]
      ext i
      fin_cases i
      · rfl
      · rfl
  
  have htransfer {K : OrientedKnot} {T : TubularNeighborhood K} {F : SphereSpanningSurface.{0} K}
      {R : FramedRibbon T F} (C : CutSurface R) (A : HalfCollarTopology C) (p : Circle × Time)
      (h : Manifold.IsImmersionAtOfComplement (Euc 0) CollarModel (𝓡∂ 2) ∞
        (fun q : Circle × Time => R.collar (q.1,affineHalfTime q.2)) p)
      (hl : IsLocalDiffeomorphAt (𝓡∂ 2) (𝓡∂ 2) ∞ C.inclusion (A.map p)) :
      Manifold.IsImmersionAtOfComplement (Euc 0) CollarModel (𝓡∂ 2) ∞ A.map p := by
    obtain ⟨df,hpoint,hagrees⟩ := hl
    let a := h.domChart
    let b := h.codChart
    let O := a.source ∩ A.map ⁻¹' df.source
    have hO : IsOpen O := a.open_source.inter (df.open_source.preimage A.continuous)
    let source := a.restr O
    have hsourceeq : source.source=O := by
      simp only [source,OpenPartialHomeomorph.restr_source,hO.interior_eq]
      exact inter_eq_right.mpr inter_subset_left
    have hsource : source∈IsManifold.maximalAtlas CollarModel ∞ (Circle × Time) :=
      restr_mem_maximalAtlas _ h.domChart_mem_maximalAtlas hO
    let bc : PartialDiffeomorph (𝓡∂ 2) (𝓡∂ 2) F.surface (EuclideanHalfSpace 2) ∞ :=
      { toPartialEquiv := b.toPartialEquiv
        open_source := b.open_source
        open_target := b.open_target
        contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
        contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas }
    let targetD := df.trans bc
    let target := targetD.toOpenPartialHomeomorph
    have htarget : target∈IsManifold.maximalAtlas (𝓡∂ 2) ∞ C.surface :=
      target.mem_maximalAtlas_of_contMDiffOn targetD.contMDiffOn_toFun targetD.contMDiffOn_invFun
    have hsmem : p∈source.source := hsourceeq.symm ▸ ⟨h.mem_domChart_source,hpoint⟩
    have hmem (q : Circle × Time) (hq : q∈source.source) :
        A.map q∈target.source := by
      have hqo := hsourceeq ▸ hq
      change A.map q∈df.source ∧ df (A.map q)∈b.source
      refine ⟨hqo.2,?_⟩
      rw [←hagrees hqo.2,A.equation]
      exact h.mapsto_domChart_source_codChart_source hqo.1
    have heq (q : Circle × Time) (hq : q∈source.source) :
        target.extend (𝓡∂ 2) (A.map q)=h.equiv (source.extend CollarModel q,0) := by
      have hqo := hsourceeq ▸ hq
      change (𝓡∂ 2) (b (df (A.map q)))=h.equiv (a.extend CollarModel q,0)
      rw [←hagrees hqo.2,A.equation]
      have hu := (a.extend CollarModel).map_source (by simpa only [OpenPartialHomeomorph.extend_source] using hqo.1)
      have hh := h.writtenInCharts hu
      change (b.extend (𝓡∂ 2)) (R.collar (((a.extend CollarModel).symm ((a.extend CollarModel) q)).1,
        affineHalfTime ((a.extend CollarModel).symm ((a.extend CollarModel) q)).2))=
        h.equiv ((a.extend CollarModel) q,0) at hh
      rw [(a.extend CollarModel).left_inv (by simpa only [OpenPartialHomeomorph.extend_source] using hqo.1)] at hh
      exact hh
    apply Manifold.IsImmersionAtOfComplement.mk_of_charts (I:=CollarModel) (J:=𝓡∂ 2)
      h.equiv source target hsmem (hmem p hsmem) hsource htarget hmem
    intro u hu
    let q := (source.extend CollarModel).symm u
    have hq : q∈source.source := by simpa only [OpenPartialHomeomorph.extend_source] using (source.extend CollarModel).map_target hu
    change target.extend (𝓡∂ 2) (A.map q)=h.equiv (u,0)
    rw [heq q hq,(source.extend CollarModel).right_inv hu]
  set_option backward.isDefEq.respectTransparency false in
  have hpositive {K : OrientedKnot} {T : TubularNeighborhood K} {F : SphereSpanningSurface.{0} K}
      {R : FramedRibbon T F} (C : CutSurface R) (A : HalfCollarTopology C) :
      ∀ z, 0 < inwardCoordinate (C.boundary.toFun z)
        (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => A.map (z,t)) 0 timeUnit) := by
    intro z
    have hinc {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
        {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
        {M : Type} [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] (U : TopologicalSpace.Opens M) (hne : Nonempty U) :
        ∃ d : PartialDiffeomorph I I U M ∞,
          (∀ x, d x=x.val) ∧ d.source=univ ∧ d.target=(U:Set M) := by
      let e := U.openPartialHomeomorphSubtypeCoe hne
      have hi : ContMDiffOn I I ∞ e.symm e.target := by
        intro x hx
        apply (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target x).mp
        have heq : EqOn (Subtype.val ∘ e.symm) id e.target :=
          fun y hy => e.right_inv hy
        exact (contMDiffOn_id.congr (fun y hy => heq hy)) x hx
      exact ⟨{ toPartialEquiv := e.toPartialEquiv
               open_source := e.open_source
               open_target := e.open_target
               contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
               contMDiffOn_invFun := hi },fun _ => rfl,rfl,
        U.openPartialHomeomorphSubtypeCoe_target hne⟩
    let p : Circle × Time := (z,0)
    let q : (openTimeStrip 1) := ⟨p,by change (0:ℝ)<1; norm_num⟩
    obtain ⟨incS,hincS,hincSs,hincSt⟩ := hinc (I:=CollarModel) (openTimeStrip 1) ⟨q⟩
    obtain ⟨incA,hincA,hincAs,hincAt⟩ := hinc (I:=𝓡∂ 2) A.image ⟨A.coordinates q⟩
    let dc : Diffeomorph CollarModel (𝓡∂ 2) (openTimeStrip 1) A.image ∞ :=
      ⟨A.coordinates.toEquiv,(H2_half_collar_smooth_inverse C A).2.1,(H2_half_collar_smooth_inverse C A).2.2⟩
    let df := (incS.symm.trans dc.toPartialDiffeomorph).trans incA
    let f := A.map
    have hp : p ∈ df.source := by
      change ((p ∈ incS.target ∧ incS.symm p ∈ univ) ∧ dc (incS.symm p) ∈ incA.source)
      rw [hincSt,hincAs]
      exact ⟨⟨q.property,mem_univ _⟩,mem_univ _⟩
    have hfeq : EqOn f df df.source := by
      intro x hx
      have hxS : x ∈ incS.target := hx.1.1
      have hsx := incS.toOpenPartialHomeomorph.right_inv hxS
      have hvalue : (incS.symm x).val=x := by
        have hh : incS (incS.symm x)=x := hsx
        rw [hincS] at hh
        exact hh
      change f x=incA (dc (incS.symm x))
      rw [hincA]
      exact ((A.coordinates_eq (incS.symm x)).trans (congrArg f hvalue)).symm
    have hf : IsLocalDiffeomorphAt CollarModel (𝓡∂ 2) ∞ f p := ⟨df,hp,hfeq⟩
    have hpbd : CollarModel.IsBoundaryPoint p := by
      change p ∈ CollarModel.boundary (Circle × Time)
      rw [ModelWithCorners.boundary_prod]
      apply Or.inl
      refine ⟨mem_univ _,?_⟩
      change (𝓡∂ 1).IsBoundaryPoint (0:Time)
      rw [ModelWithCorners.isBoundaryPoint_iff,frontier_range_modelWithCornersEuclideanHalfSpace]
      change 0=(extChartAt (𝓡∂ 1) (0:Time) (0:Time)) 0
      simp [extChartAt,Icc_chartedSpaceChartAt_of_le_top (z:=(0:Time)) (by norm_num),IccLeftChart_apply]
    have hboundary : (𝓡∂ 2).IsBoundaryPoint (f p) := (hf.isBoundaryPoint_iff (by simp)).mp hpbd
    let a := extChartAt CollarModel p p
    let F := writtenInExtChartAt CollarModel (𝓡∂ 2) p f
    let L : (Euc 1 × Euc 1) →L[ℝ] Euc 2 := mfderiv CollarModel (𝓡∂ 2) f p
    have ha : a.2 0=0 := by
      change (extChartAt (𝓡∂ 1) (0:Time) (0:Time)) 0=0
      simp [extChartAt,Icc_chartedSpaceChartAt_of_le_top (z:=(0:Time)) (by norm_num),IccLeftChart_apply]
    have hb : F a 0=0 := by
      have hb' : (extChartAt (𝓡∂ 2) (f p) (f p)) 0=0 := by
        rw [ModelWithCorners.isBoundaryPoint_iff,frontier_range_modelWithCornersEuclideanHalfSpace] at hboundary
        exact hboundary.symm
      change (extChartAt (𝓡∂ 2) (f p) (f ((extChartAt CollarModel p).symm a))) 0=0
      rw [(extChartAt CollarModel p).left_inv (mem_extChartAt_source p)]
      exact hb'
    have hmin : IsLocalMinOn (fun y => F y 0) (range CollarModel) a := by
      have h1 := extChartAt_target_mem_nhdsWithin (I:=CollarModel) p
      have h2 := extChartAt_preimage_mem_nhds (I:=CollarModel)
        (hf.contMDiffAt.continuousAt.preimage_mem_nhds
          (extChartAt_source_mem_nhds (I:=𝓡∂ 2) (f p)))
      have h2' : (extChartAt CollarModel p).symm ⁻¹' f ⁻¹' (extChartAt (𝓡∂ 2) (f p)).source ∈
          nhdsWithin a (range CollarModel) := nhdsWithin_le_nhds h2
      filter_upwards [h1,h2'] with y hy hy'
      rw [hb]
      have ht := writtenInExtChartAt_mapsTo (I:=CollarModel) (I':=𝓡∂ 2) (f:=f) ⟨hy,hy'⟩
      have hm := extChartAt_target_subset_range (f p) ht
      rw [range_modelWithCornersEuclideanHalfSpace] at hm
      exact hm
    have hL : HasFDerivWithinAt F L (range CollarModel) a := hf.mdifferentiableAt (by simp) |>.hasMFDerivAt |>.2
    have hcone : ∀ v : Euc 1 × Euc 1, 0≤v.2 0 → v ∈ posTangentConeAt (range CollarModel) a := by
      intro v hv
      apply mem_posTangentConeAt_of_frequently_mem
      apply Filter.Eventually.frequently
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [ModelWithCorners.range_prod]
      refine ⟨mem_range_self _,?_⟩
      rw [range_modelWithCornersEuclideanHalfSpace]
      change 0≤a.2 0+t*v.2 0
      rw [ha,zero_add]
      exact mul_nonneg (le_of_lt ht) hv
    have hrow (v : Euc 1 × Euc 1) (hv : 0≤v.2 0) : 0≤L v 0 := by
      let ev : Euc 2 →L[ℝ] ℝ := EuclideanSpace.proj 0
      exact hmin.hasFDerivWithinAt_nonneg (ev.hasFDerivAt.comp_hasFDerivWithinAt a hL) (hcone v hv)
    let e : Euc 1 × Euc 1 := (0,EuclideanSpace.single 0 1)
    have hformula (v : Euc 1 × Euc 1) : L v 0=(L e 0)*v.2 0 := by
      let v' := v-(v.2 0) • e
      have hz : v'.2 0=0 := by simp [v',e]
      have h1 := hrow v' (by rw [hz])
      have h2 := hrow (-v') (by change 0≤-v'.2 0; rw [hz]; norm_num)
      have h0 : L v' 0=0 := le_antisymm (by simpa using h2) h1
      change L (v-v.2 0 • e) 0=0 at h0
      rw [map_sub,map_smul] at h0
      change L v 0-v.2 0*L e 0=0 at h0
      linarith
    have hpos : 0<L e 0 := by
      have hnonneg := hrow e (by simp [e])
      refine lt_of_le_of_ne hnonneg ?_
      intro hz
      obtain ⟨v,hv⟩ := (hf.mfderivToContinuousLinearEquiv (by simp)).surjective (EuclideanSpace.single 0 1)
      change L v=EuclideanSpace.single 0 1 at hv
      have hh := hformula v
      rw [hv,←hz] at hh
      simpa using hh
    have hg : ContMDiff (𝓡∂ 1) CollarModel ∞ (fun t : Time => (z,t)) :=
      contMDiff_const.prodMk contMDiff_id
    have hchain := mfderiv_comp (0:Time) (hf.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))
    have he : tangentSpaceCastModel CollarModel p (mfderiv (𝓡∂ 1) CollarModel (fun t : Time => (z,t)) (0:Time) timeUnit)=e := by
      erw [mfderiv_prodMk mdifferentiableAt_const mdifferentiableAt_id]
      simp only [mfderiv_const,mfderiv_id]
      rfl
    have hder := congrArg (fun A => A timeUnit) hchain
    change (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => f (z,t)) (0:Time) timeUnit:Euc 2)=
      L (mfderiv (𝓡∂ 1) CollarModel (fun t : Time => (z,t)) (0:Time) timeUnit) at hder
    change _=L (tangentSpaceCastModel CollarModel p (mfderiv (𝓡∂ 1) CollarModel (fun t : Time => (z,t)) (0:Time) timeUnit)) at hder
    rw [he] at hder
    have hi : 0 < inwardCoordinate (f p)
        (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => f (z,t)) 0 timeUnit) := by
      simp only [inwardCoordinate,mfderiv_extChartAt_self]
      change 0 < (tangentSpaceCastModel (𝓡∂ 2) (f p)
        (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => f (z,t)) (0:Time) timeUnit)) 0
      rw [hder]
      exact hpos
    simp only [inwardCoordinate,mfderiv_extChartAt_self] at hi ⊢
    exact hi
  
  let l₂ : (Euc 1 × Euc 1) ≃ₗ[ℝ] Euc 2 :=
    { toFun := fun p => !₂[p.2 0, p.1 0]
      invFun := fun w => (!₂[w 1], !₂[w 0])
      left_inv := by
        intro p
        apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
      right_inv := by intro w; ext i; fin_cases i <;> rfl
      map_add' := by intro p q; ext i; fin_cases i <;> rfl
      map_smul' := by intro r p; ext i; fin_cases i <;> rfl }
  let L₂ := l₂.toContinuousLinearEquiv
  let e₂ : (Euc 1 × EuclideanHalfSpace 1) ≃ EuclideanHalfSpace 2 :=
    { toFun := fun p => ⟨L₂ (p.1, p.2.val), p.2.property⟩
      invFun := fun w => ((L₂.symm w.val).1, ⟨(L₂.symm w.val).2, w.property⟩)
      left_inv := by
        intro p
        refine Prod.ext ?_ ?_
        · ext i; fin_cases i; rfl
        · apply Subtype.ext; ext i; fin_cases i; rfl
      right_inv := by
        intro w
        apply Subtype.ext
        exact L₂.apply_symm_apply w.val }
  let h₂ : (Euc 1 × EuclideanHalfSpace 1) ≃ₜ EuclideanHalfSpace 2 :=
    { toEquiv := e₂
      continuous_toFun := (L₂.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      continuous_invFun :=
        ((continuous_fst.comp (L₂.symm.continuous.comp continuous_subtype_val)).prodMk
          ((continuous_snd.comp (L₂.symm.continuous.comp continuous_subtype_val)).subtype_mk _)) }
  let B : CollarModelBridge :=
    { homeo := h₂
      linear := L₂
      formula := fun _ => rfl
      linear_formula := fun _ => rfl
      compatible := fun _ => rfl }
  have himm : Manifold.IsImmersionOfComplement (Euc 0) CollarModel (𝓡∂ 2) ∞ A.map := by
    intro p
    by_cases hp : (p.2:ℝ)<1
    · exact hlower C A p hp
    · have hp1 : (p.2:ℝ)=1 := le_antisymm p.2.property.2 (le_of_not_gt hp)
      have hx : (𝓡∂ 2).IsInteriorPoint (A.map p) := by
        rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
        change A.map p∉C.surface.boundary
        intro hbd
        obtain ⟨z,hz⟩ := ((cut_boundary_exact_level C).2.1 (A.map p)).mp hbd
        have he := R.collar_embedding.isEmbedding.injective ((A.equation p).symm.trans hz)
        have ht := congrArg (fun q : Circle × Time => (q.2:ℝ)) he
        change 1/2+(p.2:ℝ)/4=1/2 at ht
        linarith
      have hi : (𝓡∂ 2).IsInteriorPoint (C.inclusion (A.map p)) := by
        rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
        change C.inclusion (A.map p)∉F.surface.boundary
        rw [A.equation]
        exact (ribbonSourceCollar R).interior p.1 (affineHalfTime p.2) (by
          change 0<1/2+(p.2:ℝ)/4
          linarith [p.2.property.1])
      exact htransfer C A p (hupper R p hp1) (hinclusion C (A.map p) hx hi)
  have hsm : Manifold.IsSmoothEmbedding CollarModel (𝓡∂ 2) ∞ A.map := ⟨himm.isImmersion,A.embedding⟩
  have hder : ∀ p (w : TangentSpace CollarModel p),
      mfderiv (𝓡∂ 2) (𝓡∂ 2) C.inclusion (A.map p)
        (mfderiv CollarModel (𝓡∂ 2) A.map p w) =
      mfderiv CollarModel (𝓡∂ 2) (fun q => R.collar (q.1,affineHalfTime q.2)) p w := by
    intro p w
    have hh := mfderiv_comp p (C.smooth_embedding.contMDiff.mdifferentiableAt (by simp))
      ((H2_half_collar_smooth_inverse C A).1.mdifferentiableAt (by simp))
    have he : (C.inclusion ∘ A.map : Circle × Time → F.surface)=(fun q => R.collar (q.1,affineHalfTime q.2)) := funext A.equation
    rw [he] at hh
    exact (congrArg (fun L => L w) hh).symm
  let k : GivenCutHalfCollar C :=
    { map := A.map
      equation := A.equation
      unique := A.unique
      boundary := A.boundary
      inward := hpositive C A
      continuous := A.continuous
      embedding := hsm
      image := A.image
      image_eq := A.image_eq
      coordinates := ⟨A.coordinates.toEquiv,(H2_half_collar_smooth_inverse C A).2.1,(H2_half_collar_smooth_inverse C A).2.2⟩
      coordinates_eq := A.coordinates_eq
      model := B
      derivative_equation := hder }
  exact ⟨hsm,hder,hpositive C A,⟨k,rfl,rfl,HEq.rfl⟩⟩

end HalfCollar

section Polar
variable {K : OrientedKnot} {T : TubularNeighborhood K}
  (E : SmoothExterior T) (D : TubeCoordinates T)

structure PolarTopology where
  image : TopologicalSpace.Opens E.Carrier
  image_eq : (image : Set E.Carrier)=exteriorPolarRegion E
  coordinates : openPolarStrip ≃ₜ image
  equation : ∀ p, (coordinates p:E.Carrier)=givenExteriorPolarMap E p.val
  tubeInverse : image → TubeDomain
  inverse_eq : ∀ x (y : tubeImageOpen T), (y:ThreeSphere)=E.toSphere x.val →
    tubeInverse x=D.map.symm y
  inverse_formula : ∀ x,
    let p := coordinates.symm x
    let q := tubeInverse x
    p.val.1=q.1 ∧ unitVector p.val.2.1=‖(q.2:Euc 2)‖⁻¹ • (q.2:Euc 2) ∧
      (p.val.2.2:ℝ)=2*(‖(q.2:Euc 2)‖-1)
  radius_lower : ∀ x, 1≤‖((tubeInverse x).2:Euc 2)‖
  radius_upper : ∀ x, ‖((tubeInverse x).2:Euc 2)‖<3/2


theorem H4_exact_polar_inverse : Nonempty (PolarTopology E D) := by
  classical
  obtain ⟨L,hL⟩ := complexPlane_isometry
  have hunitinj : Function.Injective unitVector := by
    intro z w h
    apply Subtype.ext
    apply L.injective
    simpa only [hL,unitVector] using h
  let f : PolarDomain → E.Carrier := givenExteriorPolarMap E
  have hnorm (p : PolarDomain) : ‖((polarTubePoint p).2:Euc 2)‖=1+(p.2.2:ℝ)/2 := by
    change ‖(1+(p.2.2:ℝ)/2) • unitVector p.2.1‖=_
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (polar_radius_bounds p.2.2).1,unitVector_norm,mul_one]
  have hfcont : Continuous f := by
    apply Continuous.subtype_mk
    apply (T.smoothEmbedding 0).isEmbedding.continuous.comp
    apply continuous_fst.prodMk
    apply Continuous.subtype_mk
    exact (continuous_const.add ((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).div_const 2)).smul
      (unitVector_smooth.continuous.comp (continuous_fst.comp continuous_snd))
  have hfinj : Function.Injective f := by
    intro p q h
    have hpq : polarTubePoint p=polarTubePoint q :=
      (T.smoothEmbedding 0).isEmbedding.injective (congrArg E.toSphere h)
    have hz := congrArg (@Prod.fst Circle TubeDisk) hpq
    have hv := congrArg (fun a : TubeDomain => (a.2:Euc 2)) hpq
    have ht : p.2.2=q.2.2 := by
      apply Subtype.ext
      have hn := congrArg norm hv
      rw [hnorm p,hnorm q] at hn
      linarith
    have htheta : p.2.1=q.2.1 := by
      apply hunitinj
      change (1+(p.2.2:ℝ)/2) • unitVector p.2.1=(1+(q.2.2:ℝ)/2) • unitVector q.2.1 at hv
      rw [ht] at hv
      have ha : (1+(q.2.2:ℝ)/2)≠0 := ne_of_gt (by linarith [q.2.2.property.1])
      have h := congrArg (fun v : Euc 2 => (1+(q.2.2:ℝ)/2)⁻¹ • v) hv
      simpa only [smul_smul,inv_mul_cancel₀ ha,one_smul] using h
    exact Prod.ext hz (Prod.ext htheta ht)
  have hemb : IsEmbedding f := (hfcont.isClosedEmbedding hfinj).isEmbedding
  let f1 : openPolarStrip → E.Carrier := fun p => f p.val
  have hreg : Set.range f1=exteriorPolarRegion E := by
    ext x
    constructor
    · rintro ⟨p,rfl⟩
      refine ⟨polarTubePoint p.val,rfl,?_⟩
      rw [hnorm]
      have hp : (p.val.2.2:ℝ)<1 := p.property
      linarith
    · rintro ⟨q,hqx,hqup⟩
      have hlo : 1≤‖(q.2:Euc 2)‖ := by
        by_contra h
        have hex := x.property
        apply hex
        apply mem_iUnion.mpr
        refine ⟨0,q,lt_of_not_ge h,?_⟩
        exact hqx
      have hpos : 0<‖(q.2:Euc 2)‖ := by linarith
      have hn : ‖‖(q.2:Euc 2)‖⁻¹ • (q.2:Euc 2)‖=1 := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos),inv_mul_cancel₀ (ne_of_gt hpos)]
      obtain ⟨theta,htheta⟩ : ∃ theta, unitVector theta=‖(q.2:Euc 2)‖⁻¹ • (q.2:Euc 2) := by
        have hm : ‖(q.2:Euc 2)‖⁻¹ • (q.2:Euc 2) ∈ Set.range unitVector := by
          rw [unitVector_range,Metric.mem_sphere,dist_zero_right]
          exact hn
        exact hm
      let t : Time := ⟨2*(‖(q.2:Euc 2)‖-1),by constructor <;> linarith⟩
      have ht : (t:ℝ)<1 := by dsimp [t]; linarith
      have hr : 1+(t:ℝ)/2=‖(q.2:Euc 2)‖ := by dsimp [t]; ring
      have hpolar : polarTubePoint (q.1,theta,t)=q := by
        refine Prod.ext (show (polarTubePoint (q.1,theta,t)).1=q.1 from rfl) ?_
        apply Subtype.ext
        change (1+(t:ℝ)/2) • unitVector theta=(q.2:Euc 2)
        rw [hr,htheta,smul_smul,mul_inv_cancel₀ (ne_of_gt hpos),one_smul]
      refine ⟨⟨(q.1,theta,t),ht⟩,?_⟩
      apply Subtype.ext
      change T.tube 0 (polarTubePoint (q.1,theta,t))=E.toSphere x
      rw [hpolar]
      exact hqx
  have hregopen : IsOpen (exteriorPolarRegion E) := by
    let U : TopologicalSpace.Opens TubeDomain :=
      ⟨{q | ‖(q.2:Euc 2)‖<3/2},isOpen_lt
        ((continuous_subtype_val.comp continuous_snd).norm) continuous_const⟩
    have hopen : IsOpen (T.tube 0 '' (U:Set TubeDomain)) :=
      ((T.smoothEmbedding 0).isEmbedding.isInducing.isOpenMap (T.image_open 0)) _ U.isOpen
    have heq : exteriorPolarRegion E=E.toSphere ⁻¹' (T.tube 0 '' (U:Set TubeDomain)) := by
      ext x
      constructor
      · rintro ⟨q,hq,hn⟩
        exact ⟨q,hn,hq⟩
      · rintro ⟨q,hn,hq⟩
        exact ⟨q,hq,hn⟩
    rw [heq]
    exact hopen.preimage continuous_subtype_val
  let image : TopologicalSpace.Opens E.Carrier := ⟨exteriorPolarRegion E,hregopen⟩
  let coords := (hemb.comp IsEmbedding.subtypeVal).toHomeomorph.trans (Homeomorph.setCongr hreg)
  have hcoord (p : openPolarStrip) : (coords p:E.Carrier)=f p.val := rfl
  have hxtube (x : image) : E.toSphere x.val ∈ Set.range (T.tube 0) := by
    obtain ⟨q,hq,_⟩ := x.property
    exact ⟨q,hq⟩
  let y : image → tubeImageOpen T := fun x => ⟨E.toSphere x.val,hxtube x⟩
  let inverse : image → TubeDomain := fun x => D.map.symm (y x)
  have heqinverse (x : image) : T.tube 0 (inverse x)=E.toSphere x.val := by
    rw [←D.equation]
    exact congrArg (fun q : tubeImageOpen T => (q:ThreeSphere)) (D.map.apply_symm_apply (y x))
  have hqpolar (x : image) : inverse x=polarTubePoint ((coords.symm x).val) := by
    apply (T.smoothEmbedding 0).isEmbedding.injective
    rw [heqinverse]
    have h := congrArg E.toSphere (hcoord (coords.symm x))
    rw [coords.apply_symm_apply] at h
    exact h
  refine ⟨{ image := image
            image_eq := rfl
            coordinates := coords
            equation := hcoord
            tubeInverse := inverse
            inverse_eq := ?_
            inverse_formula := ?_
            radius_lower := ?_
            radius_upper := ?_ }⟩
  · intro x y' hy
    have hh : y'=y x := Subtype.ext hy
    rw [hh]
  · intro x
    dsimp only
    rw [hqpolar]
    refine ⟨rfl,?_,?_⟩
    · rw [hnorm]
      change unitVector _=(1+((coords.symm x).val.2.2:ℝ)/2)⁻¹ •
        ((1+((coords.symm x).val.2.2:ℝ)/2) • unitVector _)
      rw [smul_smul,inv_mul_cancel₀ (by linarith [(coords.symm x).val.2.2.property.1]),one_smul]
    · rw [hnorm]
      ring
  · intro x
    rw [hqpolar,hnorm]
    linarith [(coords.symm x).val.2.2.property.1]
  · intro x
    rw [hqpolar,hnorm]
    have hp : ((coords.symm x).val.2.2:ℝ)<1 := (coords.symm x).property
    linarith



theorem H5_polar_smooth_inverse (A : PolarTopology E D) :
    ContMDiff PolarModel (𝓡∂ 3) ∞ (givenExteriorPolarMap E) ∧
      ContMDiff PolarModel (𝓡∂ 3) ∞ A.coordinates ∧
      ContMDiff (𝓡∂ 3) PolarModel ∞ A.coordinates.symm := by
  letI : ChartedSpace (EuclideanHalfSpace 3) T.Carrier := E.charted
  letI : IsManifold (𝓡∂ 3) ∞ T.Carrier := E.smooth
  have hpol : ContMDiff PolarModel TubeModel ∞ polarTubePoint := by
    apply contMDiff_fst.prodMk
    apply (ContMDiff.subtypeVal_comp_iff tubeDiskOpen _).mp
    exact (contMDiff_const.add ((contMDiff_subtypeVal_Icc.comp
      (contMDiff_snd.comp contMDiff_snd)).div_const 2)).smul
      (unitVector_smooth.comp (contMDiff_fst.comp contMDiff_snd))
  have hmap : ContMDiff PolarModel (𝓡∂ 3) ∞ (givenExteriorPolarMap E) := by
    apply (ContMDiff.iff_comp_isImmersion E.inclusion.isImmersion).mpr
    refine ⟨?_,?_⟩
    · exact ((T.smoothEmbedding 0).isEmbedding.continuous.comp hpol.continuous).subtype_mk _
    · exact (T.smoothEmbedding 0).contMDiff.comp hpol
  have hf : ContMDiff PolarModel (𝓡∂ 3) ∞ A.coordinates := by
    apply (ContMDiff.subtypeVal_comp_iff A.image A.coordinates).mp
    have heq : (Subtype.val ∘ A.coordinates : openPolarStrip → E.Carrier)=
        givenExteriorPolarMap E ∘ Subtype.val := funext A.equation
    rw [heq]
    exact hmap.comp contMDiff_subtype_val
  have hxtube (x : A.image) : E.toSphere x.val ∈ Set.range (T.tube 0) := by
    have hx : x.val ∈ (A.image : Set E.Carrier) := x.property
    rw [A.image_eq] at hx
    obtain ⟨q,hq,_⟩ := hx
    exact ⟨q,hq⟩
  let y : A.image → tubeImageOpen T := fun x => ⟨E.toSphere x.val,hxtube x⟩
  have hy : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ y := by
    apply (ContMDiff.subtypeVal_comp_iff (tubeImageOpen T) y).mp
    have he : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion.contMDiff
    exact he.comp contMDiff_subtype_val
  have hq : ContMDiff (𝓡∂ 3) TubeModel ∞ A.tubeInverse := by
    have heq : A.tubeInverse=D.map.symm ∘ y := funext (fun x => A.inverse_eq x (y x) rfl)
    rw [heq]
    exact D.map.symm.contMDiff.comp hy
  let w : A.image → Euc 2 := fun x => ((A.tubeInverse x).2:Euc 2)
  have hw : ContMDiff (𝓡∂ 3) 𝓘(ℝ,Euc 2) ∞ w :=
    contMDiff_subtype_val.comp (contMDiff_snd.comp hq)
  have hpos (x : A.image) : 0<‖w x‖ := lt_of_lt_of_le zero_lt_one (A.radius_lower x)
  have hn : ContMDiff (𝓡∂ 3) 𝓘(ℝ,ℝ) ∞ (fun x => ‖w x‖) := by
    intro x
    exact (contDiffAt_norm ℝ (norm_pos_iff.mp (hpos x))).contMDiffAt.comp x (hw x)
  have hninv : ContMDiff (𝓡∂ 3) 𝓘(ℝ,ℝ) ∞ (fun x => ‖w x‖⁻¹) :=
    hn.inv₀ (fun x => ne_of_gt (hpos x))
  have hinv : ContMDiff (𝓡∂ 3) PolarModel ∞ A.coordinates.symm := by
    apply (ContMDiff.subtypeVal_comp_iff openPolarStrip A.coordinates.symm).mp
    have hz : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ (fun x => (A.coordinates.symm x).val.1) := by
      have he : (fun x : A.image => (A.coordinates.symm x).val.1)=
          (fun x : A.image => (A.tubeInverse x).1) := funext (fun x => (A.inverse_formula x).1)
      rw [he]
      exact contMDiff_fst.comp hq
    have ht : ContMDiff (𝓡∂ 3) (𝓡∂ 1) ∞ (fun x => (A.coordinates.symm x).val.2.2) := by
      apply contMDiff_iff_comp_subtypeVal_Icc.mpr
      refine ⟨continuous_snd.comp (continuous_snd.comp
        (continuous_subtype_val.comp A.coordinates.symm.continuous)),?_⟩
      have he : (fun x : A.image => ((A.coordinates.symm x).val.2.2:ℝ))=
          (fun x : A.image => 2*(‖w x‖-1)) := funext (fun x => (A.inverse_formula x).2.2)
      change ContMDiff (𝓡∂ 3) 𝓘(ℝ,ℝ) ∞ (fun x : A.image => ((A.coordinates.symm x).val.2.2:ℝ))
      rw [he]
      exact contMDiff_const.mul (hn.sub contMDiff_const)
    have htheta : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ (fun x => (A.coordinates.symm x).val.2.1) := by
      obtain ⟨L,hL⟩ := complexPlane_isometry
      let v : A.image → ℂ := fun x => ((A.coordinates.symm x).val.2.1:ℂ)
      have he : v=(fun x => L.symm (‖w x‖⁻¹ • w x)) := by
        funext x
        have h := congrArg L.symm (A.inverse_formula x).2.1
        simpa only [unitVector,←hL,L.symm_apply_apply] using h
      have hv : ContMDiff (𝓡∂ 3) 𝓘(ℝ,ℂ) ∞ v := by
        rw [he]
        exact L.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp (hninv.smul hw)
      letI : Fact (Module.finrank ℝ ℂ=1+1) := ⟨by simp⟩
      have h := hv.codRestrict_sphere (n:=1) (fun x => ((A.coordinates.symm x).val.2.1).property)
      exact h
    exact hz.prodMk (htheta.prodMk ht)
  exact ⟨hmap,hf,hinv⟩


theorem H6_polar_positive_scale (A : PolarTopology E D) :
    (∀ z theta, givenExteriorPolarMap E (z,theta,0) ∈ (𝓡∂ 3).boundary E.Carrier ∧
      ∃ a : ℝ, 0<a ∧
        inwardCoordinate (givenExteriorPolarMap E (z,theta,0))
          (mfderiv (𝓡∂ 1) (𝓡∂ 3) (fun t => givenExteriorPolarMap E (z,theta,t)) 0 timeUnit)=a/2) ∧
    ∃ P : GivenExteriorPolarCollar E D, P.image=A.image ∧ HEq P.tubeInverse A.tubeInverse ∧
      HEq P.coordinates.toHomeomorph A.coordinates := by
  set_option backward.isDefEq.respectTransparency false in
  have hpositive (z theta : Circle) :
      givenExteriorPolarMap E (z,theta,0) ∈ (𝓡∂ 3).boundary E.Carrier ∧
        0 < inwardCoordinate (givenExteriorPolarMap E (z,theta,0))
          (mfderiv (𝓡∂ 1) (𝓡∂ 3) (fun t => givenExteriorPolarMap E (z,theta,t)) 0 timeUnit) := by
    have hinc {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
        {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
        {M : Type} [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] (U : TopologicalSpace.Opens M) (hne : Nonempty U) :
        ∃ d : PartialDiffeomorph I I U M ∞,
          (∀ x, d x=x.val) ∧ d.source=univ ∧ d.target=(U:Set M) := by
      let e := U.openPartialHomeomorphSubtypeCoe hne
      have hi : ContMDiffOn I I ∞ e.symm e.target := by
        intro x hx
        apply (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target x).mp
        have heq : EqOn (Subtype.val ∘ e.symm) id e.target :=
          fun y hy => e.right_inv hy
        exact (contMDiffOn_id.congr (fun y hy => heq hy)) x hx
      exact ⟨{ toPartialEquiv := e.toPartialEquiv
               open_source := e.open_source
               open_target := e.open_target
               contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
               contMDiffOn_invFun := hi },fun _ => rfl,rfl,
        U.openPartialHomeomorphSubtypeCoe_target hne⟩
    let p : PolarDomain := (z,theta,0)
    let q : openPolarStrip := ⟨p,by change (0:ℝ)<1; norm_num⟩
    obtain ⟨incS,hincS,hincSs,hincSt⟩ := hinc (I:=PolarModel) openPolarStrip ⟨q⟩
    obtain ⟨incA,hincA,hincAs,hincAt⟩ := hinc (I:=𝓡∂ 3) A.image ⟨A.coordinates q⟩
    let dc : Diffeomorph PolarModel (𝓡∂ 3) openPolarStrip A.image ∞ :=
      ⟨A.coordinates.toEquiv,(H5_polar_smooth_inverse E D A).2.1,(H5_polar_smooth_inverse E D A).2.2⟩
    let df := (incS.symm.trans dc.toPartialDiffeomorph).trans incA
    let f := givenExteriorPolarMap E
    have hp : p ∈ df.source := by
      change ((p ∈ incS.target ∧ incS.symm p ∈ univ) ∧ dc (incS.symm p) ∈ incA.source)
      rw [hincSt,hincAs]
      exact ⟨⟨q.property,mem_univ _⟩,mem_univ _⟩
    have hfeq : EqOn f df df.source := by
      intro x hx
      have hxS : x ∈ incS.target := hx.1.1
      have hsx := incS.toOpenPartialHomeomorph.right_inv hxS
      have hvalue : (incS.symm x).val=x := by
        have hh : incS (incS.symm x)=x := hsx
        rw [hincS] at hh
        exact hh
      change f x=incA (dc (incS.symm x))
      rw [hincA]
      exact ((A.equation (incS.symm x)).trans (congrArg f hvalue)).symm
    have hf : IsLocalDiffeomorphAt PolarModel (𝓡∂ 3) ∞ f p := ⟨df,hp,hfeq⟩
    have hpbd : PolarModel.IsBoundaryPoint p := by
      change p ∈ PolarModel.boundary PolarDomain
      rw [ModelWithCorners.boundary_prod]
      apply Or.inl
      refine ⟨mem_univ _,?_⟩
      rw [ModelWithCorners.boundary_prod]
      apply Or.inl
      refine ⟨mem_univ _,?_⟩
      change (𝓡∂ 1).IsBoundaryPoint (0:Time)
      rw [ModelWithCorners.isBoundaryPoint_iff,frontier_range_modelWithCornersEuclideanHalfSpace]
      change 0=(extChartAt (𝓡∂ 1) (0:Time) (0:Time)) 0
      simp [extChartAt,Icc_chartedSpaceChartAt_of_le_top (z:=(0:Time)) (by norm_num),IccLeftChart_apply]
    have hboundary : (𝓡∂ 3).IsBoundaryPoint (f p) := (hf.isBoundaryPoint_iff (by simp)).mp hpbd
    let a := extChartAt PolarModel p p
    let F := writtenInExtChartAt PolarModel (𝓡∂ 3) p f
    let L : (Euc 1 × (Euc 1 × Euc 1)) →L[ℝ] Euc 3 := mfderiv PolarModel (𝓡∂ 3) f p
    have ha : a.2.2 0=0 := by
      change (extChartAt (𝓡∂ 1) (0:Time) (0:Time)) 0=0
      simp [extChartAt,Icc_chartedSpaceChartAt_of_le_top (z:=(0:Time)) (by norm_num),IccLeftChart_apply]
    have hb : F a 0=0 := by
      have hb' : (extChartAt (𝓡∂ 3) (f p) (f p)) 0=0 := by
        rw [ModelWithCorners.isBoundaryPoint_iff,frontier_range_modelWithCornersEuclideanHalfSpace] at hboundary
        exact hboundary.symm
      change (extChartAt (𝓡∂ 3) (f p) (f ((extChartAt PolarModel p).symm a))) 0=0
      rw [(extChartAt PolarModel p).left_inv (mem_extChartAt_source p)]
      exact hb'
    have hmin : IsLocalMinOn (fun y => F y 0) (range PolarModel) a := by
      have h1 := extChartAt_target_mem_nhdsWithin (I:=PolarModel) p
      have h2 := extChartAt_preimage_mem_nhds (I:=PolarModel)
        (hf.contMDiffAt.continuousAt.preimage_mem_nhds
          (extChartAt_source_mem_nhds (I:=𝓡∂ 3) (f p)))
      have h2' : (extChartAt PolarModel p).symm ⁻¹' f ⁻¹' (extChartAt (𝓡∂ 3) (f p)).source ∈
          nhdsWithin a (range PolarModel) := nhdsWithin_le_nhds h2
      filter_upwards [h1,h2'] with y hy hy'
      rw [hb]
      have ht := writtenInExtChartAt_mapsTo (I:=PolarModel) (I':=𝓡∂ 3) (f:=f) ⟨hy,hy'⟩
      have hm := extChartAt_target_subset_range (f p) ht
      rw [range_modelWithCornersEuclideanHalfSpace] at hm
      exact hm
    have hL : HasFDerivWithinAt F L (range PolarModel) a := hf.mdifferentiableAt (by simp) |>.hasMFDerivAt |>.2
    have hcone : ∀ v : Euc 1 × (Euc 1 × Euc 1), 0≤v.2.2 0 → v ∈ posTangentConeAt (range PolarModel) a := by
      intro v hv
      apply mem_posTangentConeAt_of_frequently_mem
      apply Filter.Eventually.frequently
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [ModelWithCorners.range_prod,ModelWithCorners.range_prod]
      refine ⟨mem_range_self _,mem_range_self _,?_⟩
      rw [range_modelWithCornersEuclideanHalfSpace]
      change 0≤a.2.2 0+t*v.2.2 0
      rw [ha,zero_add]
      exact mul_nonneg (le_of_lt ht) hv
    have hrow (v : Euc 1 × (Euc 1 × Euc 1)) (hv : 0≤v.2.2 0) : 0≤L v 0 := by
      let ev : Euc 3 →L[ℝ] ℝ := EuclideanSpace.proj 0
      exact hmin.hasFDerivWithinAt_nonneg (ev.hasFDerivAt.comp_hasFDerivWithinAt a hL) (hcone v hv)
    let e : Euc 1 × (Euc 1 × Euc 1) := (0,0,EuclideanSpace.single 0 1)
    have hformula (v : Euc 1 × (Euc 1 × Euc 1)) : L v 0=(L e 0)*v.2.2 0 := by
      let v' := v-(v.2.2 0) • e
      have hz : v'.2.2 0=0 := by simp [v',e]
      have h1 := hrow v' (by rw [hz])
      have h2 := hrow (-v') (by change 0≤-v'.2.2 0; rw [hz]; norm_num)
      have h0 : L v' 0=0 := le_antisymm (by simpa using h2) h1
      change L (v-v.2.2 0 • e) 0=0 at h0
      rw [map_sub,map_smul] at h0
      change L v 0-v.2.2 0*L e 0=0 at h0
      linarith
    have hpos : 0<L e 0 := by
      have hnonneg := hrow e (by simp [e])
      refine lt_of_le_of_ne hnonneg ?_
      intro hz
      obtain ⟨v,hv⟩ := (hf.mfderivToContinuousLinearEquiv (by simp)).surjective (EuclideanSpace.single 0 1)
      change L v=EuclideanSpace.single 0 1 at hv
      have hh := hformula v
      rw [hv,←hz] at hh
      simpa using hh
    have hg : ContMDiff (𝓡∂ 1) PolarModel ∞ (fun t : Time => (z,theta,t)) :=
      contMDiff_const.prodMk (contMDiff_const.prodMk contMDiff_id)
    have hchain := mfderiv_comp (0:Time) (hf.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))
    have he : tangentSpaceCastModel PolarModel p (mfderiv (𝓡∂ 1) PolarModel (fun t : Time => (z,theta,t)) (0:Time) timeUnit)=e := by
      erw [mfderiv_prodMk mdifferentiableAt_const (mdifferentiableAt_const.prodMk mdifferentiableAt_id)]
      erw [mfderiv_prodMk mdifferentiableAt_const mdifferentiableAt_id]
      simp only [mfderiv_const,mfderiv_id]
      rfl
    have hder := congrArg (fun A => A timeUnit) hchain
    change (mfderiv (𝓡∂ 1) (𝓡∂ 3) (fun t => f (z,theta,t)) (0:Time) timeUnit:Euc 3)=
      L (mfderiv (𝓡∂ 1) PolarModel (fun t : Time => (z,theta,t)) (0:Time) timeUnit) at hder
    change _=L (tangentSpaceCastModel PolarModel p (mfderiv (𝓡∂ 1) PolarModel (fun t : Time => (z,theta,t)) (0:Time) timeUnit)) at hder
    rw [he] at hder
    refine ⟨hboundary,?_⟩
    simp only [inwardCoordinate,mfderiv_extChartAt_self]
    change 0 < (tangentSpaceCastModel (𝓡∂ 3) (f p)
      (mfderiv (𝓡∂ 1) (𝓡∂ 3) (fun t => f (z,theta,t)) (0:Time) timeUnit)) 0
    rw [hder]
    exact hpos
  let l₃ : (Euc 1 × (Euc 1 × Euc 1)) ≃ₗ[ℝ] Euc 3 :=
    { toFun := fun p => !₂[p.2.2 0, p.1 0, p.2.1 0]
      invFun := fun w => (!₂[w 1], !₂[w 2], !₂[w 0])
      left_inv := by
        intro p
        apply Prod.ext
        · ext i; fin_cases i; rfl
        · apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
      right_inv := by intro w; ext i; fin_cases i <;> rfl
      map_add' := by intro p q; ext i; fin_cases i <;> rfl
      map_smul' := by intro r p; ext i; fin_cases i <;> rfl }
  let L₃ := l₃.toContinuousLinearEquiv
  let e₃ : (Euc 1 × (Euc 1 × EuclideanHalfSpace 1)) ≃ EuclideanHalfSpace 3 :=
    { toFun := fun p => ⟨L₃ (p.1, p.2.1, p.2.2.val), p.2.2.property⟩
      invFun := fun w => ((L₃.symm w.val).1, (L₃.symm w.val).2.1,
        ⟨(L₃.symm w.val).2.2, w.property⟩)
      left_inv := by
        intro p
        refine Prod.ext ?_ ?_
        · ext i; fin_cases i; rfl
        · refine Prod.ext ?_ ?_
          · ext i; fin_cases i; rfl
          · apply Subtype.ext; ext i; fin_cases i; rfl
      right_inv := by intro w; apply Subtype.ext; exact L₃.apply_symm_apply w.val }
  let h₃ : (Euc 1 × (Euc 1 × EuclideanHalfSpace 1)) ≃ₜ EuclideanHalfSpace 3 :=
    { toEquiv := e₃
      continuous_toFun := (L₃.continuous.comp
        (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
          (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))).subtype_mk _
      continuous_invFun :=
        (continuous_fst.comp (L₃.symm.continuous.comp continuous_subtype_val)).prodMk
          (((continuous_fst.comp continuous_snd).comp
            (L₃.symm.continuous.comp continuous_subtype_val)).prodMk
            (((continuous_snd.comp continuous_snd).comp
              (L₃.symm.continuous.comp continuous_subtype_val)).subtype_mk _)) }
  let B : PolarModelBridge :=
    { homeo := h₃
      linear := L₃
      formula := fun _ => rfl
      linear_formula := fun _ => rfl
      compatible := fun _ => rfl }
  let P : GivenExteriorPolarCollar E D :=
    { image := A.image
      image_eq := A.image_eq
      coordinates := ⟨A.coordinates.toEquiv,(H5_polar_smooth_inverse E D A).2.1,(H5_polar_smooth_inverse E D A).2.2⟩
      equation := A.equation
      model := B
      tubeInverse := A.tubeInverse
      tube_inverse_eq := A.inverse_eq
      inverse_formula := A.inverse_formula
      radius_lower := A.radius_lower
      smooth := (H5_polar_smooth_inverse E D A).1
      boundary := fun z theta => (hpositive z theta).1
      normal_positive := fun z theta => (hpositive z theta).2 }
  refine ⟨?_,P,rfl,HEq.rfl,HEq.rfl⟩
  intro z theta
  refine ⟨(hpositive z theta).1,2*inwardCoordinate (givenExteriorPolarMap E (z,theta,0))
    (mfderiv (𝓡∂ 1) (𝓡∂ 3) (fun t => givenExteriorPolarMap E (z,theta,t)) 0 timeUnit),?_,?_⟩
  · exact mul_pos (by norm_num) (hpositive z theta).2
  · ring

end Polar
end
end SeifertSurfaces.LongitudeProducers.CollarCutHelpers.Remaining
