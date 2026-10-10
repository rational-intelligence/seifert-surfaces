import NormalFormAssembly
import OrientationTransition_v395
import LocalCircleDegree_v395
import CurveComplexGenusTwo.CWHurewicz.PairHomotopyInvariance
import Mathlib.Topology.Instances.Sign
import CurveComplexGenusTwo.Topology.ActualCrosscapGeometry.RawCrosscapSquareStrip
import CurveComplexGenusTwo.Topology.ActualCutRecognition.TwistedBandReflectionExportStatement

set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Topology CategoryTheory CategoryTheory.Limits
open scoped unitInterval Manifold ContDiff
open CurveComplex CurveComplexGenusTwo.CWHurewicz
open SeifertSurfaces.Foundations CurveComplex
namespace SeifertSurfaces.GenusLinking
noncomputable section

private def actualCenteredChartMap {X : Type} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) : C(e.source,ℂ) :=
  ⟨fun y => e y.val-e x,
    (e.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩

private theorem actual_centered_chart_preserves {X : Type} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) (hx : x ∈ e.source) :
    ∀ y ∈ ({y : e.source | y.val ≠ x}), actualCenteredChartMap e x y ∈ ({0}ᶜ : Set ℂ) := by
  intro y hy hzero
  exact hy (e.injOn y.property hx (sub_eq_zero.mp hzero))

private theorem actual_chart_source_inclusion_isIso {X : Type} [TopologicalSpace X] [T1Space X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) (hx : x ∈ e.source) :
    IsIso (pairRelativeHomologyMap {y : e.source | y.val ≠ x} ({x}ᶜ : Set X)
      (ReflectionGermProof.inclusion e.source) (fun y hy => hy) 2) :=
  ReflectionGermProof.inclusion_isIso ({x}ᶜ : Set X) e.source
    (ReflectionGermProof.puncture_excision x e.source e.open_source hx)

private theorem actual_centered_chart_map_isIso {X : Type} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) (hx : x ∈ e.source) :
    IsIso (pairRelativeHomologyMap {y : e.source | y.val ≠ x} ({0}ᶜ : Set ℂ)
      (actualCenteredChartMap e x) (actual_centered_chart_preserves e x hx) 2) := by
  let W := e.source
  let T := e.target
  let A : Set W := {y | y.val ≠ x}
  let B : Set T := {y | y.val ≠ e x}
  let h : W ≃ₜ T := e.toHomeomorphSourceTarget
  let k : C(W,T) := ⟨h,h.continuous⟩
  let j := ReflectionGermProof.inclusion T
  let t : ℂ ≃ₜ ℂ := Homeomorph.addRight (-e x)
  have hk : ∀ y ∈ A, k y ∈ B := by
    intro y hy hzero
    exact hy (e.injOn y.property hx hzero)
  have hki : ∀ y ∈ B, h.symm y ∈ A := by
    intro y hy hzero
    apply hy
    have he := congrArg e hzero
    change e (e.symm y.val)=e x at he
    rwa [e.right_inv y.property] at he
  have hj : ∀ y ∈ B, j y ∈ ({e x}ᶜ : Set ℂ) := fun y hy => hy
  have ht : ∀ y ∈ ({e x}ᶜ : Set ℂ), t y ∈ ({0}ᶜ : Set ℂ) := by
    intro y hy hzero
    apply hy
    exact sub_eq_zero.mp hzero
  have hti : ∀ y ∈ ({0}ᶜ : Set ℂ), t.symm y ∈ ({e x}ᶜ : Set ℂ) := by
    intro y hy hzero
    apply hy
    have he := congrArg t hzero
    simpa [t] using he
  haveI : IsIso (pairRelativeHomologyMap A B k hk 2) :=
    ReflectionGermProof.pairHomeo_isIso A B h hk hki 2
  haveI : IsIso (pairRelativeHomologyMap B ({e x}ᶜ : Set ℂ) j hj 2) :=
    ReflectionGermProof.inclusion_isIso ({e x}ᶜ : Set ℂ) T
      (ReflectionGermProof.puncture_excision (e x) T e.open_target (e.map_source hx))
  haveI : IsIso (pairRelativeHomologyMap ({e x}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ)
      ⟨t,t.continuous⟩ ht 2) :=
    ReflectionGermProof.pairHomeo_isIso _ _ t ht hti 2
  have hf : (⟨t,t.continuous⟩ : C(ℂ,ℂ)).comp (j.comp k)=actualCenteredChartMap e x := by
    ext y
    rfl
  have hcomp := pairRelativeHomologyMap_comp A ({e x}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ)
    (j.comp k) ⟨t,t.continuous⟩ (fun y hy => hk y hy) ht 2
  have hcomp' := pairRelativeHomologyMap_comp A B ({e x}ᶜ : Set ℂ) k j hk hj 2
  have hcomp0 : pairRelativeHomologyMap A ({0}ᶜ : Set ℂ)
      (actualCenteredChartMap e x) (actual_centered_chart_preserves e x hx) 2 =
      pairRelativeHomologyMap A ({e x}ᶜ : Set ℂ) (j.comp k) (fun y hy => hk y hy) 2 ≫
        pairRelativeHomologyMap ({e x}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ) ⟨t,t.continuous⟩ ht 2 := by
    simpa only [hf] using hcomp
  rw [hcomp0,hcomp']
  infer_instance

private def actualChartLocalIso {X : Type} [TopologicalSpace X] [T1Space X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) (hx : x ∈ e.source) :
    relativeHomology X ({x}ᶜ : Set X) 2 ≅ relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 := by
  letI := actual_chart_source_inclusion_isIso e x hx
  letI := actual_centered_chart_map_isIso e x hx
  exact (asIso (pairRelativeHomologyMap {y : e.source | y.val ≠ x} ({x}ᶜ : Set X)
    (ReflectionGermProof.inclusion e.source) (fun y hy => hy) 2)).symm ≪≫
      asIso (pairRelativeHomologyMap {y : e.source | y.val ≠ x} ({0}ᶜ : Set ℂ)
        (actualCenteredChartMap e x) (actual_centered_chart_preserves e x hx) 2)

private theorem actual_chart_local_iso_fac {X : Type} [TopologicalSpace X] [T1Space X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) (hx : x ∈ e.source) :
    pairRelativeHomologyMap {y : e.source | y.val ≠ x} ({x}ᶜ : Set X)
      (ReflectionGermProof.inclusion e.source) (fun y hy => hy) 2 ≫
      (actualChartLocalIso e x hx).hom =
    pairRelativeHomologyMap {y : e.source | y.val ≠ x} ({0}ᶜ : Set ℂ)
      (actualCenteredChartMap e x) (actual_centered_chart_preserves e x hx) 2 := by
  letI := actual_chart_source_inclusion_isIso e x hx
  simp [actualChartLocalIso]

private theorem actual_punctured_ball_family_homology
    (r : ℝ) (F : C(unitInterval × Metric.ball (0:ℂ) r,ℂ))
    (hpuncture : ∀ t : unitInterval, ∀ z : Metric.ball (0:ℂ) r,
      z.val ≠ 0 → F (t,z) ≠ 0) :
    pairRelativeHomologyMap {z : Metric.ball (0:ℂ) r | z.val ≠ 0} ({0}ᶜ : Set ℂ)
      ⟨fun z => F (0,z),F.continuous.comp (continuous_const.prodMk continuous_id)⟩
      (fun z hz => hpuncture 0 z hz) 2 =
    pairRelativeHomologyMap {z : Metric.ball (0:ℂ) r | z.val ≠ 0} ({0}ᶜ : Set ℂ)
      ⟨fun z => F (1,z),F.continuous.comp (continuous_const.prodMk continuous_id)⟩
      (fun z hz => hpuncture 1 z hz) 2 := by
  let H : ContinuousMap.Homotopy
      (⟨fun z => F (0,z),F.continuous.comp (continuous_const.prodMk continuous_id)⟩ :
        C(Metric.ball (0:ℂ) r,ℂ))
      ⟨fun z => F (1,z),F.continuous.comp (continuous_const.prodMk continuous_id)⟩ := {
    toContinuousMap := F
    map_zero_left := fun _ => rfl
    map_one_left := fun _ => rfl }
  exact pairRelativeHomologyMap_homotopy _ _ _ _ _ _ H hpuncture 2

#print axioms actualChartLocalIso
#print axioms actual_punctured_ball_family_homology

private def actualInteriorExtendedChart (S : CompactOrientedSurface.{0}) (p : S) :
    OpenPartialHomeomorph S (Euc 2) where
  toFun := extChartAt (𝓡∂ 2) p
  invFun := (extChartAt (𝓡∂ 2) p).symm
  source := (extChartAt (𝓡∂ 2) p).source ∩
    (extChartAt (𝓡∂ 2) p) ⁻¹' interior (extChartAt (𝓡∂ 2) p).target
  target := interior (extChartAt (𝓡∂ 2) p).target
  map_source' := fun _ h => h.2
  map_target' := by
    intro y hy
    refine ⟨(extChartAt (𝓡∂ 2) p).map_target (interior_subset hy),?_⟩
    change extChartAt (𝓡∂ 2) p ((extChartAt (𝓡∂ 2) p).symm y) ∈
      interior (extChartAt (𝓡∂ 2) p).target
    rw [(extChartAt (𝓡∂ 2) p).right_inv (interior_subset hy)]
    exact hy
  left_inv' := fun _ h => (extChartAt (𝓡∂ 2) p).left_inv h.1
  right_inv' := fun _ h => (extChartAt (𝓡∂ 2) p).right_inv (interior_subset h)
  open_source := isOpen_extChartAt_preimage' p isOpen_interior
  open_target := isOpen_interior
  continuousOn_toFun := (continuousOn_extChartAt p).mono Set.inter_subset_left
  continuousOn_invFun := (continuousOn_extChartAt_symm p).mono interior_subset

private def actualEucComplex : Euc 2 ≃L[ℝ] ℂ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans
    ((LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv.trans Complex.equivRealProdCLM.symm)

private def actualNativeComplexChart (S : CompactOrientedSurface.{0}) (p : S) :
    OpenPartialHomeomorph S ℂ :=
  (actualInteriorExtendedChart S p).trans actualEucComplex.toHomeomorph.toOpenPartialHomeomorph

private theorem actual_native_complex_chart_source (S : CompactOrientedSurface.{0}) (p x : S) :
    x ∈ (actualNativeComplexChart S p).source ↔
      x ∈ (extChartAt (𝓡∂ 2) p).source ∧ (𝓡∂ 2).IsInteriorPoint x := by
  simp only [actualNativeComplexChart,OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ]
  change (x ∈ (extChartAt (𝓡∂ 2) p).source ∧
    extChartAt (𝓡∂ 2) p x ∈ interior (extChartAt (𝓡∂ 2) p).target) ↔ _
  constructor
  · intro hx
    refine ⟨hx.1,?_⟩
    have hs : x ∈ (chartAt (EuclideanHalfSpace 2) p).source := by
      simpa only [extChartAt_source] using hx.1
    exact ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := (∞ : ℕ∞ω)) (by simp)
      (chart_mem_atlas (EuclideanHalfSpace 2) p) hs).mpr hx.2
  · intro hx
    refine ⟨hx.1,?_⟩
    have hs : x ∈ (chartAt (EuclideanHalfSpace 2) p).source := by
      simpa only [extChartAt_source] using hx.1
    exact ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := (∞ : ℕ∞ω)) (by simp)
      (chart_mem_atlas (EuclideanHalfSpace 2) p) hs).mp hx.2

#print axioms actualNativeComplexChart
#print axioms actual_native_complex_chart_source

private def actualOrientationProviderName (m leaf : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num (Lean.Name.str (Lean.Name.str .anonymous "_private") m) 0)
      "SeifertSurfaces") "GenusLinking") leaf

private def actualNativeCoefficient (S : CompactOrientedSurface.{0}) (p x : S) : ℝ :=
  S.orientation.form x
    (fun k => mfderivWithin 𝓘(ℝ,Euc 2) (𝓡∂ 2)
      (extChartAt (𝓡∂ 2) p).symm (extChartAt (𝓡∂ 2) p).target
      (extChartAt (𝓡∂ 2) p x)
      ((tangentSpaceCastModel 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) p x)).symm
        (EuclideanSpace.single k 1)))

private theorem actual_native_coefficient_ne_zero (S : CompactOrientedSurface.{0}) (p x : S)
    (hx : x ∈ (extChartAt (𝓡∂ 2) p).source) : actualNativeCoefficient S p x ≠ 0 := by
  run_tac do
    let name := actualOrientationProviderName "OrientationTransition_v395" "actual_chart_coefficient_ne_zero"
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent name) _ _ _ (by assumption)))

private theorem actual_native_coefficient_continuousOn (S : CompactOrientedSurface.{0}) (p : S) :
    ContinuousOn (actualNativeCoefficient S p) (extChartAt (𝓡∂ 2) p).source := by
  let c := extChartAt (𝓡∂ 2) p
  let f : Euc 2 → ℝ := fun y => S.orientation.form (c.symm y)
    (fun k => mfderivWithin 𝓘(ℝ,Euc 2) (𝓡∂ 2) c.symm c.target y
      ((tangentSpaceCastModel 𝓘(ℝ,Euc 2) y).symm (EuclideanSpace.single k 1)))
  have hfc : ContinuousOn f c.target := (S.orientation.smooth_coefficients p).continuousOn
  have hcomp : ContinuousOn (f ∘ c) c.source :=
    hfc.comp (continuousOn_extChartAt p) c.mapsTo
  apply hcomp.congr
  intro x hx
  change actualNativeCoefficient S p x = f (c x)
  dsimp [f,actualNativeCoefficient]
  rw [c.left_inv hx]
  rfl

private theorem actual_native_coefficient_sign_constant (S : CompactOrientedSurface.{0}) (p : S)
    (U : Set S) (hU : IsPreconnected U) (hUs : U ⊆ (extChartAt (𝓡∂ 2) p).source)
    (x y : S) (hx : x ∈ U) (hy : y ∈ U) :
    SignType.sign (actualNativeCoefficient S p x)=SignType.sign (actualNativeCoefficient S p y) := by
  apply hU.constant _ hx hy
  intro z hz
  exact (continuousAt_sign_of_ne_zero (actual_native_coefficient_ne_zero S p z (hUs hz))).comp_continuousWithinAt
    ((actual_native_coefficient_continuousOn S p z (hUs hz)).mono hUs)

#print axioms actual_native_coefficient_sign_constant

private theorem actual_chart_local_iso_on_subset {X : Type} [TopologicalSpace X] [T1Space X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) (hx : x ∈ e.source)
    (U : Set X) (hUs : U ⊆ e.source) :
    let i := ReflectionGermProof.inclusion U
    let k : C(U,ℂ) := ⟨fun y => e y.val-e x,
      (e.continuousOn.comp_continuous continuous_subtype_val (fun y => hUs y.property)).sub continuous_const⟩
    pairRelativeHomologyMap {y : U | y.val ≠ x} ({x}ᶜ : Set X) i (fun y hy => hy) 2 ≫
        (actualChartLocalIso e x hx).hom =
      pairRelativeHomologyMap {y : U | y.val ≠ x} ({0}ᶜ : Set ℂ) k
        (fun y hy hzero => hy (e.injOn (hUs y.property) hx (sub_eq_zero.mp hzero))) 2 := by
  dsimp only
  let D : Set U := {y | y.val ≠ x}
  let A : Set e.source := {y | y.val ≠ x}
  let j : C(U,e.source) := ⟨fun y => ⟨y.val,hUs y.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  have hj : ∀ y ∈ D, j y ∈ A := fun y hy => hy
  have hcomp := pairRelativeHomologyMap_comp D A ({x}ᶜ : Set X) j
    (ReflectionGermProof.inclusion e.source) hj (fun y hy => hy) 2
  have hcomp' := pairRelativeHomologyMap_comp D A ({0}ᶜ : Set ℂ) j
    (actualCenteredChartMap e x) hj (actual_centered_chart_preserves e x hx) 2
  change pairRelativeHomologyMap D ({x}ᶜ : Set X)
      ((ReflectionGermProof.inclusion e.source).comp j) _ 2 ≫ _ = _
  rw [hcomp,Category.assoc,actual_chart_local_iso_fac]
  exact hcomp'.symm

private theorem actual_chart_local_iso_on_map {X Z : Type} [TopologicalSpace X] [T1Space X]
    [TopologicalSpace Z] (e : OpenPartialHomeomorph X ℂ) (x : X) (hx : x ∈ e.source)
    (D : Set Z) (f : C(Z,X)) (hf : ∀ z, f z ∈ e.source)
    (hpres : ∀ z ∈ D, f z ∈ ({x}ᶜ : Set X)) :
    let k : C(Z,ℂ) := ⟨fun z => e (f z)-e x,
      (e.continuousOn.comp_continuous f.continuous hf).sub continuous_const⟩
    pairRelativeHomologyMap D ({x}ᶜ : Set X) f hpres 2 ≫
      (actualChartLocalIso e x hx).hom =
    pairRelativeHomologyMap D ({0}ᶜ : Set ℂ) k
      (fun z hz hzero => hpres z hz (e.injOn (hf z) hx (sub_eq_zero.mp hzero))) 2 := by
  dsimp only
  let A : Set e.source := {y | y.val ≠ x}
  let j : C(Z,e.source) := ⟨fun z => ⟨f z,hf z⟩,f.continuous.subtype_mk _⟩
  have hj : ∀ z ∈ D, j z ∈ A := fun z hz => hpres z hz
  have hcomp := pairRelativeHomologyMap_comp D A ({x}ᶜ : Set X) j
    (ReflectionGermProof.inclusion e.source) hj (fun y hy => hy) 2
  have hcomp' := pairRelativeHomologyMap_comp D A ({0}ᶜ : Set ℂ) j
    (actualCenteredChartMap e x) hj (actual_centered_chart_preserves e x hx) 2
  change pairRelativeHomologyMap D ({x}ᶜ : Set X)
      ((ReflectionGermProof.inclusion e.source).comp j) _ 2 ≫ _ = _
  rw [hcomp,Category.assoc,actual_chart_local_iso_fac]
  exact hcomp'.symm

#print axioms actual_chart_local_iso_on_map

private theorem actual_native_transition_derivative (S : CompactOrientedSurface.{0})
    (p q x : S) (hp : x ∈ (extChartAt (𝓡∂ 2) p).source)
    (hq : x ∈ (extChartAt (𝓡∂ 2) q).source) (hi : (𝓡∂ 2).IsInteriorPoint x) :
    ∃ A : Euc 2 ≃L[ℝ] Euc 2,
      HasFDerivAt ((extChartAt (𝓡∂ 2) q) ∘ (extChartAt (𝓡∂ 2) p).symm)
        A.toContinuousLinearMap (extChartAt (𝓡∂ 2) p x) ∧
      LinearMap.det A.toLinearEquiv.toLinearMap =
        actualNativeCoefficient S p x / actualNativeCoefficient S q x := by
  let cp := extChartAt (𝓡∂ 2) p
  let cq := extChartAt (𝓡∂ 2) q
  let y := cp x
  have ht : y ∈ cp.target := cp.map_source hp
  have hint : y ∈ interior cp.target := by
    have hsp : x ∈ (chartAt (EuclideanHalfSpace 2) p).source := by
      simpa only [extChartAt_source] using hp
    exact ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := (∞ : ℕ∞ω)) (by simp)
      (chart_mem_atlas (EuclideanHalfSpace 2) p) hsp).mp hi
  have hnhds : cp.target ∈ nhds y := mem_interior_iff_mem_nhds.mp hint
  have hdu : UniqueMDiffWithinAt 𝓘(ℝ,Euc 2) cp.target y :=
    (uniqueDiffOn_extChartAt_target p y ht).uniqueMDiffWithinAt
  have hd := (mdifferentiableWithinAt_extChartAt_symm ht).mfderivWithin_mono hdu
    (extChartAt_target_subset_range p)
  have hBInv : (mfderivWithin 𝓘(ℝ,Euc 2) (𝓡∂ 2) cp.symm cp.target y).IsInvertible := by
    rw [hd]
    exact isInvertible_mfderivWithin_extChartAt_symm ht
  obtain ⟨B,hB⟩ := hBInv
  obtain ⟨D,hD⟩ := isInvertible_mfderiv_extChartAt hq
  let A : Euc 2 ≃L[ℝ] Euc 2 := B.trans D
  have hBs : MDifferentiableWithinAt 𝓘(ℝ,Euc 2) (𝓡∂ 2) cp.symm cp.target y :=
    mdifferentiableOn_extChartAt_symm y ht
  have hDs : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ,Euc 2) cq x := by
    apply mdifferentiableAt_extChartAt
    simpa only [extChartAt_source] using hq
  have hDc : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ,Euc 2) cq (cp.symm y) := by
    rwa [cp.left_inv hp]
  have hchain := hDc.hasMFDerivAt.comp y (hBs.hasMFDerivWithinAt.hasMFDerivAt hnhds)
  have hder : HasFDerivAt (cq ∘ cp.symm) A.toContinuousLinearMap y := by
    have hc := hchain.hasFDerivAt
    rw [cp.left_inv hp,← hB,← hD] at hc
    exact hc
  refine ⟨A,hder,?_⟩
  have hfwithin : fderivWithin ℝ (cq ∘ cp.symm) cp.target y=A.toContinuousLinearMap :=
    hder.hasFDerivWithinAt.fderivWithin (uniqueDiffOn_extChartAt_target p y ht)
  have hm : LinearMap.det A.toLinearEquiv.toLinearMap =
      Matrix.det (show Matrix (Fin 2) (Fin 2) ℝ from
        fun i j => fderivWithin ℝ (cq ∘ cp.symm) cp.target y
          (EuclideanSpace.single j 1) i) := by
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
    congr 1
    ext i j
    simp only [LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr]
    rw [hfwithin]
    rw [show (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis j=EuclideanSpace.single j 1 from
      EuclideanSpace.basisFun_apply _ _ _]
    rfl
  rw [hm]
  run_tac do
    let name := actualOrientationProviderName "OrientationTransition_v395"
      "actual_transition_det_eq_coefficient_ratio"
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent name) _ _ _ _ (by assumption) (by assumption)))

#print axioms actual_native_transition_derivative

private theorem actual_local_chart_comparison {X : Type} [TopologicalSpace X] [T1Space X]
    (e f : OpenPartialHomeomorph X ℂ) (x : X) (he : x ∈ e.source) (hf : x ∈ f.source)
    (r : ℝ) (hr : 0 < r)
    (hball : ∀ z : Metric.ball (0:ℂ) r, z.val+e x ∈ e.target)
    (hother : ∀ z : Metric.ball (0:ℂ) r, e.symm (z.val+e x) ∈ f.source)
    (ε : Bool)
    (hdegree :
      let B := Metric.ball (0:ℂ) r
      let D : Set B := {z | z.val ≠ 0}
      let k : C(B,ℂ) := ⟨fun z => f (e.symm (z.val+e x))-f x,
        (f.continuousOn.comp_continuous
          (e.symm.continuousOn.comp_continuous
            (continuous_subtype_val.add continuous_const) hball) hother).sub continuous_const⟩
      pairRelativeHomologyMap D ({0}ᶜ : Set ℂ) k
        (fun z hz hzero => hz (by
          have heq := f.injOn (hother z) hf (sub_eq_zero.mp hzero)
          have heq' := congrArg e heq
          rw [e.right_inv (hball z)] at heq'
          exact add_right_cancel (show z.val + e x = 0 + e x by simpa using heq'))) 2 =
        if ε then pairRelativeHomologyMap D ({0}ᶜ : Set ℂ)
          (ReflectionGermProof.inclusion B) (fun z hz => hz) 2
        else -(pairRelativeHomologyMap D ({0}ᶜ : Set ℂ)
          (ReflectionGermProof.inclusion B) (fun z hz => hz) 2)) :
    (actualChartLocalIso f x hf).hom =
      if ε then (actualChartLocalIso e x he).hom else -(actualChartLocalIso e x he).hom := by
  let B := Metric.ball (0:ℂ) r
  let D : Set B := {z | z.val ≠ 0}
  let P : Set ℂ := {0}ᶜ
  let j : C(B,X) := ⟨fun z => e.symm (z.val+e x),
    e.symm.continuousOn.comp_continuous
      (continuous_subtype_val.add continuous_const) hball⟩
  have hje : ∀ z, j z ∈ e.source := fun z => e.map_target (hball z)
  have hjx : ∀ z ∈ D, j z ∈ ({x}ᶜ : Set X) := by
    intro z hz heq
    apply hz
    have heq' := congrArg e heq
    change e (e.symm (z.val+e x))=e x at heq'
    rw [e.right_inv (hball z)] at heq'
    exact add_right_cancel (show z.val + e x = 0 + e x by simpa using heq')
  let J := pairRelativeHomologyMap D ({x}ᶜ : Set X) j hjx 2
  let hIncl := pairRelativeHomologyMap D P (ReflectionGermProof.inclusion B) (fun z hz => hz) 2
  have hE : J ≫ (actualChartLocalIso e x he).hom=hIncl := by
    have hc := actual_chart_local_iso_on_map e x he D j hje hjx
    dsimp only at hc
    have hke : (⟨fun z : B => e (j z)-e x,
        (e.continuousOn.comp_continuous j.continuous hje).sub continuous_const⟩ : C(B,ℂ))=
        ReflectionGermProof.inclusion B := by
      ext z
      change e (e.symm (z.val+e x))-e x=z.val
      rw [e.right_inv (hball z)]
      abel
    simpa only [hke,hIncl] using hc
  have hF : J ≫ (actualChartLocalIso f x hf).hom = if ε then hIncl else -hIncl := by
    have hc := actual_chart_local_iso_on_map f x hf D j hother hjx
    exact hc.trans hdegree
  haveI : IsIso hIncl := ReflectionGermProof.inclusion_isIso P B
    (ReflectionGermProof.puncture_excision 0 B Metric.isOpen_ball (Metric.mem_ball_self hr))
  haveI : IsIso (J ≫ (actualChartLocalIso e x he).hom) := by
    rw [hE]
    infer_instance
  haveI : IsIso J := CategoryTheory.IsIso.of_isIso_comp_right J (actualChartLocalIso e x he).hom
  apply (cancel_epi J).mp
  cases ε <;> simp only [Bool.false_eq_true,if_false,if_true] at hF ⊢
  · rw [Preadditive.comp_neg,hE]
    exact hF
  · rw [hE]
    exact hF

#print axioms actual_local_chart_comparison

private def actualShiftChart {X : Type} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) : OpenPartialHomeomorph X ℂ :=
  e.trans (Homeomorph.addRight (-e x)).toOpenPartialHomeomorph

private theorem actual_shift_chart_source {X : Type} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) : (actualShiftChart e x).source=e.source := by
  simp [actualShiftChart,OpenPartialHomeomorph.trans_source]

private theorem actual_shift_chart_apply {X : Type} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (x y : X) : actualShiftChart e x y=e y-e x := by
  rfl

private theorem actual_shift_chart_symm_apply {X : Type} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) (z : ℂ) :
    (actualShiftChart e x).symm z=e.symm (z+e x) := by
  simp [actualShiftChart,OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_apply,Homeomorph.addRight_symm]

private theorem actual_native_complex_transition_derivative (S : CompactOrientedSurface.{0})
    (p q x : S) (hp : x ∈ (actualNativeComplexChart S p).source)
    (hq : x ∈ (actualNativeComplexChart S q).source) :
    let e := actualNativeComplexChart S p
    let f := actualNativeComplexChart S q
    let transitionMap := (actualShiftChart e x).symm.trans (actualShiftChart f x)
    ∃ A : ℂ ≃L[ℝ] ℂ, transitionMap 0=0 ∧ HasFDerivAt transitionMap A.toContinuousLinearMap 0 ∧
      LinearMap.det A.toLinearEquiv.toLinearMap =
        actualNativeCoefficient S p x / actualNativeCoefficient S q x := by
  let e := actualNativeComplexChart S p
  let f := actualNativeComplexChart S q
  let transitionMap := (actualShiftChart e x).symm.trans (actualShiftChart f x)
  obtain ⟨hps,hi⟩ := (actual_native_complex_chart_source S p x).mp hp
  obtain ⟨hqs,_⟩ := (actual_native_complex_chart_source S q x).mp hq
  obtain ⟨D,hD,hdet⟩ := actual_native_transition_derivative S p q x hps hqs hi
  let A : ℂ ≃L[ℝ] ℂ := (actualEucComplex.symm.trans D).trans actualEucComplex
  let cp := extChartAt (𝓡∂ 2) p
  let cq := extChartAt (𝓡∂ 2) q
  let g : ℂ → Euc 2 := fun z => actualEucComplex.symm (z+actualEucComplex (cp x))
  have hg : HasFDerivAt g actualEucComplex.symm.toContinuousLinearMap 0 :=
    actualEucComplex.symm.hasFDerivAt.comp 0 ((hasFDerivAt_id (0:ℂ)).add_const _)
  have hg0 : g 0=cp x := by simp [g]
  have hDg : HasFDerivAt (cq ∘ cp.symm) D.toContinuousLinearMap (g 0) := by
    rwa [hg0]
  have hcomplex := (actualEucComplex.hasFDerivAt.comp 0 (hDg.comp 0 hg)).sub_const (f x)
  have htransition : (fun z : ℂ => actualEucComplex ((cq ∘ cp.symm) (g z))-f x)=transitionMap := by
    funext z
    simp only [transitionMap,OpenPartialHomeomorph.trans_apply,actual_shift_chart_apply,
      actual_shift_chart_symm_apply]
    rfl
  have hzero : transitionMap 0=0 := by
    simp only [transitionMap,OpenPartialHomeomorph.trans_apply,actual_shift_chart_apply,
      actual_shift_chart_symm_apply,zero_add,e.left_inv hp,sub_self]
  refine ⟨A,hzero,?_,?_⟩
  · rw [← htransition]
    exact hcomplex
  · have hc : LinearMap.det A.toLinearEquiv.toLinearMap=
        LinearMap.det D.toLinearEquiv.toLinearMap := by
      exact LinearMap.det_conj D.toLinearEquiv.toLinearMap actualEucComplex.toLinearEquiv
    exact hc.trans hdet

#print axioms actual_native_complex_transition_derivative

private theorem actual_shift_chart_target {X : Type} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) (z : ℂ) :
    z ∈ (actualShiftChart e x).target ↔ z+e x ∈ e.target := by
  simp [actualShiftChart,OpenPartialHomeomorph.trans_target,Homeomorph.addRight_symm]

private theorem actual_derivative_chart_comparison {X : Type} [TopologicalSpace X] [T1Space X]
    (e f : OpenPartialHomeomorph X ℂ) (x : X) (he : x ∈ e.source) (hf : x ∈ f.source)
    (A : ℂ ≃L[ℝ] ℂ)
    (hder : HasFDerivAt ((actualShiftChart e x).symm.trans (actualShiftChart f x))
      A.toContinuousLinearMap 0) :
    (actualChartLocalIso f x hf).hom=
      if 0 < LinearMap.det A.toLinearEquiv.toLinearMap
      then (actualChartLocalIso e x he).hom else -(actualChartLocalIso e x he).hom := by
  let transitionMap := (actualShiftChart e x).symm.trans (actualShiftChart f x)
  have hzero : transitionMap 0=0 := by
    simp only [transitionMap,OpenPartialHomeomorph.trans_apply,actual_shift_chart_apply,
      actual_shift_chart_symm_apply,zero_add,e.left_inv he,sub_self]
  have hs0 : (0:ℂ) ∈ transitionMap.source := by
    change 0 ∈ (actualShiftChart e x).target ∧
      (actualShiftChart e x).symm 0 ∈ (actualShiftChart f x).source
    rw [actual_shift_chart_target,zero_add,actual_shift_chart_symm_apply,zero_add,
      e.left_inv he,actual_shift_chart_source]
    exact ⟨e.map_source he,hf⟩
  obtain ⟨R,hR,hRsub⟩ := Metric.isOpen_iff.mp transitionMap.open_source 0 hs0
  let r := R/2
  have hr : 0 < r := by dsimp [r]; linarith
  have hclosed : Metric.closedBall (0:ℂ) r ⊆ transitionMap.source :=
    (Metric.closedBall_subset_ball (by dsimp [r]; linarith)).trans hRsub
  let B := Metric.ball (0:ℂ) r
  let D : Set B := {z | z.val ≠ 0}
  have hsource (z : B) : z.val ∈ transitionMap.source :=
    hclosed (Metric.ball_subset_closedBall z.property)
  have hball (z : B) : z.val+e x ∈ e.target :=
    (actual_shift_chart_target e x z.val).mp (hsource z).1
  have hother (z : B) : e.symm (z.val+e x) ∈ f.source := by
    have h := (hsource z).2
    change (actualShiftChart e x).symm z.val ∈ (actualShiftChart f x).source at h
    rwa [actual_shift_chart_symm_apply,actual_shift_chart_source] at h
  have hlocal : ∃ k : C(B,ℂ), (∀ z : B, k z=transitionMap z.val) ∧
      ∃ hk : ∀ z ∈ D, k z ∈ ({0}ᶜ : Set ℂ),
        pairRelativeHomologyMap D ({0}ᶜ : Set ℂ) k hk 2=
          if 0 < LinearMap.det A.toLinearEquiv.toLinearMap
          then pairRelativeHomologyMap D ({0}ᶜ : Set ℂ)
            (ReflectionGermProof.inclusion B) (fun z hz => hz) 2
          else -(pairRelativeHomologyMap D ({0}ᶜ : Set ℂ)
            (ReflectionGermProof.inclusion B) (fun z hz => hz) 2) := by
    run_tac do
      let name := actualOrientationProviderName "LocalCircleDegree_v395" "actual_open_chart_relative_transport"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent name)
        _ _ (by assumption) (by assumption) _ (by assumption) (by assumption)))
  obtain ⟨k,hk,hpres,hmap⟩ := hlocal
  have hc := actual_local_chart_comparison e f x he hf r hr hball hother
    (decide (0 < LinearMap.det A.toLinearEquiv.toLinearMap))
  have hcomp : (actualChartLocalIso f x hf).hom=
      if decide (0 < LinearMap.det A.toLinearEquiv.toLinearMap)
      then (actualChartLocalIso e x he).hom else -(actualChartLocalIso e x he).hom := by
    apply hc
    dsimp only
    have hke : k=(⟨fun z : B => f (e.symm (z.val+e x))-f x,
      (f.continuousOn.comp_continuous
        (e.symm.continuousOn.comp_continuous
          (continuous_subtype_val.add continuous_const) hball) hother).sub continuous_const⟩ : C(B,ℂ)) := by
      ext z
      rw [hk]
      simp only [transitionMap,OpenPartialHomeomorph.trans_apply,actual_shift_chart_apply,
        actual_shift_chart_symm_apply,ContinuousMap.coe_mk]
    have hcongr := ReflectionGermProof.pairMap_congr D ({0}ᶜ : Set ℂ) k _ hpres
      (by simpa only [hke] using hpres) hke 2
    rw [← hcongr]
    by_cases hpos : 0 < LinearMap.det A.toLinearEquiv.toLinearMap <;>
      simpa [hpos] using hmap
  simpa only [decide_eq_true_eq] using hcomp

private def actualNativeOrientedHom (S : CompactOrientedSurface.{0}) (p x : S)
    (hx : x ∈ (actualNativeComplexChart S p).source) :
    relativeHomology S ({x}ᶜ : Set S) 2 ⟶ relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 :=
  if 0 < actualNativeCoefficient S p x
  then (actualChartLocalIso (actualNativeComplexChart S p) x hx).hom
  else -(actualChartLocalIso (actualNativeComplexChart S p) x hx).hom

private theorem actual_native_oriented_hom_compatible (S : CompactOrientedSurface.{0})
    (p q x : S) (hp : x ∈ (actualNativeComplexChart S p).source)
    (hq : x ∈ (actualNativeComplexChart S q).source) :
    actualNativeOrientedHom S p x hp=actualNativeOrientedHom S q x hq := by
  obtain ⟨A,_,hder,hdet⟩ := actual_native_complex_transition_derivative S p q x hp hq
  have hc := actual_derivative_chart_comparison
    (actualNativeComplexChart S p) (actualNativeComplexChart S q) x hp hq A hder
  have hpn := actual_native_coefficient_ne_zero S p x
    ((actual_native_complex_chart_source S p x).mp hp).1
  have hqn := actual_native_coefficient_ne_zero S q x
    ((actual_native_complex_chart_source S q x).mp hq).1
  have hs : 0 < LinearMap.det A.toLinearEquiv.toLinearMap ↔
      (0 < actualNativeCoefficient S p x ↔ 0 < actualNativeCoefficient S q x) := by
    rw [hdet]
    rcases lt_or_gt_of_ne hpn with hpn|hpn <;>
      rcases lt_or_gt_of_ne hqn with hqn|hqn
    all_goals simp [div_pos_iff,hpn,hqn,not_lt_of_ge hpn.le,not_lt_of_ge hqn.le]
  unfold actualNativeOrientedHom
  rw [hc]
  by_cases hpp : 0 < actualNativeCoefficient S p x <;>
    by_cases hqp : 0 < actualNativeCoefficient S q x <;>
    simp only [hs,hpp,hqp,iff_self,iff_false,false_iff,not_true_eq_false,
      not_false_eq_true,ite_true,ite_false,neg_neg]

#print axioms actual_derivative_chart_comparison
#print axioms actual_native_oriented_hom_compatible

private theorem actual_native_oriented_hom_isIso (S : CompactOrientedSurface.{0})
    (p x : S) (hx : x ∈ (actualNativeComplexChart S p).source) :
    IsIso (actualNativeOrientedHom S p x hx) := by
  unfold actualNativeOrientedHom
  split_ifs
  · infer_instance
  · let e := actualChartLocalIso (actualNativeComplexChart S p) x hx
    let negIso : relativeHomology S ({x}ᶜ : Set S) 2 ≅ relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 := {
      hom := -e.hom
      inv := -e.inv
      hom_inv_id := by simp
      inv_hom_id := by simp }
    exact negIso.isIso_hom

private theorem actual_plane_chart_point_interior (S : CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : S) (hx : x ∈ e.source) :
    (𝓡∂ 2).IsInteriorPoint x := by
  let c : OpenPartialHomeomorph S (Euc 2) :=
    e.trans actualEucComplex.symm.toHomeomorph.toOpenPartialHomeomorph
  have hxc : x ∈ c.source := by
    simpa [c,OpenPartialHomeomorph.trans_source] using hx
  let u : c.target := ⟨c x,c.map_source hxc⟩
  have hf : Continuous (fun y : c.target => c.symm y.val) := c.symm.continuousOn.restrict
  have hinj : Function.Injective (fun y : c.target => c.symm y.val) := by
    intro y z heq
    exact Subtype.ext (c.symm.injOn y.property z.property heq)
  have hi : (𝓡∂ 2).IsInteriorPoint (c.symm u.val) := by
    run_tac do
      let name := actualOrientationProviderName "NormalFormAssembly" "open_plane_image_interior"
      let sn := Lean.mkIdent (Lean.Name.mkSimple "S")
      let cn := Lean.mkIdent (Lean.Name.mkSimple "c")
      let un := Lean.mkIdent (Lean.Name.mkSimple "u")
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent name)
        $sn (($cn).open_target) (fun y : ($cn).target => ($cn).symm y.val)
        (by assumption) (by assumption) $un))
  rwa [c.left_inv hxc] at hi

private def actualSmoothLocalOrientation (S : CompactOrientedSurface.{0}) (x : S)
    (hi : (𝓡∂ 2).IsInteriorPoint x) :
    relativeHomology S ({x}ᶜ : Set S) 2 ⟶ relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 :=
  actualNativeOrientedHom S x x
    ((actual_native_complex_chart_source S x x).mpr ⟨mem_extChartAt_source x,hi⟩)

private theorem actual_smooth_local_orientation_isIso (S : CompactOrientedSurface.{0})
    (x : S) (hi : (𝓡∂ 2).IsInteriorPoint x) : IsIso (actualSmoothLocalOrientation S x hi) :=
  actual_native_oriented_hom_isIso S x x _

private theorem actual_smooth_local_orientation_in_chart (S : CompactOrientedSurface.{0})
    (p x : S) (hx : x ∈ (actualNativeComplexChart S p).source)
    (hi : (𝓡∂ 2).IsInteriorPoint x) :
    actualSmoothLocalOrientation S x hi=actualNativeOrientedHom S p x hx :=
  actual_native_oriented_hom_compatible S x p x _ hx

private def actualTopologicalChartIndex (S : CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : e.source) :
    relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 ⟶ relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 :=
  (actualChartLocalIso e x.val x.property).inv ≫
    actualSmoothLocalOrientation S x.val (actual_plane_chart_point_interior S e x.val x.property)

private theorem actual_topological_chart_index_isIso (S : CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : e.source) : IsIso (actualTopologicalChartIndex S e x) := by
  letI := actual_smooth_local_orientation_isIso S x.val
    (actual_plane_chart_point_interior S e x.val x.property)
  unfold actualTopologicalChartIndex
  infer_instance

#print axioms actual_plane_chart_point_interior
#print axioms actual_topological_chart_index_isIso

private def actualChartGerm {X : Type} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) (r : ℝ)
    (hball : ∀ z : Metric.ball (0:ℂ) r, z.val+e x ∈ e.target) :
    C(Metric.ball (0:ℂ) r,X) :=
  ⟨fun z => e.symm (z.val+e x),e.symm.continuousOn.comp_continuous
    (continuous_subtype_val.add continuous_const) hball⟩

private theorem actual_chart_germ_preserves {X : Type} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) (hx : x ∈ e.source) (r : ℝ)
    (hball : ∀ z : Metric.ball (0:ℂ) r, z.val+e x ∈ e.target) :
    ∀ z ∈ {z : Metric.ball (0:ℂ) r | z.val ≠ 0},
      actualChartGerm e x r hball z ∈ ({x}ᶜ : Set X) := by
  intro z hz heq
  apply hz
  have heq' := congrArg e heq
  change e (e.symm (z.val+e x))=e x at heq'
  rw [e.right_inv (hball z)] at heq'
  exact add_right_cancel (show z.val+e x=0+e x by simpa using heq')

private theorem actual_chart_germ_normalization {X : Type} [TopologicalSpace X] [T1Space X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) (hx : x ∈ e.source) (r : ℝ)
    (hball : ∀ z : Metric.ball (0:ℂ) r, z.val+e x ∈ e.target) :
    pairRelativeHomologyMap {z : Metric.ball (0:ℂ) r | z.val ≠ 0} ({x}ᶜ : Set X)
      (actualChartGerm e x r hball) (actual_chart_germ_preserves e x hx r hball) 2 ≫
        (actualChartLocalIso e x hx).hom =
    pairRelativeHomologyMap {z : Metric.ball (0:ℂ) r | z.val ≠ 0} ({0}ᶜ : Set ℂ)
      (ReflectionGermProof.inclusion (Metric.ball (0:ℂ) r)) (fun z hz => hz) 2 := by
  have hsource (z : Metric.ball (0:ℂ) r) : actualChartGerm e x r hball z ∈ e.source :=
    e.map_target (hball z)
  have hc := actual_chart_local_iso_on_map e x hx _ (actualChartGerm e x r hball)
    hsource (actual_chart_germ_preserves e x hx r hball)
  dsimp only at hc
  have hke : (⟨fun z : Metric.ball (0:ℂ) r => e (actualChartGerm e x r hball z)-e x,
      (e.continuousOn.comp_continuous (actualChartGerm e x r hball).continuous hsource).sub continuous_const⟩ :
      C(Metric.ball (0:ℂ) r,ℂ))=ReflectionGermProof.inclusion (Metric.ball (0:ℂ) r) := by
    ext z
    change e (e.symm (z.val+e x))-e x=z.val
    rw [e.right_inv (hball z)]
    abel
  simpa only [hke] using hc

private theorem actual_chart_index_germ_formula (S : CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : e.source) (p : S)
    (hx : x.val ∈ (actualNativeComplexChart S p).source) (r : ℝ)
    (hball : ∀ z : Metric.ball (0:ℂ) r, z.val+e x.val ∈ e.target)
    (hother : ∀ z : Metric.ball (0:ℂ) r,
      actualChartGerm e x.val r hball z ∈ (actualNativeComplexChart S p).source) :
    let B := Metric.ball (0:ℂ) r
    let D : Set B := {z | z.val ≠ 0}
    let c := actualNativeComplexChart S p
    let k : C(B,ℂ) := ⟨fun z => c (actualChartGerm e x.val r hball z)-c x.val,
      (c.continuousOn.comp_continuous (actualChartGerm e x.val r hball).continuous hother).sub continuous_const⟩
    let hk : ∀ z ∈ D, k z ∈ ({0}ᶜ : Set ℂ) := fun z hz hzero =>
      actual_chart_germ_preserves e x.val x.property r hball z hz
        (c.injOn (hother z) hx (sub_eq_zero.mp hzero))
    pairRelativeHomologyMap D ({0}ᶜ : Set ℂ) (ReflectionGermProof.inclusion B) (fun z hz => hz) 2 ≫
      actualTopologicalChartIndex S e x =
      if 0 < actualNativeCoefficient S p x.val then pairRelativeHomologyMap D ({0}ᶜ : Set ℂ) k hk 2
      else -(pairRelativeHomologyMap D ({0}ᶜ : Set ℂ) k hk 2) := by
  dsimp only
  rw [← actual_chart_germ_normalization e x.val x.property r hball]
  unfold actualTopologicalChartIndex
  rw [Category.assoc,← Category.assoc (actualChartLocalIso e x.val x.property).hom,
    Iso.hom_inv_id,Category.id_comp]
  rw [actual_smooth_local_orientation_in_chart S p x.val hx]
  unfold actualNativeOrientedHom
  have hc := actual_chart_local_iso_on_map (actualNativeComplexChart S p) x.val hx _
    (actualChartGerm e x.val r hball) hother (actual_chart_germ_preserves e x.val x.property r hball)
  split_ifs
  · exact hc
  · rw [Preadditive.comp_neg]
    exact congrArg Neg.neg hc

#print axioms actual_chart_index_germ_formula

private theorem actual_chart_index_uniform_path (S : CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x y : e.source) (p : S)
    (hx : x.val ∈ (actualNativeComplexChart S p).source)
    (hy : y.val ∈ (actualNativeComplexChart S p).source)
    (hsign : 0 < actualNativeCoefficient S p x.val ↔ 0 < actualNativeCoefficient S p y.val)
    (r : ℝ) (hr : 0 < r) (L : C(unitInterval,ℂ))
    (hL0 : L 0=e x.val) (hL1 : L 1=e y.val)
    (hball : ∀ t : unitInterval, ∀ z : Metric.ball (0:ℂ) r, L t+z.val ∈ e.target)
    (hother : ∀ t : unitInterval, ∀ z : Metric.ball (0:ℂ) r,
      e.symm (L t+z.val) ∈ (actualNativeComplexChart S p).source) :
    actualTopologicalChartIndex S e x=actualTopologicalChartIndex S e y := by
  let B := Metric.ball (0:ℂ) r
  let D : Set B := {z | z.val ≠ 0}
  let P : Set ℂ := {0}ᶜ
  let c := actualNativeComplexChart S p
  let z0 : B := ⟨0,Metric.mem_ball_self hr⟩
  have hbaseTarget (t : unitInterval) : L t ∈ e.target := by
    simpa [z0] using hball t z0
  have hbaseChart (t : unitInterval) : e.symm (L t) ∈ c.source := by
    simpa [z0] using hother t z0
  let F : C(unitInterval × B,ℂ) := ⟨fun a =>
      c (e.symm (L a.1+a.2.val))-c (e.symm (L a.1)),
    (c.continuousOn.comp_continuous
      (e.symm.continuousOn.comp_continuous
        ((L.continuous.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd))
        (fun a => hball a.1 a.2)) (fun a => hother a.1 a.2)).sub
      (c.continuousOn.comp_continuous
        (e.symm.continuousOn.comp_continuous (L.continuous.comp continuous_fst)
          (fun a => hbaseTarget a.1)) (fun a => hbaseChart a.1))⟩
  have hpuncture (t : unitInterval) (z : B) (hz : z.val ≠ 0) : F (t,z) ≠ 0 := by
    intro hzero
    change c (e.symm (L t+z.val))-c (e.symm (L t))=0 at hzero
    have hceq := c.injOn (hother t z) (hbaseChart t) (sub_eq_zero.mp hzero)
    have heq := e.symm.injOn (hball t z) (hbaseTarget t) hceq
    exact hz (add_left_cancel (show L t+z.val=L t+0 by simpa using heq))
  have hhom := actual_punctured_ball_family_homology r F hpuncture
  have hbx (z : B) : z.val+e x.val ∈ e.target := by
    simpa only [hL0,add_comm] using hball 0 z
  have hby (z : B) : z.val+e y.val ∈ e.target := by
    simpa only [hL1,add_comm] using hball 1 z
  have hcx (z : B) : actualChartGerm e x.val r hbx z ∈ c.source := by
    change e.symm (z.val+e x.val) ∈ c.source
    simpa only [hL0,add_comm] using hother 0 z
  have hcy (z : B) : actualChartGerm e y.val r hby z ∈ c.source := by
    change e.symm (z.val+e y.val) ∈ c.source
    simpa only [hL1,add_comm] using hother 1 z
  have hxFormula := actual_chart_index_germ_formula S e x p hx r hbx hcx
  have hyFormula := actual_chart_index_germ_formula S e y p hy r hby hcy
  dsimp only at hxFormula hyFormula
  let kx : C(B,ℂ) := ⟨fun z => c (actualChartGerm e x.val r hbx z)-c x.val,
    (c.continuousOn.comp_continuous (actualChartGerm e x.val r hbx).continuous hcx).sub continuous_const⟩
  let ky : C(B,ℂ) := ⟨fun z => c (actualChartGerm e y.val r hby z)-c y.val,
    (c.continuousOn.comp_continuous (actualChartGerm e y.val r hby).continuous hcy).sub continuous_const⟩
  have hFx : (⟨fun z : B => F (0,z),F.continuous.comp (continuous_const.prodMk continuous_id)⟩ : C(B,ℂ))=kx := by
    ext z
    change c (e.symm (L 0+z.val))-c (e.symm (L 0))=
      c (e.symm (z.val+e x.val))-c x.val
    rw [hL0,e.left_inv x.property,add_comm (e x.val) z.val]
  have hFy : (⟨fun z : B => F (1,z),F.continuous.comp (continuous_const.prodMk continuous_id)⟩ : C(B,ℂ))=ky := by
    ext z
    change c (e.symm (L 1+z.val))-c (e.symm (L 1))=
      c (e.symm (z.val+e y.val))-c y.val
    rw [hL1,e.left_inv y.property,add_comm (e y.val) z.val]
  have hxPres : ∀ z ∈ D, kx z ∈ P := by
    intro z hz
    have h := hpuncture 0 z hz
    change (⟨fun z : B => F (0,z),F.continuous.comp (continuous_const.prodMk continuous_id)⟩ : C(B,ℂ)) z ≠ 0 at h
    rw [hFx] at h
    exact h
  have hyPres : ∀ z ∈ D, ky z ∈ P := by
    intro z hz
    have h := hpuncture 1 z hz
    change (⟨fun z : B => F (1,z),F.continuous.comp (continuous_const.prodMk continuous_id)⟩ : C(B,ℂ)) z ≠ 0 at h
    rw [hFy] at h
    exact h
  have hxy : pairRelativeHomologyMap D P kx hxPres 2=pairRelativeHomologyMap D P ky hyPres 2 := by
    change pairRelativeHomologyMap D P
      (⟨fun z : B => F (0,z),F.continuous.comp (continuous_const.prodMk continuous_id)⟩ : C(B,ℂ)) _ 2 =
      pairRelativeHomologyMap D P
      (⟨fun z : B => F (1,z),F.continuous.comp (continuous_const.prodMk continuous_id)⟩ : C(B,ℂ)) _ 2 at hhom
    simpa only [hFx,hFy] using hhom
  haveI : IsIso (pairRelativeHomologyMap D P (ReflectionGermProof.inclusion B) (fun z hz => hz) 2) :=
    ReflectionGermProof.inclusion_isIso P B
      (ReflectionGermProof.puncture_excision 0 B Metric.isOpen_ball (Metric.mem_ball_self hr))
  apply (cancel_epi (pairRelativeHomologyMap D P (ReflectionGermProof.inclusion B) (fun z hz => hz) 2)).mp
  rw [hxFormula,hyFormula]
  by_cases hpos : 0 < actualNativeCoefficient S p x.val
  · have hpos' := hsign.mp hpos
    simpa only [hpos,hpos',ite_true] using hxy
  · have hpos' : ¬0 < actualNativeCoefficient S p y.val := fun h => hpos (hsign.mpr h)
    simpa only [hpos,hpos',ite_false] using congrArg Neg.neg hxy

#print axioms actual_chart_index_uniform_path

private theorem actual_chart_index_locally_constant (S : CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) : IsLocallyConstant (actualTopologicalChartIndex S e) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  let p : S := x.val
  let c := actualNativeComplexChart S p
  have hx : x.val ∈ c.source :=
    (actual_native_complex_chart_source S p x.val).mpr
      ⟨mem_extChartAt_source x.val,actual_plane_chart_point_interior S e x.val x.property⟩
  let V : Set ℂ := e.target ∩ e.symm ⁻¹' c.source
  have hV : IsOpen V := e.symm.isOpen_inter_preimage c.open_source
  have hxV : e x.val ∈ V := ⟨e.map_source x.property,by
    change e.symm (e x.val) ∈ c.source
    rwa [e.left_inv x.property]⟩
  obtain ⟨R,hR,hRV⟩ := Metric.isOpen_iff.mp hV (e x.val) hxV
  let r : ℝ := R/4
  have hr : 0 < r := by dsimp [r]; positivity
  have hnear : ∀ᶠ y : e.source in 𝓝 x, e y.val ∈ Metric.ball (e x.val) r :=
    ((e.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).continuousAt).eventually
      (Metric.ball_mem_nhds (e x.val) hr)
  filter_upwards [hnear] with y hy
  let L : C(unitInterval,ℂ) := ⟨fun t => AffineMap.lineMap (e x.val) (e y.val) (t:ℝ),
    AffineMap.lineMap_continuous.comp continuous_subtype_val⟩
  have hL0 : L 0=e x.val := by simp [L]
  have hL1 : L 1=e y.val := by simp [L]
  have hLsmall (t : unitInterval) : L t ∈ Metric.ball (e x.val) r :=
    (convex_ball (e x.val) r).lineMap_mem (Metric.mem_ball_self hr) hy t.property
  have hLV (t : unitInterval) (z : Metric.ball (0:ℂ) r) : L t+z.val ∈ V := by
    apply hRV
    apply Metric.mem_ball.mpr
    have ht := Metric.mem_ball.mp (hLsmall t)
    have hz := Metric.mem_ball.mp z.property
    have hd : dist (L t+z.val) (e x.val) ≤ dist (L t) (e x.val)+dist z.val 0 := by
      simpa using dist_add_add_le (L t) z.val (e x.val) (0:ℂ)
    dsimp [r] at ht hz
    linarith
  let z0 : Metric.ball (0:ℂ) r := ⟨0,Metric.mem_ball_self hr⟩
  have hLt (t : unitInterval) : L t ∈ V := by simpa [z0] using hLV t z0
  have hyc : y.val ∈ c.source := by
    have h := (hLt 1).2
    change e.symm (L 1) ∈ c.source at h
    rwa [hL1,e.left_inv y.property] at h
  let path : C(unitInterval,S) := ⟨fun t => e.symm (L t),
    e.symm.continuousOn.comp_continuous L.continuous (fun t => (hLt t).1)⟩
  have hpath0 : path 0=x.val := by change e.symm (L 0)=x.val; rw [hL0,e.left_inv x.property]
  have hpath1 : path 1=y.val := by change e.symm (L 1)=y.val; rw [hL1,e.left_inv y.property]
  have hsub : Set.range path ⊆ (extChartAt (𝓡∂ 2) p).source := by
    rintro z ⟨t,rfl⟩
    exact ((actual_native_complex_chart_source S p (path t)).mp (hLt t).2).1
  have hsign := actual_native_coefficient_sign_constant S p (Set.range path)
    (isPreconnected_range path.continuous) hsub x.val y.val
    ⟨0,hpath0⟩ ⟨1,hpath1⟩
  have hpos : 0 < actualNativeCoefficient S p x.val ↔ 0 < actualNativeCoefficient S p y.val := by
    rw [← sign_eq_one_iff,← sign_eq_one_iff,hsign]
  exact (actual_chart_index_uniform_path S e x y p hx hyc hpos r hr L hL0 hL1
    (fun t z => (hLV t z).1) (fun t z => (hLV t z).2)).symm

#print axioms actual_chart_index_locally_constant

private theorem actual_surface_open_plane_image (S : CompactOrientedSurface.{0})
    (f : Euc 2 → S) (U : Set (Euc 2)) (hU : IsOpen U)
    (hf : ContinuousOn f U) (hinj : InjOn f U) : IsOpen (f '' U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro z ⟨x,hx,rfl⟩
  have hi : (𝓡∂ 2).IsInteriorPoint (f x) := by
    have hfc : Continuous (fun y : U => f y.val) := hf.restrict
    have hfi : Function.Injective (fun y : U => f y.val) := by
      intro y w he
      exact Subtype.ext (hinj y.property w.property he)
    run_tac do
      let name := actualOrientationProviderName "NormalFormAssembly" "open_plane_image_interior"
      let sn := Lean.mkIdent (Lean.Name.mkSimple "S")
      let fn := Lean.mkIdent (Lean.Name.mkSimple "f")
      let un := Lean.mkIdent (Lean.Name.mkSimple "U")
      let xn := Lean.mkIdent (Lean.Name.mkSimple "x")
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent name)
        $sn (by assumption) (fun y : $un => $fn y.val)
        (by assumption) (by assumption) ⟨$xn,by assumption⟩))
  let c := actualNativeComplexChart S (f x)
  have hxc : f x ∈ c.source := (actual_native_complex_chart_source S (f x) (f x)).mpr
    ⟨mem_extChartAt_source (f x),hi⟩
  let e := c.trans actualEucComplex.symm.toHomeomorph.toOpenPartialHomeomorph
  have hxe : f x ∈ e.source := by simpa [e,OpenPartialHomeomorph.trans_source] using hxc
  let V := U ∩ f ⁻¹' e.source
  have hV : IsOpen V := hf.isOpen_inter_preimage hU e.open_source
  have hxV : x ∈ V := ⟨hx,hxe⟩
  have hcomp : ContinuousOn (e ∘ f) V :=
    e.continuousOn.comp (hf.mono inter_subset_left) (fun _ hz => hz.2)
  have hcompI : InjOn (e ∘ f) V := by
    intro a ha b hb he
    exact hinj ha.1 hb.1 (e.injOn ha.2 hb.2 he)
  have hopen : IsOpen ((e ∘ f) '' V) :=
    LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.invariance_of_domain_open_map
      (e ∘ f) V hV hcomp hcompI
  have htarget : (e ∘ f) '' V ⊆ e.target := by
    rintro z ⟨y,hy,rfl⟩
    exact e.map_source hy.2
  have heq : e.symm '' ((e ∘ f) '' V)=f '' V := by
    rw [Set.image_image]
    apply Set.image_congr
    intro y hy
    exact e.left_inv hy.2
  have hfv : IsOpen (f '' V) := by
    rw [← heq]
    exact e.symm.isOpen_image_of_subset_source hopen htarget
  exact ⟨f '' V,Set.image_mono inter_subset_left,hfv,⟨x,hxV,rfl⟩⟩

#print axioms actual_surface_open_plane_image
private def actualCrosscapRectangle : Set (Euc 2) :=
  {z | z 0 ∈ Ioo 0 2 ∧ z 1 ∈ Ioo (-1) 1}

-- The square/strip assembly is the released geometric construction, with the
-- actual manifold-with-boundary open-image theorem above in its two chart steps.
private theorem actual_twisted_square_two_charts
    (S : CompactOrientedSurface.{0})
    (ε : ℝ) (hε : 0 < ε)
    (square : Metric.closedBall ((0,0) : ℝ × ℝ) ε → S)
    (hsquare : Topology.IsEmbedding square)
    (band : unitInterval × BandWidth → S)
    (hband : Topology.IsEmbedding band)
    (hbottom : ∀ t, band (0,t) = square (squarePort ε hε 2 t))
    (htop : ∀ t, band (1,t) = square (squarePort ε hε 0 (flipBandWidth true t)))
    (hmeet : Set.range band ∩ Set.range square =
      Set.range (fun t => square (squarePort ε hε 2 t)) ∪
      Set.range (fun t => square (squarePort ε hε 0 t))) :
    ∃ f g : C(Euc 2,S),
      IsOpenEmbedding (fun z : actualCrosscapRectangle => f z.val) ∧
      IsOpenEmbedding (fun z : actualCrosscapRectangle => g z.val) ∧
      (∀ u t : ℝ, 0 < u → u < 1 → -1 < t → t < 1 →
        f (Schoenflies.Plane.mk (u+1) t)=g (Schoenflies.Plane.mk u t)) ∧
      (∀ u t : ℝ, 0 < u → u < 1 → -1 < t → t < 1 →
        f (Schoenflies.Plane.mk u t)=g (Schoenflies.Plane.mk (u+1) (-t))) := by
  classical
  have hrectangle (u : I) (t : BandWidth) :
      (ε/4 * -(t : ℝ), ε * (1 - 2 * (u : ℝ))) ∈
        Metric.closedBall ((0,0) : ℝ × ℝ) ε := by
    simp only [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq,
      sub_zero, max_le_iff]
    constructor
    · calc
        |ε/4 * -(t : ℝ)| = ε/4 * |(t : ℝ)| := by
          rw [abs_mul, abs_neg, abs_of_pos (by positivity)]
        _ ≤ ε/4 := by
          have ht := abs_le.mpr t.property
          nlinarith
        _ ≤ ε := by linarith
    · have hu : |1 - 2 * (u : ℝ)| ≤ 1 := by
        apply abs_le.mpr
        constructor <;> linarith [u.property.1,u.property.2]
      rw [abs_mul, abs_of_pos hε]
      nlinarith
  let qbase : I × BandWidth → Metric.closedBall ((0,0) : ℝ × ℝ) ε :=
    fun z => ⟨(ε/4 * -(z.2 : ℝ), ε * (1 - 2 * (z.1 : ℝ))),
      hrectangle z.1 z.2⟩
  let Q : I × BandWidth → S := fun z => square (qbase z)
  have hqcont : Continuous qbase := by
    dsimp [qbase]
    fun_prop
  have hqinj : Function.Injective qbase := by
    intro x y hh
    have hp := congrArg Subtype.val hh
    have hx := congrArg Prod.fst hp
    have hy := congrArg Prod.snd hp
    dsimp [qbase] at hx hy
    apply Prod.ext
    · apply Subtype.ext
      have hh := mul_left_cancel₀ hε.ne' hy
      linarith
    · apply Subtype.ext
      have hh := mul_left_cancel₀ (by positivity : ε/4 ≠ 0) hx
      exact neg_injective hh
  have hQembedded : IsEmbedding Q :=
    hsquare.comp (hqcont.isClosedEmbedding hqinj).isEmbedding
  have hQtop (t : BandWidth) : Q (0,t) = band (1,t) := by
    rw [htop]
    change square (qbase (0,t)) = square (squarePort ε hε 0 (flipBandWidth true t))
    apply congrArg square
    apply Subtype.ext
    simp [qbase,squarePort,crossingEndRectangle,flipBandWidth]
  have hQbottom (t : BandWidth) : Q (1,t) = band (0,flipBandWidth true t) := by
    rw [hbottom]
    change square (qbase (1,t)) = square (squarePort ε hε 2 (flipBandWidth true t))
    apply congrArg square
    apply Subtype.ext
    simp [qbase,squarePort,crossingEndRectangle,flipBandWidth]
    ring
  have hQinterior (u : I) (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1)
      (t : BandWidth) : Q (u,t) ∉ Set.range band := by
    intro hmem
    have hboth : Q (u,t) ∈ Set.range band ∩ Set.range square :=
      ⟨hmem, ⟨qbase (u,t), rfl⟩⟩
    rw [hmeet] at hboth
    rcases hboth with ⟨v, hv⟩ | ⟨v, hv⟩
    · have heq := hsquare.injective hv
      have hy := congrArg (fun z : Metric.closedBall ((0,0) : ℝ × ℝ) ε => (z : ℝ × ℝ).2) heq
      simp only [squarePort, crossingEndRectangle, qbase] at hy
      change -(ε + ε / 4 * 0) = ε * (1 - 2 * (u : ℝ)) at hy
      have hh := mul_left_cancel₀ hε.ne' (show ε * (-1) = ε * (1 - 2 * (u : ℝ)) by nlinarith [hy])
      linarith
    · have heq := hsquare.injective hv
      have hy := congrArg (fun z : Metric.closedBall ((0,0) : ℝ × ℝ) ε => (z : ℝ × ℝ).2) heq
      simp only [squarePort, crossingEndRectangle, qbase] at hy
      change ε + ε / 4 * 0 = ε * (1 - 2 * (u : ℝ)) at hy
      have hh := mul_left_cancel₀ hε.ne' (show ε * 1 = ε * (1 - 2 * (u : ℝ)) by simpa using hy)
      linarith
  let P := Set.Icc (0 : ℝ) 2 × BandWidth
  let left : P → S := fun z => band (projIcc 0 1 zero_le_one (z.1 : ℝ), z.2)
  let right : P → S := fun z => Q (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1), z.2)
  let F : P → S := fun z => if (z.1 : ℝ) ≤ 1 then left z else right z
  have hleft : Continuous left := hband.continuous.comp
    ((continuous_projIcc.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  have hright : Continuous right := hQembedded.continuous.comp
    ((continuous_projIcc.comp ((continuous_subtype_val.comp continuous_fst).sub continuous_const)).prodMk continuous_snd)
  have hFcont : Continuous F := by
    apply continuous_if_le (continuous_subtype_val.comp continuous_fst) continuous_const
      hleft.continuousOn hright.continuousOn
    intro z hz
    change (z.1 : ℝ) = 1 at hz
    change left z = right z
    dsimp only [left, right]
    rw [hz]
    simp only [sub_self, projIcc_of_mem zero_le_one (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num),
      projIcc_of_mem zero_le_one (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)]
    exact (hQtop z.2).symm
  have hFzero (t : BandWidth) : F (⟨0, by norm_num⟩,t) = band (0,t) := by
    simp [F,left]
  have hFtwo (t : BandWidth) : F (⟨2, by norm_num⟩,t) = band (0,flipBandWidth true t) := by
    simp only [F, show ¬ (2:ℝ) ≤ 1 by norm_num, ↓reduceIte, right]
    convert hQbottom t using 1 <;> norm_num [projIcc_of_mem]
  have hFinj (x y : P) (hx0 : 0 < (x.1 : ℝ)) (hx2 : (x.1 : ℝ) < 2)
      (hy0 : 0 < (y.1 : ℝ)) (hy2 : (y.1 : ℝ) < 2) (he : F x = F y) : x = y := by
    have hclipleft (z : P) (hz : (z.1 : ℝ) ≤ 1) :
        (projIcc 0 1 zero_le_one (z.1 : ℝ) : ℝ) = (z.1 : ℝ) := by
      simp only [projIcc_of_mem zero_le_one ⟨z.1.property.1, hz⟩]
    have hclipright (z : P) (hz : 1 < (z.1 : ℝ)) :
        (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1) : ℝ) = (z.1 : ℝ)-1 := by
      rw [projIcc_of_mem zero_le_one (show (z.1 : ℝ)-1 ∈ Icc (0:ℝ) 1 by
        constructor <;> linarith [z.1.property.2])]
    dsimp only [F] at he
    split_ifs at he with hx hy hy
    · have hh := hband.injective he
      apply Prod.ext
      · apply Subtype.ext
        have hh1 := congrArg (fun z : I × BandWidth => (z.1 : ℝ)) hh
        exact (hclipleft x hx).symm.trans (hh1.trans (hclipleft y hy))
      · exact congrArg (fun z : I × BandWidth => z.2) hh
    · have hy' : 1 < (y.1 : ℝ) := lt_of_not_ge hy
      have ha := hQinterior (projIcc 0 1 zero_le_one ((y.1 : ℝ)-1))
        (by rw [hclipright y hy']; linarith)
        (by rw [hclipright y hy']; linarith) y.2
      exact False.elim (ha ⟨_, he⟩)
    · have hx' : 1 < (x.1 : ℝ) := lt_of_not_ge hx
      have ha := hQinterior (projIcc 0 1 zero_le_one ((x.1 : ℝ)-1))
        (by rw [hclipright x hx']; linarith)
        (by rw [hclipright x hx']; linarith) x.2
      exact False.elim (ha ⟨_, he.symm⟩)
    · have hh := hQembedded.injective he
      apply Prod.ext
      · apply Subtype.ext
        have hh1 := congrArg (fun z : I × BandWidth => (z.1 : ℝ)) hh
        rw [hclipright x (lt_of_not_ge hx), hclipright y (lt_of_not_ge hy)] at hh1
        linarith
      · exact congrArg (fun z : I × BandWidth => z.2) hh
  let f : EuclideanSpace ℝ (Fin 2) → S := fun z =>
    F (projIcc 0 2 (by norm_num) (z 0), projIcc (-1) 1 (by norm_num) (z 1))
  let U : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | z 0 ∈ Ioo 0 2 ∧ z 1 ∈ Ioo (-1) 1}
  have hUopen : IsOpen U := (isOpen_Ioo.preimage (by fun_prop)).inter
    (isOpen_Ioo.preimage (by fun_prop))
  have hfcont : Continuous f := hFcont.comp
    ((continuous_projIcc.comp (by fun_prop)).prodMk
      (continuous_projIcc.comp (by fun_prop)))
  have hclip (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ U) :
      (projIcc 0 2 (by norm_num) (z 0) : ℝ) = z 0 ∧
      (projIcc (-1) 1 (by norm_num) (z 1) : ℝ) = z 1 := by
    constructor
    · exact congrArg Subtype.val (projIcc_of_mem (by norm_num) ⟨hz.1.1.le,hz.1.2.le⟩)
    · exact congrArg Subtype.val (projIcc_of_mem (by norm_num) ⟨hz.2.1.le,hz.2.2.le⟩)
  have hfinj : InjOn f U := by
    intro x hx y hy he
    have hh := hFinj
      (projIcc 0 2 (by norm_num) (x 0), projIcc (-1) 1 (by norm_num) (x 1))
      (projIcc 0 2 (by norm_num) (y 0), projIcc (-1) 1 (by norm_num) (y 1))
      (by rw [(hclip x hx).1]; exact hx.1.1)
      (by rw [(hclip x hx).1]; exact hx.1.2)
      (by rw [(hclip y hy).1]; exact hy.1.1)
      (by rw [(hclip y hy).1]; exact hy.1.2) he
    have h0 := congrArg (fun z : P => (z.1 : ℝ)) hh
    have h1 := congrArg (fun z : P => (z.2 : ℝ)) hh
    rw [(hclip x hx).1, (hclip y hy).1] at h0
    rw [(hclip x hx).2, (hclip y hy).2] at h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hTubeChartOpen : IsOpen (f '' U) :=
    actual_surface_open_plane_image S f U hUopen hfcont.continuousOn hfinj
  let fU : U → S := fun z => f z
  have hfUopen : IsOpenMap fU := by
    intro V hV
    let W : Set (EuclideanSpace ℝ (Fin 2)) := Subtype.val '' V
    have hW : IsOpen W := hUopen.isOpenMap_subtype_val V hV
    have hWU : W ⊆ U := by
      rintro z ⟨w,hw,rfl⟩
      exact w.property
    have hWi : InjOn f W := hfinj.mono hWU
    have heq : fU '' V = f '' W := by
      simp only [W, Set.image_image]
      rfl
    rw [heq]
    exact actual_surface_open_plane_image S f W hW hfcont.continuousOn hWi
  have hfUembedded : IsOpenEmbedding fU :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap
      (hfcont.comp continuous_subtype_val)
      (by intro x y he; exact Subtype.ext (hfinj x.property y.property he)) hfUopen
  let tubeChart : U ≃ₜ Set.range fU := hfUembedded.isEmbedding.toHomeomorph
  have hMeet : Set.range Q ∩ Set.range band =
      Set.range (fun t => Q (0,t)) ∪ Set.range (fun t => Q (1,t)) := by
    ext z
    constructor
    · rintro ⟨⟨⟨u,t⟩,hu⟩, hBz⟩
      by_cases h0 : u = 0
      · exact Or.inl ⟨t, by simpa [h0] using hu⟩
      by_cases h1 : u = 1
      · exact Or.inr ⟨t, by simpa [h1] using hu⟩
      have hu0 : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (by
        intro heq; exact h0 (Subtype.ext heq.symm))
      have hu1 : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 (by
        intro heq; exact h1 (Subtype.ext heq))
      exact False.elim (hQinterior u hu0 hu1 t (hu.symm ▸ hBz))
    · rintro (⟨t,rfl⟩ | ⟨t,rfl⟩)
      · exact ⟨⟨(0,t),rfl⟩, ⟨(1,t), (hQtop t).symm⟩⟩
      · exact ⟨⟨(1,t),rfl⟩, ⟨(0,flipBandWidth true t), (hQbottom t).symm⟩⟩
  have hQband (u v : I) (t w : BandWidth) (he : Q (u,t) = band (v,w)) :
      (u = 0 ∧ v = 1 ∧ w = t) ∨
      (u = 1 ∧ v = 0 ∧ w = flipBandWidth true t) := by
    by_cases h0 : u = 0
    · subst u
      have hh := hband.injective ((hQtop t).symm.trans he)
      exact Or.inl ⟨rfl, (congrArg Prod.fst hh).symm,
        (congrArg Prod.snd hh).symm⟩
    by_cases h1 : u = 1
    · subst u
      have hh := hband.injective ((hQbottom t).symm.trans he)
      exact Or.inr ⟨rfl, (congrArg Prod.fst hh).symm,
        (congrArg Prod.snd hh).symm⟩
    have hu0 : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (by
      intro heq; exact h0 (Subtype.ext heq.symm))
    have hu1 : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 (by
      intro heq; exact h1 (Subtype.ext heq))
    exact False.elim (hQinterior u hu0 hu1 t ⟨(v,w),he.symm⟩)
  let left2 : P → S := fun z => Q (projIcc 0 1 zero_le_one (z.1 : ℝ), z.2)
  let right2 : P → S := fun z => band
    (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1), flipBandWidth true z.2)
  let G : P → S := fun z => if (z.1 : ℝ) ≤ 1 then left2 z else right2 z
  have hleft2 : Continuous left2 := hQembedded.continuous.comp
    ((continuous_projIcc.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  have hflip : Continuous (flipBandWidth true) :=
    continuous_subtype_val.neg.subtype_mk _
  have hright2 : Continuous right2 := hband.continuous.comp
    ((continuous_projIcc.comp ((continuous_subtype_val.comp continuous_fst).sub continuous_const)).prodMk
      (hflip.comp continuous_snd))
  have hGcont : Continuous G := by
    apply continuous_if_le (continuous_subtype_val.comp continuous_fst) continuous_const
      hleft2.continuousOn hright2.continuousOn
    intro z hz
    change (z.1 : ℝ) = 1 at hz
    change Q (projIcc 0 1 zero_le_one (z.1 : ℝ), z.2) =
      band (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1), flipBandWidth true z.2)
    rw [hz]
    simp only [sub_self, projIcc_of_mem zero_le_one (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num),
      projIcc_of_mem zero_le_one (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)]
    exact hQbottom z.2
  have hGinj (x y : P) (hx0 : 0 < (x.1 : ℝ)) (hx2 : (x.1 : ℝ) < 2)
      (hy0 : 0 < (y.1 : ℝ)) (hy2 : (y.1 : ℝ) < 2) (he : G x = G y) : x = y := by
    have hclipleft (z : P) (hz : (z.1 : ℝ) ≤ 1) :
        (projIcc 0 1 zero_le_one (z.1 : ℝ) : ℝ) = (z.1 : ℝ) := by
      simp only [projIcc_of_mem zero_le_one ⟨z.1.property.1, hz⟩]
    have hclipright (z : P) (hz : 1 < (z.1 : ℝ)) :
        (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1) : ℝ) = (z.1 : ℝ)-1 := by
      rw [projIcc_of_mem zero_le_one (show (z.1 : ℝ)-1 ∈ Icc (0:ℝ) 1 by
        constructor <;> linarith [z.1.property.2])]
    dsimp only [G] at he
    split_ifs at he with hx hy hy
    · have hh := hQembedded.injective he
      apply Prod.ext
      · apply Subtype.ext
        have hh1 := congrArg (fun z : I × BandWidth => (z.1 : ℝ)) hh
        exact (hclipleft x hx).symm.trans (hh1.trans (hclipleft y hy))
      · exact congrArg (fun z : I × BandWidth => z.2) hh
    · have hh := hQband _ _ _ _ he
      rcases hh with ⟨h0,_,_⟩ | ⟨_,h0,_⟩
      · have hv := congrArg Subtype.val h0
        rw [hclipleft x hx] at hv
        norm_num at hv
        linarith
      · have hv := congrArg Subtype.val h0
        rw [hclipright y (lt_of_not_ge hy)] at hv
        norm_num at hv
        linarith
    · have hh := hQband _ _ _ _ he.symm
      rcases hh with ⟨h0,_,_⟩ | ⟨_,h0,_⟩
      · have hv := congrArg Subtype.val h0
        rw [hclipleft y hy] at hv
        norm_num at hv
        linarith
      · have hv := congrArg Subtype.val h0
        rw [hclipright x (lt_of_not_ge hx)] at hv
        norm_num at hv
        linarith
    · have hh := hband.injective he
      apply Prod.ext
      · apply Subtype.ext
        have hh1 := congrArg (fun z : I × BandWidth => (z.1 : ℝ)) hh
        rw [hclipright x (lt_of_not_ge hx), hclipright y (lt_of_not_ge hy)] at hh1
        linarith
      · apply Subtype.ext
        have hh2 := congrArg (fun z : I × BandWidth => (z.2 : ℝ)) hh
        change -(x.2 : ℝ) = -(y.2 : ℝ) at hh2
        exact neg_injective hh2
  let g : EuclideanSpace ℝ (Fin 2) → S := fun z =>
    G (projIcc 0 2 (by norm_num) (z 0), projIcc (-1) 1 (by norm_num) (z 1))
  have hgcont : Continuous g := hGcont.comp
    ((continuous_projIcc.comp (by fun_prop)).prodMk
      (continuous_projIcc.comp (by fun_prop)))
  have hginj : InjOn g U := by
    intro x hx y hy he
    have hh := hGinj
      (projIcc 0 2 (by norm_num) (x 0), projIcc (-1) 1 (by norm_num) (x 1))
      (projIcc 0 2 (by norm_num) (y 0), projIcc (-1) 1 (by norm_num) (y 1))
      (by rw [(hclip x hx).1]; exact hx.1.1)
      (by rw [(hclip x hx).1]; exact hx.1.2)
      (by rw [(hclip y hy).1]; exact hy.1.1)
      (by rw [(hclip y hy).1]; exact hy.1.2) he
    have h0 := congrArg (fun z : P => (z.1 : ℝ)) hh
    have h1 := congrArg (fun z : P => (z.2 : ℝ)) hh
    rw [(hclip x hx).1, (hclip y hy).1] at h0
    rw [(hclip x hx).2, (hclip y hy).2] at h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hTubeChartOpen2 : IsOpen (g '' U) :=
    actual_surface_open_plane_image S g U hUopen hgcont.continuousOn hginj
  let gU : U → S := fun z => g z
  have hgUopen : IsOpenMap gU := by
    intro V hV
    let W : Set (EuclideanSpace ℝ (Fin 2)) := Subtype.val '' V
    have hW : IsOpen W := hUopen.isOpenMap_subtype_val V hV
    have hWU : W ⊆ U := by
      rintro z ⟨w,hw,rfl⟩
      exact w.property
    have hWi : InjOn g W := hginj.mono hWU
    have heq : gU '' V = g '' W := by
      simp only [W, Set.image_image]
      rfl
    rw [heq]
    exact actual_surface_open_plane_image S g W hW hgcont.continuousOn hWi
  have hgUembedded : IsOpenEmbedding gU :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap
      (hgcont.comp continuous_subtype_val)
      (by intro x y he; exact Subtype.ext (hginj x.property y.property he)) hgUopen
  let tubeChart2 : U ≃ₜ Set.range gU := hgUembedded.isEmbedding.toHomeomorph
  have hFG (u : I) (hu0 : 0 < (u : ℝ)) (t : BandWidth) :
      F (⟨(u : ℝ)+1, by constructor <;> linarith [u.property.1,u.property.2]⟩, t) =
      G (⟨(u : ℝ), ⟨u.property.1, by linarith [u.property.2]⟩⟩, t) := by
    dsimp only [F,G]
    rw [if_neg (show ¬ (u : ℝ)+1 ≤ 1 by linarith), if_pos u.property.2]
    dsimp only [right,left2]
    simp only [add_sub_cancel_right]
  have hGF (u : I) (hu0 : 0 < (u : ℝ)) (t : BandWidth) :
      F (⟨(u : ℝ), ⟨u.property.1, by linarith [u.property.2]⟩⟩, t) =
      G (⟨(u : ℝ)+1, by constructor <;> linarith [u.property.1,u.property.2]⟩,
        flipBandWidth true t) := by
    dsimp only [F,G]
    rw [if_pos u.property.2, if_neg (show ¬ (u : ℝ)+1 ≤ 1 by linarith)]
    dsimp only [left,right2]
    simp only [add_sub_cancel_right]
    have hflipflip : flipBandWidth true (flipBandWidth true t) = t := by
      apply Subtype.ext
      simp [flipBandWidth]
    rw [hflipflip]
  refine ⟨⟨f,hfcont⟩,⟨g,hgcont⟩,hfUembedded,hgUembedded,?_,?_⟩
  · intro u t hu0 hu1 ht0 ht1
    have h := hFG (⟨u,⟨hu0.le,hu1.le⟩⟩ : I) hu0 (⟨t,⟨ht0.le,ht1.le⟩⟩ : BandWidth)
    change f (Schoenflies.Plane.mk (u+1) t)=g (Schoenflies.Plane.mk u t)
    dsimp only [f,g]
    simpa [Schoenflies.Plane.mk,projIcc_of_mem,show u+1 ∈ Icc (0:ℝ) 2 by constructor <;> linarith,
      show u ∈ Icc (0:ℝ) 2 by constructor <;> linarith,
      show t ∈ Icc (-1:ℝ) 1 from ⟨ht0.le,ht1.le⟩] using h
  · intro u t hu0 hu1 ht0 ht1
    have h := hGF (⟨u,⟨hu0.le,hu1.le⟩⟩ : I) hu0 (⟨t,⟨ht0.le,ht1.le⟩⟩ : BandWidth)
    change f (Schoenflies.Plane.mk u t)=g (Schoenflies.Plane.mk (u+1) (-t))
    dsimp only [f,g]
    simpa [Schoenflies.Plane.mk,projIcc_of_mem,flipBandWidth,
      show u+1 ∈ Icc (0:ℝ) 2 by constructor <;> linarith,
      show u ∈ Icc (0:ℝ) 2 by constructor <;> linarith,
      show t ∈ Icc (-1:ℝ) 1 from ⟨ht0.le,ht1.le⟩,
      show -t ∈ Icc (-1:ℝ) 1 by constructor <;> linarith] using h

#print axioms actual_twisted_square_two_charts

private def actualInversePlaneChart (S : CompactOrientedSurface.{0})
    (f : C(Euc 2,S)) (U : Set (Euc 2)) (hU : IsOpen U)
    (hf : IsOpenEmbedding (fun z : U => f z.val)) : OpenPartialHomeomorph S ℂ := by
  let hinj : InjOn f U := by
    intro x hx y hy he
    exact congrArg Subtype.val (hf.injective (show f (⟨x,hx⟩ : U).val=f (⟨y,hy⟩ : U).val from he))
  let a : OpenPartialHomeomorph (Euc 2) S :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict (hinj.toPartialEquiv f U)
      f.continuous.continuousOn hf.isOpenMap hU
  exact a.symm.trans actualEucComplex.toHomeomorph.toOpenPartialHomeomorph

private theorem actual_inverse_plane_chart_source (S : CompactOrientedSurface.{0})
    (f : C(Euc 2,S)) (U : Set (Euc 2)) (hU : IsOpen U)
    (hf : IsOpenEmbedding (fun z : U => f z.val)) :
    (actualInversePlaneChart S f U hU hf).source=f '' U := by
  simp [actualInversePlaneChart,OpenPartialHomeomorph.trans_source,Set.InjOn.toPartialEquiv]

private theorem actual_inverse_plane_chart_symm (S : CompactOrientedSurface.{0})
    (f : C(Euc 2,S)) (U : Set (Euc 2)) (hU : IsOpen U)
    (hf : IsOpenEmbedding (fun z : U => f z.val)) (z : ℂ) :
    (actualInversePlaneChart S f U hU hf).symm z=f (actualEucComplex.symm z) := rfl

private theorem actual_inverse_plane_chart_at (S : CompactOrientedSurface.{0})
    (f : C(Euc 2,S)) (U : Set (Euc 2)) (hU : IsOpen U)
    (hf : IsOpenEmbedding (fun z : U => f z.val)) (z : Euc 2) (hz : z ∈ U) :
    (actualInversePlaneChart S f U hU hf) (f z)=actualEucComplex z := by
  let e := actualInversePlaneChart S f U hU hf
  have hx : f z ∈ e.source := by rw [actual_inverse_plane_chart_source];exact ⟨z,hz,rfl⟩
  have he := e.left_inv hx
  rw [actual_inverse_plane_chart_symm] at he
  have hu : actualEucComplex.symm (e (f z)) ∈ U := by
    have ht := e.map_source hx
    simpa [e,actualInversePlaneChart,OpenPartialHomeomorph.trans_target,
      OpenPartialHomeomorph.symm_target] using ht
  have hzinj : actualEucComplex.symm (e (f z))=z :=
    congrArg Subtype.val (hf.injective (show f (⟨_,hu⟩ : U).val=f (⟨z,hz⟩ : U).val from he))
  have h := congrArg actualEucComplex hzinj
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

private theorem actual_euc_complex_coordinates (u t : ℝ) :
    actualEucComplex (Schoenflies.Plane.mk u t)=(u:ℂ)+(t:ℂ)*Complex.I := by
  apply Complex.ext <;> simp [actualEucComplex,Schoenflies.Plane.mk,
    EuclideanSpace.equiv,LinearEquiv.finTwoArrow]

private theorem actual_euc_complex_symm_coordinates (z : ℂ) :
    actualEucComplex.symm z=Schoenflies.Plane.mk z.re z.im := by
  apply actualEucComplex.injective
  rw [ContinuousLinearEquiv.apply_symm_apply,actual_euc_complex_coordinates]
  exact (Complex.re_add_im z).symm

#print axioms actualInversePlaneChart
#print axioms actual_inverse_plane_chart_at

private theorem actual_crosscap_rectangle_open : IsOpen actualCrosscapRectangle :=
  (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))

private theorem actual_crosscap_rectangle_preconnected : IsPreconnected actualCrosscapRectangle := by
  apply Convex.isPreconnected
  intro x hx y hy a b ha hb hab
  change (0 < (a • x+b • y) 0 ∧ (a • x+b • y) 0 < 2) ∧
    (-1 < (a • x+b • y) 1 ∧ (a • x+b • y) 1 < 1)
  change (0 < a*x 0+b*y 0 ∧ a*x 0+b*y 0 < 2) ∧
    (-1 < a*x 1+b*y 1 ∧ a*x 1+b*y 1 < 1)
  exact ⟨(convex_Ioo (0:ℝ) 2) hx.1 hy.1 ha hb hab,
    (convex_Ioo (-1:ℝ) 1) hx.2 hy.2 ha hb hab⟩

private theorem actual_plane_local_id_ne_neg :
    (𝟙 (relativeHomology ℂ ({0}ᶜ : Set ℂ) 2)) ≠
      -(𝟙 (relativeHomology ℂ ({0}ᶜ : Set ℂ) 2)) := by
  have hz1 := CircleHomologyComputation.contractible_positive_homology ℂ 1 (by decide)
  have hz2 := CircleHomologyComputation.contractible_positive_homology ℂ 2 (by decide)
  obtain ⟨_,he1⟩ := pairHomology_exact_at_relative ℂ ({0}ᶜ) 1
  obtain ⟨_,he0⟩ := pairHomology_exact_at_subspace ℂ ({0}ᶜ) 1
  letI : Mono (relativeConnecting ℂ ({0}ᶜ) 1) := he1.mono_g (hz2.eq_of_src _ _)
  letI : Epi (relativeConnecting ℂ ({0}ᶜ) 1) := he0.epi_f (hz1.eq_of_tgt _ _)
  letI : IsIso (relativeConnecting ℂ ({0}ᶜ) 1) := isIso_of_mono_of_epi _
  let e := asIso (relativeConnecting ℂ ({0}ᶜ) 1) ≪≫
    ReflectionRadial.circlePuncturedIso 1 ≪≫ CircleHomologyComputation.circleH1Iso
  intro heq
  have h := congrArg (fun q => e.inv ≫ q ≫ e.hom) heq
  have hh : (𝟙 (ModuleCat.of ℤ ℤ))=-(𝟙 (ModuleCat.of ℤ ℤ)) := by simpa using h
  have h1 := congrArg (fun q : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => q (1:ℤ)) hh
  norm_num at h1

#print axioms actual_plane_local_id_ne_neg

private theorem actual_affine_overlap_derivative (S : CompactOrientedSurface.{0})
    (f g : C(Euc 2,S)) (U : Set (Euc 2)) (hU : IsOpen U)
    (hf : IsOpenEmbedding (fun z : U => f z.val))
    (hg : IsOpenEmbedding (fun z : U => g z.val))
    (a b : Euc 2) (ha : a ∈ U) (hb : b ∈ U) (hab : f a=g b)
    (A : ℂ ≃L[ℝ] ℂ) (N : Set ℂ) (hN : IsOpen N) (h0 : (0:ℂ) ∈ N)
    (hcoord : ∀ z ∈ N,
      actualEucComplex.symm (z+actualEucComplex a) ∈ U ∧
      actualEucComplex.symm (A z+actualEucComplex b) ∈ U ∧
      f (actualEucComplex.symm (z+actualEucComplex a))=
        g (actualEucComplex.symm (A z+actualEucComplex b))) :
    HasFDerivAt
      ((actualShiftChart (actualInversePlaneChart S f U hU hf) (f a)).symm.trans
        (actualShiftChart (actualInversePlaneChart S g U hU hg) (f a)))
      A.toContinuousLinearMap 0 := by
  let e := actualInversePlaneChart S f U hU hf
  let d := actualInversePlaneChart S g U hU hg
  have hea : e (f a)=actualEucComplex a := actual_inverse_plane_chart_at S f U hU hf a ha
  have hdb : d (f a)=actualEucComplex b := by
    rw [hab]
    exact actual_inverse_plane_chart_at S g U hU hg b hb
  apply A.hasFDerivAt.congr_of_eventuallyEq
  filter_upwards [hN.mem_nhds h0] with z hz
  change (actualShiftChart d (f a)) ((actualShiftChart e (f a)).symm z)=A z
  rw [actual_shift_chart_apply,actual_shift_chart_symm_apply,hea,hdb,
    actual_inverse_plane_chart_symm,(hcoord z hz).2.2,
    actual_inverse_plane_chart_at S g U hU hg _ (hcoord z hz).2.1,
    ContinuousLinearEquiv.apply_symm_apply]
  simp

#print axioms actual_affine_overlap_derivative

private theorem actual_crosscap_chart_contradiction (S : CompactOrientedSurface.{0})
    (f g : C(Euc 2,S))
    (hf : IsOpenEmbedding (fun z : actualCrosscapRectangle => f z.val))
    (hg : IsOpenEmbedding (fun z : actualCrosscapRectangle => g z.val))
    (hFG : ∀ u t : ℝ, 0 < u → u < 1 → -1 < t → t < 1 →
      f (Schoenflies.Plane.mk (u+1) t)=g (Schoenflies.Plane.mk u t))
    (hGF : ∀ u t : ℝ, 0 < u → u < 1 → -1 < t → t < 1 →
      f (Schoenflies.Plane.mk u t)=g (Schoenflies.Plane.mk (u+1) (-t))) : False := by
  let U := actualCrosscapRectangle
  let a : Euc 2 := Schoenflies.Plane.mk (1/2) 0
  let b : Euc 2 := Schoenflies.Plane.mk (3/2) 0
  have ha : a ∈ U := by norm_num [a,U,actualCrosscapRectangle,Schoenflies.Plane.mk]
  have hb : b ∈ U := by norm_num [b,U,actualCrosscapRectangle,Schoenflies.Plane.mk]
  have hab : f a=g b := by
    convert hGF (1/2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1 <;>
      simp [a,b,Schoenflies.Plane.mk] <;> norm_num
  have hba : f b=g a := by
    convert hFG (1/2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1 <;>
      simp [a,b,Schoenflies.Plane.mk] <;> norm_num
  let e := actualInversePlaneChart S f U actual_crosscap_rectangle_open hf
  let d := actualInversePlaneChart S g U actual_crosscap_rectangle_open hg
  let N : Set ℂ := {z | z.re ∈ Ioo (-1/2) (1/2) ∧ z.im ∈ Ioo (-1) 1}
  have hN : IsOpen N := (isOpen_Ioo.preimage Complex.continuous_re).inter
    (isOpen_Ioo.preimage Complex.continuous_im)
  have h0 : (0:ℂ) ∈ N := by norm_num [N]
  have hcoordsNeg (z : ℂ) (hz : z ∈ N) :
      actualEucComplex.symm (z+actualEucComplex a) ∈ U ∧
      actualEucComplex.symm (Complex.conjCLE z+actualEucComplex b) ∈ U ∧
      f (actualEucComplex.symm (z+actualEucComplex a))=
        g (actualEucComplex.symm (Complex.conjCLE z+actualEucComplex b)) := by
    have hu0 : 0 < z.re+1/2 := by linarith [hz.1.1]
    have hu1 : z.re+1/2 < 1 := by linarith [hz.1.2]
    simp only [a,b,actual_euc_complex_symm_coordinates,actual_euc_complex_coordinates,
      Complex.conjCLE_apply,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.conj_re,Complex.conj_im,
      mul_zero,zero_mul,mul_one,zero_sub,sub_zero,zero_add,add_zero]
    refine ⟨?_,?_,?_⟩
    · change (0 < z.re+1/2 ∧ z.re+1/2 < 2) ∧ (-1 < z.im ∧ z.im < 1)
      exact ⟨⟨hu0,by linarith⟩,hz.2⟩
    · change (0 < z.re+3/2 ∧ z.re+3/2 < 2) ∧ (-1 < -z.im ∧ -z.im < 1)
      constructor <;> constructor <;> linarith [hz.1.1,hz.1.2,hz.2.1,hz.2.2]
    · convert hGF (z.re+1/2) z.im hu0 hu1 hz.2.1 hz.2.2 using 1 <;> congr 2 <;> ring
  have hcoordsPos (z : ℂ) (hz : z ∈ N) :
      actualEucComplex.symm (z+actualEucComplex b) ∈ U ∧
      actualEucComplex.symm (ContinuousLinearEquiv.refl ℝ ℂ z+actualEucComplex a) ∈ U ∧
      f (actualEucComplex.symm (z+actualEucComplex b))=
        g (actualEucComplex.symm (ContinuousLinearEquiv.refl ℝ ℂ z+actualEucComplex a)) := by
    have hu0 : 0 < z.re+1/2 := by linarith [hz.1.1]
    have hu1 : z.re+1/2 < 1 := by linarith [hz.1.2]
    simp only [a,b,actual_euc_complex_symm_coordinates,actual_euc_complex_coordinates,
      ContinuousLinearEquiv.refl_apply,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,mul_one,
      sub_zero,zero_add,add_zero]
    refine ⟨?_,?_,?_⟩
    · change (0 < z.re+3/2 ∧ z.re+3/2 < 2) ∧ (-1 < z.im ∧ z.im < 1)
      exact ⟨⟨by linarith,by linarith [hz.1.2]⟩,hz.2⟩
    · change (0 < z.re+1/2 ∧ z.re+1/2 < 2) ∧ (-1 < z.im ∧ z.im < 1)
      exact ⟨⟨hu0,by linarith⟩,hz.2⟩
    · convert hFG (z.re+1/2) z.im hu0 hu1 hz.2.1 hz.2.2 using 1 <;> congr 2 <;> ring
  have hderNeg := actual_affine_overlap_derivative S f g U actual_crosscap_rectangle_open
    hf hg a b ha hb hab Complex.conjCLE N hN h0 hcoordsNeg
  have hderPos := actual_affine_overlap_derivative S f g U actual_crosscap_rectangle_open
    hf hg b a hb ha hba (ContinuousLinearEquiv.refl ℝ ℂ) N hN h0 hcoordsPos
  have hxe : f a ∈ e.source := by rw [actual_inverse_plane_chart_source];exact ⟨a,ha,rfl⟩
  have hye : f b ∈ e.source := by rw [actual_inverse_plane_chart_source];exact ⟨b,hb,rfl⟩
  have hxd : f a ∈ d.source := by rw [hab,actual_inverse_plane_chart_source];exact ⟨b,hb,rfl⟩
  have hyd : f b ∈ d.source := by rw [hba,actual_inverse_plane_chart_source];exact ⟨a,ha,rfl⟩
  have hneg : (actualChartLocalIso d (f a) hxd).hom=-(actualChartLocalIso e (f a) hxe).hom := by
    have h := actual_derivative_chart_comparison e d (f a) hxe hxd Complex.conjCLE hderNeg
    rw [show LinearMap.det Complex.conjCLE.toLinearEquiv.toLinearMap=(-1:ℝ) from Complex.det_conjLIE,
      if_neg (by norm_num : ¬(0:ℝ)< -1)] at h
    exact h
  have hpos : (actualChartLocalIso d (f b) hyd).hom=(actualChartLocalIso e (f b) hye).hom := by
    have h := actual_derivative_chart_comparison e d (f b) hye hyd (ContinuousLinearEquiv.refl ℝ ℂ) hderPos
    have hdet : LinearMap.det (ContinuousLinearEquiv.refl ℝ ℂ).toLinearEquiv.toLinearMap=(1:ℝ) := by
      change LinearMap.det (LinearMap.id : ℂ →ₗ[ℝ] ℂ)=1
      exact LinearMap.det_id
    rw [hdet,if_pos (by norm_num : (0:ℝ)<1)] at h
    exact h
  let xe : e.source := ⟨f a,hxe⟩
  let ye : e.source := ⟨f b,hye⟩
  let xd : d.source := ⟨f a,hxd⟩
  let yd : d.source := ⟨f b,hyd⟩
  have hpreE : IsPreconnected e.source := by
    rw [actual_inverse_plane_chart_source]
    exact actual_crosscap_rectangle_preconnected.image f f.continuous.continuousOn
  have hpreD : IsPreconnected d.source := by
    rw [actual_inverse_plane_chart_source]
    exact actual_crosscap_rectangle_preconnected.image g g.continuous.continuousOn
  letI : PreconnectedSpace e.source := isPreconnected_iff_preconnectedSpace.mp hpreE
  letI : PreconnectedSpace d.source := isPreconnected_iff_preconnectedSpace.mp hpreD
  have heconst := (actual_chart_index_locally_constant S e).apply_eq_of_preconnectedSpace xe ye
  have hdconst := (actual_chart_index_locally_constant S d).apply_eq_of_preconnectedSpace xd yd
  have hxindex : actualTopologicalChartIndex S d xd=-(actualTopologicalChartIndex S e xe) := by
    apply (cancel_epi (actualChartLocalIso d (f a) hxd).hom).mp
    dsimp only [actualTopologicalChartIndex,xe,xd]
    rw [← Category.assoc,Iso.hom_inv_id,Category.id_comp,Preadditive.comp_neg,
      hneg,Preadditive.neg_comp,neg_neg,← Category.assoc,Iso.hom_inv_id,Category.id_comp]
  have hyindex : actualTopologicalChartIndex S d yd=actualTopologicalChartIndex S e ye := by
    apply (cancel_epi (actualChartLocalIso d (f b) hyd).hom).mp
    dsimp only [actualTopologicalChartIndex,ye,yd]
    rw [← Category.assoc,Iso.hom_inv_id,Category.id_comp,hpos,
      ← Category.assoc,Iso.hom_inv_id,Category.id_comp]
  have hself : actualTopologicalChartIndex S e xe=-(actualTopologicalChartIndex S e xe) := by
    calc
      actualTopologicalChartIndex S e xe=actualTopologicalChartIndex S e ye := heconst
      _=actualTopologicalChartIndex S d yd := hyindex.symm
      _=actualTopologicalChartIndex S d xd := hdconst.symm
      _=-(actualTopologicalChartIndex S e xe) := hxindex
  letI := actual_topological_chart_index_isIso S e xe
  apply actual_plane_local_id_ne_neg
  apply (cancel_epi (actualTopologicalChartIndex S e xe)).mp
  simpa only [Category.comp_id,Preadditive.comp_neg] using hself

#print axioms actual_crosscap_chart_contradiction

theorem actual_oriented_surface_nonorientable_exclusion (S : CompactOrientedSurface.{0})
    (p n : ℕ) (hp : 1 ≤ p) :
    ¬Nonempty (S ≃ₜ Quot (LeanEval.Topology.ClassificationOfSurfaces.NonOrientableRel p n)) := by
  classical
  rintro ⟨e⟩
  obtain ⟨ε,hε,square,band,hs,hb,hbottom,htop,hmeet⟩ :=
    CurveComplex.Hyperbolic.actual_nonorientable_normal_form_first_crosscap_square_strip p n hp
  let squareS := e.symm ∘ square
  let bandS := e.symm ∘ band
  have hsS : IsEmbedding squareS := e.symm.isEmbedding.comp hs
  have hbS : IsEmbedding bandS := e.symm.isEmbedding.comp hb
  have hbottomS : ∀ t, bandS (0,t)=squareS (squarePort ε hε 2 t) := by
    intro t
    exact congrArg e.symm (hbottom t)
  have htopS : ∀ t, bandS (1,t)=squareS (squarePort ε hε 0 (flipBandWidth true t)) := by
    intro t
    exact congrArg e.symm (htop t)
  have hmeetS : Set.range bandS ∩ Set.range squareS =
      Set.range (fun t => squareS (squarePort ε hε 2 t)) ∪
      Set.range (fun t => squareS (squarePort ε hε 0 t)) := by
    change Set.range (e.symm ∘ band) ∩ Set.range (e.symm ∘ square) =
      Set.range (e.symm ∘ (fun t => square (squarePort ε hε 2 t))) ∪
      Set.range (e.symm ∘ (fun t => square (squarePort ε hε 0 t)))
    simp only [Set.range_comp]
    rw [← Set.image_inter e.symm.injective,hmeet,Set.image_union]
  obtain ⟨f,g,hf,hg,hFG,hGF⟩ := actual_twisted_square_two_charts
    S ε hε squareS hsS bandS hbS hbottomS htopS hmeetS
  exact actual_crosscap_chart_contradiction S f g hf hg hFG hGF

#print axioms actual_oriented_surface_nonorientable_exclusion
end
end SeifertSurfaces.GenusLinking
