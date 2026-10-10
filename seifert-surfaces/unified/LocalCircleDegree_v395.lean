import SurfaceInvariants
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.VerifiedRealNondegenerateIndex
import CurveComplexGenusTwo.Topology.Orientation.CircleReflection
import CurveComplexGenusTwo.Topology.Orientation.PlaneReflection
import CurveComplexGenusTwo.CWHurewicz.ConnectingNaturality
import CurveComplexGenusTwo.CWHurewicz.PairExactnessInterface
import CurveComplexGenusTwo.Topology.LocalOrientation.LocalReflectionGerm
import Lean

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open Set Topology CategoryTheory CategoryTheory.Limits
open scoped unitInterval
open CurveComplex CurveComplexGenusTwo.CWHurewicz
namespace SeifertSurfaces.GenusLinking
noncomputable section

private theorem actual_nondegenerate_circle_homotopy
    (g : C(ℂ,ℂ)) (A : ℂ ≃L[ℝ] ℂ)
    (hg0 : g 0 = 0) (hderiv : HasFDerivAt g A.toContinuousLinearMap 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      (∀ z : Circle, g ((ρ : ℂ)*z) ≠ 0) ∧
      ∀ f : C(Circle,Circle),
        (∀ z, (f z : ℂ) = g ((ρ : ℂ)*z)/(‖g ((ρ : ℂ)*z)‖ : ℂ)) →
        f.Homotopic ⟨fun z => z ^
          (if 0 < LinearMap.det A.toLinearEquiv.toLinearMap then (1 : ℤ) else -1),
          continuous_zpow _⟩ := by
  have hindex : ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      (∀ z : Circle, g ((ρ : ℂ)*z) ≠ 0) ∧
      ∀ f : C(Circle,Circle),
        (∀ z, (f z : ℂ) = g ((ρ : ℂ)*z)/(‖g ((ρ : ℂ)*z)‖ : ℂ)) →
        Classical.choose (actual_circle_map_winding_homotopy_source f) =
          if 0 < (A 1).re*(A Complex.I).im - (A Complex.I).re*(A 1).im then 1 else -1 := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous
          "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports")
          "VerifiedRealNondegenerateIndex") 0)
        "actual_real_nondegenerate_zero_literal_circle_index"
      Lean.Elab.Tactic.evalTactic
        (← `(tactic| exact $(Lean.mkIdent n) _ _ (by assumption) (by assumption)))
  have hdet : LinearMap.det A.toLinearEquiv.toLinearMap =
      (A 1).re*(A Complex.I).im - (A Complex.I).re*(A 1).im := by
    rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
    simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI]
  obtain ⟨r, hr, hi⟩ := hindex
  refine ⟨r,hr,?_⟩
  intro ρ hρ hρr
  obtain ⟨hn, hf⟩ := hi ρ hρ hρr
  refine ⟨hn,?_⟩
  intro f he
  have hw := Classical.choose_spec (actual_circle_map_winding_homotopy_source f)
  rw [hf f he, ← hdet] at hw
  exact hw

private theorem actual_positive_derivative_circle_homology
    (g : C(ℂ,ℂ)) (A : ℂ ≃L[ℝ] ℂ)
    (hg0 : g 0 = 0) (hderiv : HasFDerivAt g A.toContinuousLinearMap 0)
    (hpos : 0 < LinearMap.det A.toLinearEquiv.toLinearMap) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      ∀ f : C(Circle,Circle),
        (∀ z, (f z : ℂ) = g ((ρ : ℂ)*z)/(‖g ((ρ : ℂ)*z)‖ : ℂ)) →
        (CircleHomologyComputation.HF 1).map (TopCat.ofHom f) =
          𝟙 (H Circle 1) := by
  obtain ⟨r,hr,hi⟩ := actual_nondegenerate_circle_homotopy g A hg0 hderiv
  refine ⟨r,hr,?_⟩
  intro ρ hρ hρr f hf
  have hh := (hi ρ hρ hρr).2 f hf
  have hid : (⟨fun z : Circle => z ^
      (if 0 < LinearMap.det A.toLinearEquiv.toLinearMap then (1 : ℤ) else -1),
      continuous_zpow _⟩ : C(Circle,Circle)) = ContinuousMap.id Circle := by
    ext z
    simp [hpos]
  rw [hid] at hh
  have hht : TopCat.Homotopy (TopCat.ofHom f) (𝟙 (TopCat.of Circle)) := hh.some
  have hmap := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    hht (ModuleCat.of ℤ ℤ) 1
  exact hmap.trans ((CircleHomologyComputation.HF 1).map_id _)

private theorem actual_positive_derivative_puncture_homology
    (g : C(ℂ,ℂ)) (A : ℂ ≃L[ℝ] ℂ)
    (hg0 : g 0 = 0) (hderiv : HasFDerivAt g A.toContinuousLinearMap 0)
    (hpos : 0 < LinearMap.det A.toLinearEquiv.toLinearMap)
    (hpuncture : ∀ z ∈ ({0}ᶜ : Set ℂ), g z ∈ ({0}ᶜ : Set ℂ)) :
    (CircleHomologyComputation.HF 1).map
      (pairMapOnSubspace ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ) g hpuncture) =
      𝟙 (H ({0}ᶜ : Set ℂ) 1) := by
  let P := ReflectionRadial.Punctured ℂ
  let F := CircleHomologyComputation.HF 1
  let N := ReflectionRadial.circleRetraction
  let G : C(P,P) := ⟨fun z => ⟨g z.val,hpuncture z.val z.property⟩,
    (g.continuous.comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨r,hr,hi⟩ := actual_positive_derivative_circle_homology g A hg0 hderiv hpos
  let ρ : ℝ := r/2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρr : ρ < r := by dsimp [ρ]; linarith
  let i : C(Circle,P) := ⟨fun z => ⟨ρ • (z : ℂ),
    smul_ne_zero hρ.ne' (ne_zero_of_mem_unit_sphere z)⟩,
    ((continuous_const : Continuous (fun _ : Circle => (ρ : ℝ))).smul
      (continuous_subtype_val : Continuous (fun z : Circle => (z : ℂ)))).subtype_mk _⟩
  have hNi : N.comp i = ContinuousMap.id Circle := by
    ext z
    change NormedSpace.normalize (ρ • (z : ℂ)) = (z : ℂ)
    rw [NormedSpace.normalize_smul_of_pos hρ,
      NormedSpace.normalize_eq_self_of_norm_eq_one (Circle.norm_coe z)]
  have hNiMap : F.map (TopCat.ofHom i) ≫ F.map (TopCat.ofHom N) = 𝟙 _ := by
    rw [← F.map_comp]
    change F.map (TopCat.ofHom (N.comp i)) = _
    rw [hNi]
    exact F.map_id _
  haveI : IsIso (F.map (TopCat.ofHom N)) :=
    (ReflectionRadial.circlePuncturedIso 1).isIso_hom
  let ei : H Circle 1 ≅ H P 1 := {
    hom := F.map (TopCat.ofHom i)
    inv := F.map (TopCat.ofHom N)
    hom_inv_id := hNiMap
    inv_hom_id := by
      apply (cancel_mono (F.map (TopCat.ofHom N))).1
      rw [Category.assoc,hNiMap]
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      simp only [Category.comp_id,Category.id_comp] }
  haveI : IsIso (F.map (TopCat.ofHom i)) := ei.isIso_hom
  haveI : Epi (F.map (TopCat.ofHom i)) := by infer_instance
  let f := N.comp (G.comp i)
  have hf : ∀ z : Circle,
      (f z : ℂ) = g ((ρ : ℂ)*z)/(‖g ((ρ : ℂ)*z)‖ : ℂ) := by
    intro z
    change NormedSpace.normalize (g (ρ • (z : ℂ))) = _
    simp only [NormedSpace.normalize,Complex.real_smul,Complex.ofReal_inv,
      div_eq_mul_inv,mul_comm]
  have hmap := hi ρ hρ hρr f hf
  have hcomp : F.map (TopCat.ofHom i) ≫ F.map (TopCat.ofHom G) ≫
      F.map (TopCat.ofHom N) = 𝟙 (H Circle 1) := by
    rw [← F.map_comp,← F.map_comp]
    exact hmap
  have hG : F.map (TopCat.ofHom G) = 𝟙 (H P 1) := by
    apply (cancel_epi (F.map (TopCat.ofHom i))).1
    apply (cancel_mono (F.map (TopCat.ofHom N))).1
    simp only [Category.assoc,Category.comp_id,Category.id_comp] 
    exact hcomp.trans hNiMap.symm
  exact hG

private theorem actual_positive_derivative_local_homology
    (g : C(ℂ,ℂ)) (A : ℂ ≃L[ℝ] ℂ)
    (hg0 : g 0 = 0) (hderiv : HasFDerivAt g A.toContinuousLinearMap 0)
    (hpos : 0 < LinearMap.det A.toLinearEquiv.toLinearMap)
    (hpuncture : ∀ z ∈ ({0}ᶜ : Set ℂ), g z ∈ ({0}ᶜ : Set ℂ)) :
    pairRelativeHomologyMap ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ) g hpuncture 2 =
      𝟙 (relativeHomology ℂ ({0}ᶜ : Set ℂ) 2) := by
  have hz : IsZero (H ℂ 2) :=
    CircleHomologyComputation.contractible_positive_homology ℂ 2 (by decide)
  obtain ⟨_,hexact⟩ := pairHomology_exact_at_relative ℂ ({0}ᶜ) 1
  haveI : Mono (relativeConnecting ℂ ({0}ᶜ) 1) := hexact.mono_g (hz.eq_of_src _ _)
  have hmap := actual_positive_derivative_puncture_homology g A hg0 hderiv hpos hpuncture
  have hn := relativeConnecting_natural ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ) g hpuncture 1
  apply (cancel_mono (relativeConnecting ℂ ({0}ᶜ) 1)).1
  rw [hmap,Category.comp_id] at hn
  simpa only [Category.id_comp] using hn.symm

private theorem actual_derivative_circle_homology_sign
    (g : C(ℂ,ℂ)) (A : ℂ ≃L[ℝ] ℂ)
    (hg0 : g 0 = 0) (hderiv : HasFDerivAt g A.toContinuousLinearMap 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      ∀ f : C(Circle,Circle),
        (∀ z, (f z : ℂ) = g ((ρ : ℂ)*z)/(‖g ((ρ : ℂ)*z)‖ : ℂ)) →
        (CircleHomologyComputation.HF 1).map (TopCat.ofHom f) =
          if 0 < LinearMap.det A.toLinearEquiv.toLinearMap
          then 𝟙 (H Circle 1) else -(𝟙 (H Circle 1)) := by
  by_cases hpos : 0 < LinearMap.det A.toLinearEquiv.toLinearMap
  · obtain ⟨r,hr,hi⟩ := actual_positive_derivative_circle_homology g A hg0 hderiv hpos
    refine ⟨r,hr,?_⟩
    intro ρ hρ hρr f hf
    simpa only [if_pos hpos] using hi ρ hρ hρr f hf
  · obtain ⟨r,hr,hi⟩ := actual_nondegenerate_circle_homotopy g A hg0 hderiv
    refine ⟨r,hr,?_⟩
    intro ρ hρ hρr f hf
    have hh := (hi ρ hρ hρr).2 f hf
    have hinv : (⟨fun z : Circle => z ^
        (if 0 < LinearMap.det A.toLinearEquiv.toLinearMap then (1 : ℤ) else -1),
        continuous_zpow _⟩ : C(Circle,Circle)) =
        CurveComplex.GenusOrientationCandidate.circleInverse := by
      ext z
      simp only [if_neg hpos,zpow_neg_one,
        CurveComplex.GenusOrientationCandidate.circleInverse,ContinuousMap.coe_mk]
    rw [hinv] at hh
    have hht : TopCat.Homotopy (TopCat.ofHom f)
        (TopCat.ofHom CurveComplex.GenusOrientationCandidate.circleInverse) := hh.some
    have hmap := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      hht (ModuleCat.of ℤ ℤ) 1
    rw [if_neg hpos]
    exact hmap.trans CurveComplex.GenusOrientationCandidate.circleInverse_homologyMap_eq_neg_id

private theorem actual_negative_derivative_puncture_homology
    (g : C(ℂ,ℂ)) (A : ℂ ≃L[ℝ] ℂ)
    (hg0 : g 0 = 0) (hderiv : HasFDerivAt g A.toContinuousLinearMap 0)
    (hneg : LinearMap.det A.toLinearEquiv.toLinearMap < 0)
    (hpuncture : ∀ z ∈ ({0}ᶜ : Set ℂ), g z ∈ ({0}ᶜ : Set ℂ)) :
    (CircleHomologyComputation.HF 1).map
      (pairMapOnSubspace ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ) g hpuncture) =
      -(𝟙 (H ({0}ᶜ : Set ℂ) 1)) := by
  let P := ReflectionRadial.Punctured ℂ
  let F := CircleHomologyComputation.HF 1
  let N := ReflectionRadial.circleRetraction
  let G : C(P,P) := ⟨fun z => ⟨g z.val,hpuncture z.val z.property⟩,
    (g.continuous.comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨r,hr,hi⟩ := actual_derivative_circle_homology_sign g A hg0 hderiv
  let ρ : ℝ := r/2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρr : ρ < r := by dsimp [ρ]; linarith
  let i : C(Circle,P) := ⟨fun z => ⟨ρ • (z : ℂ),
    smul_ne_zero hρ.ne' (ne_zero_of_mem_unit_sphere z)⟩,
    ((continuous_const : Continuous (fun _ : Circle => (ρ : ℝ))).smul
      (continuous_subtype_val : Continuous (fun z : Circle => (z : ℂ)))).subtype_mk _⟩
  have hNi : N.comp i = ContinuousMap.id Circle := by
    ext z
    change NormedSpace.normalize (ρ • (z : ℂ)) = (z : ℂ)
    rw [NormedSpace.normalize_smul_of_pos hρ,
      NormedSpace.normalize_eq_self_of_norm_eq_one (Circle.norm_coe z)]
  have hNiMap : F.map (TopCat.ofHom i) ≫ F.map (TopCat.ofHom N) = 𝟙 _ := by
    rw [← F.map_comp]
    change F.map (TopCat.ofHom (N.comp i)) = _
    rw [hNi]
    exact F.map_id _
  haveI : IsIso (F.map (TopCat.ofHom N)) :=
    (ReflectionRadial.circlePuncturedIso 1).isIso_hom
  let ei : H Circle 1 ≅ H P 1 := {
    hom := F.map (TopCat.ofHom i)
    inv := F.map (TopCat.ofHom N)
    hom_inv_id := hNiMap
    inv_hom_id := by
      apply (cancel_mono (F.map (TopCat.ofHom N))).1
      rw [Category.assoc,hNiMap]
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      simp only [Category.comp_id,Category.id_comp] }
  haveI : IsIso (F.map (TopCat.ofHom i)) := ei.isIso_hom
  haveI : Epi (F.map (TopCat.ofHom i)) := by infer_instance
  let f := N.comp (G.comp i)
  have hf : ∀ z : Circle,
      (f z : ℂ) = g ((ρ : ℂ)*z)/(‖g ((ρ : ℂ)*z)‖ : ℂ) := by
    intro z
    change NormedSpace.normalize (g (ρ • (z : ℂ))) = _
    simp only [NormedSpace.normalize,Complex.real_smul,Complex.ofReal_inv,
      div_eq_mul_inv,mul_comm]
  have hmap := hi ρ hρ hρr f hf
  rw [if_neg (not_lt_of_ge hneg.le)] at hmap
  have hcomp : F.map (TopCat.ofHom i) ≫ F.map (TopCat.ofHom G) ≫
      F.map (TopCat.ofHom N) = -(𝟙 (H Circle 1)) := by
    rw [← F.map_comp,← F.map_comp]
    exact hmap
  have hG : F.map (TopCat.ofHom G) = -(𝟙 (H P 1)) := by
    apply (cancel_epi (F.map (TopCat.ofHom i))).1
    apply (cancel_mono (F.map (TopCat.ofHom N))).1
    simp only [Category.assoc,Preadditive.comp_neg,Preadditive.neg_comp,
      Category.comp_id,Category.id_comp]
    exact hcomp.trans (congrArg Neg.neg hNiMap.symm)
  exact hG

private theorem actual_negative_derivative_local_homology
    (g : C(ℂ,ℂ)) (A : ℂ ≃L[ℝ] ℂ)
    (hg0 : g 0 = 0) (hderiv : HasFDerivAt g A.toContinuousLinearMap 0)
    (hneg : LinearMap.det A.toLinearEquiv.toLinearMap < 0)
    (hpuncture : ∀ z ∈ ({0}ᶜ : Set ℂ), g z ∈ ({0}ᶜ : Set ℂ)) :
    pairRelativeHomologyMap ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ) g hpuncture 2 =
      -(𝟙 (relativeHomology ℂ ({0}ᶜ : Set ℂ) 2)) := by
  have hz : IsZero (H ℂ 2) :=
    CircleHomologyComputation.contractible_positive_homology ℂ 2 (by decide)
  obtain ⟨_,hexact⟩ := pairHomology_exact_at_relative ℂ ({0}ᶜ) 1
  haveI : Mono (relativeConnecting ℂ ({0}ᶜ) 1) := hexact.mono_g (hz.eq_of_src _ _)
  have hmap := actual_negative_derivative_puncture_homology g A hg0 hderiv hneg hpuncture
  have hn := relativeConnecting_natural ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ) g hpuncture 1
  apply (cancel_mono (relativeConnecting ℂ ({0}ᶜ) 1)).1
  rw [hmap,Preadditive.comp_neg,Category.comp_id] at hn
  simpa only [Preadditive.neg_comp,Category.id_comp] using hn.symm

private def actualRadialClamp (r : ℝ) (z : ℂ) : ℂ :=
  (r / max r ‖z‖) • z

private theorem actual_radial_clamp_properties (r : ℝ) (hr : 0 < r) :
    Continuous (actualRadialClamp r) ∧
    (∀ z : ℂ, ‖actualRadialClamp r z‖ ≤ r) ∧
    (∀ z : ℂ, ‖z‖ ≤ r → actualRadialClamp r z = z) ∧
    (∀ z : ℂ, actualRadialClamp r z = 0 ↔ z = 0) := by
  have hmax (z : ℂ) : 0 < max r ‖z‖ := lt_of_lt_of_le hr (le_max_left _ _)
  refine ⟨?_,?_,?_,?_⟩
  · exact (continuous_const.div (continuous_const.max continuous_norm)
      (fun z => (hmax z).ne')).smul continuous_id
  · intro z
    change ‖(r / max r ‖z‖) • z‖ ≤ r
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hr (hmax z))]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (hmax z)).mpr
    exact mul_le_mul_of_nonneg_left (le_max_right r ‖z‖) hr.le
  · intro z hz
    change (r / max r ‖z‖) • z = z
    rw [max_eq_left hz,div_self hr.ne',one_smul]
  · intro z
    change (r / max r ‖z‖) • z = 0 ↔ z = 0
    exact smul_eq_zero_iff_right (div_pos hr (hmax z)).ne'

private theorem actual_positive_open_chart_local_homology
    (e : OpenPartialHomeomorph ℂ ℂ) (A : ℂ ≃L[ℝ] ℂ)
    (he0 : e 0 = 0) (hderiv : HasFDerivAt e A.toContinuousLinearMap 0)
    (hpos : 0 < LinearMap.det A.toLinearEquiv.toLinearMap)
    (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall 0 r ⊆ e.source) :
    ∃ g : C(ℂ,ℂ),
      (∀ z : ℂ, ‖z‖ ≤ r → g z = e z) ∧
      g 0 = 0 ∧ HasFDerivAt g A.toContinuousLinearMap 0 ∧
      ∃ hpuncture : ∀ z ∈ ({0}ᶜ : Set ℂ), g z ∈ ({0}ᶜ : Set ℂ),
        pairRelativeHomologyMap ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ) g hpuncture 2 =
          𝟙 (relativeHomology ℂ ({0}ᶜ : Set ℂ) 2) := by
  obtain ⟨hc,hbound,hid,hzero⟩ := actual_radial_clamp_properties r hr
  have hsource (z : ℂ) : actualRadialClamp r z ∈ e.source := by
    apply hball
    simpa only [Metric.mem_closedBall,dist_zero_right] using hbound z
  let g : C(ℂ,ℂ) := ⟨fun z => e (actualRadialClamp r z),
    e.continuousOn.comp_continuous hc hsource⟩
  have hvalue (z : ℂ) (hz : ‖z‖ ≤ r) : g z = e z := by
    change e (actualRadialClamp r z) = e z
    rw [hid z hz]
  have hg0 : g 0 = 0 := (hvalue 0 (by simp only [norm_zero]; exact hr.le)).trans he0
  have hgerm : g =ᶠ[nhds (0 : ℂ)] e := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
    have hn : ‖z‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    exact hvalue z hn.le
  have hgderiv : HasFDerivAt g A.toContinuousLinearMap 0 :=
    hderiv.congr_of_eventuallyEq hgerm
  have hzsource : (0 : ℂ) ∈ e.source := hball (Metric.mem_closedBall_self hr.le)
  have hpuncture : ∀ z ∈ ({0}ᶜ : Set ℂ), g z ∈ ({0}ᶜ : Set ℂ) := by
    intro z hz hgz
    change g z = 0 at hgz
    have heq : e (actualRadialClamp r z) = e 0 := hgz.trans he0.symm
    have hcz := e.injOn (hsource z) hzsource heq
    exact hz ((hzero z).mp hcz)
  exact ⟨g,hvalue,hg0,hgderiv,hpuncture,
    actual_positive_derivative_local_homology g A hg0 hgderiv hpos hpuncture⟩

private theorem actual_open_chart_extension
    (e : OpenPartialHomeomorph ℂ ℂ) (A : ℂ ≃L[ℝ] ℂ)
    (he0 : e 0 = 0) (hderiv : HasFDerivAt e A.toContinuousLinearMap 0)
    (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall 0 r ⊆ e.source) :
    ∃ g : C(ℂ,ℂ),
      (∀ z : ℂ, ‖z‖ ≤ r → g z = e z) ∧
      g 0 = 0 ∧ HasFDerivAt g A.toContinuousLinearMap 0 ∧
      (∀ z ∈ ({0}ᶜ : Set ℂ), g z ∈ ({0}ᶜ : Set ℂ)) := by
  obtain ⟨hc,hbound,hid,hzero⟩ := actual_radial_clamp_properties r hr
  have hsource (z : ℂ) : actualRadialClamp r z ∈ e.source := by
    apply hball
    simpa only [Metric.mem_closedBall,dist_zero_right] using hbound z
  let g : C(ℂ,ℂ) := ⟨fun z => e (actualRadialClamp r z),
    e.continuousOn.comp_continuous hc hsource⟩
  have hvalue (z : ℂ) (hz : ‖z‖ ≤ r) : g z = e z := by
    change e (actualRadialClamp r z) = e z
    rw [hid z hz]
  have hg0 : g 0 = 0 := (hvalue 0 (by simp only [norm_zero]; exact hr.le)).trans he0
  have hgerm : g =ᶠ[nhds (0 : ℂ)] e := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
    have hn : ‖z‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    exact hvalue z hn.le
  have hgderiv : HasFDerivAt g A.toContinuousLinearMap 0 :=
    hderiv.congr_of_eventuallyEq hgerm
  have hzsource : (0 : ℂ) ∈ e.source := hball (Metric.mem_closedBall_self hr.le)
  have hpuncture : ∀ z ∈ ({0}ᶜ : Set ℂ), g z ∈ ({0}ᶜ : Set ℂ) := by
    intro z hz hgz
    change g z = 0 at hgz
    have heq : e (actualRadialClamp r z) = e 0 := hgz.trans he0.symm
    exact hz ((hzero z).mp (e.injOn (hsource z) hzsource heq))
  exact ⟨g,hvalue,hg0,hgderiv,hpuncture⟩

private theorem actual_open_chart_local_homology_sign
    (e : OpenPartialHomeomorph ℂ ℂ) (A : ℂ ≃L[ℝ] ℂ)
    (he0 : e 0 = 0) (hderiv : HasFDerivAt e A.toContinuousLinearMap 0)
    (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall 0 r ⊆ e.source) :
    ∃ g : C(ℂ,ℂ),
      (∀ z : ℂ, ‖z‖ ≤ r → g z = e z) ∧
      ∃ hpuncture : ∀ z ∈ ({0}ᶜ : Set ℂ), g z ∈ ({0}ᶜ : Set ℂ),
        pairRelativeHomologyMap ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ) g hpuncture 2 =
          if 0 < LinearMap.det A.toLinearEquiv.toLinearMap
          then 𝟙 (relativeHomology ℂ ({0}ᶜ : Set ℂ) 2)
          else -(𝟙 (relativeHomology ℂ ({0}ᶜ : Set ℂ) 2)) := by
  obtain ⟨g,hvalue,hg0,hgderiv,hpuncture⟩ := actual_open_chart_extension e A he0 hderiv r hr hball
  refine ⟨g,hvalue,hpuncture,?_⟩
  by_cases hpos : 0 < LinearMap.det A.toLinearEquiv.toLinearMap
  · rw [if_pos hpos]
    exact actual_positive_derivative_local_homology g A hg0 hgderiv hpos hpuncture
  · rw [if_neg hpos]
    have hne : LinearMap.det A.toLinearEquiv.toLinearMap ≠ 0 :=
      A.toLinearEquiv.isUnit_det'.ne_zero
    exact actual_negative_derivative_local_homology g A hg0 hgderiv
      (lt_of_le_of_ne (le_of_not_gt hpos) hne) hpuncture

private theorem actual_open_chart_relative_transport
    (e : OpenPartialHomeomorph ℂ ℂ) (A : ℂ ≃L[ℝ] ℂ)
    (he0 : e 0 = 0) (hderiv : HasFDerivAt e A.toContinuousLinearMap 0)
    (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall 0 r ⊆ e.source) :
    let B := Metric.ball (0 : ℂ) r
    let D : Set B := {z | z.val ≠ 0}
    let P : Set ℂ := {0}ᶜ
    ∃ k : C(B,ℂ),
      (∀ z : B, k z = e z.val) ∧
      ∃ hk : ∀ z ∈ D, k z ∈ P,
        pairRelativeHomologyMap D P k hk 2 =
          if 0 < LinearMap.det A.toLinearEquiv.toLinearMap
          then pairRelativeHomologyMap D P (ReflectionGermProof.inclusion B) (fun z hz => hz) 2
          else -(pairRelativeHomologyMap D P (ReflectionGermProof.inclusion B) (fun z hz => hz) 2) := by
  let B := Metric.ball (0 : ℂ) r
  let D : Set B := {z | z.val ≠ 0}
  let P : Set ℂ := {0}ᶜ
  obtain ⟨g,hvalue,hpuncture,hsign⟩ := actual_open_chart_local_homology_sign e A he0 hderiv r hr hball
  let i := ReflectionGermProof.inclusion B
  let k := g.comp i
  have hip : ∀ z ∈ D, i z ∈ P := fun z hz => hz
  have hk : ∀ z ∈ D, k z ∈ P := fun z hz => hpuncture z.val hz
  refine ⟨k,?_,hk,?_⟩
  · intro z
    exact hvalue z.val (by
      simpa only [Metric.mem_closedBall,dist_zero_right] using
        Metric.ball_subset_closedBall z.property)
  · change pairRelativeHomologyMap D P k hk 2 =
      if 0 < LinearMap.det A.toLinearEquiv.toLinearMap
      then pairRelativeHomologyMap D P i hip 2
      else -(pairRelativeHomologyMap D P i hip 2)
    have hcomp := pairRelativeHomologyMap_comp D P P i g hip hpuncture 2
    change pairRelativeHomologyMap D P k hk 2 = _ ≫ _ at hcomp
    rw [hcomp,hsign]
    split_ifs
    · exact Category.comp_id _
    · rw [Preadditive.comp_neg,Category.comp_id]

#print axioms actual_nondegenerate_circle_homotopy
#print axioms actual_positive_derivative_circle_homology
#print axioms actual_positive_derivative_puncture_homology
#print axioms actual_positive_derivative_local_homology
#print axioms actual_radial_clamp_properties
#print axioms actual_positive_open_chart_local_homology
#print axioms actual_derivative_circle_homology_sign
#print axioms actual_negative_derivative_puncture_homology
#print axioms actual_negative_derivative_local_homology
#print axioms actual_open_chart_extension
#print axioms actual_open_chart_local_homology_sign
#print axioms actual_open_chart_relative_transport
end
end SeifertSurfaces.GenusLinking
