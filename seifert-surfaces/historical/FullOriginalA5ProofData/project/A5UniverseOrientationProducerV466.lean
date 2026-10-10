import DiagramGeometry
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import GeometricArea
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Determinant

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff
open Set Topology Module Filter
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
universe u
open Foundations MetricFoundations
noncomputable section

structure A5CompactSmoothCarrier where
  carrier : Type u
  [topology : TopologicalSpace carrier]
  [charted : ChartedSpace (EuclideanHalfSpace 2) carrier]
  [smooth : IsManifold (𝓡∂ 2) ∞ carrier]
  [compact : CompactSpace carrier]
  [hausdorff : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
attribute [instance] A5CompactSmoothCarrier.topology A5CompactSmoothCarrier.charted
  A5CompactSmoothCarrier.smooth A5CompactSmoothCarrier.compact A5CompactSmoothCarrier.hausdorff
  A5CompactSmoothCarrier.secondCountable
instance : CoeSort A5CompactSmoothCarrier (Type u) := ⟨A5CompactSmoothCarrier.carrier⟩

def a5TransitionJacobian (S : A5CompactSmoothCarrier) (p q x : S) : Matrix (Fin 2) (Fin 2) ℝ :=
  let e := extChartAt (𝓡∂ 2) p
  let f := extChartAt (𝓡∂ 2) q
  fun i j => fderivWithin ℝ (f ∘ e.symm) e.target (e x) (EuclideanSpace.single j 1) i

structure A5CoherentFiniteAtlas (S : A5CompactSmoothCarrier) where
  count : ℕ
  center : Fin count → S
  covers : (⋃ i, (extChartAt (𝓡∂ 2) (center i)).source) = univ
  positive_transition : ∀ i j x,
    x ∈ (extChartAt (𝓡∂ 2) (center i)).source →
    x ∈ (extChartAt (𝓡∂ 2) (center j)).source →
    0 < (a5TransitionJacobian S (center i) (center j) x).det

def A5PositiveAtlasForm {S : A5CompactSmoothCarrier} (C : A5CoherentFiniteAtlas S)
    (O : SmoothVolumeOrientation (𝓡∂ 2) S) : Prop :=
  ∀ i x, x ∈ (extChartAt (𝓡∂ 2) (C.center i)).source →
    0 < O.form x (fun j =>
      mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) (extChartAt (𝓡∂ 2) (C.center i)).symm
        (extChartAt (𝓡∂ 2) (C.center i)).target (extChartAt (𝓡∂ 2) (C.center i) x)
        ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) (extChartAt (𝓡∂ 2) (C.center i) x)).symm
          (EuclideanSpace.single j 1)))

set_option backward.isDefEq.respectTransparency false in
/-- Smooth partition-of-unity orientation producer: actual smooth
alternating two-form, nonvanishing, and positive in each coherent chart. -/
theorem a5_coherent_atlas_orientation_exists (S : A5CompactSmoothCarrier)
    (C : A5CoherentFiniteAtlas S) :
    ∃ O : SmoothVolumeOrientation (𝓡∂ 2) S, A5PositiveAtlasForm C O := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : SmoothPartitionOfUnity (Fin C.count) (𝓡∂ 2) S,
      ρ.IsSubordinate (fun i => (extChartAt (𝓡∂ 2) (C.center i)).source) := by
    apply SmoothPartitionOfUnity.exists_isSubordinate _ isClosed_univ
    · intro i
      exact isOpen_extChartAt_source (I := 𝓡∂ 2) (C.center i)
    · rw [C.covers]
  let localForm (i : S) (x : S) :
      TangentSpace (𝓡∂ 2) x [⋀^Fin 2]→ₗ[ℝ] ℝ :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.det.compLinearMap
      (mfderiv (𝓡∂ 2) 𝓘(ℝ, Euc 2)
        (extChartAt (𝓡∂ 2) i) x).toLinearMap
  let form (x : S) : TangentSpace (𝓡∂ 2) x [⋀^Fin 2]→ₗ[ℝ] ℝ :=
    ∑ i, (ρ i x) • localForm (C.center i) x
  let frame (j : S) (x : S) : Fin 2 → TangentSpace (𝓡∂ 2) x :=
    fun k => mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2)
      (extChartAt (𝓡∂ 2) j).symm
      (extChartAt (𝓡∂ 2) j).target
      (extChartAt (𝓡∂ 2) j x)
      ((tangentSpaceCastModel 𝓘(ℝ, Euc 2)
        (extChartAt (𝓡∂ 2) j x)).symm (EuclideanSpace.single k 1))
  have frame_transition : ∀ i j x,
      x ∈ (extChartAt (𝓡∂ 2) i).source →
      x ∈ (extChartAt (𝓡∂ 2) j).source →
      localForm i x (frame j x) =
        (a5TransitionJacobian S j i x).det := by
    intro i j x hi hj
    have ht := (extChartAt (𝓡∂ 2) j).map_source hj
    have hd : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡∂ 2)
        (extChartAt (𝓡∂ 2) j).symm
        (extChartAt (𝓡∂ 2) j).target
        (extChartAt (𝓡∂ 2) j x) :=
      (contMDiffWithinAt_extChartAt_symm_target j ht
        (n := (∞ : ℕ∞ω))).mdifferentiableWithinAt (by simp)
    have hdu : UniqueMDiffWithinAt 𝓘(ℝ, Euc 2)
        (extChartAt (𝓡∂ 2) j).target
        (extChartAt (𝓡∂ 2) j x) :=
      (uniqueDiffOn_extChartAt_target j _ ht).uniqueMDiffWithinAt
    have he : (extChartAt (𝓡∂ 2) j).symm
        (extChartAt (𝓡∂ 2) j x) = x :=
      (extChartAt (𝓡∂ 2) j).left_inv hj
    have hg : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ, Euc 2)
        (extChartAt (𝓡∂ 2) i)
        ((extChartAt (𝓡∂ 2) j).symm
          (extChartAt (𝓡∂ 2) j x)) := by
      rw [he]
      exact mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hi)
    have hc := mfderiv_comp_mfderivWithin
      (extChartAt (𝓡∂ 2) j x) hg hd hdu
    rw [he, mfderivWithin_eq_fderivWithin] at hc
    have hc' : (mfderiv (𝓡∂ 2) 𝓘(ℝ, Euc 2)
        (extChartAt (𝓡∂ 2) i) x) ∘L
        (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2)
          (extChartAt (𝓡∂ 2) j).symm
          (extChartAt (𝓡∂ 2) j).target
          (extChartAt (𝓡∂ 2) j x)) =
      fderivWithin ℝ ((extChartAt (𝓡∂ 2) i) ∘
        (extChartAt (𝓡∂ 2) j).symm)
        (extChartAt (𝓡∂ 2) j).target
        (extChartAt (𝓡∂ 2) j x) := hc.symm
    change (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.det
      (fun k => (mfderiv (𝓡∂ 2) 𝓘(ℝ, Euc 2)
          (extChartAt (𝓡∂ 2) i) x)
        ((mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2)
            (extChartAt (𝓡∂ 2) j).symm
            (extChartAt (𝓡∂ 2) j).target
            (extChartAt (𝓡∂ 2) j x))
          (EuclideanSpace.single k 1))) = _
    rw [Module.Basis.det_apply]
    congr 1
    ext a b
    simp only [Module.Basis.toMatrix_apply]
    simp only [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
    exact congrArg (fun L : Euc 2 →L[ℝ] Euc 2 =>
      (L (EuclideanSpace.single b (1 : ℝ))).ofLp a) hc'
  have positive : ∀ j x,
      x ∈ (extChartAt (𝓡∂ 2) (C.center j)).source →
      0 < form x (frame (C.center j) x) := by
    intro j x hx
    have hsum : form x (frame (C.center j) x) =
        ∑ i, ρ i x * localForm (C.center i) x (frame (C.center j) x) := by
      classical
      dsimp [form]
      induction (Finset.univ : Finset (Fin C.count)) using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, AlternatingMap.add_apply,
          AlternatingMap.smul_apply, smul_eq_mul, ih]
    rw [hsum]
    have hterm : ∀ i : Fin C.count, 0 ≤ ρ i x * localForm (C.center i) x (frame (C.center j) x) := by
      intro i
      by_cases hzero : ρ i x = 0
      · simp [hzero]
      · have hi : x ∈ (extChartAt (𝓡∂ 2) (C.center i)).source :=
          hρ i (subset_tsupport _ (Function.mem_support.mpr hzero))
        rw [frame_transition (C.center i) (C.center j) x hi hx]
        exact mul_nonneg (ρ.nonneg i x) (C.positive_transition j i x hx hi).le
    apply Finset.sum_pos' (fun i _ => hterm i)
    obtain ⟨i, hi⟩ := ρ.exists_pos_of_mem (mem_univ x)
    have hix : x ∈ (extChartAt (𝓡∂ 2) (C.center i)).source :=
      hρ i (subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hi)))
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [frame_transition (C.center i) (C.center j) x hix hx]
    exact mul_pos hi (C.positive_transition j i x hx hix)
  have smooth_coefficients : ∀ p : S,
      ContDiffOn ℝ ∞
        (fun y : Euc 2 => form ((extChartAt (𝓡∂ 2) p).symm y)
          (fun k => mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2)
            (extChartAt (𝓡∂ 2) p).symm (extChartAt (𝓡∂ 2) p).target y
            ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm (EuclideanSpace.single k 1))))
        (extChartAt (𝓡∂ 2) p).target := by
    intro p
    let e := extChartAt (𝓡∂ 2) p
    let frameY (y : Euc 2) : Fin 2 → TangentSpace (𝓡∂ 2) (e.symm y) :=
      fun k => mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) e.symm e.target y
        ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm (EuclideanSpace.single k 1))
    let term (i : Fin C.count) (y : Euc 2) : ℝ :=
      ρ i (e.symm y) * localForm (C.center i) (e.symm y) (frameY y)
    have hsum : ∀ y : Euc 2,
        form (e.symm y) (frameY y) = ∑ i, term i y := by
      intro y
      classical
      dsimp [form]
      induction (Finset.univ : Finset (Fin C.count)) using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, AlternatingMap.add_apply,
          AlternatingMap.smul_apply, smul_eq_mul, ih]
    have hterm : ∀ i, ContDiffOn ℝ ∞ (term i) e.target := by
      intro i y hy
      have hcont := (contMDiffOn_extChartAt_symm (n := (∞ : ℕ∞ω)) p).continuousOn y hy
      by_cases hs : e.symm y ∈ tsupport (ρ i)
      · have hi : e.symm y ∈ (extChartAt (𝓡∂ 2) (C.center i)).source := hρ i hs
        have hxy : e (e.symm y) = y := e.right_inv hy
        have hys : y ∈ (e.symm ≫ extChartAt (𝓡∂ 2) (C.center i)).source := ⟨hy, hi⟩
        have ht : ContDiffWithinAt ℝ ∞
            ((extChartAt (𝓡∂ 2) (C.center i)) ∘ e.symm) e.target y :=
          (contDiffWithinAt_ext_coord_change (C.center i) p hys).mono
            (extChartAt_target_subset_range p)
        have hder := ht.fderivWithin_right (uniqueDiffOn_extChartAt_target p)
          (m := (∞ : ℕ∞ω)) (by simp) hy
        have hcoeff : ∀ a b : Fin 2, ContDiffWithinAt ℝ ∞
            (fun z => (fderivWithin ℝ ((extChartAt (𝓡∂ 2) (C.center i)) ∘ e.symm)
              e.target z (EuclideanSpace.single b 1)) a) e.target y := by
          intro a b
          have hdv := hder.clm_apply (contDiffWithinAt_const (c := EuclideanSpace.single b (1 : ℝ)))
          exact (EuclideanSpace.proj a).contDiff.contDiffAt.comp_contDiffWithinAt y hdv
        have hdet : ContDiffWithinAt ℝ ∞
            (fun z => Matrix.det (fun a b : Fin 2 => fderivWithin ℝ
              ((extChartAt (𝓡∂ 2) (C.center i)) ∘ e.symm)
              e.target z (EuclideanSpace.single b 1) a))
            e.target y := by
          simp only [Matrix.det_fin_two]
          exact ((hcoeff 0 0).mul (hcoeff 1 1)).sub ((hcoeff 0 1).mul (hcoeff 1 0))
        have hw : ContDiffWithinAt ℝ ∞ (fun z => ρ i (e.symm z)) e.target y := by
          exact ((ρ i).contMDiff.comp_contMDiffOn
            (contMDiffOn_extChartAt_symm (n := (∞ : ℕ∞ω)) p)).contDiffOn y hy
        apply (hw.mul hdet).congr_of_eventuallyEq_of_mem ?_ hy
        filter_upwards [hcont.preimage_mem_nhdsWithin
            ((isOpen_extChartAt_source (I := 𝓡∂ 2) (C.center i)).mem_nhds hi),
          self_mem_nhdsWithin] with z hiz hz
        have hpz := e.map_target hz
        have hframe := frame_transition (C.center i) p (e.symm z) hiz hpz
        have hez := e.right_inv hz
        change localForm (C.center i) (e.symm z)
          (fun k => mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) e.symm e.target
            (e (e.symm z)) ((tangentSpaceCastModel 𝓘(ℝ, Euc 2)
            (e (e.symm z))).symm (EuclideanSpace.single k 1))) =
          Matrix.det (fun a b : Fin 2 => fderivWithin ℝ
            ((extChartAt (𝓡∂ 2) (C.center i)) ∘ e.symm) e.target
            (e (e.symm z)) (EuclideanSpace.single b 1) a) at hframe
        rw [hez] at hframe
        change ρ i (e.symm z) * localForm (C.center i) (e.symm z) (frameY z) = _
        rw [hframe]
      · have hzero : ∀ᶠ z in 𝓝[e.target] y, ρ i (e.symm z) = 0 := by
          have hz : {x | ρ i x = 0} ∈ 𝓝 (e.symm y) := by
            have hopen := isClosed_tsupport (ρ i) |>.isOpen_compl
            exact mem_of_superset (hopen.mem_nhds hs) (fun x hx => by
              exact Function.notMem_support.mp (fun hm => hx (subset_tsupport _ hm)))
          exact hcont.preimage_mem_nhdsWithin hz
        apply (contDiffWithinAt_const (c := (0 : ℝ))).congr_of_eventuallyEq_of_mem ?_ hy
        filter_upwards [hzero] with z hz
        simp [term, hz]
    have htotal : ContDiffOn ℝ ∞ (fun y => ∑ i, term i y) e.target :=
      ContDiffOn.sum (fun i _ => hterm i)
    exact htotal.congr (fun y _ => hsum y)
  refine ⟨{ form := form, nowhere_zero := ?_, smooth_coefficients := smooth_coefficients }, ?_⟩
  · intro x hzero
    have hx : x ∈ ⋃ i, (extChartAt (𝓡∂ 2) (C.center i)).source := by
      rw [C.covers]
      exact mem_univ x
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hp := positive i x hi
    rw [hzero, AlternatingMap.zero_apply] at hp
    exact (lt_irrefl 0) hp
  · exact positive

#print axioms a5_coherent_atlas_orientation_exists
end
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
