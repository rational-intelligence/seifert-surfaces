import CurveComplexGenusTwo.CWHurewicz.CWBasic
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Complex.Circle
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHelpers
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHZero
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseAssemblyHelpers

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
namespace CircleHomologyComputation

abbrev East := ↥({1}ᶜ : Set Circle)
abbrev West := ↥({-1}ᶜ : Set Circle)
abbrev Overlap := ↥(({1}ᶜ : Set Circle) ∩ {-1}ᶜ)

def overlapToEast : TopCat.of Overlap ⟶ TopCat.of East :=
  TopCat.ofHom ⟨fun x => ⟨x.val, x.property.1⟩, by fun_prop⟩
def overlapToWest : TopCat.of Overlap ⟶ TopCat.of West :=
  TopCat.ofHom ⟨fun x => ⟨x.val, x.property.2⟩, by fun_prop⟩

abbrev HF (n : ℕ) :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)

/-- Component coordinates intertwine both actual inclusion-induced maps with sum.
The two coordinate vectors are sent to the positive generator of each arc's H₀. -/
def ComponentCoordinates : Prop :=
  ∃ e : H Overlap 0 ≃ₗ[ℤ] (ℤ × ℤ),
    ∀ x : H Overlap 0,
      ((TopCat.of East).singularHomology₀ε (ModuleCat.of ℤ ℤ))
          ((HF 0).map overlapToEast x) = (e x).1 + (e x).2 ∧
      ((TopCat.of West).singularHomology₀ε (ModuleCat.of ℤ ℤ))
          ((HF 0).map overlapToWest x) = (e x).1 + (e x).2

theorem contractible_positive_homology (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (n : ℕ) (hn : 0 < n) : IsZero (H X n) := by
  exact (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of Unit) (by omega)).of_iso
      (homotopyHomologyIso (ContractibleSpace.hequiv_unit X).some n)

theorem overlap_positive_homology (n : ℕ) (hn : 0 < n) :
    IsZero (H Overlap n) := by
  exact (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of (Unit ⊕ Unit)) (by omega)).of_iso
      (homotopyHomologyIso overlapHomotopyEquiv n)

theorem overlap_component_coordinates : ComponentCoordinates := by
  refine ⟨overlapCoordinatesIso.toLinearEquiv, ?_⟩
  intro x
  have hc := congrArg (fun f => f x) overlapCoordinatesIso_sum
  have he := congrArg (fun f => f x) (augmentation_naturality overlapToEast)
  have hw := congrArg (fun f => f x) (augmentation_naturality overlapToWest)
  exact ⟨he.trans hc.symm, hw.trans hc.symm⟩

private abbrev CX := TopCat.of Circle
private abbrev CU : Set CX := CircleCoverGeometry.eastArc
private abbrev CV : Set CX := CircleCoverGeometry.westArc

private theorem circlePairZero (n : ℕ) (hn : 0 < n) :
    IsZero ((mvPairComplex CX CU CV).homology n) := by
  letI := CircleCoverGeometry.eastArc_contractible
  letI := CircleCoverGeometry.westArc_contractible
  exact pairHomology_zero CX CU CV n
    (contractible_positive_homology _ n hn) (contractible_positive_homology _ n hn)

private def overlapMVCoordinates : (mvOrdinaryComplex CX (CU ∩ CV)).homology 0 ≃ₗ[ℤ]
    (ℤ × ℤ) :=
  (ordinaryHomologyIso CX (CU ∩ CV) 0).toLinearEquiv.trans overlapCoordinatesIso.toLinearEquiv

private theorem difference_kernel_coordinates
    (x : (mvOrdinaryComplex CX (CU ∩ CV)).homology 0) :
    mvHomologyDifference CX CU CV 0 x = 0 ↔
      (overlapMVCoordinates x).1 + (overlapMVCoordinates x).2 = 0 := by
  letI : ContractibleSpace East := CircleCoverGeometry.eastArc_contractible
  letI : ContractibleSpace West := CircleCoverGeometry.westArc_contractible
  letI : PathConnectedSpace (TopCat.of East) := inferInstanceAs (PathConnectedSpace East)
  letI : PathConnectedSpace (TopCat.of West) := inferInstanceAs (PathConnectedSpace West)
  have ze : ((TopCat.of East).singularHomology₀ε RZ) (0 : H East 0) = 0 :=
    ((TopCat.of East).singularHomology₀ε RZ).hom.map_zero
  have zw : ((TopCat.of West).singularHomology₀ε RZ) (0 : H West 0) = 0 :=
    ((TopCat.of West).singularHomology₀ε RZ).hom.map_zero
  let z : H Overlap 0 := (ordinaryHomologyIso CX (CU ∩ CV) 0).hom x
  let a := HomologicalComplex.homologyMap (mvPairFst CX CU CV) 0
    (mvHomologyDifference CX CU CV 0 x)
  let b := HomologicalComplex.homologyMap (mvPairSnd CX CU CV) 0
    (mvHomologyDifference CX CU CV 0 x)
  have hf : (ordinaryHomologyIso CX CU 0).hom a = (HF 0).map overlapToEast z := by
    have h := congrArg (fun f => f ≫ (ordinaryHomologyIso CX CU 0).hom)
      (mvHomologyDifference_fst CX CU CV 0)
    rw [ordinaryHomologyIso_naturality] at h
    exact congrArg (fun f => f x) h
  have hs : (ordinaryHomologyIso CX CV 0).hom b = -(HF 0).map overlapToWest z := by
    have h := congrArg (fun f => f ≫ (ordinaryHomologyIso CX CV 0).hom)
      (mvHomologyDifference_snd CX CU CV 0)
    rw [Preadditive.neg_comp, ordinaryHomologyIso_naturality] at h
    exact congrArg (fun f => f x) h
  have hsum : (overlapMVCoordinates x).1 + (overlapMVCoordinates x).2 =
      (TopCat.of Overlap).singularHomology₀ε RZ z :=
    congrArg (fun f => f z) overlapCoordinatesIso_sum
  have hae : (TopCat.of East).singularHomology₀ε RZ ((ordinaryHomologyIso CX CU 0).hom a) =
      (overlapMVCoordinates x).1 + (overlapMVCoordinates x).2 := by
    rw [hf, hsum]
    exact congrArg (fun f => f z) (augmentation_naturality overlapToEast)
  have hbe : (TopCat.of West).singularHomology₀ε RZ ((ordinaryHomologyIso CX CV 0).hom b) =
      -((overlapMVCoordinates x).1 + (overlapMVCoordinates x).2) := by
    rw [hs, map_neg, hsum]
    exact congrArg Neg.neg (congrArg (fun f => f z) (augmentation_naturality overlapToWest))
  constructor
  · intro hx
    have ha : a = 0 := by dsimp [a]; rw [hx]; simp
    rw [← hae, ha]
    exact (congrArg ((TopCat.of East).singularHomology₀ε RZ)
      (ordinaryHomologyIso CX CU 0).hom.hom.map_zero).trans ze
  · intro hx
    have ia : Function.Injective ((TopCat.of East).singularHomology₀ε RZ) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    have ib : Function.Injective ((TopCat.of West).singularHomology₀ε RZ) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    have ha : a = 0 := by
      apply (ordinaryHomologyIso CX CU 0).toLinearEquiv.injective
      apply ia
      change ((TopCat.of East).singularHomology₀ε RZ)
        ((ordinaryHomologyIso CX CU 0).hom a) =
          ((TopCat.of East).singularHomology₀ε RZ) ((ordinaryHomologyIso CX CU 0).hom 0)
      exact (hae.trans hx).trans
        ((congrArg ((TopCat.of East).singularHomology₀ε RZ)
          (ordinaryHomologyIso CX CU 0).hom.hom.map_zero).trans ze).symm
    have hb : b = 0 := by
      apply (ordinaryHomologyIso CX CV 0).toLinearEquiv.injective
      apply ib
      change ((TopCat.of West).singularHomology₀ε RZ)
        ((ordinaryHomologyIso CX CV 0).hom b) =
          ((TopCat.of West).singularHomology₀ε RZ) ((ordinaryHomologyIso CX CV 0).hom 0)
      exact ((hbe.trans (congrArg Neg.neg hx)).trans (neg_zero)).trans
        ((congrArg ((TopCat.of West).singularHomology₀ε RZ)
          (ordinaryHomologyIso CX CV 0).hom.hom.map_zero).trans zw).symm
    apply (mvPairHomologyEquiv CX CU CV 0).injective
    change (a,b) = _
    rw [ha,hb]
    exact (map_zero (mvPairHomologyEquiv CX CU CV 0)).symm


/-- The desired degree-one result uses the existing integral singular homology object. -/
def circleH1Iso : H Circle 1 ≅ ModuleCat.of ℤ ℤ := by
  let δ := mvAmbientConnecting CX CU CV CircleCoverGeometry.eastArc_open
    CircleCoverGeometry.westArc_open CircleCoverGeometry.arcs_cover 0
  have ex := mvAmbient_exact_ambient CX CU CV CircleCoverGeometry.eastArc_open
    CircleCoverGeometry.westArc_open CircleCoverGeometry.arcs_cover 0
  have hz : mvAmbientHomologySum CX CU CV 1 = 0 := (circlePairZero 1 (by omega)).eq_of_src _ _
  have hm : Mono δ := (ShortComplex.exact_iff_mono _ hz).mp ex
  have hi : Function.Injective δ := (ModuleCat.mono_iff_injective _).mp hm
  exact (singularHomologyRepresentation CX 1).symm ≪≫
    isoOfSumKernel δ (mvHomologyDifference CX CU CV 0)
      (mvAmbientConnecting_difference CX CU CV CircleCoverGeometry.eastArc_open
        CircleCoverGeometry.westArc_open CircleCoverGeometry.arcs_cover 0)
      (mvAmbient_exact_intersection CX CU CV CircleCoverGeometry.eastArc_open
        CircleCoverGeometry.westArc_open CircleCoverGeometry.arcs_cover 0)
      hi overlapMVCoordinates difference_kernel_coordinates

theorem circle_higher_homology (n : ℕ) (hn : 2 ≤ n) : IsZero (H Circle n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have ex := mvAmbient_exact_ambient CX CU CV CircleCoverGeometry.eastArc_open
    CircleCoverGeometry.westArc_open CircleCoverGeometry.arcs_cover k
  have hp := circlePairZero (k + 1) (by omega)
  have hi := (overlap_positive_homology k (by omega)).of_iso
    (ordinaryHomologyIso CX (CU ∩ CV) k)
  exact (ex.isZero_X₂ (hp.eq_of_src _ _) (hi.eq_of_tgt _ _)).of_iso
    (singularHomologyRepresentation CX (k + 1)).symm

end CircleHomologyComputation
