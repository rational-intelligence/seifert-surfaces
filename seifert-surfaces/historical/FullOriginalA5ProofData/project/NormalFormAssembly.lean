import SurfaceInvariants
import DifferentialGeometry.Topology.FixedPoint.Brouwer
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Connected.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Homotopy.Contractible
import ClassificationOfSurfaces.EvalStatement
import Mathlib.SetTheory.Cardinal.Finite
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereProbe
import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.LinearAlgebra.TensorProduct.Free
import CurveComplexGenusTwo.Topology.ActualClosedOrientableHomology.ActualClosedOrientableModelHomologyOneProof
import CurveComplexGenusTwo.Topology.ActualCutRecognition.ActualOrientableBoundaryOfAtlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.LinearAlgebra.Determinant
import DifferentialGeometry.Topology.SimplicialComplex.GeometricEulerCharacteristic
import ClassificationOfSurfaces.Moise.ChartInduction
import DifferentialGeometry.Topology.SimplicialComplex.GeometricCompactness
import Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Dimension.Constructions
import DependencyImports
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Algebra.Category.ModuleCat.Products
import CurveComplexGenusTwo.Topology.ActualBoundaryModels.ZeroHandleClosedDisc
import Mathlib.Geometry.Manifold.Instances.Sphere
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set Topology
open scoped TensorProduct Manifold ContDiff
open SeifertSurfaces.Foundations
open CurveComplex CurveComplexGenusTwo.CWHurewicz
open LeanEval.Topology.ClassificationOfSurfaces
open LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain
namespace SeifertSurfaces.GenusLinking
noncomputable section
private theorem connected_component_count_one (S : CompactOrientedSurface.{0})
    [ConnectedSpace S] : componentCount S = 1 := by
  unfold componentCount
  have : Unique (ConnectedComponents S) := (nonempty_unique _).some
  exact Nat.card_unique


private abbrev QExtend := ModuleCat.extendScalars.{0,0,0} (algebraMap ℤ ℚ)

private instance : QExtend.Additive where
  map_add := by
    intro M N f g
    ext m
    change (1 : ℚ) ⊗ₜ[ℤ] (f.hom + g.hom) m =
      (1 : ℚ) ⊗ₜ[ℤ] f.hom m + (1 : ℚ) ⊗ₜ[ℤ] g.hom m
    simp [TensorProduct.tmul_add]

private instance : PreservesFiniteLimits QExtend :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    ((RingHom.flat_algebraMap_iff (R := ℤ) (S := ℚ)).mpr inferInstance)

private def qExtendIntIso : QExtend.obj (ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℚ ℚ := by
  let e : (ℚ ⊗[ℤ] ℤ) ≃ₗ[ℚ] ℚ := {
    (TensorProduct.rid ℤ ℚ).toAddEquiv with
    map_smul' := map_rat_smul (TensorProduct.rid ℤ ℚ).toAddEquiv.toAddMonoidHom }
  exact e.toModuleIso

/-- Flat extension of coefficients on the actual singular chain complex. -/
private def rationalHomologyIntegralExtensionIso
    (X : Type) [TopologicalSpace X] (k : ℕ) :
    rationalHomology X k ≅ QExtend.obj
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)) := by
  let RZ := ModuleCat.of ℤ ℤ
  let K := ((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj RZ).obj (TopCat.of X)
  let eChain := (SSet.chainComplexFunctorObjCompMapIso QExtend RZ).app
    (TopCat.toSSet.obj (TopCat.of X))
  let eCoeff := (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).map
    qExtendIntIso.hom).app (TopCat.of X))
  have eCoeffIso : ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (QExtend.obj RZ)).obj (TopCat.of X) ≅
      ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
        (ModuleCat.of ℚ ℚ)).obj (TopCat.of X) :=
    ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).mapIso qExtendIntIso).app
      (TopCat.of X)
  let eHom := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (.down ℕ) k).mapIso
    (eChain ≪≫ eCoeffIso)
  exact eHom.symm ≪≫ (K.sc k).mapHomologyIso QExtend

private theorem rationalHomology_isZero_of_integral_isZero
    (X : Type) [TopologicalSpace X] (k : ℕ)
    (hz : IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))) :
    IsZero (rationalHomology X k) := by
  exact (Functor.map_isZero QExtend hz).of_iso
    (rationalHomologyIntegralExtensionIso X k)


private theorem twoSphere_integral_homology_one_isZero :
    IsZero (CurveComplex.integralHomology
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) 1) := by
  classical
  let puncturedChart (n : ℕ) (v : SphereSpace n) :
      ↥({v}ᶜ : Set (SphereSpace n)) ≃ₜ EuclideanSpace ℝ (Fin n) := by
    have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) := ⟨by simp⟩
    exact (Homeomorph.setCongr (stereographic'_source v).symm).trans
      ((stereographic' n v).toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr (stereographic'_target v)).trans (Homeomorph.Set.univ _)))
  have puncturedChart_antipode (n : ℕ) (v : SphereSpace n) :
      puncturedChart n v ⟨-v, by simpa using (ne_neg_of_mem_unit_sphere ℝ v).symm⟩ = 0 := by
    have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) := ⟨by simp⟩
    change (stereographic' n v) (-v) = 0
    simp [stereographic', stereographic_apply_neg]
  have punctured_contractible (n : ℕ) (v : SphereSpace n) :
      ContractibleSpace ↥({v}ᶜ : Set (SphereSpace n)) :=
    (puncturedChart n v).contractibleSpace
  let overlapChart (n : ℕ) (v : SphereSpace n) :
      ↥(({v}ᶜ : Set (SphereSpace n)) ∩ {-v}ᶜ) ≃ₜ
        ↥({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := {
    toFun x := ⟨puncturedChart n v ⟨x.val, x.property.1⟩, by
      change puncturedChart n v ⟨x.val, x.property.1⟩ ≠ 0
      rw [← puncturedChart_antipode n v]
      intro h
      have hh := congrArg Subtype.val ((puncturedChart n v).injective h)
      exact x.property.2 hh⟩
    invFun y := ⟨((puncturedChart n v).symm y.val).val,
      ((puncturedChart n v).symm y.val).property, by
      change ((puncturedChart n v).symm y.val).val ≠ -v
      intro h
      apply y.property
      have hh : (puncturedChart n v).symm y.val =
          ⟨-v, by simpa using (ne_neg_of_mem_unit_sphere ℝ v).symm⟩ := Subtype.ext h
      have := congrArg (puncturedChart n v) hh
      simpa [puncturedChart_antipode] using this⟩
    left_inv x := by apply Subtype.ext; simp
    right_inv y := by apply Subtype.ext; simp
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (puncturedChart n v).continuous.comp (continuous_subtype_val.subtype_mk _)
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp ((puncturedChart n v).symm.continuous.comp continuous_subtype_val)
  }
  have antipodal_open_cover (n : ℕ) (v : SphereSpace n) :
      ({v}ᶜ : Set (SphereSpace n)) ∪ {-v}ᶜ = univ := by
    ext x
    simp only [mem_union, mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
    by_cases h : x = v
    · right
      subst x
      exact ne_neg_of_mem_unit_sphere ℝ v
    · exact Or.inl h
  let v : SphereSpace 2 := ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.1 0⟩
  let X := TopCat.of (SphereSpace 2)
  let U : Set X := {v}ᶜ
  let V : Set X := {-v}ᶜ
  let hU : IsOpen U := isClosed_singleton.isOpen_compl
  let hV : IsOpen V := isClosed_singleton.isOpen_compl
  let hc : U ∪ V = univ := antipodal_open_cover 2 v
  have : ContractibleSpace U := punctured_contractible 2 v
  have : ContractibleSpace V := punctured_contractible 2 (-v)
  have : PathConnectedSpace ↥({(0 : EuclideanSpace ℝ (Fin 2))}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_compl_singleton_of_one_lt_rank
      (Module.one_lt_rank_of_one_lt_finrank (by simp)) (0 : EuclideanSpace ℝ (Fin 2)))
  have : PathConnectedSpace ↥(U ∩ V) := (overlapChart 2 v).symm.pathConnectedSpace
  let RZ := ModuleCat.of ℤ ℤ
  let F := (singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj RZ
  let inc : TopCat.of ↥(U ∩ V) ⟶ TopCat.of U :=
    TopCat.ofHom ⟨fun x => ⟨x.val, x.property.1⟩, by fun_prop⟩
  have hg : Function.Injective (actualMVDifference X U V 0) := by
    apply (injective_iff_map_eq_zero (actualMVDifference X U V 0).hom).mpr
    intro x hx
    have hxu := congrArg Prod.fst hx
    rw [actualMVDifference_apply] at hxu
    change F.map inc x = 0 at hxu
    have he := CircleHomologyComputation.augmentation_naturality inc
    have hex := congrArg (fun m => m x) he
    change (TopCat.of U).singularHomology₀ε RZ (F.map inc x) =
      (TopCat.of ↥(U ∩ V)).singularHomology₀ε RZ x at hex
    rw [hxu, map_zero] at hex
    have hi := (ModuleCat.mono_iff_injective ((TopCat.of ↥(U ∩ V)).singularHomology₀ε RZ)).mp
      (inferInstance : Mono ((TopCat.of ↥(U ∩ V)).singularHomology₀ε RZ))
    apply hi
    simpa using hex.symm
  have hu1 : IsZero (H U 1) := CircleHomologyComputation.contractible_positive_homology U 1 (by omega)
  have hv1 : IsZero (H V 1) := CircleHomologyComputation.contractible_positive_homology V 1 (by omega)
  have := ModuleCat.subsingleton_of_isZero hu1
  have := ModuleCat.subsingleton_of_isZero hv1
  have hz (x : H X 1) : x = 0 := by
    have hd : actualMVConnecting X U V hU hV hc 0 x = 0 := by
      apply hg
      have he := congrArg (fun m => m x) (actualMVConnecting_difference X U V hU hV hc 0)
      simpa using he
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
      (actualMV_exact_ambient X U V hU hV hc 0) x hd
    have hy0 : y = 0 := Subsingleton.elim _ _
    simpa [hy0] using hy.symm
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩


private theorem sphere_homeomorph_genus_zero (S : CompactOrientedSurface.{0})
    [ConnectedSpace S] (hclosed : S.boundary = ∅)
    (hsphere : Nonempty (S ≃ₜ TwoSphere)) : surfaceGenus S = 0 := by
  obtain ⟨e⟩ := hsphere
  have : PathConnectedSpace TwoSphere :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere
        (Module.one_lt_rank_of_one_lt_finrank (by simp)) (0 : Euc 3) (by norm_num))
  have : PathConnectedSpace S := e.symm.pathConnectedSpace
  have hzQ : IsZero (rationalHomology TwoSphere 1) :=
    rationalHomology_isZero_of_integral_isZero TwoSphere 1
      twoSphere_integral_homology_one_isZero
  have : Subsingleton (rationalHomology TwoSphere 1) :=
    ModuleCat.subsingleton_of_isZero hzQ
  have hmodel : betti TwoSphere 1 = 0 := Module.finrank_zero_of_subsingleton
  have hb1 : betti S 1 = 0 := (betti_homeomorph e 1).trans hmodel
  have hb0 : betti S 0 = 1 := by
    let e0 := asIso ((TopCat.of S).singularHomology₀ε (ModuleCat.of ℚ ℚ))
    have he := e0.toLinearEquiv.finrank_eq
    simpa only [betti, rationalHomology, Module.finrank_self] using he
  have : IsEmpty ↥S.boundary := by rw [hclosed]; infer_instance
  have : IsEmpty (ConnectedComponents ↥S.boundary) :=
    ConnectedComponents.isEmpty_iff_isEmpty.mpr inferInstance
  have hb : boundaryCount S = 0 := Nat.card_eq_zero.mpr (Or.inl inferInstance)
  simp only [surfaceGenus, connected_component_count_one S, hb,
    eulerCharacteristic, hb0, hb1]
  omega


private theorem sphere_betti_two : betti TwoSphere 2 = 1 := by
  let e : rationalHomology TwoSphere 2 ≅ ModuleCat.of ℚ ℚ :=
    rationalHomologyIntegralExtensionIso TwoSphere 2 ≪≫
      QExtend.mapIso (SphereProbe.sphereTopIso 1) ≪≫ qExtendIntIso
  simpa only [betti, Module.finrank_self] using e.toLinearEquiv.finrank_eq

private theorem closed_orientable_model_betti_one
    (p : ℕ) (hp : 1 ≤ p) : betti (Quot
      (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 0)) 1 = 2*p := by
  obtain ⟨ez⟩ := CurveComplex.Hyperbolic.actual_closed_orientable_model_homology_one p hp
  let ee : QExtend.obj (ModuleCat.of ℤ (Fin (2*p) → ℤ)) ≅
      ModuleCat.of ℚ (Fin (2*p) → ℚ) :=
    (Algebra.TensorProduct.equivPiOfFiniteBasis ℚ (Pi.basisFun ℤ (Fin (2*p)))).toModuleIso
  let e := rationalHomologyIntegralExtensionIso _ 1 ≪≫ QExtend.mapIso ez ≪≫ ee
  simpa only [betti, Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one]
    using e.toLinearEquiv.finrank_eq

private theorem sphere_euler_two (S : CompactOrientedSurface.{0})
    (e : S ≃ₜ TwoSphere) : eulerCharacteristic S = 2 := by
  have : PathConnectedSpace TwoSphere :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere
        (Module.one_lt_rank_of_one_lt_finrank (by simp)) (0 : Euc 3) (by norm_num))
  have : PathConnectedSpace S := e.symm.pathConnectedSpace
  have hb0 : betti S 0 = 1 := by
    let e0 := asIso ((TopCat.of S).singularHomology₀ε (ModuleCat.of ℚ ℚ))
    simpa only [betti, rationalHomology, Module.finrank_self]
      using e0.toLinearEquiv.finrank_eq
  have hzQ : IsZero (rationalHomology TwoSphere 1) :=
    rationalHomology_isZero_of_integral_isZero TwoSphere 1
      twoSphere_integral_homology_one_isZero
  have : Subsingleton (rationalHomology TwoSphere 1) :=
    ModuleCat.subsingleton_of_isZero hzQ
  have hb1 : betti S 1 = 0 :=
    (betti_homeomorph e 1).trans Module.finrank_zero_of_subsingleton
  have hb2 : betti S 2 = 1 := (betti_homeomorph e 2).trans sphere_betti_two
  norm_num [eulerCharacteristic, hb0, hb1, hb2]

private theorem sphere_euler_genus_boundary
    (S : CompactOrientedSurface.{0}) [ConnectedSpace S]
    (hclosed : S.boundary = ∅) (e : S ≃ₜ TwoSphere) :
    eulerCharacteristic S = 2 * (componentCount S : ℤ) -
      2 * (surfaceGenus S : ℤ) - (boundaryCount S : ℤ) := by
  have hg := sphere_homeomorph_genus_zero S hclosed ⟨e⟩
  have : IsEmpty ↥S.boundary := by rw [hclosed]; infer_instance
  have : IsEmpty (ConnectedComponents ↥S.boundary) :=
    ConnectedComponents.isEmpty_iff_isEmpty.mpr inferInstance
  have hb : boundaryCount S = 0 := Nat.card_eq_zero.mpr (Or.inl inferInstance)
  rw [sphere_euler_two S e, connected_component_count_one S, hg, hb]
  norm_num






private theorem component_card_fin_circle (n : ℕ) :
    letI : TopologicalSpace (Fin n) := ⊥
    Nat.card (ConnectedComponents (Fin n × Circle)) = n := by
  classical
  letI : TopologicalSpace (Fin n) := ⊥
  let U : Fin n → Set (Fin n × Circle) := fun i => {i} ×ˢ Set.univ
  have hc : ∀ i, IsClopen (U i) := by
    intro i
    convert (isClopen_discrete ({i} : Set (Fin n))).preimage
      (continuous_fst : Continuous (Prod.fst : Fin n × Circle → Fin n)) using 1
    ext x
    simp [U]
  have hd : Pairwise (Function.onFun Disjoint U) := by
    intro i j hij
    change Disjoint (U i) (U j)
    rw [Set.disjoint_left]
    rintro ⟨k,z⟩ ⟨hki,_⟩ ⟨hkj,_⟩
    exact hij (hki.symm.trans hkj)
  have hu : ⋃ i, U i = Set.univ := by
    ext x
    simp [U]
  have hconn : ∀ i, IsConnected (U i) := by
    intro i
    exact isConnected_singleton.prod isConnected_univ
  let e := ConnectedComponents.equivOfIsClopenOfIsConnected hc hd hu hconn
  exact (Nat.card_congr e).trans (Nat.card_fin n)

private theorem boundary_count_of_orientable_model
    (S : CompactOrientedSurface.{0}) (p n : ℕ)
    (hadmissible : 1 ≤ p ∨ 1 ≤ n)
    (e : S ≃ₜ Quot (OrientableRel p n)) : boundaryCount S = n := by
  classical
  letI : ChartedSpace (EuclideanHalfSpace 2) (Quot (OrientableRel p n)) :=
    e.chartedSpace
  let I := modelWithCornersEuclideanHalfSpace 2
  have hb : ∀ x : S, x ∈ S.boundary ↔
      e x ∈ I.boundary (Quot (OrientableRel p n)) := by
    intro x
    let f := e.toOpenPartialHomeomorph.trans (chartAt (EuclideanHalfSpace 2) (e x))
    have hf : x ∈ f.source := by
      change x ∈ Set.univ ∧ e x ∈ (chartAt (EuclideanHalfSpace 2) (e x)).source
      exact ⟨Set.mem_univ x, ChartedSpace.mem_chart_source (e x)⟩
    change I.IsBoundaryPoint x ↔ I.IsBoundaryPoint (e x)
    rw [DifferentialGeometry.Topology.isBoundaryPoint_iff_any_chart I hf,
      DifferentialGeometry.Topology.isBoundaryPoint_iff_any_chart I
        (ChartedSpace.mem_chart_source (e x))]
    rfl
  let eb := e.subtype hb
  letI : TopologicalSpace (Fin n) := ⊥
  obtain ⟨em,_⟩ :=
    CurveComplex.Hyperbolic.actual_orientable_normal_form_intrinsic_boundary_components_of_atlas
      p n hadmissible (inferInstance : ChartedSpace (EuclideanHalfSpace 2)
        (Quot (OrientableRel p n)))
  obtain ⟨em⟩ := em
  let ec := eb.trans em
  let ecc := ec.isQuotientMap.isCoinducing.connectedComponentsHomeomorph (by
    intro y
    have hfiber : (ec ⁻¹' {y}) = {ec.symm y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ec.toEquiv.eq_symm_apply.symm
    rw [hfiber]
    exact isConnected_singleton)
  exact (Nat.card_congr ecc.toEquiv).trans (component_card_fin_circle n)





private theorem open_plane_image_interior (S : CompactOrientedSurface.{0}) {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    (f : U → S) (hfcont : Continuous f)
    (hfinj : Function.Injective f) (u : U) :
    (modelWithCornersEuclideanHalfSpace 2).IsInteriorPoint (f u) := by
  let I := modelWithCornersEuclideanHalfSpace 2
  let c : PartialEquiv (S) (EuclideanSpace ℝ (Fin 2)) := extChartAt I (f u)
  let f₀ : (EuclideanSpace ℝ (Fin 2)) → (S) :=
    Function.extend ((↑) : U → (EuclideanSpace ℝ (Fin 2))) f (fun _ ↦ f u)
  have hf₀_eq (x : U) : f₀ x.1 = f x := by
    exact Function.Injective.extend_apply Subtype.val_injective f
      (fun _ ↦ f u) x
  have hf₀_cont : ContinuousOn f₀ U := by
    rw [continuousOn_iff_continuous_restrict]
    convert hfcont using 1
    funext x
    exact hf₀_eq x
  let W : Set (EuclideanSpace ℝ (Fin 2)) := U ∩ f₀ ⁻¹' c.source
  have hWopen : IsOpen W :=
    hf₀_cont.isOpen_inter_preimage hU (isOpen_extChartAt_source (I := I) (f u))
  have huW : u.1 ∈ W := by
    refine ⟨u.2, ?_⟩
    change f₀ u.1 ∈ c.source
    rw [hf₀_eq u]
    exact mem_extChartAt_source (I := I) (f u)
  let g : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2)) := fun x ↦ c (f₀ x)
  have hg_cont : ContinuousOn g W := by
    apply (continuousOn_extChartAt (I := I) (f u)).comp
      (hf₀_cont.mono inter_subset_left)
    exact fun x hx ↦ hx.2
  have hg_inj : Set.InjOn g W := by
    intro x hx y hy hxy
    have hf₀xy : f₀ x = f₀ y :=
      c.injOn hx.2 hy.2 hxy
    have hfx :
        f (⟨x, hx.1⟩ : U) = f (⟨y, hy.1⟩ : U) := by
      rw [← hf₀_eq ⟨x, hx.1⟩, ← hf₀_eq ⟨y, hy.1⟩]
      exact hf₀xy
    exact congrArg Subtype.val (hfinj hfx)
  let φ : PartialEquiv (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
    hg_inj.toPartialEquiv g W
  have hφ_cont : ContinuousOn φ φ.source := by
    change ContinuousOn g W
    exact hg_cont
  have hWnhds : W ∈ nhds u.1 :=
    hWopen.mem_nhds huW
  have himage :
      g '' W ∈ nhds (g u.1) := by
    have h :=
      maps_nhds_to_nhds (EuclideanSpace ℝ (Fin 2)) hφ_cont hWnhds
        (show W ⊆ φ.source by
          change W ⊆ W
          exact subset_rfl)
    change g '' W ∈ nhds (g u.1) at h
    exact h
  have hsub : g '' W ⊆ Set.range I := by
    rintro y ⟨x,hx,rfl⟩
    exact Set.mem_range_self ((chartAt (EuclideanHalfSpace 2) (f u)) (f₀ x))
  have hr : Set.range I ∈ nhds (g u.val) := Filter.mem_of_superset himage hsub
  apply (isInteriorPoint_iff_any_chart I (ChartedSpace.mem_chart_source (f u))).mpr
  change c (f u) ∈ interior (Set.range I)
  rw [mem_interior_iff_mem_nhds]
  convert hr using 1
  congr 1
  change c (f u) = c (f₀ u.val)
  rw [hf₀_eq u]

private theorem plane_charted_boundary_empty (S : CompactOrientedSurface.{0})
    [ChartedSpace (Euc 2) S] : S.boundary = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  apply ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint x).mp
  let c := chartAt (Euc 2) x
  let u : c.target := ⟨c x,c.map_source (ChartedSpace.mem_chart_source x)⟩
  have hcont : Continuous (fun y : c.target => c.symm y.val) :=
    c.continuousOn_symm.restrict
  have hinj : Function.Injective (fun y : c.target => c.symm y.val) := by
    intro y z hyz
    apply Subtype.ext
    exact c.symm.injOn y.property z.property hyz
  have hi := open_plane_image_interior S c.open_target
    (fun y : c.target => c.symm y.val) hcont hinj u
  have hx : c.symm u.val = x := c.left_inv (ChartedSpace.mem_chart_source x)
  rwa [hx] at hi

private theorem sphere_homeomorph_boundary_empty (S : CompactOrientedSurface.{0})
    (e : S ≃ₜ TwoSphere) : S.boundary = ∅ := by
  letI : ChartedSpace (Euc 2) S := e.symm.chartedSpace
  exact plane_charted_boundary_empty S


private theorem connected_orientable_normal_form_of_exclusion
    (S : CompactOrientedSurface.{0}) [ConnectedSpace S]
    (hexclude : ∀ p n : ℕ, 1 ≤ p →
      ¬ Nonempty (S ≃ₜ Quot (NonOrientableRel p n))) :
    Nonempty (S ≃ₜ TwoSphere) ∨
      ∃ p n, (1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (S ≃ₜ Quot (OrientableRel p n)) := by
  rcases classification_of_surfaces S with hs | ⟨p,n,hm⟩
  · exact Or.inl hs
  · rcases hm with ⟨hadm,he⟩ | ⟨hp,he⟩
    · exact Or.inr ⟨p,n,hadm,he⟩
    · exact (hexclude p n hp he).elim

private theorem orientable_normal_form_genus_parameter
    (S : CompactOrientedSurface.{0}) [ConnectedSpace S]
    (p n : ℕ) (hadm : 1 ≤ p ∨ 1 ≤ n) (e : S ≃ₜ Quot (OrientableRel p n))
    (heuler : eulerCharacteristic S = 2 - 2 * (p : ℤ) - (n : ℤ)) :
    surfaceGenus S = p := by
  have hb := boundary_count_of_orientable_model S p n hadm e
  unfold surfaceGenus
  rw [connected_component_count_one S, heuler, hb]
  have hz : 2 * (1 : ℤ) - (2 - 2 * (p : ℤ) - (n : ℤ)) - (n : ℤ) =
      (2 * p : ℕ) := by omega
  rw [Nat.cast_one, hz, Int.toNat_natCast, Nat.mul_div_right _ (by omega : 0 < 2)]

private theorem connected_packet_of_normal_form_obligations
    (S : CompactOrientedSurface.{0}) [ConnectedSpace S]
    (hexclude : ∀ p n : ℕ, 1 ≤ p →
      ¬ Nonempty (S ≃ₜ Quot (NonOrientableRel p n)))
    (hmodelEuler : ∀ (p n : ℕ), (1 ≤ p ∨ 1 ≤ n) →
      (S ≃ₜ Quot (OrientableRel p n)) →
      eulerCharacteristic S = 2 - 2 * (p : ℤ) - (n : ℤ)) :
    0 ≤ 2 - eulerCharacteristic S - (boundaryCount S : ℤ) ∧
    Even (2 - eulerCharacteristic S - (boundaryCount S : ℤ)) := by
  rcases connected_orientable_normal_form_of_exclusion S hexclude with hs | ⟨p,n,hadm,⟨e⟩⟩
  · obtain ⟨e⟩ := hs
    have heuler := sphere_euler_two S e
    have hb : boundaryCount S = 0 := by
      unfold boundaryCount
      haveI : IsEmpty ↥S.boundary := by
        rw [sphere_homeomorph_boundary_empty S e]
        infer_instance
      haveI : IsEmpty (ConnectedComponents ↥S.boundary) :=
        ConnectedComponents.isEmpty_iff_isEmpty.mpr inferInstance
      exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
    rw [heuler,hb]
    norm_num
  · have heuler := hmodelEuler p n hadm e
    have hb := boundary_count_of_orientable_model S p n hadm e
    rw [heuler,hb]
    refine ⟨by omega, ⟨(p : ℤ),by omega⟩⟩

private theorem closed_zero_forward_of_normal_form_obligations
    (S : CompactOrientedSurface.{0}) [ConnectedSpace S] (hclosed : S.boundary = ∅)
    (hexclude : ∀ p n : ℕ, 1 ≤ p →
      ¬ Nonempty (S ≃ₜ Quot (NonOrientableRel p n)))
    (hmodelEuler : ∀ (p n : ℕ), (1 ≤ p ∨ 1 ≤ n) →
      (S ≃ₜ Quot (OrientableRel p n)) →
      eulerCharacteristic S = 2 - 2 * (p : ℤ) - (n : ℤ))
    (hg : surfaceGenus S = 0) : Nonempty (S ≃ₜ TwoSphere) := by
  rcases connected_orientable_normal_form_of_exclusion S hexclude with hs | ⟨p,n,hadm,⟨e⟩⟩
  · exact hs
  · have hb0 : boundaryCount S = 0 := by
      unfold boundaryCount
      haveI : IsEmpty ↥S.boundary := by rw [hclosed]; infer_instance
      haveI : IsEmpty (ConnectedComponents ↥S.boundary) :=
        ConnectedComponents.isEmpty_iff_isEmpty.mpr inferInstance
      exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
    have hbn := boundary_count_of_orientable_model S p n hadm e
    have hgp := orientable_normal_form_genus_parameter S p n hadm e (hmodelEuler p n hadm e)
    have : False := by omega
    exact this.elim

private theorem one_boundary_zero_forward_of_normal_form_obligations
    (S : CompactOrientedSurface.{0}) [ConnectedSpace S] (hb : boundaryCount S = 1)
    (hexclude : ∀ p n : ℕ, 1 ≤ p →
      ¬ Nonempty (S ≃ₜ Quot (NonOrientableRel p n)))
    (hmodelEuler : ∀ (p n : ℕ), (1 ≤ p ∨ 1 ≤ n) →
      (S ≃ₜ Quot (OrientableRel p n)) →
      eulerCharacteristic S = 2 - 2 * (p : ℤ) - (n : ℤ))
    (hg : surfaceGenus S = 0) : Nonempty (S ≃ₜ ClosedDisk) := by
  rcases connected_orientable_normal_form_of_exclusion S hexclude with hs | ⟨p,n,hadm,⟨e⟩⟩
  · obtain ⟨e⟩ := hs
    have hb0 : boundaryCount S = 0 := by
      unfold boundaryCount
      haveI : IsEmpty ↥S.boundary := by
        rw [sphere_homeomorph_boundary_empty S e]
        infer_instance
      haveI : IsEmpty (ConnectedComponents ↥S.boundary) :=
        ConnectedComponents.isEmpty_iff_isEmpty.mpr inferInstance
      exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
    have : False := by omega
    exact this.elim
  · have hbn := boundary_count_of_orientable_model S p n hadm e
    have hgp := orientable_normal_form_genus_parameter S p n hadm e (hmodelEuler p n hadm e)
    have hp : p = 0 := hgp.symm.trans hg
    have hn : n = 1 := hbn.symm.trans hb
    have e01 : S ≃ₜ Quot (OrientableRel 0 1) := by
      rw [← hp, ← hn]
      exact e
    obtain ⟨d,_⟩ := CurveComplex.Hyperbolic.actual_zero_handle_one_boundary_model_closed_disc
    exact ⟨e01.trans d.symm⟩

#print axioms connected_orientable_normal_form_of_exclusion
#print axioms orientable_normal_form_genus_parameter
#print axioms connected_packet_of_normal_form_obligations
#print axioms closed_zero_forward_of_normal_form_obligations
#print axioms one_boundary_zero_forward_of_normal_form_obligations
end
end SeifertSurfaces.GenusLinking
