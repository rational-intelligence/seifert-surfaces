import CurveComplexGenusTwo.CWHurewicz.MVComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CurveComplexGenusTwo.CWHurewicz
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable abbrev actualSingularFunctor : TopCat ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- The existing free-simplex basis isomorphisms commute with the actual differential. -/
theorem singularRepresentation_boundary (X : TopCat) (n : ℕ) :
    ModuleCat.ofHom (singularBoundaryFinsupp X n) ≫ (singularChainsFinsuppIso X n).inv =
      (singularChainsFinsuppIso X (n + 1)).inv ≫ (singularChains X).d (n + 1) n := by
  change ((singularChainsFinsuppIso X (n + 1)).inv ≫
    (singularChains X).d (n + 1) n ≫ (singularChainsFinsuppIso X n).hom) ≫
      (singularChainsFinsuppIso X n).inv = _
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Canonical chain isomorphism from explicit Finsupp chains to the project's actual
singular chain complex, with component the existing free-simplex basis isomorphism. -/
noncomputable def singularRepresentation (X : TopCat) :
    mvAmbientComplex X ≅ singularChains X where
  hom := ChainComplex.ofHom (fun n => (singularChainsFinsuppIso X n).inv) (fun n => by
    simp only [mvAmbientComplex, ChainComplex.of_d]
    exact (singularRepresentation_boundary X n).symm)
  inv := ChainComplex.ofHom (fun n => (singularChainsFinsuppIso X n).hom) (fun n => by
    simp only [mvAmbientComplex, ChainComplex.of_d]
    apply (cancel_mono (singularChainsFinsuppIso X n).inv).mp
    simp only [Category.assoc, singularRepresentation_boundary,
      Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id])
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (singularChainsFinsuppIso X n).inv_hom_id
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (singularChainsFinsuppIso X n).hom_inv_id

@[simp]
theorem singularRepresentation_hom_f (X : TopCat) (n : ℕ) :
    (singularRepresentation X).hom.f n = (singularChainsFinsuppIso X n).inv := rfl

@[simp]
theorem singularRepresentation_inv_f (X : TopCat) (n : ℕ) :
    (singularRepresentation X).inv.f n = (singularChainsFinsuppIso X n).hom := rfl

noncomputable def singularFinsuppPush {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :=
  Finsupp.lmapDomain ℤ ℤ ((TopCat.toSSet.map f).app (.op ⦋n⦌))

/-- Naturality of the actual free-simplex basis for every continuous map. -/
theorem singularRepresentation_basis_naturality {X Y : TopCat} (f : X ⟶ Y) (n : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) :
    (actualSingularFunctor.map f).f n ((singularChainsFinsuppIso X n).inv c) =
      (singularChainsFinsuppIso Y n).inv (singularFinsuppPush f n c) := by
  classical
  have hgen (Z : TopCat) (x : (TopCat.toSSet.obj Z) _⦋n⦌) :
      (singularChainsFinsuppIso Z n).inv (Finsupp.single x 1) =
        ((TopCat.toSSet.obj Z).ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom 1 := by
    rw [← singularChainsFinsuppIso_generator Z n x]
    exact (singularChainsFinsuppIso Z n).hom_inv_id_apply _
  have hs (x : (TopCat.toSSet.obj X) _⦋n⦌) :
      (actualSingularFunctor.map f).f n ((singularChainsFinsuppIso X n).inv (Finsupp.single x 1)) =
        (singularChainsFinsuppIso Y n).inv (singularFinsuppPush f n (Finsupp.single x 1)) := by
    simp only [singularFinsuppPush, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hgen]
    exact congrArg (fun g : ModuleCat.of ℤ ℤ ⟶ _ => g.hom 1)
      (SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ) x)
  have hc : c = ∑ x ∈ c.support, c x • Finsupp.single x 1 := by
    conv_lhs => rw [← Finsupp.sum_single c]
    simp [Finsupp.sum, Finsupp.smul_single]
  change ((actualSingularFunctor.map f).f n).hom ((singularChainsFinsuppIso X n).inv.hom c) =
    (singularChainsFinsuppIso Y n).inv.hom (singularFinsuppPush f n c)
  rw [hc]
  simp only [map_sum, LinearMap.map_smul]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  exact hs x

noncomputable def singularFinsuppMap {X Y : TopCat} (f : X ⟶ Y) :
    mvAmbientComplex X ⟶ mvAmbientComplex Y :=
  (singularRepresentation X).hom ≫ actualSingularFunctor.map f ≫ (singularRepresentation Y).inv

@[simp]
theorem singularFinsuppMap_f {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    (singularFinsuppMap f).f n = ModuleCat.ofHom (singularFinsuppPush f n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change (singularChainsFinsuppIso Y n).hom
    ((actualSingularFunctor.map f).f n ((singularChainsFinsuppIso X n).inv c)) = _
  rw [singularRepresentation_basis_naturality]
  exact (singularChainsFinsuppIso Y n).inv_hom_id_apply _

theorem singularRepresentation_naturality {X Y : TopCat} (f : X ⟶ Y) :
    singularFinsuppMap f ≫ (singularRepresentation Y).hom =
      (singularRepresentation X).hom ≫ actualSingularFunctor.map f := by
  simp [singularFinsuppMap, Category.assoc]

noncomputable def singularFinsuppFunctor : TopCat ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ where
  obj X := mvAmbientComplex X
  map f := singularFinsuppMap f
  map_id X := by simp [singularFinsuppMap]
  map_comp f g := by simp [singularFinsuppMap, Category.assoc]

noncomputable def singularRepresentationNatIso :
    singularFinsuppFunctor ≅ actualSingularFunctor :=
  NatIso.ofComponents singularRepresentation (fun f => singularRepresentation_naturality f)

/-- All-degree identification with the exact H object used by the project. -/
noncomputable def singularHomologyRepresentation (X : TopCat) (n : ℕ) :
    (mvAmbientComplex X).homology n ≅ H X n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).mapIso
    (singularRepresentation X)

theorem singularHomologyRepresentation_naturality {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap (singularFinsuppMap f) n ≫
      (singularHomologyRepresentation Y n).hom =
    (singularHomologyRepresentation X n).hom ≫
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map f) := by
  change HomologicalComplex.homologyMap (singularFinsuppMap f) n ≫
    HomologicalComplex.homologyMap (singularRepresentation Y).hom n =
      HomologicalComplex.homologyMap (singularRepresentation X).hom n ≫
        HomologicalComplex.homologyMap (actualSingularFunctor.map f) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    singularRepresentation_naturality]



theorem singularFinsuppPush_boundary {X Y : TopCat} (f : X ⟶ Y) (n : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ) :
    singularBoundaryFinsupp Y n (singularFinsuppPush f (n + 1) c) =
      singularFinsuppPush f n (singularBoundaryFinsupp X n c) := by
  have h := (singularFinsuppMap f).comm (n + 1) n
  simp only [singularFinsuppMap_f, mvAmbientComplex, ChainComplex.of_d] at h
  exact congrArg (fun g => g c) h

theorem singularRepresentation_single (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    (singularRepresentation X).hom.f n (Finsupp.single x 1) =
      ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom 1 := by
  change (singularChainsFinsuppIso X n).inv (Finsupp.single x 1) = _
  rw [← singularChainsFinsuppIso_generator X n x]
  exact (singularChainsFinsuppIso X n).hom_inv_id_apply _

noncomputable def ordinarySingularRepresentation (X : TopCat) (U : Set X) :
    mvOrdinaryComplex X U ≅ singularChains U :=
  singularRepresentation (TopCat.of U)

noncomputable def ordinaryHomologyRepresentation (X : TopCat) (U : Set X) (n : ℕ) :
    (mvOrdinaryComplex X U).homology n ≅ H U n :=
  singularHomologyRepresentation (TopCat.of U) n

theorem singularFinsuppMap_pairInclusion (X : TopCat) (U : Set X) :
    singularFinsuppMap (pairInclusion X U) = mvAmbientPush X U := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [singularFinsuppMap_f]
  rfl

theorem ordinarySingularRepresentation_inclusion (X : TopCat) (U : Set X) :
    mvAmbientPush X U ≫ (singularRepresentation X).hom =
      (ordinarySingularRepresentation X U).hom ≫
        actualSingularFunctor.map (pairInclusion X U) := by
  rw [← singularFinsuppMap_pairInclusion]
  exact singularRepresentation_naturality (pairInclusion X U)

theorem ordinaryHomologyRepresentation_inclusion (X : TopCat) (U : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (mvAmbientPush X U) n ≫
      (singularHomologyRepresentation X n).hom =
    (ordinaryHomologyRepresentation X U n).hom ≫ homologyInclusion X U n := by
  rw [← singularFinsuppMap_pairInclusion]
  exact singularHomologyRepresentation_naturality (pairInclusion X U) n

def singularSubsetInclusion (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun a => ⟨a.1, h a.2⟩, continuous_subtype_val.subtype_mk _⟩

noncomputable def actualSubsetHomologyMap (X : TopCat) (A B : Set X) (h : A ⊆ B) (n : ℕ) :
    H A n ⟶ H B n :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).map (singularSubsetInclusion X A B h)

theorem singularFinsuppMap_subset (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    singularFinsuppMap (singularSubsetInclusion X A B h) = mvSubsetMap X A B h := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [singularFinsuppMap_f]
  rfl

theorem ordinaryHomologyRepresentation_subset (X : TopCat) (A B : Set X) (h : A ⊆ B) (n : ℕ) :
    HomologicalComplex.homologyMap (mvSubsetMap X A B h) n ≫
      (ordinaryHomologyRepresentation X B n).hom =
    (ordinaryHomologyRepresentation X A n).hom ≫ actualSubsetHomologyMap X A B h n := by
  rw [← singularFinsuppMap_subset]
  exact singularHomologyRepresentation_naturality (singularSubsetInclusion X A B h) n

/-- Open-cover small homology maps directly to the project's named H functor. -/
noncomputable def actualOpenCoverHomologyIso (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (mvSmallComplex X U V).homology n ≅ H X n :=
  mvOpenCoverHomologyIso X U V hU hV hcover n ≪≫ singularHomologyRepresentation X n

noncomputable def actualPairHomologyIso (X : TopCat) (U V : Set X) (n : ℕ) :
    (mvPairComplex X U V).homology n ≅ ModuleCat.of ℤ (H U n × H V n) :=
  ((mvPairHomologyEquiv X U V n).toAddEquiv.trans
    ((ordinaryHomologyRepresentation X U n).toLinearEquiv.toAddEquiv.prodCongr
      (ordinaryHomologyRepresentation X V n).toLinearEquiv.toAddEquiv)).toIntLinearEquiv.toModuleIso

noncomputable def actualMVDifference (X : TopCat) (U V : Set X) (n : ℕ) :
    H ↥(U ∩ V) n ⟶ ModuleCat.of ℤ (H U n × H V n) :=
  (ordinaryHomologyRepresentation X (U ∩ V) n).inv ≫
    mvHomologyDifference X U V n ≫ (actualPairHomologyIso X U V n).hom

noncomputable def actualMVSum (X : TopCat) (U V : Set X) (n : ℕ) :
    ModuleCat.of ℤ (H U n × H V n) ⟶ H X n :=
  (actualPairHomologyIso X U V n).inv ≫ mvAmbientHomologySum X U V n ≫
    (singularHomologyRepresentation X n).hom

noncomputable def actualMVConnecting (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    H X (n + 1) ⟶ H ↥(U ∩ V) n :=
  (singularHomologyRepresentation X (n + 1)).inv ≫
    mvAmbientConnecting X U V hU hV hcover n ≫
      (ordinaryHomologyRepresentation X (U ∩ V) n).hom

theorem actualMVDifference_sum (X : TopCat) (U V : Set X) (n : ℕ) :
    actualMVDifference X U V n ≫ actualMVSum X U V n = 0 := by
  simp [actualMVDifference, actualMVSum, Category.assoc,
    ← Category.assoc (mvHomologyDifference X U V n), mvHomologyDifference_ambientSum]

theorem actualMVConnecting_difference (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    actualMVConnecting X U V hU hV hcover n ≫ actualMVDifference X U V n = 0 := by
  simp [actualMVConnecting, actualMVDifference, Category.assoc,
    ← Category.assoc (mvAmbientConnecting X U V hU hV hcover n), mvAmbientConnecting_difference]

theorem actualMVSum_connecting (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    actualMVSum X U V (n + 1) ≫ actualMVConnecting X U V hU hV hcover n = 0 := by
  simp [actualMVSum, actualMVConnecting, Category.assoc,
    ← Category.assoc (mvAmbientHomologySum X U V (n + 1)), mvAmbientSum_connecting]

theorem actualMV_exact_intersection (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (ShortComplex.mk (actualMVConnecting X U V hU hV hcover n) (actualMVDifference X U V n)
      (actualMVConnecting_difference X U V hU hV hcover n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mvAmbient_exact_intersection X U V hU hV hcover n)
  refine ShortComplex.isoMk (singularHomologyRepresentation X (n + 1))
    (ordinaryHomologyRepresentation X (U ∩ V) n) (actualPairHomologyIso X U V n) ?_ ?_
  · simp [actualMVConnecting]
  · simp [actualMVDifference]

theorem actualMV_exact_pair (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (ShortComplex.mk (actualMVDifference X U V n) (actualMVSum X U V n)
      (actualMVDifference_sum X U V n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mvAmbient_exact_pair X U V hU hV hcover n)
  refine ShortComplex.isoMk (ordinaryHomologyRepresentation X (U ∩ V) n)
    (actualPairHomologyIso X U V n) (singularHomologyRepresentation X n) ?_ ?_
  · simp [actualMVDifference]
  · simp [actualMVSum]

theorem actualMV_exact_ambient (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (ShortComplex.mk (actualMVSum X U V (n + 1)) (actualMVConnecting X U V hU hV hcover n)
      (actualMVSum_connecting X U V hU hV hcover n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mvAmbient_exact_ambient X U V hU hV hcover n)
  refine ShortComplex.isoMk (actualPairHomologyIso X U V (n + 1))
    (singularHomologyRepresentation X (n + 1)) (ordinaryHomologyRepresentation X (U ∩ V) n) ?_ ?_
  · simp [actualMVSum]
  · simp [actualMVConnecting]

theorem actualMVSum_zero_epi (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    Epi (actualMVSum X U V 0) := by
  letI := mvAmbientHomologySum_zero_epi X U V hU hV hcover
  dsimp only [actualMVSum]
  infer_instance



theorem actualPairHomologyIso_hom_apply (X : TopCat) (U V : Set X) (n : ℕ)
    (q : (mvPairComplex X U V).homology n) :
    (actualPairHomologyIso X U V n).hom q =
      ((ordinaryHomologyRepresentation X U n).hom
        (HomologicalComplex.homologyMap (mvPairFst X U V) n q),
      (ordinaryHomologyRepresentation X V n).hom
        (HomologicalComplex.homologyMap (mvPairSnd X U V) n q)) := rfl

theorem actualPairHomologyIso_inv_apply (X : TopCat) (U V : Set X) (n : ℕ)
    (q : H U n × H V n) :
    (actualPairHomologyIso X U V n).inv q =
      HomologicalComplex.homologyMap (mvPairInl X U V) n
        ((ordinaryHomologyRepresentation X U n).inv q.1) +
      HomologicalComplex.homologyMap (mvPairInr X U V) n
        ((ordinaryHomologyRepresentation X V n).inv q.2) := rfl

/-- The H-valued first map is exactly the signed pair of actual subset inclusions. -/
theorem actualMVDifference_apply (X : TopCat) (U V : Set X) (n : ℕ)
    (q : H ↥(U ∩ V) n) :
    actualMVDifference X U V n q =
      (actualSubsetHomologyMap X (U ∩ V) U Set.inter_subset_left n q,
        -actualSubsetHomologyMap X (U ∩ V) V Set.inter_subset_right n q) := by
  let z := (ordinaryHomologyRepresentation X (U ∩ V) n).inv q
  change (actualPairHomologyIso X U V n).hom (mvHomologyDifference X U V n z) = _
  rw [actualPairHomologyIso_hom_apply]
  apply Prod.ext
  · have h := congrArg (fun f => f z) (mvHomologyDifference_fst X U V n)
    change HomologicalComplex.homologyMap (mvPairFst X U V) n
      (mvHomologyDifference X U V n z) = _ at h
    rw [h]
    have hn := congrArg (fun f => f z)
      (ordinaryHomologyRepresentation_subset X (U ∩ V) U Set.inter_subset_left n)
    change (ordinaryHomologyRepresentation X U n).hom
      (HomologicalComplex.homologyMap (mvSubsetMap X (U ∩ V) U Set.inter_subset_left) n z) =
      actualSubsetHomologyMap X (U ∩ V) U Set.inter_subset_left n
        ((ordinaryHomologyRepresentation X (U ∩ V) n).hom z) at hn
    simpa only [z, Iso.inv_hom_id_apply] using hn
  · have h := congrArg (fun f => f z) (mvHomologyDifference_snd X U V n)
    change HomologicalComplex.homologyMap (mvPairSnd X U V) n
      (mvHomologyDifference X U V n z) =
      -HomologicalComplex.homologyMap (mvSubsetMap X (U ∩ V) V Set.inter_subset_right) n z at h
    rw [h, map_neg]
    have hn := congrArg (fun f => f z)
      (ordinaryHomologyRepresentation_subset X (U ∩ V) V Set.inter_subset_right n)
    change (ordinaryHomologyRepresentation X V n).hom
      (HomologicalComplex.homologyMap (mvSubsetMap X (U ∩ V) V Set.inter_subset_right) n z) =
      actualSubsetHomologyMap X (U ∩ V) V Set.inter_subset_right n
        ((ordinaryHomologyRepresentation X (U ∩ V) n).hom z) at hn
    simpa only [z, Iso.inv_hom_id_apply] using congrArg Neg.neg hn

/-- The H-valued second map is exactly the sum of the two actual cover inclusions. -/
theorem actualMVSum_apply (X : TopCat) (U V : Set X) (n : ℕ)
    (q : H U n × H V n) :
    actualMVSum X U V n q = homologyInclusion X U n q.1 + homologyInclusion X V n q.2 := by
  change (singularHomologyRepresentation X n).hom
    (mvAmbientHomologySum X U V n ((actualPairHomologyIso X U V n).inv q)) = _
  rw [actualPairHomologyIso_inv_apply, map_add, map_add]
  congr 1
  · let z := (ordinaryHomologyRepresentation X U n).inv q.1
    have h := congrArg (fun f => f z) (mvHomologyInl_sum_inclusion X U V n)
    change mvAmbientHomologySum X U V n
      (HomologicalComplex.homologyMap (mvPairInl X U V) n z) =
      HomologicalComplex.homologyMap (mvAmbientPush X U) n z at h
    rw [h]
    have hn := congrArg (fun f => f z) (ordinaryHomologyRepresentation_inclusion X U n)
    change (singularHomologyRepresentation X n).hom
      (HomologicalComplex.homologyMap (mvAmbientPush X U) n z) =
      homologyInclusion X U n ((ordinaryHomologyRepresentation X U n).hom z) at hn
    simpa only [z, Iso.inv_hom_id_apply] using hn
  · let z := (ordinaryHomologyRepresentation X V n).inv q.2
    have h := congrArg (fun f => f z) (mvHomologyInr_sum_inclusion X U V n)
    change mvAmbientHomologySum X U V n
      (HomologicalComplex.homologyMap (mvPairInr X U V) n z) =
      HomologicalComplex.homologyMap (mvAmbientPush X V) n z at h
    rw [h]
    have hn := congrArg (fun f => f z) (ordinaryHomologyRepresentation_inclusion X V n)
    change (singularHomologyRepresentation X n).hom
      (HomologicalComplex.homologyMap (mvAmbientPush X V) n z) =
      homologyInclusion X V n ((ordinaryHomologyRepresentation X V n).hom z) at hn
    simpa only [z, Iso.inv_hom_id_apply] using hn

end CurveComplexGenusTwo.CWHurewicz
