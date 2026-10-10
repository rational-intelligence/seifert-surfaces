import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHelpers

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
open scoped Simplicial
namespace CircleHomologyComputation
abbrev RZ := ModuleCat.of ℤ ℤ
abbrev HF0 := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj RZ

def pointClass (X : SSet) (x : X _⦋0⦌) : RZ ⟶ X.homology RZ 0 :=
  (X.chainComplex RZ).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
    (X.chainComplex RZ).homologyπ 0

lemma pointClass_iso (X : SSet) (x : X _⦋0⦌) :
    pointClass X x ≫ (X.homology₀Iso RZ).hom =
      Sigma.ι (fun _ : X.π₀ => RZ) (SSet.π₀.mk x) := by
  simp [pointClass]

lemma hzero_ext {X : SSet} {M : ModuleCat ℤ} {f g : X.homology RZ 0 ⟶ M}
    (h : ∀ x, pointClass X x ≫ f = pointClass X x ≫ g) : f = g := by
  apply (cancel_epi (X.homology₀Iso RZ).inv).mp
  apply Sigma.hom_ext
  intro i
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective i
  rw [← pointClass_iso X x]
  simpa using h x

lemma pointClass_map {X Y : SSet} (f : X ⟶ Y) (x : X _⦋0⦌) :
    pointClass X x ≫ HomologicalComplex.homologyMap (SSet.chainComplexMap f RZ) 0 =
      pointClass Y (f.app _ x) := by
  simp [pointClass]

lemma augmentation_naturality {X Y : TopCat} (f : X ⟶ Y) :
    HF0.map f ≫ Y.singularHomology₀ε RZ = X.singularHomology₀ε RZ := by
  apply hzero_ext
  intro x
  change pointClass (TopCat.toSSet.obj X) x ≫
    (HomologicalComplex.homologyMap (SSet.chainComplexMap (TopCat.toSSet.map f) RZ) 0 ≫
      (TopCat.toSSet.obj Y).homology₀ε RZ) = _
  rw [← Category.assoc, pointClass_map]
  simp [pointClass, TopCat.singularHomology₀ε]

def discreteComponentsEquiv (D : Type) [TopologicalSpace D] [DiscreteTopology D] :
    ZerothHomotopy D ≃ D where
  toFun := ZerothHomotopy.lift id (fun _ _ p => by
    have h := (IsLocallyConstant.iff_continuous p).mpr p.continuous
    simpa using h.apply_eq_of_preconnectedSpace 0 1)
  invFun := ZerothHomotopy.mk
  left_inv c := by induction c; rfl
  right_inv _ := rfl

abbrev Two := Unit ⊕ Unit

def twoCoproductIso : (∐ fun _ : Two => RZ) ≅ ModuleCat.of ℤ (ℤ × ℤ) where
  hom := Sigma.desc (fun i => match i with
    | .inl _ => ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ)
    | .inr _ => ModuleCat.ofHom (LinearMap.inr ℤ ℤ ℤ))
  inv := ModuleCat.ofHom ((Sigma.ι (fun _ : Two => RZ) (.inl ())).hom.coprod
    (Sigma.ι (fun _ : Two => RZ) (.inr ())).hom)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    cases i <;> ext z <;> simp
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨a,b⟩
    simp

def coordinateSum : ModuleCat.of ℤ (ℤ × ℤ) ⟶ RZ :=
  ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ + LinearMap.snd ℤ ℤ ℤ)

lemma twoCoproductIso_sum :
    twoCoproductIso.hom ≫ coordinateSum = Sigma.desc (fun _ : Two => 𝟙 RZ) := by
  apply Sigma.hom_ext
  intro i
  cases i <;> simp [twoCoproductIso, coordinateSum] <;> ext z <;> simp

def twoHomologyIso : H Two 0 ≅ ModuleCat.of ℤ (ℤ × ℤ) :=
  (TopCat.of Two).singularHomology₀Iso RZ ≪≫
    (sigmaConst.obj RZ).mapIso (discreteComponentsEquiv Two).toIso ≪≫
      twoCoproductIso

lemma twoHomologyIso_sum :
    twoHomologyIso.hom ≫ coordinateSum = (TopCat.of Two).singularHomology₀ε RZ := by
  dsimp only [twoHomologyIso, Iso.trans_hom]
  rw [Category.assoc, Category.assoc, twoCoproductIso_sum]
  have h : ((sigmaConst.obj RZ).mapIso (discreteComponentsEquiv Two).toIso).hom ≫
      Sigma.desc (fun _ : Two => 𝟙 RZ) =
        Sigma.desc (fun _ : ZerothHomotopy Two => 𝟙 RZ) := by
    apply Sigma.hom_ext
    intro i
    simp
  rw [h, TopCat.singularHomology₀Iso_sigma_desc_id]

def overlapCoordinatesIso :
    H ↥(CircleCoverGeometry.eastArc ∩ CircleCoverGeometry.westArc) 0 ≅
      ModuleCat.of ℤ (ℤ × ℤ) :=
  homotopyHomologyIso overlapHomotopyEquiv 0 ≪≫ twoHomologyIso

lemma overlapCoordinatesIso_sum :
    overlapCoordinatesIso.hom ≫ coordinateSum =
      (TopCat.of ↥(CircleCoverGeometry.eastArc ∩ CircleCoverGeometry.westArc)).singularHomology₀ε RZ := by
  rw [overlapCoordinatesIso, Iso.trans_hom, Category.assoc, twoHomologyIso_sum]
  exact augmentation_naturality (TopCat.ofHom overlapHomotopyEquiv.toFun)

end CircleHomologyComputation
