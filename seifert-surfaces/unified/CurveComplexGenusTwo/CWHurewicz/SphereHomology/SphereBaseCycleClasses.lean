import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseStatements

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz CircleHomologyComputation
open scoped Simplicial
namespace CircleFundamentalCycle

abbrev scalar (M : ModuleCat.{0} ℤ) (x : M) : ModuleCat.of ℤ ℤ ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M x)

lemma scalar_naturality {M N : ModuleCat.{0} ℤ} (f : M ⟶ N) (x : M) :
    scalar M x ≫ f = scalar N (f x) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact f.hom.map_smul r x

lemma scalar_eq_zero {M : ModuleCat.{0} ℤ} : scalar M 0 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact smul_zero r

def cycleClass (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (z : K.X n)
    (hz : K.d n (n-1) z = 0) : K.homology n :=
  (K.liftCycles (scalar _ z) (n-1) (by cases n <;> simp) (by
    rw [scalar_naturality, hz, scalar_eq_zero]) ≫ K.homologyπ n) 1

lemma cycleClass_map {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ L)
    (n : ℕ) (z : K.X n) (hz : K.d n (n-1) z = 0)
    (hw : L.d n (n-1) (f.f n z) = 0) :
    HomologicalComplex.homologyMap f n (cycleClass K n z hz) =
      cycleClass L n (f.f n z) hw := by
  have h : (K.liftCycles (scalar _ z) (n-1) (by cases n <;> simp) (by
      rw [scalar_naturality,hz,scalar_eq_zero]) ≫ K.homologyπ n) ≫
      HomologicalComplex.homologyMap f n =
        L.liftCycles (scalar _ (f.f n z)) (n-1) (by cases n <;> simp) (by
          rw [scalar_naturality,hw,scalar_eq_zero]) ≫ L.homologyπ n := by
    simp [scalar_naturality]
  exact congrArg (fun m => m (1:ℤ)) h

lemma cycleClass_zero_degree_add (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (a b : K.X 0) :
    cycleClass K 0 (a+b) (by simp) =
      cycleClass K 0 a (by simp) + cycleClass K 0 b (by simp) := by
  let f : K.X 0 ⟶ K.homology 0 := (ChainComplex.cycles₀Iso K).inv ≫ K.homologyπ 0
  have h (z : K.X 0) : cycleClass K 0 z (by simp) = f z := by
    dsimp only [cycleClass, f]
    have he : K.liftCycles (scalar _ z) (0-1) (by simp) (by simp) =
        scalar _ z ≫ (ChainComplex.cycles₀Iso K).inv := by
      apply (cancel_mono (K.iCycles 0)).mp
      simp
    rw [he]
    change (K.homologyπ 0) ((ChainComplex.cycles₀Iso K).inv
      ((LinearMap.toSpanSingleton ℤ (K.X 0) z) 1)) = _
    rw [LinearMap.toSpanSingleton_apply_one]
    rfl
  rw [h,h,h]
  exact f.hom.map_add a b


def zeroClassMap (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) : K.X 0 ⟶ K.homology 0 :=
  (ChainComplex.cycles₀Iso K).inv ≫ K.homologyπ 0

lemma zeroClassMap_apply (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (z : K.X 0) :
    zeroClassMap K z = cycleClass K 0 z (by simp) := by
  have he : K.liftCycles (scalar _ z) 0 (by simp) (by simp) =
      scalar _ z ≫ (ChainComplex.cycles₀Iso K).inv := by
    apply (cancel_mono (K.iCycles 0)).mp
    simp
  dsimp only [cycleClass]
  rw [he]
  change _ = (K.homologyπ 0) ((ChainComplex.cycles₀Iso K).inv
    ((LinearMap.toSpanSingleton ℤ (K.X 0) z) 1))
  rw [LinearMap.toSpanSingleton_apply_one]
  rfl

lemma zeroClassMap_naturality {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ L) :
    f.f 0 ≫ zeroClassMap L = zeroClassMap K ≫ HomologicalComplex.homologyMap f 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact (zeroClassMap_apply L _).trans
    ((cycleClass_map f 0 z (by simp) (by simp)).symm.trans
      (congrArg _ (zeroClassMap_apply K z).symm))

lemma pointClass_zeroClassMap (T : TopCat) (p : (TopCat.toSSet.obj T) _⦋0⦌) :
    (TopCat.toSSet.obj T).ιChainComplex p ≫ zeroClassMap (singularChains T) =
      pointClass (TopCat.toSSet.obj T) p := by
  change (TopCat.toSSet.obj T).ιChainComplex p ≫
    zeroClassMap ((TopCat.toSSet.obj T).chainComplex RZ) = _
  unfold pointClass zeroClassMap
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono (((TopCat.toSSet.obj T).chainComplex RZ).iCycles 0)).mp
  simp

lemma singular_point_class (T : TopCat) (p : (TopCat.toSSet.obj T) _⦋0⦌) :
    (singularHomologyRepresentation T 0).hom
      (zeroClassMap (mvAmbientComplex T) (Finsupp.single p 1)) =
        pointClass (TopCat.toSSet.obj T) p (1:ℤ) := by
  have h := congrArg (fun f => f (Finsupp.single p 1))
    (zeroClassMap_naturality (singularRepresentation T).hom)
  change (zeroClassMap (singularChains T))
    ((singularChainsFinsuppIso T 0).inv (Finsupp.single p 1)) = _ at h
  have hg : (singularChainsFinsuppIso T 0).inv (Finsupp.single p 1) =
      ((TopCat.toSSet.obj T).ιChainComplex (R := RZ) p).hom 1 := by
    rw [← singularChainsFinsuppIso_generator T 0 p]
    exact (singularChainsFinsuppIso T 0).hom_inv_id_apply _
  rw [hg] at h
  exact h.symm.trans (congrArg (fun f => f (1:ℤ)) (pointClass_zeroClassMap T p))

lemma two_pointClass (p : Two) :
    pointClass (TopCat.toSSet.obj (TopCat.of Two)) (TopCat.toSSetObj₀Equiv.symm p) ≫
      twoHomologyIso.hom =
        (match p with
          | .inl _ => ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ)
          | .inr _ => ModuleCat.ofHom (LinearMap.inr ℤ ℤ ℤ)) := by
  have hp : pointClass (TopCat.toSSet.obj (TopCat.of Two)) (TopCat.toSSetObj₀Equiv.symm p) ≫
      ((TopCat.of Two).singularHomology₀Iso RZ).hom =
        Sigma.ι (fun _ : ZerothHomotopy Two => RZ) (ZerothHomotopy.mk p) := by
    dsimp only [TopCat.singularHomology₀Iso, Iso.trans_hom]
    rw [← Category.assoc, pointClass_iso]
    simp
    congr 1
  dsimp only [twoHomologyIso, Iso.trans_hom]
  rw [← Category.assoc, ← Category.assoc, hp]
  cases p <;> simp [twoCoproductIso,discreteComponentsEquiv]


end CircleFundamentalCycle
