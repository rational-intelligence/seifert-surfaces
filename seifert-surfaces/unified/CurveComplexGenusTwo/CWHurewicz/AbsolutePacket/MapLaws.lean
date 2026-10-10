import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereProbe
import CurveComplexGenusTwo.CWHurewicz.PublicExport.FiniteAvoidancePair

noncomputable section
open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval
namespace CurveComplexGenusTwo.CWHurewicz.AbsolutePacket

abbrev HF (n : ℕ) :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)

/-- Public specification of the already constructed continuous quotient map. -/
theorem sphereMap_mk {X : Type} [TopologicalSpace X]
    (n : ℕ) (x : X) (f : GenLoop (Fin n) X x) (a : Fin n → I) :
    loopSphereMap n x f (Quotient.mk (cubeBoundarySetoid n) a) = f a := by
  rfl

/-- Descent of a relative-boundary cube homotopy to the quotient sphere. -/
theorem sphereMap_homotopic {X : Type} [TopologicalSpace X]
    (n : ℕ) (x : X) (f g : GenLoop (Fin n) X x)
    (h : GenLoop.Homotopic f g) :
    Nonempty (TopCat.Homotopy (TopCat.ofHom (loopSphereMap n x f))
      (TopCat.ofHom (loopSphereMap n x g))) := by
  rcases h with ⟨K⟩
  let q : (Fin n → I) → CubeSphere n := Quotient.mk (cubeBoundarySetoid n)
  have hq : IsQuotientMap q := ⟨⟨rfl⟩, Quotient.mk_surjective⟩
  let L : I × CubeSphere n → X := fun p =>
    Quotient.lift (fun a => K (p.1, a)) (by
      intro a b hab
      rcases hab with hab | ⟨ha, hb⟩
      · exact congrArg (fun a => K (p.1, a)) hab
      · exact (K.eq_fst p.1 ha).trans
          ((GenLoop.boundary f a ha).trans (GenLoop.boundary f b hb).symm) |>.trans
          (K.eq_fst p.1 hb).symm) p.2
  have hL : Continuous L := by
    apply hq.continuous_lift_prod_right
    exact K.continuous
  refine ⟨{
    toContinuousMap := ⟨L, hL⟩
    map_zero_left := by
      intro z
      induction z using Quotient.inductionOn with
      | _ a => exact K.apply_zero a
    map_one_left := by
      intro z
      induction z using Quotient.inductionOn with
      | _ a => exact K.apply_one a }⟩

/-- Fixed orientation from the public integral sphere homology calculation. -/
def fundamentalClass (k : ℕ) : H (CubeSphere (k + 2)) (k + 2) :=
  (SphereProbe.cubeSphereTopIso (k + 2) (Nat.zero_lt_succ _)).inv 1

def value {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
    (f : GenLoop (Fin (k + 2)) X x) : H X (k + 2) :=
  ((HF (k + 2)).map (TopCat.ofHom (loopSphereMap (k + 2) x f)))
    (fundamentalClass k)

theorem value_homotopic {X : Type} [TopologicalSpace X]
    (k : ℕ) (x : X) (f g : GenLoop (Fin (k + 2)) X x)
    (h : GenLoop.Homotopic f g) : value k x f = value k x g := by
  obtain ⟨K⟩ := sphereMap_homotopic (k + 2) x f g h
  have heq := K.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) (k + 2)
  change (HF (k + 2)).map (TopCat.ofHom (loopSphereMap (k + 2) x f)) =
    (HF (k + 2)).map (TopCat.ofHom (loopSphereMap (k + 2) x g)) at heq
  exact congrArg (fun m => m (fundamentalClass k)) heq

def hurewiczFunction {X : Type} [TopologicalSpace X] (k : ℕ) (x : X) :
    HomotopyGroup.Pi (k + 2) X x → H X (k + 2) :=
  Quotient.lift (value k x) (fun f g h => value_homotopic k x f g h)

/-- Separate zero law; no homomorphism is assumed. -/
theorem value_const {X : Type} [TopologicalSpace X] (k : ℕ) (x : X) :
    value k x (GenLoop.const : GenLoop (Fin (k + 2)) X x) = 0 := by
  let n := k + 2
  have hn : 1 ≤ n := by dsimp [n]; omega
  let b := x
  let u := fundamentalClass k
  have hc : loopSphereMap n x (GenLoop.const : GenLoop (Fin n) X x) =
      ContinuousMap.const (CubeSphere n) b := by
    ext z
    induction z using Quotient.inductionOn with
    | _ a => rfl
  unfold value
  rw [hc]

  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)
  let q : TopCat.of (CubeSphere n) ⟶ TopCat.of PUnit :=
    TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let p : TopCat.of PUnit ⟶ TopCat.of X :=
    TopCat.ofHom ⟨fun _ => b, continuous_const⟩
  have hf : TopCat.ofHom (ContinuousMap.const (CubeSphere n) b) = q ≫ p := by
    ext a
    rfl
  have hzero : IsZero (H PUnit n) := by
    exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of PUnit) (by omega)
  haveI : Subsingleton (H PUnit n) := homology_subsingleton_of_isZero n hzero
  have hz : (F.map q) u = 0 := Subsingleton.elim _ _
  change (F.map (TopCat.ofHom (ContinuousMap.const (CubeSphere n) b))) u = 0
  rw [hf, F.map_comp]
  change (F.map p) ((F.map q) u) = 0
  rw [hz]
  simp

/-- Separate geometric pinch/additivity obligation for the actual cube concatenation. -/
theorem value_transAt {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
    (f g : GenLoop (Fin (k + 2)) X x) (i : Fin (k + 2)) :
    value k x (GenLoop.transAt i f g) = value k x f + value k x g := by
  exact loopSphereMap_transAt_homology (k + 2) (by omega) x f g i (fundamentalClass k)

theorem function_one {X : Type} [TopologicalSpace X] (k : ℕ) (x : X) :
    hurewiczFunction k x 1 = 0 := by
  rw [HomotopyGroup.one_def]
  exact value_const k x

theorem function_mul {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
    (a b : HomotopyGroup.Pi (k + 2) X x) :
    hurewiczFunction k x (a * b) = hurewiczFunction k x a + hurewiczFunction k x b :=
  by
  induction a using Quotient.inductionOn with
  | _ f =>
    induction b using Quotient.inductionOn with
    | _ g =>
      have hm := HomotopyGroup.mul_spec (N := Fin (k + 2)) (i := (0 : Fin (k + 2))) (p := f) (q := g)
      exact (congrArg (hurewiczFunction k x) hm).trans (by
        change value k x (GenLoop.transAt 0 g f) = value k x f + value k x g
        exact (value_transAt k x g f 0).trans (add_comm _ _))

/-- Bundling is downstream of the explicit laws, rather than a hypothesis. -/
def hurewiczMap {X : Type} [TopologicalSpace X] (k : ℕ) (x : X) :
    HomotopyGroup.Pi (k + 2) X x →* Multiplicative (H X (k + 2)) where
  toFun a := Multiplicative.ofAdd (hurewiczFunction k x a)
  map_one' := function_one k x
  map_mul' := function_mul k x


end CurveComplexGenusTwo.CWHurewicz.AbsolutePacket
