import CurveComplexGenusTwo.CWHurewicz.CWBasic
import CurveComplexGenusTwo.Topology.CircleCoverGeometry

noncomputable section
open CategoryTheory CategoryTheory.Limits ContinuousMap
open CurveComplexGenusTwo.CWHurewicz
namespace CircleHomologyComputation

private abbrev HF' (n : ℕ) :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)

def homotopyHomologyIso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (n : ℕ) : H X n ≅ H Y n where
  hom := (HF' n).map (TopCat.ofHom e.toFun)
  inv := (HF' n).map (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← Functor.map_comp]
    have h := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (f := TopCat.ofHom (e.invFun.comp e.toFun))
      (g := 𝟙 (TopCat.of X)) e.left_inv.some
      (ModuleCat.of ℤ ℤ) n
    exact h.trans ((HF' n).map_id _)
  inv_hom_id := by
    rw [← Functor.map_comp]
    have h := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (f := TopCat.ofHom (e.toFun.comp e.invFun))
      (g := 𝟙 (TopCat.of Y)) e.right_inv.some
      (ModuleCat.of ℤ ℤ) n
    exact h.trans ((HF' n).map_id _)

def sumHomotopy {X Y A B : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B]
    {f g : C(X,A)} {f' g' : C(Y,B)} (h : f.Homotopy g) (h' : f'.Homotopy g') :
    ContinuousMap.Homotopy
      ⟨Sum.map f f', f.continuous.sumMap f'.continuous⟩
      ⟨Sum.map g g', g.continuous.sumMap g'.continuous⟩ where
  toFun p := Sum.elim (fun x => Sum.inl (h (p.1,x)))
    (fun y => Sum.inr (h' (p.1,y))) p.2
  continuous_toFun := by
    convert ((continuous_inl.comp h.continuous).sumElim
      (continuous_inr.comp h'.continuous)).comp
        (Homeomorph.prodSumDistrib.continuous) using 1
    funext p
    rcases p with ⟨t, x | y⟩ <;> rfl
  map_zero_left x := by cases x <;> simp
  map_one_left x := by cases x <;> simp

def sumHomotopyEquiv {X Y A B : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] (e : X ≃ₕ A) (f : Y ≃ₕ B) :
    (X ⊕ Y) ≃ₕ (A ⊕ B) where
  toFun := ⟨Sum.map e f, e.continuous.sumMap f.continuous⟩
  invFun := ⟨Sum.map e.symm f.symm, e.symm.continuous.sumMap f.symm.continuous⟩
  left_inv := by
    refine ⟨?_⟩
    convert sumHomotopy e.left_inv.some f.left_inv.some using 1 <;>
      ext x <;> cases x <;> rfl
  right_inv := by
    refine ⟨?_⟩
    convert sumHomotopy e.right_inv.some f.right_inv.some using 1 <;>
      ext x <;> cases x <;> rfl

def overlapHomotopyEquiv :
    ↥(CircleCoverGeometry.eastArc ∩ CircleCoverGeometry.westArc) ≃ₕ (Unit ⊕ Unit) := by
  letI := CircleCoverGeometry.upperArc_contractible
  letI := CircleCoverGeometry.lowerArc_contractible
  exact CircleCoverGeometry.intersectionHomeomorph.toHomotopyEquiv.trans
    (sumHomotopyEquiv (ContractibleSpace.hequiv_unit _).some
      (ContractibleSpace.hequiv_unit _).some)

end CircleHomologyComputation
