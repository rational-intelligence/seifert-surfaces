import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHZero
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.Algebra.Category.ModuleCat.Products

noncomputable section
open CategoryTheory CategoryTheory.Limits CircleHomologyComputation
open CurveComplexGenusTwo.CWHurewicz

namespace CurveComplex.Octagon.AttachingMap.GraphMV

set_option backward.isDefEq.respectTransparency false

def finiteDiscreteH0Iso (D : Type) [Fintype D] [TopologicalSpace D]
    [DiscreteTopology D] : H D 0 ≅ ModuleCat.of ℤ (D → ℤ) := by
  classical
  exact (TopCat.of D).singularHomology₀Iso RZ ≪≫
    (sigmaConst.obj RZ).mapIso (discreteComponentsEquiv D).toIso ≪≫
      ModuleCat.coprodIsoDirectSum (fun _ : D => RZ) ≪≫
        ((finsuppLEquivDirectSum ℤ ℤ D).symm.trans
          (Finsupp.linearEquivFunOnFinite ℤ ℤ D)).toModuleIso

theorem finiteDiscreteH0Iso_point (D : Type) [Fintype D] [TopologicalSpace D]
    [DiscreteTopology D] [DecidableEq D] (p : D) :
    (finiteDiscreteH0Iso D).hom
      (pointClass (TopCat.toSSet.obj (TopCat.of D))
        (TopCat.toSSetObj₀Equiv.symm p) (1 : ℤ)) =
      Pi.single p (1 : ℤ) := by
  classical
  have hp : pointClass (TopCat.toSSet.obj (TopCat.of D))
      (TopCat.toSSetObj₀Equiv.symm p) ≫
      ((TopCat.of D).singularHomology₀Iso RZ).hom =
        Sigma.ι (fun _ : ZerothHomotopy D => RZ) (ZerothHomotopy.mk p) := by
    simp only [TopCat.singularHomology₀Iso, Iso.trans_hom, ← Category.assoc,
      pointClass_iso]
    simp
    congr 1
  have hcoord : pointClass (TopCat.toSSet.obj (TopCat.of D))
      (TopCat.toSSetObj₀Equiv.symm p) ≫ (finiteDiscreteH0Iso D).hom =
      ModuleCat.ofHom (LinearMap.single ℤ (fun _ : D => ℤ) p) := by
    dsimp only [finiteDiscreteH0Iso, Iso.trans_hom]
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hp]
    simp only [discreteComponentsEquiv, Functor.mapIso_hom]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext i
    by_cases h : i = p
    · subst i
      simp
    · simp [h]
  exact congrArg (fun f : RZ ⟶ ModuleCat.of ℤ (D → ℤ) => f (1 : ℤ)) hcoord

end CurveComplex.Octagon.AttachingMap.GraphMV
