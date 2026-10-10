import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
universe v u w
namespace CurveComplexGenusTwo.CWHurewicz
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [CategoryWithHomology C]
  {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- Homotopy inverse continuous maps induce inverse singular homology maps. -/
noncomputable def singularHomologyIsoOfHomotopyInverse (R : C) (n : ℕ)
    (f : C(X, Y)) (g : C(Y, X))
    (hX : ContinuousMap.Homotopic (g.comp f) (ContinuousMap.id X))
    (hY : ContinuousMap.Homotopic (f.comp g) (ContinuousMap.id Y)) :
    ((singularHomologyFunctor C n).obj R).obj (TopCat.of X) ≅
      ((singularHomologyFunctor C n).obj R).obj (TopCat.of Y) := by
  let F := (singularHomologyFunctor C n).obj R
  refine ⟨F.map (TopCat.ofHom f), F.map (TopCat.ofHom g), ?_, ?_⟩
  · rw [← F.map_comp, ← F.map_id]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor hX.some R n
  · rw [← F.map_comp, ← F.map_id]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor hY.some R n

/-- A deformation retraction induces an isomorphism in every homology degree. -/
theorem singularHomologyMap_isIso_of_retraction (R : C) (n : ℕ)
    (r : C(X, Y)) (i : C(Y, X))
    (hri : r.comp i = ContinuousMap.id Y)
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) (i.comp r)) :
    IsIso (((singularHomologyFunctor C n).obj R).map (TopCat.ofHom r)) := by
  let e := singularHomologyIsoOfHomotopyInverse R n r i
    ⟨H.symm⟩ (hri ▸ ⟨ContinuousMap.Homotopy.refl _⟩)
  exact e.isIso_hom
end CurveComplexGenusTwo.CWHurewicz
