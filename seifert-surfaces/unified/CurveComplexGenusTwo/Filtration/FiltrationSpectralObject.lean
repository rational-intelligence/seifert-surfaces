import CurveComplexGenusTwo.Filtration.GenericFiltrationQuotient
import Mathlib.Algebra.Homology.SpectralObject.Basic
import CurveComplexGenusTwo.Filtration.FiltrationTripleSequence

namespace CurveGenusTwo.Filtration

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
open ComposableArrows

universe u v

variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

/- The fully functorial arrow-indexed object is assembled over the preorder of
natural filtration indices.  The quotient complex and all square maps are
provided by `GenericFiltrationQuotient`. -/

noncomputable def filtrationQuotientObj
    (K : FiniteComplex V) (a : ArcLabels V B)
    (F : ComposableArrows ℕ 1) :
    ChainComplex (ModuleCat.{u} ℤ) ℤ :=
  genericQuotientComplex K a F.left F.right (leOfHom F.hom)

noncomputable def filtrationQuotientFunctor
    (K : FiniteComplex V) (a : ArcLabels V B) :
    ComposableArrows ℕ 1 ⥤ ChainComplex (ModuleCat.{u} ℤ) ℤ where
  obj F := filtrationQuotientObj K a F
  map {F G} φ := genericQuotientChainMap K a
    (leOfHom F.hom) (leOfHom (φ.app 0)) (leOfHom (φ.app 1))
    (leOfHom G.hom)
  map_id F := by
    exact genericQuotientChainMap_id K a (leOfHom F.hom)
  map_comp {F G H} φ ψ := by
    exact (genericQuotientChainMap_comp K a
      (leOfHom F.hom) (leOfHom (φ.app 0)) (leOfHom (φ.app 1))
      (leOfHom G.hom) (leOfHom (ψ.app 0)) (leOfHom (ψ.app 1))
      (leOfHom H.hom)).symm

noncomputable def filtrationHomologyFunctor
    (K : FiniteComplex V) (a : ArcLabels V B) (n : ℤ) :
    ComposableArrows ℕ 1 ⥤ ModuleCat.{u} ℤ :=
  filtrationQuotientFunctor K a ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ)
      (ComplexShape.down ℤ) n

end CurveGenusTwo.Filtration
