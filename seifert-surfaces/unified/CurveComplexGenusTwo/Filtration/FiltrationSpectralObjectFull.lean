import CurveComplexGenusTwo.Filtration.FiltrationSpectralObject
import Mathlib.Algebra.Homology.SpectralObject.Basic
import Mathlib.Algebra.Homology.HomologySequenceLemmas

namespace CurveGenusTwo.Filtration

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
open ComposableArrows

universe u v

variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

noncomputable def filtrationTripleObj (K : FiniteComplex V) (a : ArcLabels V B)
    (D : ComposableArrows ℕ 2) :
    ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℤ) :=
  filtrationTripleShortComplex K a
    (leOfHom (D.map' 0 1)) (leOfHom (D.map' 1 2))

noncomputable def filtrationTripleHom (K : FiniteComplex V)
    (a : ArcLabels V B) {D E : ComposableArrows ℕ 2} (φ : D ⟶ E) :
    filtrationTripleObj K a D ⟶ filtrationTripleObj K a E := by
  let p := D.obj' 0
  let q := D.obj' 1
  let r := D.obj' 2
  let p' := E.obj' 0
  let q' := E.obj' 1
  let r' := E.obj' 2
  refine {
    τ₁ := genericQuotientChainMap K a
      (leOfHom (D.map' 0 1)) (leOfHom (app' φ 0)) (leOfHom (app' φ 1))
      (leOfHom (E.map' 0 1))
    τ₂ := genericQuotientChainMap K a
      (leOfHom (D.map' 0 2)) (leOfHom (app' φ 0)) (leOfHom (app' φ 2))
      (leOfHom (E.map' 0 2))
    τ₃ := genericQuotientChainMap K a
      (leOfHom (D.map' 1 2)) (leOfHom (app' φ 1)) (leOfHom (app' φ 2))
      (leOfHom (E.map' 1 2))
    comm₁₂ := ?_
    comm₂₃ := ?_ }
  · dsimp [filtrationTripleObj, filtrationTripleShortComplex, tripleFirstChainMap]
    rw [genericQuotientChainMap_comp, genericQuotientChainMap_comp]
  · dsimp [filtrationTripleObj, filtrationTripleShortComplex, tripleSecondChainMap]
    rw [genericQuotientChainMap_comp, genericQuotientChainMap_comp]

noncomputable def filtrationSpectralHomologyFunctor
    (K : FiniteComplex V) (a : ArcLabels V B) (n : ℤ) :
    ComposableArrows ℕ 1 ⥤ ModuleCat.{u} ℤ :=
  filtrationQuotientFunctor K a ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ)
      (ComplexShape.down ℤ) (-n)

private theorem down_adjacent (n m : ℤ) (h : n + 1 = m) :
    (ComplexShape.down ℤ).Rel (-n) (-m) := by
  exact ComplexShape.down_mk (-n) (-m) (by omega)

noncomputable def filtrationSpectralConnecting
    (K : FiniteComplex V) (a : ArcLabels V B)
    (D : ComposableArrows ℕ 2) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (filtrationSpectralHomologyFunctor K a n₀).obj
        (mk₁ (D.map' 1 2)) ⟶
      (filtrationSpectralHomologyFunctor K a n₁).obj
        (mk₁ (D.map' 0 1)) := by
  exact (filtrationTripleShortComplex_shortExact K a
      (leOfHom (D.map' 0 1)) (leOfHom (D.map' 1 2))).δ
    (-n₀) (-n₁) (down_adjacent n₀ n₁ h)

noncomputable def filtrationSpectralObject
    (K : FiniteComplex V) (a : ArcLabels V B) :
    Abelian.SpectralObject (ModuleCat.{u} ℤ) ℕ where
  H := filtrationSpectralHomologyFunctor K a
  δ' n₀ n₁ h := {
    app := fun D => filtrationSpectralConnecting K a D n₀ n₁ h
    naturality := by
      intro D E φ
      let ψ := filtrationTripleHom K a φ
      have hSD := filtrationTripleShortComplex_shortExact K a
        (leOfHom (D.map' 0 1)) (leOfHom (D.map' 1 2))
      have hSE := filtrationTripleShortComplex_shortExact K a
        (leOfHom (E.map' 0 1)) (leOfHom (E.map' 1 2))
      exact (HomologicalComplex.HomologySequence.δ_naturality ψ hSD hSE
        (-n₀) (-n₁) (down_adjacent n₀ n₁ h)).symm }
  exact₁' n₀ n₁ h D := by
    have hS := filtrationTripleShortComplex_shortExact K a
      (leOfHom (D.map' 0 1)) (leOfHom (D.map' 1 2))
    change (mk₂ (hS.δ (-n₀) (-n₁) (down_adjacent n₀ n₁ h))
      (HomologicalComplex.homologyMap _ (-n₁))).Exact
    exact (hS.homology_exact₁ (-n₀) (-n₁) (down_adjacent n₀ n₁ h)).exact_toComposableArrows
  exact₂' n D := by
    have hS := filtrationTripleShortComplex_shortExact K a
      (leOfHom (D.map' 0 1)) (leOfHom (D.map' 1 2))
    change (mk₂ (HomologicalComplex.homologyMap _ (-n))
      (HomologicalComplex.homologyMap _ (-n))).Exact
    exact (hS.homology_exact₂ (-n)).exact_toComposableArrows
  exact₃' n₀ n₁ h D := by
    have hS := filtrationTripleShortComplex_shortExact K a
      (leOfHom (D.map' 0 1)) (leOfHom (D.map' 1 2))
    change (mk₂ (HomologicalComplex.homologyMap _ (-n₀))
      (hS.δ (-n₀) (-n₁) (down_adjacent n₀ n₁ h))).Exact
    exact (hS.homology_exact₃ (-n₀) (-n₁) (down_adjacent n₀ n₁ h)).exact_toComposableArrows

end CurveGenusTwo.Filtration
