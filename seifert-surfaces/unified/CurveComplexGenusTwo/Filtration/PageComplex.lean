import CurveComplexGenusTwo.Filtration.PageDifferential
import Mathlib.Algebra.Homology.SpectralSequence.Basic

namespace CurveGenusTwo.Filtration
universe u v
variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]
open CategoryTheory

theorem pageShape_rel_iff (r : ℤ) (i j : ℤ × ℤ) :
    (pageShape r).Rel i j ↔ j = (i.1 - r, i.2 + r - 1) := by
  change j + (⟨r, 1-r⟩ : ℤ × ℤ) = i ↔ _
  constructor
  · intro h
    apply Prod.ext
    · have hf := congrArg Prod.fst h
      dsimp at hf ⊢
      omega
    · have hs := congrArg Prod.snd h
      dsimp at hs ⊢
      omega
  · intro h
    subst j
    apply Prod.ext <;> dsimp <;> omega

noncomputable def pageDifferentialHom (K : FiniteComplex V)
    (a : ArcLabels V B) (r : ℤ) (i j : ℤ × ℤ)
    (h : (pageShape r).Rel i j) :
    ModuleCat.of ℤ (spectralPageGroup K a r i.1 i.2) ⟶
      ModuleCat.of ℤ (spectralPageGroup K a r j.1 j.2) := by
  have h' : j + (⟨r, 1-r⟩ : ℤ × ℤ) = i := by
    exact h
  have hfst := congrArg Prod.fst h'
  have hsnd := congrArg Prod.snd h'
  have hp : j.1 = i.1 - r := by
    have hf : j.1 + r = i.1 := by simpa using hfst
    omega
  have hq : j.2 = i.2 + r - 1 := by
    have hs : j.2 + (1 - r) = i.2 := by simpa using hsnd
    omega
  cases i with | mk i₁ i₂ =>
    cases j with | mk j₁ j₂ =>
      dsimp at h' hp hq ⊢
      subst j₁; subst j₂
      exact ModuleCat.ofHom (concretePageDifferential K a r i₁ i₂).toIntLinearMap

theorem pageDifferentialHom_eq (K : FiniteComplex V)
    (a : ArcLabels V B) (r : ℤ) (i : ℤ × ℤ)
    (h : (pageShape r).Rel i (i.1 - r, i.2 + r - 1)) :
    pageDifferentialHom K a r i (i.1 - r, i.2 + r - 1) h =
      ModuleCat.ofHom (concretePageDifferential K a r i.1 i.2).toIntLinearMap := by
  cases i with
  | mk p q =>
    unfold pageDifferentialHom
    rfl

noncomputable def concretePageHomologicalComplex (K : FiniteComplex V)
    (a : ArcLabels V B) (r : ℤ) :
    HomologicalComplex (ModuleCat ℤ) (pageShape r) := by
  classical
  exact
  { X := fun i => ModuleCat.of ℤ (spectralPageGroup K a r i.1 i.2)
    d := fun i j => if h : (pageShape r).Rel i j then pageDifferentialHom K a r i j h else 0
    shape := by intro i j h; simp [h]
    d_comp_d' := by
      intro i j k hij hjk
      rw [dite_eq_left hij, dite_eq_left hjk]
      have hj := (pageShape_rel_iff r i j).mp hij
      have hk := (pageShape_rel_iff r j k).mp hjk
      subst k
      subst j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have hz := congrArg (fun f => f x)
        (concretePageDifferential_comp_zero K a r i.1 i.2)
      simpa [pageDifferentialHom] using hz }

end CurveGenusTwo.Filtration
