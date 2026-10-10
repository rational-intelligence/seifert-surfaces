import CurveComplexGenusTwo.Filtration.SpectralCast
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Category.ModuleCat.Abelian

namespace CurveGenusTwo.Filtration

open CategoryTheory CategoryTheory.Limits

universe u v

variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

private theorem cast_comp_zero {ι : Type*} {F G : ι → Type*}
    [∀ i, AddCommGroup (F i)] [∀ i, AddCommGroup (G i)]
    {i j : ι} (h : i = j) {A : Type*} [AddCommGroup A]
    (f : A →+ F i) (g : (k : ι) → F k →+ G k)
    (hz : (g i).comp f = 0) :
    (g j).comp (Eq.mp (congrArg (fun k => A →+ F k) h) f) = 0 := by
  cases h
  exact hz

private theorem cast_zero {ι : Type*} {F : ι → Type*}
    [∀ i, Zero (F i)] {i j : ι} (h : i = j) :
    Eq.mp (congrArg F h) (0 : F i) = 0 := by
  cases h
  rfl

private theorem cast_map_apply {ι : Type*} {F G : ι → Type*}
    [∀ i, AddCommGroup (F i)] [∀ i, AddCommGroup (G i)]
    {i j : ι} (h : i = j)
    (f : (k : ι) → F k →+ G k) (x : F i) :
    Eq.mp (congrArg G h) (f i x) =
      f j (Eq.mp (congrArg F h) x) := by
  cases h
  rfl

private theorem boundaryNextCast_sq (K : FiniteComplex V) (n : ℤ) :
    (boundaryNextCast K n).comp (boundaryNextCast K (n + 1)) = 0 := by
  have hn : n + 1 - 1 = n := by omega
  have hn' : (n + 1) + 1 - 1 = n + 1 := by omega
  have hsq : (boundary K (n + 1)).comp (boundaryNextCast K (n + 1)) = 0 := by
    change (boundary K (n + 1)).comp
      (Eq.mp (congrArg (fun m : ℤ => chains K ((n + 1) + 1) →+ chains K m) hn')
        (boundary K ((n + 1) + 1))) = 0
    exact cast_comp_zero hn' (boundary K ((n + 1) + 1)) (boundary K)
      (boundary_boundary K ((n + 1) + 1))
  apply AddMonoidHom.ext
  intro x
  have hzero := congrArg (fun f => f x) hsq
  change boundaryNextCast K n (boundaryNextCast K (n + 1) x) = 0
  rw [boundaryNextCast_apply K n]
  have hz : boundary K (n + 1) (boundaryNextCast K (n + 1) x) = 0 := by
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] using hzero
  rw [hz]
  exact cast_zero (F := chains K) hn

noncomputable def filteredChainComplex (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℤ) : ChainComplex (ModuleCat.{u} ℤ) ℤ :=
  ChainComplex.of
    (fun n => ModuleCat.of ℤ (chains (filtration K a p) n))
    (fun n => ModuleCat.ofHom
      (AddMonoidHom.toIntLinearMap (boundaryNextCast (filtration K a p) n)))
    (by
      intro n
      ext x
      have h := congrArg (fun f => f x) (boundaryNextCast_sq (filtration K a p) n)
      simpa using h)

noncomputable def filteredChainComplexIncl (K : FiniteComplex V)
    (a : ArcLabels V B) {p q : ℤ} (hpq : p ≤ q) :
    filteredChainComplex K a p ⟶ filteredChainComplex K a q :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (AddMonoidHom.toIntLinearMap
      (chainInclusion (filtration K a p) (filtration K a q)
        (filtration_mono K a hpq) n)))
    (by
      intro n
      simp only [filteredChainComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      ext x
      have hnat := congrArg (fun f => f x)
        (chainInclusion_boundary (filtration K a p) (filtration K a q)
          (filtration_mono K a hpq) (n + 1))
      simp only [AddMonoidHom.comp_apply] at hnat
      change boundaryNextCast (filtration K a q) n
          (chainInclusion (filtration K a p) (filtration K a q)
            (filtration_mono K a hpq) (n + 1) x) =
        chainInclusion (filtration K a p) (filtration K a q)
          (filtration_mono K a hpq) n
          (boundaryNextCast (filtration K a p) n x)
      rw [boundaryNextCast_apply, hnat,
        cast_map_apply (show n + 1 - 1 = n by omega) (fun m =>
          chainInclusion (filtration K a p) (filtration K a q)
            (filtration_mono K a hpq) m)]
      congr 1
      exact (boundaryNextCast_apply (filtration K a p) n x).symm)

private theorem freeAbelian_lift_injective {α β : Type*}
    (f : α → β) (hf : Function.Injective f) :
    Function.Injective (FreeAbelianGroup.lift
      (fun x : α => FreeAbelianGroup.of (f x))) := by
  classical
  by_cases hα : Nonempty α
  · let g : β → α := fun b =>
      if hb : ∃ a, f a = b then Classical.choose hb else Classical.choice hα
    have hgf : ∀ a : α, g (f a) = a := by
      intro a
      dsimp [g]
      rw [dite_eq_left ⟨a, rfl⟩]
      exact hf (Classical.choose_spec (show ∃ x, f x = f a from ⟨a, rfl⟩))
    let F : FreeAbelianGroup α →+ FreeAbelianGroup β :=
      FreeAbelianGroup.lift (fun a => FreeAbelianGroup.of (f a))
    let G : FreeAbelianGroup β →+ FreeAbelianGroup α :=
      FreeAbelianGroup.lift (fun b => FreeAbelianGroup.of (g b))
    have hcomp : G.comp F = AddMonoidHom.id (FreeAbelianGroup α) := by
      apply FreeAbelianGroup.lift_ext
      intro a
      change G (F (FreeAbelianGroup.of a)) = FreeAbelianGroup.of a
      simp only [F, G, FreeAbelianGroup.lift_apply_of, hgf]
    intro x y hxy
    change F x = F y at hxy
    calc
      x = (G.comp F) x := (congrArg (fun H => H x) hcomp).symm
      _ = (G.comp F) y := congrArg G hxy
      _ = y := congrArg (fun H => H y) hcomp
  · have : IsEmpty α := not_nonempty_iff.mp hα
    have : Subsingleton (FreeAbelianGroup α) := inferInstance
    intro x y _
    exact Subsingleton.elim x y

omit [LinearOrder V] in
theorem filteredChainComplexIncl_injective (K : FiniteComplex V)
    (a : ArcLabels V B) {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    Function.Injective (chainInclusion (filtration K a p) (filtration K a q)
      (filtration_mono K a hpq) n) := by
  let f : SimplexAt (filtration K a p) n → SimplexAt (filtration K a q) n :=
    fun σ => ⟨σ.1, filtration_mono K a hpq σ.2.1, σ.2.2⟩
  have hf : Function.Injective f := by
    intro σ τ he
    have hv : σ.1 = τ.1 := congrArg (fun z : SimplexAt (filtration K a q) n => z.1) he
    exact Subtype.ext hv
  exact freeAbelian_lift_injective f hf

theorem filteredChainComplexIncl_mono (K : FiniteComplex V)
    (a : ArcLabels V B) {p q : ℤ} (hpq : p ≤ q) :
    Mono (filteredChainComplexIncl K a hpq) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  apply (ModuleCat.mono_iff_injective _).mpr
  exact filteredChainComplexIncl_injective K a hpq n

end CurveGenusTwo.Filtration
