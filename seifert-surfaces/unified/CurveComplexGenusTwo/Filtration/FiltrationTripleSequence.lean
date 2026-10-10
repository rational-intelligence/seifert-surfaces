import CurveComplexGenusTwo.Filtration.GenericFiltrationQuotient
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

namespace CurveGenusTwo.Filtration

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

universe u v

variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

noncomputable def tripleFirstMap (K : FiniteComplex V) (a : ArcLabels V B)
    {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) (n : ℤ) :
    genericQuotient K a p q hpq n →+
      genericQuotient K a p r (hpq.trans hqr) n :=
  genericQuotientMap K a hpq (le_refl p) hqr (hpq.trans hqr) n

noncomputable def tripleSecondMap (K : FiniteComplex V) (a : ArcLabels V B)
    {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) (n : ℤ) :
    genericQuotient K a p r (hpq.trans hqr) n →+
      genericQuotient K a q r hqr n :=
  genericQuotientMap K a (hpq.trans hqr) hpq (le_refl r) hqr n

omit [LinearOrder V] in
theorem triple_maps_comp_zero (K : FiniteComplex V) (a : ArcLabels V B)
    {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) (n : ℤ) :
    (tripleSecondMap K a hpq hqr n).comp (tripleFirstMap K a hpq hqr n) = 0 := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
    change QuotientAddGroup.mk' _
        (chainInclusion (filtration K a r) (filtration K a r)
          (by intro s hs; exact hs) n
          (chainInclusion (filtration K a q) (filtration K a r)
          (filtration_mono K a (by omega)) n x)) = 0
    have hid : chainInclusion (filtration K a r) (filtration K a r)
        (by intro s hs; exact hs) n =
        AddMonoidHom.id (chains (filtration K a r) n) := by
      apply FreeAbelianGroup.lift_ext
      intro σ
      rfl
    rw [hid]
    exact (QuotientAddGroup.eq_zero_iff _).2
      ⟨x, rfl⟩

set_option linter.style.haveILetI false in
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
  · haveI : IsEmpty α := not_nonempty_iff.mp hα
    haveI : Subsingleton (FreeAbelianGroup α) := inferInstance
    intro x y _
    exact Subsingleton.elim x y

omit [DecidableEq V] [LinearOrder V] in
private theorem chainInclusion_injective_local (A B : FiniteComplex V)
    (h : A.simplices ⊆ B.simplices) (n : ℤ) :
    Function.Injective (chainInclusion A B h n) := by
  let f : SimplexAt A n → SimplexAt B n := fun σ => ⟨σ.1, h σ.2.1, σ.2.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : SimplexAt B n => z.1) hxy
  exact freeAbelian_lift_injective f hf

omit [DecidableEq V] [LinearOrder V] in
private theorem chainInclusion_comp_local (A B C : FiniteComplex V)
    (hAB : A.simplices ⊆ B.simplices) (hBC : B.simplices ⊆ C.simplices)
    (n : ℤ) :
    (chainInclusion B C hBC n).comp (chainInclusion A B hAB n) =
      chainInclusion A C (hAB.trans hBC) n := by
  apply AddMonoidHom.ext
  intro c
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | neg x hx => simp [map_neg, hx]
  | of σ => rfl

omit [DecidableEq V] [LinearOrder V] in
private theorem chainInclusion_self_local (A : FiniteComplex V) (n : ℤ) :
    chainInclusion A A (by intro x hx; exact hx) n =
      AddMonoidHom.id (chains A n) := by
  apply FreeAbelianGroup.lift_ext
  intro σ
  rfl

omit [LinearOrder V] in
theorem tripleFirstMap_injective (K : FiniteComplex V) (a : ArcLabels V B)
    {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) (n : ℤ) :
    Function.Injective (tripleFirstMap K a hpq hqr n) := by
  intro x y hxy
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
    induction y using QuotientAddGroup.induction_on with
    | _ y =>
      apply Quotient.sound
      have hmem : x - y ∈
        (chainInclusion (filtration K a p) (filtration K a q)
          (filtration_mono K a (by omega)) n).range := by
        have hclass :
            QuotientAddGroup.mk' _
              (chainInclusion (filtration K a q) (filtration K a r)
                (filtration_mono K a (by omega)) n x) =
            QuotientAddGroup.mk' _
              (chainInclusion (filtration K a q) (filtration K a r)
                (filtration_mono K a (by omega)) n y) := hxy
        have hz := (QuotientAddGroup.eq_iff_sub_mem.mp hclass)
        obtain ⟨z, hz⟩ := hz
        have hcomp := chainInclusion_comp_local (filtration K a p)
          (filtration K a q) (filtration K a r)
          (filtration_mono K a (by omega)) (filtration_mono K a (by omega)) n
        have hleft : chainInclusion (filtration K a q) (filtration K a r)
            (filtration_mono K a (by omega)) n (x - y) =
          chainInclusion (filtration K a p) (filtration K a r)
            (filtration_mono K a (by omega)) n z := by
          simpa only [map_sub] using hz.symm
        have hxy' : x - y = chainInclusion (filtration K a p) (filtration K a q)
            (filtration_mono K a (by omega)) n z :=
          chainInclusion_injective_local (filtration K a q) (filtration K a r)
            (filtration_mono K a (by omega)) n (by
              calc
                chainInclusion (filtration K a q) (filtration K a r)
                    (filtration_mono K a (by omega)) n (x - y) =
                  chainInclusion (filtration K a p) (filtration K a r)
                    (filtration_mono K a (by omega)) n z := hleft
                _ = chainInclusion (filtration K a q) (filtration K a r)
                    (filtration_mono K a (by omega)) n
                      (chainInclusion (filtration K a p) (filtration K a q)
                        (filtration_mono K a (by omega)) n z) :=
                  (congrArg (fun f => f z) hcomp).symm)
        exact ⟨z, hxy'.symm⟩
      have hneg := (chainInclusion (filtration K a p) (filtration K a q)
        (filtration_mono K a (by omega)) n).range.neg_mem hmem
      exact QuotientAddGroup.leftRel_apply.mpr (by convert hneg using 1; abel)

omit [LinearOrder V] in
theorem tripleSecondMap_surjective (K : FiniteComplex V) (a : ArcLabels V B)
    {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) (n : ℤ) :
    Function.Surjective (tripleSecondMap K a hpq hqr n) := by
  intro y
  induction y using QuotientAddGroup.induction_on with
  | _ c =>
    refine ⟨QuotientAddGroup.mk' _ c, ?_⟩
    change QuotientAddGroup.mk' _
      (chainInclusion (filtration K a r) (filtration K a r)
        (by intro s hs; exact hs) n c) = _
    rw [show chainInclusion (filtration K a r) (filtration K a r)
        (by intro s hs; exact hs) n = AddMonoidHom.id _ by
      apply FreeAbelianGroup.lift_ext
      intro σ
      rfl]
    rfl

omit [LinearOrder V] in
private theorem tripleSecondMap_kernel_eq_range
    (K : FiniteComplex V) (a : ArcLabels V B)
    {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) (n : ℤ) :
    (tripleSecondMap K a hpq hqr n).ker =
      (tripleFirstMap K a hpq hqr n).range := by
  apply AddSubgroup.ext
  intro x
  constructor
  · intro hx
    induction x using QuotientAddGroup.induction_on with
    | _ c =>
      have hzero :
          (QuotientAddGroup.mk'
            (chainInclusion (filtration K a q) (filtration K a r)
              (filtration_mono K a (by omega)) n).range c :
            genericQuotient K a q r hqr n) = 0 := by
        change tripleSecondMap K a hpq hqr n
          (QuotientAddGroup.mk' _ c) = 0 at hx
        change QuotientAddGroup.mk' _
          (chainInclusion (filtration K a r) (filtration K a r)
            (by intro s hs; exact hs) n c) = 0 at hx
        rw [show chainInclusion (filtration K a r) (filtration K a r)
            (by intro s hs; exact hs) n = AddMonoidHom.id _ by
          apply FreeAbelianGroup.lift_ext
          intro σ
          rfl] at hx
        exact hx
      have hmem : c ∈
          (chainInclusion (filtration K a q) (filtration K a r)
            (filtration_mono K a (by omega)) n).range :=
        (QuotientAddGroup.eq_zero_iff _).mp hzero
      obtain ⟨d, hd⟩ := hmem
      refine ⟨QuotientAddGroup.mk' _ d, ?_⟩
      change QuotientAddGroup.mk' _
          (chainInclusion (filtration K a q) (filtration K a r)
            (filtration_mono K a (by omega)) n d) =
        QuotientAddGroup.mk' _ c
      rw [hd]
  · rintro ⟨y, rfl⟩
    change tripleSecondMap K a hpq hqr n
      (tripleFirstMap K a hpq hqr n y) = 0
    exact congrArg (fun f => f y)
      (triple_maps_comp_zero K a hpq hqr n)

omit [LinearOrder V] in
theorem tripleSecondMap_exact (K : FiniteComplex V) (a : ArcLabels V B)
    {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) (n : ℤ) :
    Function.Exact (tripleFirstMap K a hpq hqr n)
      (tripleSecondMap K a hpq hqr n) := by
  intro x
  rw [← AddMonoidHom.mem_ker, tripleSecondMap_kernel_eq_range]
  rfl

noncomputable def tripleFirstChainMap (K : FiniteComplex V) (a : ArcLabels V B)
    {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) :
    genericQuotientComplex K a p q hpq ⟶
      genericQuotientComplex K a p r (hpq.trans hqr) :=
  genericQuotientChainMap K a hpq (le_refl p) hqr (hpq.trans hqr)

noncomputable def tripleSecondChainMap (K : FiniteComplex V) (a : ArcLabels V B)
    {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) :
    genericQuotientComplex K a p r (hpq.trans hqr) ⟶
      genericQuotientComplex K a q r hqr :=
  genericQuotientChainMap K a (hpq.trans hqr) hpq (le_refl r) hqr

noncomputable def filtrationTripleShortComplex (K : FiniteComplex V)
    (a : ArcLabels V B) {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) :
    ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℤ) :=
  ShortComplex.mk (tripleFirstChainMap K a hpq hqr)
    (tripleSecondChainMap K a hpq hqr)
    (by
      ext n x
      exact congrArg (fun f => f x) (triple_maps_comp_zero K a hpq hqr n))

theorem filtrationTripleShortComplex_shortExact (K : FiniteComplex V)
    (a : ArcLabels V B) {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) :
    (filtrationTripleShortComplex K a hpq hqr).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (tripleFirstMap K a hpq hqr n)
      (tripleSecondMap K a hpq hqr n)
    exact tripleSecondMap_exact K a hpq hqr n
  · exact tripleFirstMap_injective K a hpq hqr n
  · exact tripleSecondMap_surjective K a hpq hqr n

end CurveGenusTwo.Filtration
