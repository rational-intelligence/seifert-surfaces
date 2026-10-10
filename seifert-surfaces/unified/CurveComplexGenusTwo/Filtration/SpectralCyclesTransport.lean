import CurveComplexGenusTwo.Filtration.SignedFiltrationQuotient
import CurveComplexGenusTwo.Filtration.SpectralCast

namespace CurveGenusTwo.Filtration.Signed

universe u v
variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

set_option linter.style.haveILetI false in
private theorem freeAbelian_lift_injective_local {α β : Type*}
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
private theorem inclusion_injective (A C : FiniteComplex V)
    (h : A.simplices ⊆ C.simplices) (n : ℤ) :
    Function.Injective (chainInclusion A C h n) := by
  let f : SimplexAt A n → SimplexAt C n := fun σ => ⟨σ.1, h σ.2.1, σ.2.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : SimplexAt C n => z.1) hxy
  exact freeAbelian_lift_injective_local f hf

omit [DecidableEq V] [LinearOrder V] in
private theorem inclusion_comp (A C D : FiniteComplex V)
    (hAC : A.simplices ⊆ C.simplices) (hCD : C.simplices ⊆ D.simplices)
    (n : ℤ) :
    (chainInclusion C D hCD n).comp (chainInclusion A C hAC n) =
      chainInclusion A D (hAC.trans hCD) n := by
  apply FreeAbelianGroup.lift_ext
  intro σ
  rfl

omit [LinearOrder V] in
/-- Membership in the lower filtration can be reflected along the ambient
chain inclusion, including the bottom column `p = 0`. -/
theorem lowerFiltration_reflect (K : FiniteComplex V) (a : ArcLabels V B)
    (p n : ℤ) (c : chains (filtration K a p) n) :
    c ∈ (chainInclusion (filtration K a (p - 1)) (filtration K a p)
        (filtration_mono K a (by omega)) n).range ↔
      chainInclusion (filtration K a p) K (by intro σ hσ; exact hσ.1) n c ∈
        filteredChains K a (p - 1) n := by
  let A := filtration K a (p - 1)
  let C := filtration K a p
  let i : chains A n →+ chains C n :=
    chainInclusion A C (filtration_mono K a (by omega)) n
  let j : chains C n →+ chains K n :=
    chainInclusion C K (by intro σ hσ; exact hσ.1) n
  let k : chains A n →+ chains K n :=
    chainInclusion A K (by intro σ hσ; exact hσ.1) n
  have hcomp : j.comp i = k := inclusion_comp A C K _ _ n
  change c ∈ i.range ↔ j c ∈ k.range
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (congrArg (fun f => f y) hcomp).symm⟩
  · rintro ⟨y, hy⟩
    have heq : j (i y) = j c := by
      rw [← hy]
      exact congrArg (fun f => f y) hcomp
    exact ⟨y, inclusion_injective C K _ n heq⟩

/-- The signed adjacent-quotient differential vanishes precisely when the
ambient representative belongs to the source's actual first-page cycles. -/
theorem quotientBoundary_zero_iff_spectralCycles
    (K : FiniteComplex V) (a : ArcLabels V B) (p q : ℤ)
    (c : chains (filtration K a p) (p + q)) :
    genericQuotientBoundary K a (p - 1) p (by omega) (p + q)
        (QuotientAddGroup.mk' _ c) = 0 ↔
      chainInclusion (filtration K a p) K
        (by intro σ hσ; exact hσ.1) (p + q) c ∈
        spectralCycles K a 1 p (p + q) := by
  let j (n : ℤ) : chains (filtration K a p) n →+ chains K n :=
    chainInclusion (filtration K a p) K (by intro σ hσ; exact hσ.1) n
  have hnat := congrArg (fun f => f c)
    (chainInclusion_boundary (filtration K a p) K
      (by intro σ hσ; exact hσ.1) (p + q))
  have hb : boundary K (p + q) (j (p + q) c) =
      j (p + q - 1) (boundary (filtration K a p) (p + q) c) := by
    simpa only [AddMonoidHom.comp_apply] using hnat
  change QuotientAddGroup.mk' _
      (boundary (filtration K a p) (p + q) c) = 0 ↔ _
  refine (QuotientAddGroup.eq_zero_iff _).trans ?_
  change boundary (filtration K a p) (p + q) c ∈
      (chainInclusion (filtration K a (p - 1)) (filtration K a p)
        (filtration_mono K a (by omega)) (p + q - 1)).range ↔ _
  rw [lowerFiltration_reflect K a p (p + q - 1), ← hb]
  change boundary K (p + q) (j (p + q) c) ∈
      filteredChains K a (p - 1) (p + q - 1) ↔
    j (p + q) c ∈ filteredChains K a p (p + q) ⊓
      (filteredChains K a (p - 1) (p + q - 1)).comap
        (boundary K (p + q))
  constructor
  · intro hc
    exact ⟨⟨c, rfl⟩, hc⟩
  · exact And.right

/-- The exact first-page cycle comparison at signed bidegree `(p,q)`.
The left side is the preimage of the lower filtration inside `F_p` under
the filtered differential; the right side is the pullback of the source's
ambient `spectralCycles` subgroup. -/
theorem filteredPreimage_eq_spectralCycles_comap
    (K : FiniteComplex V) (a : ArcLabels V B) (p q : ℤ) :
    ((chainInclusion (filtration K a (p - 1)) (filtration K a p)
        (filtration_mono K a (by omega)) (p + q - 1)).range).comap
      (boundary (filtration K a p) (p + q)) =
    (spectralCycles K a 1 p (p + q)).comap
      (chainInclusion (filtration K a p) K
        (by intro σ hσ; exact hσ.1) (p + q)) := by
  ext c
  change boundary (filtration K a p) (p + q) c ∈
      (chainInclusion (filtration K a (p - 1)) (filtration K a p)
        (filtration_mono K a (by omega)) (p + q - 1)).range ↔ _
  have h := quotientBoundary_zero_iff_spectralCycles K a p q c
  change QuotientAddGroup.mk' _
      (boundary (filtration K a p) (p + q) c) = 0 ↔ _ at h
  exact (QuotientAddGroup.eq_zero_iff _).symm.trans h

/-- Ambient form of the comparison: first-page cycles are precisely the
embedded filtered chains whose boundary lies in the preceding column. -/
theorem filteredPreimage_map_eq_spectralCycles
    (K : FiniteComplex V) (a : ArcLabels V B) (p q : ℤ) :
    (((chainInclusion (filtration K a (p - 1)) (filtration K a p)
        (filtration_mono K a (by omega)) (p + q - 1)).range).comap
      (boundary (filtration K a p) (p + q))).map
        (chainInclusion (filtration K a p) K
          (by intro σ hσ; exact hσ.1) (p + q)) =
      spectralCycles K a 1 p (p + q) := by
  let j := chainInclusion (filtration K a p) K
    (by intro σ hσ; exact hσ.1) (p + q)
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact (filteredPreimage_eq_spectralCycles_comap K a p q).le hc
  · intro hx
    have hfiltered : x ∈ filteredChains K a p (p + q) := hx.1
    obtain ⟨c, rfl⟩ := hfiltered
    refine ⟨c, ?_, rfl⟩
    exact (filteredPreimage_eq_spectralCycles_comap K a p q).ge hx

/-- Kernel of the adjacent filtered quotient differential, expressed as the
quotient of its ambient boundary preimage. -/
noncomputable abbrev genericQuotientKernelTarget
    (K : FiniteComplex V) (a : ArcLabels V B) (p q : ℤ) : Type u :=
  ((chainInclusion (filtration K a (p - 1)) (filtration K a p)
      (filtration_mono K a (by omega)) (p + q - 1)).range.comap
      (boundary (filtration K a p) (p + q))) ⧸
    (((chainInclusion (filtration K a (p - 1)) (filtration K a p)
      (filtration_mono K a (by omega)) (p + q)).range).comap
      (((chainInclusion (filtration K a (p - 1)) (filtration K a p)
        (filtration_mono K a (by omega)) (p + q - 1)).range.comap
        (boundary (filtration K a p) (p + q))).subtype))

noncomputable def genericQuotientKernelEquiv
    (K : FiniteComplex V) (a : ArcLabels V B) (p q : ℤ) :
    (genericQuotientBoundary K a (p - 1) p (by omega) (p + q)).ker ≃+
      genericQuotientKernelTarget K a p q := by
  let A := filtration K a (p - 1)
  let C := filtration K a p
  let d := boundary C (p + q)
  let L₀ := (chainInclusion A C (filtration_mono K a (by omega)) (p + q - 1)).range
  let L₁ := (chainInclusion A C (filtration_mono K a (by omega)) (p + q)).range
  let Z := L₀.comap d
  let qZ : Z →+ (genericQuotientBoundary K a (p - 1) p (by omega) (p + q)).ker := {
    toFun := fun z => ⟨QuotientAddGroup.mk' L₁ z.1, by
      change QuotientAddGroup.mk' L₀ (d z.1) = 0
      exact (QuotientAddGroup.eq_zero_iff _).2 z.2⟩
    map_zero' := by ext; rfl
    map_add' := by intro x y; ext; rfl }
  have hsurj : Function.Surjective qZ := by
    intro x
    obtain ⟨y, hyq⟩ := QuotientAddGroup.mk'_surjective L₁ x.1
    have hy : d y ∈ L₀ := by
      have hx := x.2
      rw [← hyq] at hx
      change QuotientAddGroup.mk' L₀ (d y) = 0 at hx
      exact (QuotientAddGroup.eq_zero_iff _).mp hx
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    exact hyq
  have hker : qZ.ker = L₁.comap Z.subtype := by
    ext x
    change qZ x = 0 ↔ x.1 ∈ L₁
    constructor
    · intro hx
      exact (QuotientAddGroup.eq_zero_iff _).mp (congrArg Subtype.val hx)
    · intro hx
      apply Subtype.ext
      exact (QuotientAddGroup.eq_zero_iff _).mpr hx
  exact ((QuotientAddGroup.quotientAddEquivOfEq hker).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective qZ hsurj)).symm

end CurveGenusTwo.Filtration.Signed
