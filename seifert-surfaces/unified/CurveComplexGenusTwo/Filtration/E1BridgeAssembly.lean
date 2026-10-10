import CurveComplexGenusTwo.Filtration.SpectralCastE1Bridge
import CurveComplexGenusTwo.Filtration.SpectralDefinitions
import CurveComplexGenusTwo.Filtration.FirstPageSplit

namespace CurveGenusTwo.Filtration

universe u v

variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

set_option maxHeartbeats 2000000

set_option linter.style.haveILetI false in
private theorem freeAbelian_lift_injective_bridge {α β : Type*}
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

omit [LinearOrder V] in
private theorem filteredInclusion_injective_bridge (K : FiniteComplex V)
    (a : ArcLabels V B) (p n : ℤ) :
    Function.Injective (chainInclusion (filtration K a p) K
      (by intro σ hσ; exact hσ.1) n) := by
  let f : SimplexAt (filtration K a p) n → SimplexAt K n :=
    fun σ => ⟨σ.1, σ.2.1.1, σ.2.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : SimplexAt K n => z.1) hxy
  exact freeAbelian_lift_injective_bridge f hf

private noncomputable def quotientAddEquiv_bridge
    {A C : Type*} [AddCommGroup A] [AddCommGroup C]
    (e : A ≃+ C) (SA : AddSubgroup A) (SC : AddSubgroup C)
    (h : ∀ x : A, x ∈ SA ↔ e x ∈ SC) :
    A ⧸ SA ≃+ C ⧸ SC := by
  let f : A ⧸ SA →+ C ⧸ SC :=
    QuotientAddGroup.lift SA
      ((QuotientAddGroup.mk' SC).comp e.toAddMonoidHom)
      (by
        intro x hx
        change QuotientAddGroup.mk' SC (e x) = 0
        exact (QuotientAddGroup.eq_zero_iff (e x)).2 ((h x).mp hx))
  let g : C ⧸ SC →+ A ⧸ SA :=
    QuotientAddGroup.lift SC
      ((QuotientAddGroup.mk' SA).comp e.symm.toAddMonoidHom)
      (by
        intro y hy
        change QuotientAddGroup.mk' SA (e.symm y) = 0
        exact (QuotientAddGroup.eq_zero_iff (e.symm y)).2
          ((h (e.symm y)).mpr (by simpa using hy)))
  refine {
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    map_add' := f.map_add }
  · intro x
    induction x using QuotientAddGroup.induction_on with
    | _ x =>
      change QuotientAddGroup.mk' SA (e.symm (e x)) =
        QuotientAddGroup.mk' SA x
      rw [e.symm_apply_apply]
  · intro y
    induction y using QuotientAddGroup.induction_on with
    | _ y =>
      change QuotientAddGroup.mk' SC (e (e.symm y)) =
        QuotientAddGroup.mk' SC y
      rw [e.apply_symm_apply]

noncomputable def spectralCyclesFilteredPreimageEquiv
    (K : FiniteComplex V) (a : ArcLabels V B) (p q : ℤ) :
    let C := filtration K a p
    let L₀ := (chainInclusion (filtration K a (p - 1)) C
      (filtration_mono K a (by omega)) (p + q - 1)).range
    let Z := L₀.comap (boundary C (p + q))
    Z ≃+ spectralCycles K a 1 p (p + q) := by
  let C := filtration K a p
  let j := chainInclusion C K (by intro σ hσ; exact hσ.1) (p + q)
  let L₀ := (chainInclusion (filtration K a (p - 1)) C
    (filtration_mono K a (by omega)) (p + q - 1)).range
  let Z := L₀.comap (boundary C (p + q))
  have hj : Function.Injective j := filteredInclusion_injective_bridge K a p (p + q)
  have hmap : Z.map j = spectralCycles K a 1 p (p + q) := by
    exact Signed.filteredPreimage_map_eq_spectralCycles K a p q
  let f : Z →+ spectralCycles K a 1 p (p + q) :=
    (j.comp Z.subtype).codRestrict _ (by
      intro z
      exact (Signed.filteredPreimage_eq_spectralCycles_comap K a p q).le z.2)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply hj
    exact congrArg Subtype.val hxy
  have hf_surj : Function.Surjective f := by
    intro y
    have hy : y.1 ∈ Z.map j := by rw [hmap]; exact y.2
    obtain ⟨x, hx, heq⟩ := hy
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext heq
  exact AddEquiv.ofBijective f ⟨hf_inj, hf_surj⟩

noncomputable def filteredSpectralQuotientEquiv
    (K : FiniteComplex V) (a : ArcLabels V B) (p q : ℤ) :
    let C := filtration K a p
    let n := p + q
    let L₀ := (chainInclusion (filtration K a (p - 1)) C
      (filtration_mono K a (by omega)) (n - 1)).range
    let L₁ := (chainInclusion (filtration K a (p - 1)) C
      (filtration_mono K a (by omega)) n).range
    let Z := L₀.comap (boundary C n)
    let u := boundaryNextCast C n
    Z ⧸ ((L₁ ⊔ u.range).comap Z.subtype) ≃+
      spectralPageGroup K a 1 p q := by
  let C := filtration K a p
  let n := p + q
  let L₀ := (chainInclusion (filtration K a (p - 1)) C
    (filtration_mono K a (by omega)) (n - 1)).range
  let L₁ := (chainInclusion (filtration K a (p - 1)) C
    (filtration_mono K a (by omega)) n).range
  let Z := L₀.comap (boundary C n)
  let u := boundaryNextCast C n
  let S := spectralCycles K a 1 p n
  let N := spectralNullChains K a 1 p n
  let e : Z ≃+ S := spectralCyclesFilteredPreimageEquiv K a p q
  apply quotientAddEquiv_bridge e
    ((L₁ ⊔ u.range).comap Z.subtype) (N.comap S.subtype)
  intro z
  have hden := filteredIncoming_denominator_comap_eq_spectralNullChains K a p q
  change z ∈ (L₁ ⊔ u.range).comap Z.subtype ↔
    e z ∈ N.comap S.subtype
  rw [hden]
  rfl

private theorem cast_hom_apply_bridge {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A : Type*} [AddCommGroup A] (f : A →+ F i) (x : A) :
    (Eq.mp (congrArg (fun k => A →+ F k) h) f) x =
      Eq.mp (congrArg F h) (f x) := by
  cases h
  rfl

private theorem cast_quotient_mk_bridge {ι : Type*} (F : ι → Type*)
    [∀ i, AddCommGroup (F i)] (L : (i : ι) → AddSubgroup (F i))
    {i j : ι} (h : i = j) (x : F i) :
    Eq.mp (congrArg (fun k => F k ⧸ L k) h)
      (QuotientAddGroup.mk' (L i) x) =
      QuotientAddGroup.mk' (L j) (Eq.mp (congrArg F h) x) := by
  cases h
  rfl

private noncomputable def quotientByComapEquiv_bridge
    {A C : Type*} [AddCommGroup A] [AddCommGroup C]
    (f : A →+ C) (hf : Function.Surjective f) (S : AddSubgroup C) :
    A ⧸ S.comap f ≃+ C ⧸ S := by
  let g : A →+ C ⧸ S := (QuotientAddGroup.mk' S).comp f
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective S y
    obtain ⟨a, rfl⟩ := hf c
    exact ⟨a, rfl⟩
  have hker : g.ker = S.comap f := by
    ext a
    change QuotientAddGroup.mk' S (f a) = 0 ↔ f a ∈ S
    exact QuotientAddGroup.eq_zero_iff _
  exact (QuotientAddGroup.quotientAddEquivOfEq hker).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective g hg)

noncomputable def signedAdjacentQuotientHomologyEquiv
    (K : FiniteComplex V) (a : ArcLabels V B) (p q : ℤ) :
    let n := p + q
    let d := Signed.genericQuotientBoundary K a (p - 1) p (by omega) n
    let u := Signed.genericQuotientBoundaryNextCast K a (p - 1) p (by omega) n
    d.ker ⧸ (u.range.comap d.ker.subtype) ≃+
      spectralPageGroup K a 1 p q := by
  let C := filtration K a p
  let A := filtration K a (p - 1)
  let n := p + q
  let i (m : ℤ) := chainInclusion A C (filtration_mono K a (by omega)) m
  let L₀ := (i (n - 1)).range
  let L₁ := (i n).range
  let L₂ := (i (n + 1)).range
  let d := boundary C n
  let u := boundaryNextCast C n
  let D := Signed.genericQuotientBoundary K a (p - 1) p (by omega) n
  let U := Signed.genericQuotientBoundaryNextCast K a (p - 1) p (by omega) n
  let Z := L₀.comap d
  let qZ : Z →+ D.ker := {
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
  have hdesc (x : chains C (n + 1)) :
      U (QuotientAddGroup.mk' L₂ x) = QuotientAddGroup.mk' L₁ (u x) := by
    let Q (m : ℤ) := Signed.genericQuotient K a (p - 1) p (by omega) m
    have hn : n + 1 - 1 = n := by omega
    change (Eq.mp (congrArg (fun m : ℤ => Q (n + 1) →+ Q m) hn)
      (Signed.genericQuotientBoundary K a (p - 1) p (by omega) (n + 1)))
        (QuotientAddGroup.mk' L₂ x) = QuotientAddGroup.mk' L₁ (u x)
    rw [cast_hom_apply_bridge]
    change Eq.mp (congrArg Q hn)
      (QuotientAddGroup.mk' (i (n + 1 - 1)).range
        (boundary C (n + 1) x)) = QuotientAddGroup.mk' L₁ (u x)
    rw [cast_quotient_mk_bridge (F := fun m : ℤ => chains C m)
      (L := fun m => (i m).range) hn]
    rw [boundaryNextCast_apply]
    exact hn
  have heq :
      (U.range.comap D.ker.subtype).comap qZ =
        (L₁ ⊔ u.range).comap Z.subtype := by
    ext z
    change (∃ y : Signed.genericQuotient K a (p - 1) p (by omega) (n + 1),
      U y = QuotientAddGroup.mk' L₁ z.1) ↔ z.1 ∈ L₁ ⊔ u.range
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L₂ y
      rw [hdesc] at hy
      have hsub : u x - z.1 ∈ L₁ := (QuotientAddGroup.eq_iff_sub_mem).mp hy
      have hl : z.1 - u x ∈ L₁ := by simpa only [neg_sub] using L₁.neg_mem hsub
      have hr : u x ∈ u.range := ⟨x, rfl⟩
      have hs : (z.1 - u x) + u x ∈ L₁ ⊔ u.range :=
        AddSubgroup.add_mem_sup hl hr
      simpa only [sub_add_cancel] using hs
    · intro hz
      obtain ⟨l, hl, r, hr, heqr⟩ := (AddSubgroup.mem_sup).mp hz
      obtain ⟨x, rfl⟩ := hr
      refine ⟨QuotientAddGroup.mk' L₂ x, ?_⟩
      rw [hdesc]
      apply (QuotientAddGroup.eq_iff_sub_mem).mpr
      have : u x - z.1 = -l := by rw [← heqr]; abel
      rw [this]
      exact L₁.neg_mem hl
  let f := filteredSpectralQuotientEquiv K a p q
  let g := (QuotientAddGroup.quotientAddEquivOfEq heq.symm).trans
    (quotientByComapEquiv_bridge qZ hsurj
      (U.range.comap D.ker.subtype))
  exact g.symm.trans f

end CurveGenusTwo.Filtration
