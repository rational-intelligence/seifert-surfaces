import CurveComplexGenusTwo.Filtration.SpectralCast

namespace CurveGenusTwo.Filtration

open scoped BigOperators

universe u

private noncomputable def quotientBoundary
    {B₀ B₁ : Type u} [AddCommGroup B₀] [AddCommGroup B₁]
    (d : B₁ →+ B₀) (L₀ : AddSubgroup B₀) (L₁ : AddSubgroup B₁)
    (hL : L₁ ≤ L₀.comap d) : B₁ ⧸ L₁ →+ B₀ ⧸ L₀ := by
  apply QuotientAddGroup.lift L₁
    ((QuotientAddGroup.mk' L₀).comp d)
  intro x hx
  exact (QuotientAddGroup.eq_zero_iff _).2 (hL hx)

private theorem quotientBoundary_desc
    {B₀ B₁ : Type u} [AddCommGroup B₀] [AddCommGroup B₁]
    (d : B₁ →+ B₀) (L₀ : AddSubgroup B₀) (L₁ : AddSubgroup B₁)
    (hL : L₁ ≤ L₀.comap d) (x : B₁) :
    quotientBoundary d L₀ L₁ hL (QuotientAddGroup.mk' L₁ x) =
      QuotientAddGroup.mk' L₀ (d x) := rfl

/-- Kernel/range comparison for a differential descending through additive quotients.
The quotient differential's kernel is the quotient of the ambient preimage kernel;
the incoming range is handled by `chainHomologyEquiv` separately. -/
noncomputable def incomingRangeQuotientKernelEquiv
    {B₀ B₁ : Type u} [AddCommGroup B₀] [AddCommGroup B₁]
    (d : B₁ →+ B₀) (L₀ : AddSubgroup B₀) (L₁ : AddSubgroup B₁)
    (hL : L₁ ≤ L₀.comap d) :
    (quotientBoundary d L₀ L₁ hL).ker ≃+
      L₀.comap d ⧸ (L₁.comap (L₀.comap d).subtype) := by
  let Z := L₀.comap d
  let qZ : Z →+ (quotientBoundary d L₀ L₁ hL).ker := {
    toFun := fun z => ⟨QuotientAddGroup.mk' L₁ z.1, by
      rw [AddMonoidHom.mem_ker, quotientBoundary_desc]
      exact (QuotientAddGroup.eq_zero_iff _).2 z.2⟩
    map_zero' := by ext; rfl
    map_add' := by intro x y; ext; rfl }
  have hsurj : Function.Surjective qZ := by
    intro x
    obtain ⟨y, hyq⟩ := QuotientAddGroup.mk'_surjective L₁ x.1
    have hy : d y ∈ L₀ := by
      have hx := x.2
      rw [← hyq] at hx
      change quotientBoundary d L₀ L₁ hL (QuotientAddGroup.mk' L₁ y) = 0 at hx
      rw [quotientBoundary_desc] at hx
      exact (QuotientAddGroup.eq_zero_iff _).mp hx
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    exact hyq
  have hker : qZ.ker = L₁.comap Z.subtype := by
    ext x
    change qZ x = 0 ↔ x.1 ∈ L₁
    constructor
    · intro hx
      have hx' := congrArg Subtype.val hx
      exact (QuotientAddGroup.eq_zero_iff _).mp hx'
    · intro hx
      apply Subtype.ext
      exact (QuotientAddGroup.eq_zero_iff _).mpr hx
  exact ((QuotientAddGroup.quotientAddEquivOfEq hker).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective qZ hsurj)).symm

private noncomputable def incomingQuotientBoundary
    {B₀ B₁ B₂ : Type u} [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    (d₁ : B₁ →+ B₀) (d₂ : B₂ →+ B₁)
    (L₀ : AddSubgroup B₀) (L₁ : AddSubgroup B₁) (L₂ : AddSubgroup B₂)
    (h₁ : L₁ ≤ L₀.comap d₁) (h₂ : L₂ ≤ L₁.comap d₂)
    (hd : ∀ x, d₁ (d₂ x) ∈ L₀) :
    B₂ ⧸ L₂ →+ (quotientBoundary d₁ L₀ L₁ h₁).ker := {
  toFun := fun x => ⟨quotientBoundary d₂ L₁ L₂ h₂ x, by
    induction x using QuotientAddGroup.induction_on with | _ x =>
      change quotientBoundary d₂ L₁ L₂ h₂ (QuotientAddGroup.mk' L₂ x) ∈
        (quotientBoundary d₁ L₀ L₁ h₁).ker
      rw [AddMonoidHom.mem_ker, quotientBoundary_desc, quotientBoundary_desc]
      exact (QuotientAddGroup.eq_zero_iff _).2 (hd x)⟩
  map_zero' := by ext; exact map_zero _
  map_add' := by intro x y; ext; exact map_add _ _ _ }

private theorem incomingQuotientBoundary_desc
    {B₀ B₁ B₂ : Type u} [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    (d₁ : B₁ →+ B₀) (d₂ : B₂ →+ B₁)
    (L₀ : AddSubgroup B₀) (L₁ : AddSubgroup B₁) (L₂ : AddSubgroup B₂)
    (h₁ : L₁ ≤ L₀.comap d₁) (h₂ : L₂ ≤ L₁.comap d₂)
    (hd : ∀ x, d₁ (d₂ x) ∈ L₀) (x : B₂) :
    (incomingQuotientBoundary d₁ d₂ L₀ L₁ L₂ h₁ h₂ hd
      (QuotientAddGroup.mk' L₂ x)).1 = QuotientAddGroup.mk' L₁ (d₂ x) := rfl

/-- The incoming range, pulled back to ambient quotient cycles, consists exactly of
the lower subgroup plus the image of the incoming differential. -/
theorem incomingRange_pullback
    {B₀ B₁ B₂ : Type u} [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    (d₁ : B₁ →+ B₀) (d₂ : B₂ →+ B₁)
    (L₀ : AddSubgroup B₀) (L₁ : AddSubgroup B₁) (L₂ : AddSubgroup B₂)
    (h₁ : L₁ ≤ L₀.comap d₁) (h₂ : L₂ ≤ L₁.comap d₂)
    (hd : ∀ x, d₁ (d₂ x) ∈ L₀) :
    let Z := L₀.comap d₁
    let qZ : Z →+ (quotientBoundary d₁ L₀ L₁ h₁).ker := {
      toFun := fun z => ⟨QuotientAddGroup.mk' L₁ z.1, by
        rw [AddMonoidHom.mem_ker, quotientBoundary_desc]
        exact (QuotientAddGroup.eq_zero_iff _).2 z.2⟩
      map_zero' := by ext; rfl
      map_add' := by intro x y; ext; rfl }
    (incomingQuotientBoundary d₁ d₂ L₀ L₁ L₂ h₁ h₂ hd).range.comap qZ =
      (L₁ ⊔ d₂.range).comap Z.subtype := by
  dsimp
  ext z
  change (∃ y : B₂ ⧸ L₂,
    incomingQuotientBoundary d₁ d₂ L₀ L₁ L₂ h₁ h₂ hd y =
      ⟨QuotientAddGroup.mk' L₁ z.1, _⟩) ↔ z.1 ∈ L₁ ⊔ d₂.range
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L₂ y
    have heq := congrArg Subtype.val hy
    rw [incomingQuotientBoundary_desc] at heq
    have hsub : d₂ x - z.1 ∈ L₁ := (QuotientAddGroup.eq_iff_sub_mem).mp heq
    have hl : z.1 - d₂ x ∈ L₁ := by simpa only [neg_sub] using L₁.neg_mem hsub
    have hr : d₂ x ∈ d₂.range := ⟨x, rfl⟩
    have hs : (z.1 - d₂ x) + d₂ x ∈ L₁ ⊔ d₂.range :=
      AddSubgroup.add_mem_sup hl hr
    simpa only [sub_add_cancel] using hs
  · intro hz
    obtain ⟨l, hl, r, hr, heq⟩ := (AddSubgroup.mem_sup).mp hz
    obtain ⟨x, rfl⟩ := hr
    refine ⟨QuotientAddGroup.mk' L₂ x, ?_⟩
    apply Subtype.ext
    rw [incomingQuotientBoundary_desc]
    apply (QuotientAddGroup.eq_iff_sub_mem).mpr
    have : d₂ x - z.1 = -l := by rw [← heq]; abel
    rw [this]
    exact L₁.neg_mem hl

private noncomputable def quotientByComapEquiv
    {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hf : Function.Surjective f) (S : AddSubgroup B) :
    A ⧸ S.comap f ≃+ B ⧸ S := by
  let g : A →+ B ⧸ S := (QuotientAddGroup.mk' S).comp f
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective S y
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨a, rfl⟩
  have hker : g.ker = S.comap f := by
    ext a
    change QuotientAddGroup.mk' S (f a) = 0 ↔ f a ∈ S
    exact QuotientAddGroup.eq_zero_iff _
  exact (QuotientAddGroup.quotientAddEquivOfEq hker).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective g hg)

/-- Homology of the quotient complex as the quotient of ambient quotient cycles
by the lower subgroup and the incoming image. -/
noncomputable def quotientHomologyEquiv
    {B₀ B₁ B₂ : Type u} [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    (d₁ : B₁ →+ B₀) (d₂ : B₂ →+ B₁)
    (L₀ : AddSubgroup B₀) (L₁ : AddSubgroup B₁) (L₂ : AddSubgroup B₂)
    (h₁ : L₁ ≤ L₀.comap d₁) (h₂ : L₂ ≤ L₁.comap d₂)
    (hd : ∀ x, d₁ (d₂ x) ∈ L₀) :
    let Z := L₀.comap d₁
    Z ⧸ ((L₁ ⊔ d₂.range).comap Z.subtype) ≃+
      (quotientBoundary d₁ L₀ L₁ h₁).ker ⧸
        (incomingQuotientBoundary d₁ d₂ L₀ L₁ L₂ h₁ h₂ hd).range := by
  let Z := L₀.comap d₁
  let qZ : Z →+ (quotientBoundary d₁ L₀ L₁ h₁).ker := {
    toFun := fun z => ⟨QuotientAddGroup.mk' L₁ z.1, by
      rw [AddMonoidHom.mem_ker, quotientBoundary_desc]
      exact (QuotientAddGroup.eq_zero_iff _).2 z.2⟩
    map_zero' := by ext; rfl
    map_add' := by intro x y; ext; rfl }
  have hsurj : Function.Surjective qZ := by
    intro x
    obtain ⟨y, hyq⟩ := QuotientAddGroup.mk'_surjective L₁ x.1
    have hy : d₁ y ∈ L₀ := by
      have hx := x.2
      rw [← hyq] at hx
      change quotientBoundary d₁ L₀ L₁ h₁ (QuotientAddGroup.mk' L₁ y) = 0 at hx
      rw [quotientBoundary_desc] at hx
      exact (QuotientAddGroup.eq_zero_iff _).mp hx
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    exact hyq
  have heq :
      (incomingQuotientBoundary d₁ d₂ L₀ L₁ L₂ h₁ h₂ hd).range.comap qZ =
      (L₁ ⊔ d₂.range).comap Z.subtype := by
    exact incomingRange_pullback d₁ d₂ L₀ L₁ L₂ h₁ h₂ hd
  exact (QuotientAddGroup.quotientAddEquivOfEq heq.symm).trans
    (quotientByComapEquiv qZ hsurj _)

end CurveGenusTwo.Filtration
