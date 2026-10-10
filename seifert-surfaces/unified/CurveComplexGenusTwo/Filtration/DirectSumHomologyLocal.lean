import Mathlib

namespace CurveGenusTwo.Filtration

universe u v

variable {ι : Type u} [DecidableEq ι]

private noncomputable def quotientAddEquiv
    {A B : Type v} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (SA : AddSubgroup A) (SB : AddSubgroup B)
    (h : ∀ x : A, x ∈ SA ↔ e x ∈ SB) :
    A ⧸ SA ≃+ B ⧸ SB := by
  let f : A ⧸ SA →+ B ⧸ SB :=
    QuotientAddGroup.lift SA
      ((QuotientAddGroup.mk' SB).comp e.toAddMonoidHom)
      (by
        intro x hx
        change QuotientAddGroup.mk' SB (e x) = 0
        exact (QuotientAddGroup.eq_zero_iff (e x)).2 ((h x).mp hx))
  let g : B ⧸ SB →+ A ⧸ SA :=
    QuotientAddGroup.lift SB
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
      change QuotientAddGroup.mk' SB (e (e.symm y)) =
        QuotientAddGroup.mk' SB y
      rw [e.apply_symm_apply]

/-- Quotienting a direct sum by the direct sum of subgroups acts componentwise. -/
noncomputable def directSumQuotientEquiv
    (G : ι → Type v) [∀ i, AddCommGroup (G i)]
    (S : ∀ i, AddSubgroup (G i)) :
    (DirectSum ι G) ⧸ (DirectSum.map (fun i => (S i).subtype)).range ≃+
      DirectSum ι (fun i => G i ⧸ S i) := by
  let q : DirectSum ι G →+ DirectSum ι (fun i => G i ⧸ S i) :=
    DirectSum.map (fun i => QuotientAddGroup.mk' (S i))
  have hsurj : Function.Surjective q := by
    exact (DirectSum.map_surjective _).2
      (fun i => QuotientAddGroup.mk'_surjective (S i))
  have hker : q.ker = (DirectSum.map (fun i => (S i).subtype)).range := by
    rw [DirectSum.ker_map, DirectSum.range_map]
    simp only [QuotientAddGroup.ker_mk', AddSubgroup.range_subtype]
  let e : (DirectSum ι G) ⧸ (DirectSum.map (fun i => (S i).subtype)).range ≃+
      (DirectSum ι G) ⧸ q.ker :=
    QuotientAddGroup.quotientAddEquivOfEq hker.symm
  exact e.trans (QuotientAddGroup.quotientKerEquivOfSurjective q hsurj)

/-- The kernel of a componentwise map is the direct sum of the kernels. -/
noncomputable def directSumKernelEquiv
    (A B : ι → Type v) [∀ i, AddCommGroup (A i)]
    [∀ i, AddCommGroup (B i)]
    (f : ∀ i, A i →+ B i) :
    DirectSum ι (fun i => (f i).ker) ≃+ (DirectSum.map f).ker := by
  let m : DirectSum ι (fun i => (f i).ker) →+ DirectSum ι A :=
    DirectSum.map (fun i => (f i).ker.subtype)
  have hrange : m.range = (DirectSum.map f).ker := by
    rw [DirectSum.range_map, DirectSum.ker_map]
    simp only [AddSubgroup.range_subtype]
  let mc : DirectSum ι (fun i => (f i).ker) →+ (DirectSum.map f).ker :=
    m.codRestrict _ (fun x => by
      rw [← hrange]
      exact ⟨x, rfl⟩)
  have hinj : Function.Injective mc := by
    intro x y hxy
    apply (DirectSum.map_injective _).2 (fun i => (f i).ker.subtype_injective)
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective mc := by
    intro y
    have hy : y.1 ∈ m.range := hrange.symm ▸ y.2
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    exact Subtype.ext hx
  exact AddEquiv.ofBijective mc ⟨hinj, hsurj⟩

/-- Homology of a componentwise chain pair is the direct sum of component
homologies. The quotient uses incoming boundaries intersected with cycles,
so the statement remains meaningful before imposing `d ∘ u = 0`. -/
noncomputable def directSumHomologyEquiv
    (A B C : ι → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, AddCommGroup (C i)]
    (d : ∀ i, A i →+ B i) (u : ∀ i, C i →+ A i) :
    (DirectSum.map d).ker ⧸
      ((DirectSum.map u).range.comap (DirectSum.map d).ker.subtype) ≃+
    DirectSum ι (fun i => (d i).ker ⧸
      ((u i).range.comap (d i).ker.subtype)) := by
  let S (i : ι) := (u i).range.comap (d i).ker.subtype
  let e := directSumKernelEquiv A B d
  let T := (DirectSum.map (fun i => (S i).subtype)).range
  let U := (DirectSum.map u).range.comap (DirectSum.map d).ker.subtype
  have hmem (x : DirectSum ι (fun i => (d i).ker)) :
      x ∈ T ↔ e x ∈ U := by
    simp only [T, U, S]
    rw [DirectSum.range_map, DirectSum.range_map]
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ,
      true_implies, DirectSum.coeFnAddMonoidHom_apply,
      AddSubgroup.range_subtype]
    have he (i : ι) : ((e x).1) i = (x i).1 := by
      rfl
    change (∀ i, (x i).1 ∈ (u i).range) ↔
      ∀ i, ((e x).1) i ∈ (u i).range
    simp only [he]
  exact (quotientAddEquiv e T U hmem).symm.trans
    (directSumQuotientEquiv (fun i => (d i).ker) S)

#print axioms directSumQuotientEquiv
#print axioms directSumKernelEquiv
#print axioms directSumHomologyEquiv

private theorem smul_pm_one_ker_eq
    {A B : Type v} [AddCommGroup A] [AddCommGroup B]
    (d : A →+ B) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    (ε • d).ker = d.ker := by
  rcases hε with rfl | rfl <;> simp [AddSubgroup.ext_iff]

private theorem smul_pm_one_range_eq
    {A B : Type v} [AddCommGroup A] [AddCommGroup B]
    (d : A →+ B) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    (ε • d).range = d.range := by
  rcases hε with rfl | rfl
  · ext x
    simp only [one_smul]
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      simp
    · rintro _ ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      simp

/-- Multiplying both differentials of a chain pair by the same sign `±1`
does not change its additive homology quotient. -/
noncomputable def smulPmOneHomologyEquiv
    {A₀ A₁ A₂ : Type v} [AddCommGroup A₀] [AddCommGroup A₁]
    [AddCommGroup A₂] (d : A₁ →+ A₀) (u : A₂ →+ A₁)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    (ε • d).ker ⧸ ((ε • u).range.comap (ε • d).ker.subtype) ≃+
      d.ker ⧸ (u.range.comap d.ker.subtype) := by
  let hker := smul_pm_one_ker_eq d ε hε
  let hrange := smul_pm_one_range_eq u ε hε
  let e : (ε • d).ker ≃+ d.ker := {
    toFun := fun x => ⟨x.1, by simpa only [hker] using x.2⟩
    invFun := fun x => ⟨x.1, by simpa only [hker] using x.2⟩
    left_inv := fun x => rfl
    right_inv := fun x => rfl
    map_add' := fun x y => rfl }
  apply quotientAddEquiv e _ _
  intro x
  simp only [AddSubgroup.mem_comap, hrange]
  change x.1 ∈ u.range ↔ x.1 ∈ u.range
  rfl

#print axioms smulPmOneHomologyEquiv

end CurveGenusTwo.Filtration
