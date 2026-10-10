import CurveComplexGenusTwo.Filtration.FiltrationSplittingIntegrated
import CurveComplexGenusTwo.Filtration.DirectSumHomologyLocal
import CurveComplexGenusTwo.Filtration.FiltrationHomology

namespace CurveGenusTwo.Filtration

universe u v

variable {V : Type u} {B : Type v} [DecidableEq V]

section Split

variable [LinearOrder V]

noncomputable def chainsDegreeCast (L : FiniteComplex V) {m n : ℤ} (h : m = n) :
    chains L m ≃+ chains L n := by
  cases h
  exact AddEquiv.refl _

private theorem castSmulHom {A : Type*} [AddCommGroup A]
    (C : ℤ → Type*) [∀ i, AddCommGroup (C i)]
    {m n : ℤ} (h : m = n) (f : A →+ C m) (z : ℤ) :
    cast (congrArg (fun j : ℤ => A →+ C j) h) (z • f) =
      z • cast (congrArg (fun j : ℤ => A →+ C j) h) f := by
  cases h
  rfl

private theorem castCompHom {A : Type*} [AddCommGroup A]
    (C : ℤ → Type*) [∀ i, AddCommGroup (C i)]
    {i j k : ℤ} (hij : i = j) (hjk : j = k) (f : A →+ C i) :
    cast (congrArg (fun t : ℤ => A →+ C t) hjk)
      (cast (congrArg (fun t : ℤ => A →+ C t) hij) f) =
    cast (congrArg (fun t : ℤ => A →+ C t) (hij.trans hjk)) f := by
  cases hij
  cases hjk
  rfl

private theorem castHomApply {A : Type*} [AddCommGroup A]
    (C : ℤ → Type*) [∀ i, AddCommGroup (C i)]
    {m n : ℤ} (h : m = n) (f : A →+ C m) (x : A) :
    (cast (congrArg (fun j : ℤ => A →+ C j) h) f) x =
      cast (congrArg C h) (f x) := by
  cases h
  rfl

private theorem castEqZeroIff (C : ℤ → Type*) [∀ i, AddCommGroup (C i)]
    {m n : ℤ} (h : m = n) (x : C m) :
    cast (congrArg C h) x = 0 ↔ x = 0 := by
  cases h
  rfl

private theorem castHomRange {A : Type*} [AddCommGroup A]
    (C : ℤ → Type*) [∀ i, AddCommGroup (C i)]
    {m n : ℤ} (h : m = n) (f : A →+ C m) :
    (cast (congrArg (fun j : ℤ => A →+ C j) h) f).range =
      cast (congrArg (fun j : ℤ => AddSubgroup (C j)) h) f.range := by
  cases h
  rfl

private theorem boundaryCastRange (L : FiniteComplex V)
    {m k : ℤ} (hm : m = k + 1) (hk : m - 1 = k) :
    (cast (congrArg (fun j : ℤ => chains L m →+ chains L j) hk)
      (boundary L m)).range = boundaries L k := by
  cases hm
  unfold boundaries
  exact castHomRange (chains L) hk (boundary L (k + 1))

noncomputable def relativeHomologyDegreeCast (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) {m n : ℤ} (h : m = n) :
    relativeHomology K a p m ≃+ relativeHomology K a p n := by
  cases h
  exact AddEquiv.refl _

noncomputable def reducedHomologyDegreeCast (L : FiniteComplex V) {m n : ℤ} (h : m = n) :
    reducedHomology L m ≃+ reducedHomology L n := by
  cases h
  exact AddEquiv.refl _

noncomputable def directSumChainsDegreeCast (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) {m n : ℤ} (h : m = n) :
    DirectSum (strata K a p) (fun S => chains (restrictedLink K a S) m) ≃+
      DirectSum (strata K a p) (fun S => chains (restrictedLink K a S) n) := by
  cases h
  exact AddEquiv.refl _

noncomputable def directSumReducedHomologyDegreeCast (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) {m n : ℤ} (h : m = n) :
    DirectSum (strata K a p)
      (fun S => reducedHomology (restrictedLink K a S) m) ≃+
      DirectSum (strata K a p)
        (fun S => reducedHomology (restrictedLink K a S) n) := by
  cases h
  exact AddEquiv.refl _

noncomputable def quotientAddEquiv' {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (SA : AddSubgroup A) (SB : AddSubgroup B)
    (h : ∀ x : A, x ∈ SA ↔ e x ∈ SB) : A ⧸ SA ≃+ B ⧸ SB := by
  let f : A ⧸ SA →+ B ⧸ SB := QuotientAddGroup.lift SA
    ((QuotientAddGroup.mk' SB).comp e.toAddMonoidHom)
    (by intro x hx; exact (QuotientAddGroup.eq_zero_iff (e x)).2 ((h x).mp hx))
  let g : B ⧸ SB →+ A ⧸ SA := QuotientAddGroup.lift SB
    ((QuotientAddGroup.mk' SA).comp e.symm.toAddMonoidHom)
    (by
      intro y hy
      change QuotientAddGroup.mk' SA (e.symm y) = 0
      exact (QuotientAddGroup.eq_zero_iff (e.symm y)).2
        ((h (e.symm y)).mpr (by simpa using hy)))
  refine { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_, map_add' := f.map_add }
  · intro x; induction x using QuotientAddGroup.induction_on with | _ x =>
      change QuotientAddGroup.mk' SA (e.symm (e x)) = QuotientAddGroup.mk' SA x
      rw [e.symm_apply_apply]
  · intro y; induction y using QuotientAddGroup.induction_on with | _ y =>
      change QuotientAddGroup.mk' SB (e (e.symm y)) = QuotientAddGroup.mk' SB y
      rw [e.apply_symm_apply]

noncomputable def chainHomologyEquiv' {A₀ A₁ A₂ B₀ B₁ B₂ : Type u}
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    (dA : A₁ →+ A₀) (uA : A₂ →+ A₁)
    (dB : B₁ →+ B₀) (uB : B₂ →+ B₁)
    (e₀ : A₀ ≃+ B₀) (e₁ : A₁ ≃+ B₁) (e₂ : A₂ ≃+ B₂)
    (hd : ∀ x, e₀ (dA x) = dB (e₁ x))
    (hu : ∀ x, e₁ (uA x) = uB (e₂ x)) :
    dA.ker ⧸ (uA.range.comap dA.ker.subtype) ≃+
      dB.ker ⧸ (uB.range.comap dB.ker.subtype) := by
  let ec : dA.ker ≃+ dB.ker := {
    toFun := fun x => ⟨e₁ x.1, by
      have hx : dA x.1 = 0 := x.2
      have hh := hd x.1
      rw [hx, map_zero] at hh
      exact hh.symm⟩
    invFun := fun y => ⟨e₁.symm y.1, by
      apply e₀.injective
      rw [hd, map_zero]
      have hy : dB y.1 = 0 := y.2
      simpa only [e₁.apply_symm_apply] using hy⟩
    left_inv := fun x => Subtype.ext (e₁.symm_apply_apply x.1)
    right_inv := fun y => Subtype.ext (e₁.apply_symm_apply y.1)
    map_add' := fun x y => Subtype.ext (e₁.map_add x.1 y.1) }
  apply quotientAddEquiv' ec _ _
  intro x
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e₂ y, ?_⟩
    change uB (e₂ y) = e₁ x.1
    rw [← hu y]
    change uA y = x.1 at hy
    exact congrArg e₁ hy
  · rintro ⟨y, hy⟩
    refine ⟨e₂.symm y, ?_⟩
    apply e₁.injective
    rw [hu, e₂.apply_symm_apply]
    exact hy

private theorem directSumMapCastApply (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ)
    {m : ℤ} (h : m = n)
    (f : ∀ S : strata K a p,
      chains (restrictedLink K a S) ((n + 1) - p) →+
      chains (restrictedLink K a S) (m - p))
    (x : DirectSum (strata K a p)
      (fun S => chains (restrictedLink K a S) ((n + 1) - p))) :
    (cast (congrArg (fun j : ℤ =>
      DirectSum (strata K a p)
        (fun S => chains (restrictedLink K a S) ((n + 1) - p)) →+
      DirectSum (strata K a p)
        (fun S => chains (restrictedLink K a S) (j - p))) h)
      (DirectSum.map f)) x =
    DirectSum.map (fun S =>
      cast (congrArg (fun j : ℤ =>
        chains (restrictedLink K a S) ((n + 1) - p) →+
          chains (restrictedLink K a S) (j - p)) h) (f S)) x := by
  classical
  cases h
  rfl

theorem firstPage_split (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) (q : ℤ) :
    Nonempty (firstPage K a p q ≃+
      DirectSum (strata K a p)
        (fun S => reducedHomology (restrictedLink K a S) q)) := by
  obtain ⟨es, hes⟩ := relativeChains_split K a p
  let n : ℤ := (p : ℤ) + q
  let d : ∀ S : strata K a p,
      chains (restrictedLink K a S) (n - p) →+
        chains (restrictedLink K a S) ((n - 1) - p) := fun S => by
    have hn : n - (p : ℤ) - 1 = (n - 1) - p := by omega
    exact ((-1 : ℤ) ^ p) •
      (cast (congrArg (fun j : ℤ =>
        chains (restrictedLink K a S) (n - p) →+
          chains (restrictedLink K a S) j) hn)
        (boundary (restrictedLink K a S) (n - p)))
  let u0 : ∀ S : strata K a p,
      chains (restrictedLink K a S) ((n + 1) - p) →+
        chains (restrictedLink K a S) ((n + 1 - 1) - p) := fun S => by
    have hn : (n + 1) - (p : ℤ) - 1 = (n + 1 - 1) - p := by omega
    exact ((-1 : ℤ) ^ p) •
      (cast (congrArg (fun j : ℤ =>
        chains (restrictedLink K a S) ((n + 1) - p) →+
          chains (restrictedLink K a S) j) hn)
        (boundary (restrictedLink K a S) ((n + 1) - p)))
  let hcast : n + 1 - 1 = n := by omega
  let u : ∀ S : strata K a p,
      chains (restrictedLink K a S) ((n + 1) - p) →+
        chains (restrictedLink K a S) (n - p) := fun S =>
    cast (congrArg (fun j : ℤ =>
      chains (restrictedLink K a S) ((n + 1) - p) →+
        chains (restrictedLink K a S) (j - p)) hcast) (u0 S)
  let D := DirectSum.map d
  let U := DirectSum.map u
  let ec := directSumHomologyEquiv
    (fun S : strata K a p => chains (restrictedLink K a S) (n - p))
    (fun S : strata K a p => chains (restrictedLink K a S) ((n - 1) - p))
    (fun S : strata K a p => chains (restrictedLink K a S) ((n + 1) - p)) d u
  let hn : n - 1 = (n - 1) := rfl
  have hd : ∀ x : relativeChains K a p n,
      es (n - 1) (relativeBoundary K a p n x) =
        D (es n x) := by
    intro x
    simpa [D, d] using hes n x
  let uA : relativeChains K a p (n + 1) →+
      relativeChains K a p n :=
    cast (congrArg (fun j : ℤ => relativeChains K a p (n + 1) →+
      relativeChains K a p j) hcast)
      (relativeBoundary K a p (n + 1))
  have transport (m k : ℤ) (hmk : m = k)
      (fA : relativeChains K a p (n + 1) →+ relativeChains K a p m)
      (fB : DirectSum (strata K a p)
        (fun S => chains (restrictedLink K a S) ((n + 1) - p)) →+
        DirectSum (strata K a p)
        (fun S => chains (restrictedLink K a S) (m - p)))
      (x : relativeChains K a p (n + 1))
      (hc : es m (fA x) = fB (es (n + 1) x)) :
      es k ((cast (congrArg (fun j : ℤ =>
        relativeChains K a p (n + 1) →+ relativeChains K a p j) hmk) fA) x) =
      (cast (congrArg (fun j : ℤ => DirectSum (strata K a p)
        (fun S => chains (restrictedLink K a S) (n + 1 - p)) →+
        DirectSum (strata K a p)
        (fun S => chains (restrictedLink K a S) (j - p))) hmk) fB)
        (es (n + 1) x) := by
    cases hmk
    exact hc
  have hnext : ∀ x : relativeChains K a p (n + 1),
      es n (uA x) =
        U (es (n + 1) x) := by
    intro x
    have ht := transport (n + 1 - 1) n hcast
      (relativeBoundary K a p (n + 1)) (DirectSum.map u0) x
      (by simpa [u0] using hes (n + 1) x)
    have hmap :
        (cast (congrArg (fun j : ℤ =>
          DirectSum (strata K a p)
            (fun S => chains (restrictedLink K a S) ((n + 1) - p)) →+
          DirectSum (strata K a p)
            (fun S => chains (restrictedLink K a S) (j - p))) hcast)
          (DirectSum.map u0)) (es (n + 1) x) =
          (DirectSum.map u) (es (n + 1) x) := by
      simpa only [u] using
        (directSumMapCastApply K a p n (show n + 1 - 1 = n by omega)
          u0 (es (n + 1) x))
    exact ht.trans hmap
  have hh := chainHomologyEquiv'
    (relativeBoundary K a p n)
    uA
    D U
    (es (n - 1)) (es n) (es (n + 1)) hd hnext
  have hrA : uA.range = relativeBoundaries K a p n := by
    unfold uA relativeBoundaries
    have h : ∀ {m k : ℤ} (hmk : m = k)
        (f : relativeChains K a p (n + 1) →+ relativeChains K a p m),
        (cast (congrArg (fun j : ℤ =>
          relativeChains K a p (n + 1) →+ relativeChains K a p j) hmk) f).range =
        cast (congrArg (fun j : ℤ => AddSubgroup (relativeChains K a p j)) hmk)
          f.range := by
      intro m k hmk f
      cases hmk
      rfl
    exact h hcast (relativeBoundary K a p (n + 1))
  rw [hrA] at hh
  have hdeg : n - (p : ℤ) = q := by dsimp [n]; omega
  let compCast : DirectSum (strata K a p)
      (fun S => reducedHomology (restrictedLink K a S) (n - p)) ≃+
      DirectSum (strata K a p)
        (fun S => reducedHomology (restrictedLink K a S) q) :=
    directSumReducedHomologyDegreeCast K a p hdeg
  have hsign : (-1 : ℤ) ^ p = 1 ∨ (-1 : ℤ) ^ p = -1 := neg_one_pow_eq_or ℤ p
  let componentEquiv (S : strata K a p) :
      (d S).ker ⧸ ((u S).range.comap (d S).ker.subtype) ≃+
        reducedHomology (restrictedLink K a S) (n - p) := by
    let L := restrictedLink K a S
    let d0 : chains L (n - p) →+ chains L ((n - 1) - p) := by
      have hj : n - (p : ℤ) - 1 = (n - 1) - p := by omega
      exact cast (congrArg (fun j : ℤ => chains L (n - p) →+ chains L j) hj)
        (boundary L (n - p))
    let u0 : chains L ((n + 1) - p) →+ chains L (n - p) := by
      have hj : (n + 1) - (p : ℤ) - 1 = n - p := by omega
      exact cast (congrArg (fun j : ℤ => chains L ((n + 1) - p) →+ chains L j) hj)
        (boundary L ((n + 1) - p))
    have hd0 : d S = ((-1 : ℤ) ^ p) • d0 := by rfl
    have hu0 : u S = ((-1 : ℤ) ^ p) • u0 := by
      dsimp [u, u0, u0]
      rw [castSmulHom]
      rw [castCompHom]
      all_goals omega
    rw [hd0, hu0]
    let he := smulPmOneHomologyEquiv d0 u0 ((-1 : ℤ) ^ p) hsign
    have hdRange : u0.range = boundaries L (n - p) := by
      dsimp [u0]
      exact boundaryCastRange L
        (show (n + 1) - (p : ℤ) = (n - p) + 1 by omega)
        (show (n + 1) - (p : ℤ) - 1 = n - p by omega)
    rw [hdRange] at he
    have hdKer : d0.ker = cycles L (n - p) := by
      ext x
      change d0 x = 0 ↔ boundary L (n - p) x = 0
      dsimp [d0]
      have hj : n - (p : ℤ) - 1 = (n - 1) - p := by omega
      rw [castHomApply]
      exact castEqZeroIff (chains L) hj _
      all_goals omega
    rw [hdKer] at he
    exact he
  exact ⟨hh.trans (ec.trans (DirectSum.congrAddEquiv componentEquiv |>.trans compCast))⟩

end Split

end CurveGenusTwo.Filtration

#print axioms CurveGenusTwo.Filtration.firstPage_split
