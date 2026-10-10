import CurveComplexGenusTwo.Filtration.IncomingRange
import CurveComplexGenusTwo.Filtration.SpectralCyclesTransport

namespace CurveGenusTwo.Filtration

universe u v
variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

private theorem cast_comp_range_local {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A D : Type*} [AddCommGroup A] [AddCommGroup D]
    (f : A →+ F i) (g : D →+ A) :
    Eq.mp (congrArg (fun k => AddSubgroup (F k)) h) (f.comp g).range =
      ((Eq.mp (congrArg (fun k => A →+ F k) h) f).comp g).range := by
  cases h
  rfl

private theorem cast_map_apply_local {ι : Type*} {F G : ι → Type*}
    [∀ i, AddCommGroup (F i)] [∀ i, AddCommGroup (G i)]
    {i j : ι} (h : i = j)
    (f : (k : ι) → F k →+ G k) (x : F i) :
    Eq.mp (congrArg G h) (f i x) =
      f j (Eq.mp (congrArg F h) x) := by
  cases h
  rfl

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

omit [LinearOrder V] in
private theorem filteredInclusion_injective (K : FiniteComplex V)
    (a : ArcLabels V B) (p n : ℤ) :
    Function.Injective (chainInclusion (filtration K a p) K
      (by intro σ hσ; exact hσ.1) n) := by
  let f : SimplexAt (filtration K a p) n → SimplexAt K n :=
    fun σ => ⟨σ.1, σ.2.1.1, σ.2.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : SimplexAt K n => z.1) hxy
  exact freeAbelian_lift_injective_local f hf

theorem spectralCycles_zero_eq_filteredChains (K : FiniteComplex V)
    (a : ArcLabels V B) (p n : ℤ) :
    spectralCycles K a 0 p n = filteredChains K a p n := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    obtain ⟨c, rfl⟩ := hx
    refine ⟨⟨c, rfl⟩, ?_⟩
    change boundary K n
        (chainInclusion (filtration K a p) K
          (by intro σ hσ; exact hσ.1) n c) ∈ filteredChains K a (p - 0) (n - 1)
    rw [sub_zero]
    have hnat := congrArg (fun f => f c)
      (chainInclusion_boundary (filtration K a p) K
        (by intro σ hσ; exact hσ.1) n)
    rw [show boundary K n
        (chainInclusion (filtration K a p) K
          (by intro σ hσ; exact hσ.1) n c) =
        chainInclusion (filtration K a p) K
          (by intro σ hσ; exact hσ.1) (n - 1)
          (boundary (filtration K a p) n c) by
          simpa only [AddMonoidHom.comp_apply] using hnat]
    exact ⟨boundary (filtration K a p) n c, rfl⟩

/-- At page one, the null-chain subgroup is lower filtration together with
the incoming ambient boundary from all chains in filtration level `p`.
The source definition transports this range from degree `n + 1` to `n`;
the cast-normalized form makes that transport explicit. -/
theorem spectralNullChains_pageOne_cast_normal_form
    (K : FiniteComplex V) (a : ArcLabels V B) (p n : ℤ) :
    spectralNullChains K a 1 p n =
      filteredChainsCast K a (p - 1) n ⊔
        ((boundaryNextCast K n).comp
          (filteredChainsCast K a p (n + 1)).subtype).range := by
  rw [← spectralNullChainsCast_eq_original]
  rw [spectralNullChainsCast_eq_source]
  have hcycles :
      filteredCyclesCast K a 0 p (n + 1) =
        filteredChainsCast K a p (n + 1) := by
    rw [filteredCyclesCast_eq_original, spectralCycles_zero_eq_filteredChains]
    rfl
  rw [show (1 : ℤ) - 1 = 0 by norm_num,
    show p + 1 - 1 = p by omega, hcycles]
  rw [show boundaryNextCast K n =
      Eq.mp (congrArg (fun m : ℤ => chains K (n + 1) →+ chains K m)
        (show n + 1 - 1 = n by omega)) (boundary K (n + 1)) by rfl]
  exact congrArg (fun H : AddSubgroup (chains K n) =>
    filteredChainsCast K a (p - 1) n ⊔ H)
    (cast_comp_range_local (F := fun m : ℤ => chains K m)
      (show n + 1 - 1 = n by omega) (boundary K (n + 1))
      (filteredChainsCast K a p (n + 1)).subtype)

/-- Inclusion commutes with the cast-normalized boundary at signed degree `n`. -/
theorem filteredBoundary_inclusion_cast (K : FiniteComplex V)
    (a : ArcLabels V B) (p n : ℤ)
    (x : chains (filtration K a p) (n + 1)) :
    boundaryNextCast K n
      (chainInclusion (filtration K a p) K
        (by intro σ hσ; exact hσ.1) (n + 1) x) =
    chainInclusion (filtration K a p) K
      (by intro σ hσ; exact hσ.1) n
      (boundaryNextCast (filtration K a p) n x) := by
  have hnat := congrArg (fun f => f x)
    (chainInclusion_boundary (filtration K a p) K
      (by intro σ hσ; exact hσ.1) (n + 1))
  simp only [AddMonoidHom.comp_apply] at hnat
  rw [boundaryNextCast_apply, hnat,
    cast_map_apply_local (show n + 1 - 1 = n by omega) (fun m =>
      chainInclusion (filtration K a p) K
        (by intro σ hσ; exact hσ.1) m)]
  congr 1
  exact (boundaryNextCast_apply (filtration K a p) n x).symm

/-- The incoming filtered boundary, embedded in ambient chains, is exactly
the boundary summand of `spectralNullChains` on page one. -/
theorem filteredIncoming_range_eq_pageOne_boundaryPart
    (K : FiniteComplex V) (a : ArcLabels V B) (p n : ℤ) :
    ((chainInclusion (filtration K a p) K
      (by intro σ hσ; exact hσ.1) n).comp
      (boundaryNextCast (filtration K a p) n)).range =
    ((boundaryNextCast K n).comp
      (spectralCycles K a 0 p (n + 1)).subtype).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    let z : spectralCycles K a 0 p (n + 1) :=
      ⟨chainInclusion (filtration K a p) K
        (by intro σ hσ; exact hσ.1) (n + 1) y, by
          rw [spectralCycles_zero_eq_filteredChains]
          exact ⟨y, rfl⟩⟩
    exact ⟨z, filteredBoundary_inclusion_cast K a p n y⟩
  · rintro ⟨z, rfl⟩
    have hz : z.1 ∈ filteredChains K a p (n + 1) := by
      rw [← spectralCycles_zero_eq_filteredChains]
      exact z.2
    obtain ⟨y, hy⟩ := hz
    refine ⟨y, ?_⟩
    change chainInclusion (filtration K a p) K
        (by intro σ hσ; exact hσ.1) n
        (boundaryNextCast (filtration K a p) n y) =
      boundaryNextCast K n z.1
    rw [← hy]
    exact (filteredBoundary_inclusion_cast K a p n y).symm

/-- The concrete page-one null-chain subgroup is exactly the join of the
embedded lower-filtration chain range and the embedded incoming boundary
range. This is the denominator produced by `incomingRange_pullback`. -/
theorem spectralNullChains_pageOne_eq_filteredIncoming
    (K : FiniteComplex V) (a : ArcLabels V B) (p n : ℤ) :
    spectralNullChains K a 1 p n =
      ((chainInclusion (filtration K a p) K
        (by intro σ hσ; exact hσ.1) n).comp
        (chainInclusion (filtration K a (p - 1)) (filtration K a p)
          (filtration_mono K a (by omega)) n)).range ⊔
      ((chainInclusion (filtration K a p) K
        (by intro σ hσ; exact hσ.1) n).comp
        (boundaryNextCast (filtration K a p) n)).range := by
  have hlow :
      ((chainInclusion (filtration K a p) K
        (by intro σ hσ; exact hσ.1) n).comp
        (chainInclusion (filtration K a (p - 1)) (filtration K a p)
          (filtration_mono K a (by omega)) n)).range =
      filteredChains K a (p - 1) n := by
    change (((chainInclusion (filtration K a p) K
        (by intro σ hσ; exact hσ.1) n).comp
        (chainInclusion (filtration K a (p - 1)) (filtration K a p)
          (filtration_mono K a (by omega)) n)).range) =
      (chainInclusion (filtration K a (p - 1)) K
        (by intro σ hσ; exact hσ.1) n).range
    congr 1
    apply FreeAbelianGroup.lift_ext
    intro σ
    rfl
  rw [spectralNullChains_pageOne_cast_normal_form,
    filteredChainsCast_eq_original]
  rw [← hlow]
  congr 1
  rw [filteredChainsCast_eq_original,
    ← spectralCycles_zero_eq_filteredChains]
  exact (filteredIncoming_range_eq_pageOne_boundaryPart K a p n).symm

/-- The denominator in the generic incoming-range packet is reflected by the
ambient inclusion, with all signed indices and dependent boundary casts made
explicit. -/
theorem filteredIncoming_sup_mem_iff_spectralNullChains
    (K : FiniteComplex V) (a : ArcLabels V B) (p n : ℤ)
    (c : chains (filtration K a p) n) :
    c ∈ (chainInclusion (filtration K a (p - 1)) (filtration K a p)
          (filtration_mono K a (by omega)) n).range ⊔
        (boundaryNextCast (filtration K a p) n).range ↔
      chainInclusion (filtration K a p) K
        (by intro σ hσ; exact hσ.1) n c ∈
        spectralNullChains K a 1 p n := by
  let i := chainInclusion (filtration K a (p - 1)) (filtration K a p)
    (filtration_mono K a (by omega)) n
  let j := chainInclusion (filtration K a p) K
    (by intro σ hσ; exact hσ.1) n
  let d := boundaryNextCast (filtration K a p) n
  rw [spectralNullChains_pageOne_eq_filteredIncoming]
  change c ∈ i.range ⊔ d.range ↔ j c ∈ (j.comp i).range ⊔ (j.comp d).range
  constructor
  · intro hc
    obtain ⟨l, ⟨y, rfl⟩, r, ⟨z, rfl⟩, heq⟩ :=
      (AddSubgroup.mem_sup).mp hc
    apply (AddSubgroup.mem_sup).mpr
    refine ⟨j (i y), ⟨y, rfl⟩, j (d z), ⟨z, rfl⟩, ?_⟩
    rw [← map_add, heq]
  · intro hc
    obtain ⟨l, ⟨y, rfl⟩, r, ⟨z, rfl⟩, heq⟩ :=
      (AddSubgroup.mem_sup).mp hc
    apply (AddSubgroup.mem_sup).mpr
    refine ⟨i y, ⟨y, rfl⟩, d z, ⟨z, rfl⟩, ?_⟩
    apply filteredInclusion_injective K a p n
    rw [map_add]
    exact heq

/-- Exact denominator comparison for the signed adjacent quotient at bidegree
`(p,q)`. The left subgroup is the pullback computed by
`incomingRange_pullback`; the right is the concrete `E₁` denominator, pulled
back along the cycle transport from `SpectralCyclesTransport`. -/
theorem filteredIncoming_denominator_comap_eq_spectralNullChains
    (K : FiniteComplex V) (a : ArcLabels V B) (p q : ℤ) :
    let n := p + q
    let L₀ := (chainInclusion (filtration K a (p - 1)) (filtration K a p)
      (filtration_mono K a (by omega)) (n - 1)).range
    let L₁ := (chainInclusion (filtration K a (p - 1)) (filtration K a p)
      (filtration_mono K a (by omega)) n).range
    let d := boundary (filtration K a p) n
    let u := boundaryNextCast (filtration K a p) n
    let Z := L₀.comap d
    let j := chainInclusion (filtration K a p) K
      (by intro σ hσ; exact hσ.1) n
    let e : Z →+ spectralCycles K a 1 p n :=
      (j.comp Z.subtype).codRestrict (spectralCycles K a 1 p n) (by
        intro z
        exact (Signed.filteredPreimage_eq_spectralCycles_comap K a p q).le z.2)
    (L₁ ⊔ u.range).comap Z.subtype =
      ((spectralNullChains K a 1 p n).comap
        (spectralCycles K a 1 p n).subtype).comap e := by
  dsimp
  ext z
  change z.1 ∈
      (chainInclusion (filtration K a (p - 1)) (filtration K a p)
        (filtration_mono K a (by omega)) (p + q)).range ⊔
      (boundaryNextCast (filtration K a p) (p + q)).range ↔
    chainInclusion (filtration K a p) K
      (by intro σ hσ; exact hσ.1) (p + q) z.1 ∈
      spectralNullChains K a 1 p (p + q)
  exact filteredIncoming_sup_mem_iff_spectralNullChains K a p (p + q) z.1

end CurveGenusTwo.Filtration
