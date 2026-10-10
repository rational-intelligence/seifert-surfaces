import CurveComplexGenusTwo.Filtration.FinalAbutment

namespace CurveGenusTwo.Filtration

universe u v
variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

private theorem cast_mem_spectralCycles (K : FiniteComplex V)
    (a : ArcLabels V B) (r p : ℤ) {i j : ℤ}
    (h : i = j) (x : chains K j)
    (hx : x ∈ spectralCycles K a r p j) :
    (h.symm ▸ x) ∈ spectralCycles K a r p i := by
  cases h
  exact hx

private theorem cast_boundary (K : FiniteComplex V)
    {i j : ℤ} (h : i = j) (x : chains K j) :
    Eq.mp (congrArg (chains K) (show i - 1 = j - 1 by omega))
      (boundary K i (h.symm ▸ x)) = boundary K j x := by
  cases h
  rfl

theorem boundary_mem_spectralCycles (K : FiniteComplex V) (a : ArcLabels V B)
    (r p n : ℤ) (x : spectralCycles K a r p n) :
    boundary K n x.1 ∈ spectralCycles K a r (p - r) (n - 1) := by
  constructor
  · exact x.2.2
  · change boundary K (n - 1) (boundary K n x.1) ∈
      filteredChains K a (p - r - r) (n - 1 - 1)
    have hb := congrArg (fun f => f x.1) (boundary_boundary K n)
    have hb' : boundary K (n - 1) (boundary K n x.1) = 0 := by
      simpa only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] using hb
    exact hb' ▸
      (AddSubgroup.zero_mem (filteredChains K a (p - r - r) (n - 1 - 1)))

noncomputable def spectralCycleBoundary (K : FiniteComplex V)
    (a : ArcLabels V B) (r p n : ℤ) :
    spectralCycles K a r p n →+
      spectralCycles K a r (p - r) (n - 1) :=
  ((boundary K n).comp (spectralCycles K a r p n).subtype).codRestrict
    (spectralCycles K a r (p - r) (n - 1))
    (boundary_mem_spectralCycles K a r p n)

theorem spectralNullChains_mem_iff (K : FiniteComplex V)
    (a : ArcLabels V B) (r p n : ℤ) (x : chains K n) :
    x ∈ spectralNullChains K a r p n ↔
      ∃ y : chains K n, y ∈ filteredChains K a (p - 1) n ∧
        ∃ z : spectralCycles K a (r - 1) (p + r - 1) (n + 1),
          y + boundaryNextCast K n z.1 = x := by
  rw [← spectralNullChainsCast_eq_original]
  change x ∈ filteredChains K a (p - 1) n ⊔
    ((boundaryNextCast K n).comp
      (spectralCycles K a (r - 1) (p + r - 1) (n + 1)).subtype).range ↔ _
  constructor
  · intro hx
    obtain ⟨y, hy, w, hw, heq⟩ := (AddSubgroup.mem_sup).mp hx
    obtain ⟨z, rfl⟩ := hw
    exact ⟨y, hy, z, heq⟩
  · rintro ⟨y, hy, z, heq⟩
    apply (AddSubgroup.mem_sup).mpr
    exact ⟨y, hy, boundaryNextCast K n z.1, ⟨z, rfl⟩, heq⟩

private theorem incoming_boundary_null (K : FiniteComplex V)
    (a : ArcLabels V B) (r p n : ℤ)
    (y : spectralCycles K a (r - 1) (p - 1) n) :
    boundary K n y.1 ∈ spectralNullChains K a r (p - r) (n - 1) := by
  have hdeg : n - 1 + 1 = n := by omega
  have hparam : p - r + r - 1 = p - 1 := by omega
  let z : spectralCycles K a (r - 1) ((p - r) + r - 1) ((n - 1) + 1) :=
    ⟨hdeg.symm ▸ y.1, by
      simpa only [hparam] using
        cast_mem_spectralCycles K a (r - 1) (p - 1) hdeg y.1 y.2⟩
  apply (spectralNullChains_mem_iff K a r (p - r) (n - 1)
    (boundary K n y.1)).mpr
  refine ⟨0, AddSubgroup.zero_mem _, z, ?_⟩
  simp only [zero_add]
  rw [boundaryNextCast_apply]
  exact cast_boundary K hdeg y.1

theorem spectralCycleBoundary_null (K : FiniteComplex V)
    (a : ArcLabels V B) (r p n : ℤ)
    (x : spectralCycles K a r p n)
    (hx : x.1 ∈ spectralNullChains K a r p n) :
    (spectralCycleBoundary K a r p n x).1 ∈
      spectralNullChains K a r (p - r) (n - 1) := by
  obtain ⟨y, hy, z, heq⟩ :=
    (spectralNullChains_mem_iff K a r p n x.1).mp hx
  have hzin : boundaryNextCast K n z.1 ∈
      ((boundaryNextCast K n).comp
        (filteredCyclesCast K a (r - 1) (p + r - 1) (n + 1)).subtype).range :=
    ⟨z, rfl⟩
  have hzcy := spectralNullChainsCast_boundary_part_le_cycles K a r p n hzin
  have hzero : boundary K n (boundaryNextCast K n z.1) = 0 := hzcy
  have hby : boundary K n y ∈ filteredChains K a (p - r) (n - 1) := by
    have hbx := x.2.2
    change boundary K n x.1 ∈ filteredChains K a (p - r) (n - 1) at hbx
    rw [← heq, map_add, hzero, add_zero] at hbx
    exact hbx
  have hyc : y ∈ spectralCycles K a (r - 1) (p - 1) n := by
    refine ⟨hy, ?_⟩
    change boundary K n y ∈ filteredChains K a ((p - 1) - (r - 1)) (n - 1)
    simpa only [show (p - 1) - (r - 1) = p - r by omega] using hby
  have hnull := incoming_boundary_null K a r p n ⟨y, hyc⟩
  change boundary K n x.1 ∈ spectralNullChains K a r (p - r) (n - 1)
  rw [← heq, map_add, hzero, add_zero]
  exact hnull

noncomputable def spectralBoundaryQuotient (K : FiniteComplex V)
    (a : ArcLabels V B) (r p n : ℤ) :
    (spectralCycles K a r p n ⧸
      (spectralNullChains K a r p n).comap
        (spectralCycles K a r p n).subtype) →+
    (spectralCycles K a r (p - r) (n - 1) ⧸
      (spectralNullChains K a r (p - r) (n - 1)).comap
        (spectralCycles K a r (p - r) (n - 1)).subtype) :=
  QuotientAddGroup.map _ _ (spectralCycleBoundary K a r p n) (by
    intro x hx
    change x.1 ∈ spectralNullChains K a r p n at hx
    exact spectralCycleBoundary_null K a r p n x hx)

private noncomputable def pageDegreeCast (K : FiniteComplex V)
    (a : ArcLabels V B) (r p : ℤ) {n m : ℤ} (h : n = m) :
    (spectralCycles K a r p n ⧸
      (spectralNullChains K a r p n).comap
        (spectralCycles K a r p n).subtype) ≃+
    (spectralCycles K a r p m ⧸
      (spectralNullChains K a r p m).comap
        (spectralCycles K a r p m).subtype) := by
  cases h
  exact AddEquiv.refl _

noncomputable def concretePageDifferential (K : FiniteComplex V)
    (a : ArcLabels V B) (r p q : ℤ) :
    spectralPageGroup K a r p q →+
      spectralPageGroup K a r (p - r) (q + r - 1) :=
  ((pageDegreeCast K a r (p - r)
    (show p + q - 1 = (p - r) + (q + r - 1) by omega)).toAddMonoidHom).comp
    (spectralBoundaryQuotient K a r p (p + q))

private theorem pageDegreeCast_mk (K : FiniteComplex V)
    (a : ArcLabels V B) (r p : ℤ) {n m : ℤ} (h : n = m)
    (x : spectralCycles K a r p n) :
    pageDegreeCast K a r p h (QuotientAddGroup.mk' _ x) =
      QuotientAddGroup.mk' _ (h ▸ x) := by
  cases h
  rfl

private theorem pageDegreeCast_val (K : FiniteComplex V)
    (a : ArcLabels V B) (r p : ℤ) {n m : ℤ} (h : n = m)
    (x : spectralCycles K a r p n) :
    ((h ▸ x) : spectralCycles K a r p m).1 =
      h ▸ x.1 := by
  cases h
  rfl

theorem concretePageDifferential_isConcrete (K : FiniteComplex V)
    (a : ArcLabels V B) (r p q : ℤ) :
    IsConcretePageDifferential K a r p q
      (concretePageDifferential K a r p q) := by
  intro x
  let hdeg : p + q - 1 = (p - r) + (q + r - 1) := by omega
  let y : spectralCycles K a r (p - r) ((p - r) + (q + r - 1)) :=
    hdeg ▸ spectralCycleBoundary K a r p (p + q) x
  refine ⟨y, ?_, ?_⟩
  · exact pageDegreeCast_val K a r (p - r) hdeg
      (spectralCycleBoundary K a r p (p + q) x)
  · change pageDegreeCast K a r (p - r) hdeg
        (spectralBoundaryQuotient K a r p (p + q)
          (QuotientAddGroup.mk' _ x)) = QuotientAddGroup.mk' _ y
    unfold spectralBoundaryQuotient
    rw [QuotientAddGroup.map_mk']
    change pageDegreeCast K a r (p - r) hdeg
      (QuotientAddGroup.mk' _ (spectralCycleBoundary K a r p (p + q) x)) =
        QuotientAddGroup.mk' _ y
    rw [pageDegreeCast_mk]

theorem spectralCycleBoundary_comp_zero (K : FiniteComplex V)
    (a : ArcLabels V B) (r p n : ℤ) :
    (spectralCycleBoundary K a r (p - r) (n - 1)).comp
      (spectralCycleBoundary K a r p n) = 0 := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  change boundary K (n - 1) (boundary K n x.1) = 0
  have hb := congrArg (fun f => f x.1) (boundary_boundary K n)
  simpa only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] using hb

theorem spectralBoundaryQuotient_comp_zero (K : FiniteComplex V)
    (a : ArcLabels V B) (r p n : ℤ) :
    (spectralBoundaryQuotient K a r (p - r) (n - 1)).comp
      (spectralBoundaryQuotient K a r p n) = 0 := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    change spectralBoundaryQuotient K a r (p - r) (n - 1)
        (spectralBoundaryQuotient K a r p n
          (QuotientAddGroup.mk' _ z)) = 0
    unfold spectralBoundaryQuotient
    rw [QuotientAddGroup.map_mk']
    change (QuotientAddGroup.map _ _
      (spectralCycleBoundary K a r (p - r) (n - 1)) _)
        (QuotientAddGroup.mk' _ (spectralCycleBoundary K a r p n z)) = 0
    rw [QuotientAddGroup.map_mk']
    have hz := congrArg (fun f => f z)
      (spectralCycleBoundary_comp_zero K a r p n)
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] at hz
    rw [hz]
    rfl

private theorem pageDegreeCast_boundary_comm (K : FiniteComplex V)
    (a : ArcLabels V B) (r p : ℤ) {n m : ℤ} (h : n = m)
    (x : spectralCycles K a r p n ⧸
      (spectralNullChains K a r p n).comap
        (spectralCycles K a r p n).subtype) :
    spectralBoundaryQuotient K a r p m (pageDegreeCast K a r p h x) =
      pageDegreeCast K a r (p - r) (congrArg (· - 1) h)
        (spectralBoundaryQuotient K a r p n x) := by
  cases h
  rfl

theorem concretePageDifferential_comp_zero (K : FiniteComplex V)
    (a : ArcLabels V B) (r p q : ℤ) :
    (concretePageDifferential K a r (p - r) (q + r - 1)).comp
      (concretePageDifferential K a r p q) = 0 := by
  apply AddMonoidHom.ext
  intro x
  let n : ℤ := p + q
  let m : ℤ := (p - r) + (q + r - 1)
  let k : ℤ := ((p - r) - r) + ((q + r - 1) + r - 1)
  have h₁ : n - 1 = m := by dsimp [n, m]; omega
  have h₂ : m - 1 = k := by dsimp [m, k]; omega
  change pageDegreeCast K a r (p - r - r) h₂
    (spectralBoundaryQuotient K a r (p - r) m
      (pageDegreeCast K a r (p - r) h₁
        (spectralBoundaryQuotient K a r p n x))) = 0
  rw [pageDegreeCast_boundary_comm]
  have hz := congrArg (fun f => f x)
    (spectralBoundaryQuotient_comp_zero K a r p n)
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] at hz
  rw [hz]
  rw [map_zero, map_zero]

end CurveGenusTwo.Filtration
