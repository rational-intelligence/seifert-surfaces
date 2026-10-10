import CurveComplexGenusTwo.Filtration.SpectralCast

namespace CurveGenusTwo.Filtration

universe u v

variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

/-- A concrete page group of the filtered augmented chain complex. -/
noncomputable abbrev spectralPageGroup (K : FiniteComplex V) (a : ArcLabels V B)
    (r p q : ℤ) : Type u :=
  (spectralCycles K a r p (p + q)) ⧸
    ((spectralNullChains K a r p (p + q)).comap
      (spectralCycles K a r p (p + q)).subtype)

/-- A homology class represented by a cycle at filtration level `p`. -/
theorem filteredCycle_inclusion_isCycle (K : FiniteComplex V) (a : ArcLabels V B)
    (p n : ℤ) (c : chains (filtration K a p) n)
    (hc : boundary (filtration K a p) n c = 0) :
    chainInclusion (filtration K a p) K (by intro σ hσ; exact hσ.1) n c ∈ cycles K n := by
  change boundary K n (chainInclusion (filtration K a p) K
    (by intro σ hσ; exact hσ.1) n c) = 0
  have h := congrArg (fun f => f c)
    (chainInclusion_boundary (filtration K a p) K
      (by intro σ hσ; exact hσ.1) n)
  simpa [AddMonoidHom.comp_apply, hc] using h

noncomputable def filteredCycleClass (K : FiniteComplex V) (a : ArcLabels V B)
    (p n : ℤ) (c : chains (filtration K a p) n)
    (hc : boundary (filtration K a p) n c = 0) : reducedHomology K n :=
  QuotientAddGroup.mk' _
    (⟨chainInclusion (filtration K a p) K (by intro σ hσ; exact hσ.1) n c,
      filteredCycle_inclusion_isCycle K a p n c hc⟩ : cycles K n)

/-- The filtration on the abutment induced by the actual filtered chain groups. -/
noncomputable def inducedHomologyFiltration (K : FiniteComplex V)
    (a : ArcLabels V B) (n : ℤ) (p : ℕ) :
    AddSubgroup (reducedHomology K n) :=
  AddSubgroup.closure
    {h | ∃ c : chains (filtration K a ((p : ℤ) - 1)) n,
      ∃ hc : boundary (filtration K a ((p : ℤ) - 1)) n c = 0,
        filteredCycleClass K a ((p : ℤ) - 1) n c hc = h}

/-- Mathlib's homological differential lowers `p` by `r` and raises `q` by `r-1`. -/
def pageShape (r : ℤ) : ComplexShape (ℤ × ℤ) :=
  ComplexShape.down' (⟨r, 1 - r⟩ : ℤ × ℤ)

/-- The concrete pages carry the differential induced by ambient boundary. -/
def IsConcretePageDifferential (K : FiniteComplex V) (a : ArcLabels V B)
    (r : ℤ) (p q : ℤ)
    (d : spectralPageGroup K a r p q →+
      spectralPageGroup K a r (p - r) (q + r - 1)) : Prop :=
  ∀ x : spectralCycles K a r p (p + q),
    ∃ y : spectralCycles K a r (p - r) ((p - r) + (q + r - 1)),
      y.1 = (show chains K ((p - r) + (q + r - 1)) from
        (by have h : p + q - 1 = (p - r) + (q + r - 1) := by omega
            exact h ▸ boundary K (p + q) x.1)) ∧
      d (QuotientAddGroup.mk' _ x) = QuotientAddGroup.mk' _ y

end CurveGenusTwo.Filtration
