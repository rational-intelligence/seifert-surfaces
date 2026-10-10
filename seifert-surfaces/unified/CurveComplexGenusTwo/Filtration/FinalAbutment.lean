import CurveComplexGenusTwo.Filtration.AbutmentConvergenceRebased

namespace CurveGenusTwo.Filtration

universe u v
variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

private noncomputable def quotientTransport {G : Type*} [AddCommGroup G]
    (S T P Q : AddSubgroup G) (hS : S = T) (hP : P = Q) :
    (S ⧸ P.comap S.subtype) ≃+ (T ⧸ Q.comap T.subtype) := by
  subst T
  subst Q
  exact AddEquiv.refl _

theorem castHomologyStage_eq_filteredRange (K : FiniteComplex V)
    (a : ArcLabels V B) (p n : ℤ) :
    castHomologyStage K a p n = (filteredHomologyMap K a p n).range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨c, rfl⟩ :=
      (filteredCyclesAmbientEquiv K a p n).surjective x
    exact ⟨c, filteredCyclesAmbientEquiv_class K a p n c⟩
  · rintro ⟨c, rfl⟩
    exact ⟨filteredCyclesAmbientEquiv K a p n c,
      (filteredCyclesAmbientEquiv_class K a p n c).symm⟩

theorem castHomologyStage_eq_induced_nat (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    castHomologyStage K a (p : ℤ) n =
      inducedHomologyFiltration K a n (p + 1) := by
  rw [castHomologyStage_eq_filteredRange, inducedHomologyFiltration_eq_range]
  have hi : (((p + 1 : ℕ) : ℤ) - 1) = (p : ℤ) := by omega
  rw [hi]

theorem castHomologyStage_prev_eq_induced_nat (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    castHomologyStage K a ((p : ℤ) - 1) n =
      inducedHomologyFiltration K a n p := by
  rw [castHomologyStage_eq_filteredRange, inducedHomologyFiltration_eq_range]

theorem castGradedHomologyMap_surjective (K : FiniteComplex V)
    (a : ArcLabels V B) (p n : ℤ) :
    Function.Surjective (castGradedHomologyMap K a p n) := by
  intro y
  induction y using Quotient.inductionOn with
  | _ z =>
    obtain ⟨x, hx⟩ := z.2
    refine ⟨x, ?_⟩
    apply congrArg (QuotientAddGroup.mk' _)
    apply Subtype.ext
    exact hx

noncomputable def stablePageToGraded (K : FiniteComplex V)
    (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12)
    (r : ℤ) (hr : 13 ≤ r) (p : ℕ) (hp : p ≤ 12) (q : ℤ) :
    spectralPageGroup K a r (p : ℤ) q ≃+
      ((inducedHomologyFiltration K a ((p : ℤ) + q) (p + 1)) ⧸
        ((inducedHomologyFiltration K a ((p : ℤ) + q) p).comap
          (inducedHomologyFiltration K a ((p : ℤ) + q) (p + 1)).subtype)) := by
  let n : ℤ := (p : ℤ) + q
  have hs : spectralCycles K a r (p : ℤ) n =
      filteredChains K a p n ⊓ cycles K n :=
    spectralCycles_stable K a hr (by exact_mod_cast hp)
  have hk := castGradedHomologyMap_ker_eq_spectralNullChains
    K a hcard hr (show (0 : ℤ) ≤ p by exact_mod_cast Nat.zero_le p)
    (n := n)
  let e₁ := quotientTransport
    (spectralCycles K a r (p : ℤ) n)
    (filteredChains K a p n ⊓ cycles K n)
    (spectralNullChains K a r (p : ℤ) n)
    (spectralNullChains K a r (p : ℤ) n) hs rfl
  let e₂ := QuotientAddGroup.quotientAddEquivOfEq hk.symm
  let e₃ := QuotientAddGroup.quotientKerEquivOfSurjective
    (castGradedHomologyMap K a p n)
    (castGradedHomologyMap_surjective K a p n)
  let e₄ := quotientTransport
    (castHomologyStage K a p n)
    (inducedHomologyFiltration K a n (p + 1))
    (castHomologyStage K a ((p : ℤ) - 1) n)
    (inducedHomologyFiltration K a n p)
    (castHomologyStage_eq_induced_nat K a p n)
    (castHomologyStage_prev_eq_induced_nat K a p n)
  exact ((e₁.trans e₂).trans e₃).trans e₄

theorem boundedFiltrationConvergenceData (K : FiniteComplex V)
    (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12) :
    (∀ n : ℤ, inducedHomologyFiltration K a n 0 = ⊥ ∧
      inducedHomologyFiltration K a n 13 = ⊤ ∧
      ∀ p : ℕ, p < 13 →
        inducedHomologyFiltration K a n p ≤
          inducedHomologyFiltration K a n (p + 1)) ∧
    (∀ p : ℕ, p ≤ 12 → ∀ q : ℤ, -1 ≤ q →
      Nonempty (spectralPageGroup K a 13 (p : ℤ) q ≃+
        ((inducedHomologyFiltration K a ((p : ℤ) + q) (p + 1)) ⧸
          ((inducedHomologyFiltration K a ((p : ℤ) + q) p).comap
            (inducedHomologyFiltration K a ((p : ℤ) + q) (p + 1)).subtype)))) ∧
    (∀ r : ℤ, 13 ≤ r → ∀ p : ℕ, p ≤ 12 → ∀ q : ℤ, -1 ≤ q →
      Nonempty (spectralPageGroup K a r (p : ℤ) q ≃+
        spectralPageGroup K a 13 (p : ℤ) q)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    refine ⟨inducedHomologyFiltration_zero K a n,
      inducedHomologyFiltration_top K a hcard n, ?_⟩
    intro p _
    exact inducedHomologyFiltration_mono K a n (Nat.le_succ p)
  · intro p hp q _
    exact ⟨stablePageToGraded K a hcard 13 (by omega) p hp q⟩
  · intro r hr p hp q _
    exact ⟨(stablePageToGraded K a hcard r hr p hp q).trans
      (stablePageToGraded K a hcard 13 (by omega) p hp q).symm⟩

end CurveGenusTwo.Filtration
