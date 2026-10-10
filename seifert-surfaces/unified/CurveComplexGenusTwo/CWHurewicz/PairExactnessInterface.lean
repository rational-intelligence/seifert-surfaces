import CurveComplexGenusTwo.CWHurewicz.RelativeExactClean

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Topology

private noncomputable abbrev F :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)

private instance pairInclusion_mono {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (pairInclusion X A) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

private instance chainInclusion_mono {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (F.map (pairInclusion X A)) :=
  F.map_mono _

/-- Public short exact sequence of singular chains for a topological pair. -/
noncomputable def pairHomologyShortComplex (X : Type) [TopologicalSpace X]
    (A : Set X) : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (F.map (pairInclusion X A))
    (cokernel.π (F.map (pairInclusion X A)))
    (cokernel.condition _)

theorem pairHomologyShortExact (X : Type) [TopologicalSpace X]
    (A : Set X) : (pairHomologyShortComplex X A).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := by
    dsimp [pairHomologyShortComplex]
    infer_instance
  epi_g := by
    dsimp [pairHomologyShortComplex]
    infer_instance

/-- The public short sequence recovers the target connecting morphism. -/
theorem pairHomologyConnecting_eq (X : Type) [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    (pairHomologyShortExact X A).δ (n + 1) n (by simp) =
      relativeConnecting X A n := by
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem pairHomology_exact_at_absolute (X : Type) [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    ∃ hzero : homologyInclusion X A n ≫ homologyToRelative X A n = 0,
      (⟨homologyInclusion X A n, homologyToRelative X A n, hzero⟩ :
        ShortComplex (ModuleCat.{0} ℤ)).Exact := by
  let S := pairHomologyShortComplex X A
  have hS : S.ShortExact := pairHomologyShortExact X A
  refine ⟨?_, ?_⟩
  · change HomologicalComplex.homologyMap S.f n ≫
      HomologicalComplex.homologyMap S.g n = 0
    rw [← HomologicalComplex.homologyMap_comp, S.zero,
      HomologicalComplex.homologyMap_zero]
  · exact hS.homology_exact₂ n

set_option backward.isDefEq.respectTransparency false in
theorem pairHomology_exact_at_relative (X : Type) [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    ∃ hzero : homologyToRelative X A (n + 1) ≫ relativeConnecting X A n = 0,
      (⟨homologyToRelative X A (n + 1), relativeConnecting X A n, hzero⟩ :
        ShortComplex (ModuleCat.{0} ℤ)).Exact := by
  let S := pairHomologyShortComplex X A
  have hS : S.ShortExact := pairHomologyShortExact X A
  refine ⟨?_, ?_⟩
  · exact hS.comp_δ (n + 1) n (by simp)
  · exact hS.homology_exact₃ (n + 1) n (by simp)

set_option backward.isDefEq.respectTransparency false in
theorem pairHomology_exact_at_subspace (X : Type) [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    ∃ hzero : relativeConnecting X A n ≫ homologyInclusion X A n = 0,
      (⟨relativeConnecting X A n, homologyInclusion X A n, hzero⟩ :
        ShortComplex (ModuleCat.{0} ℤ)).Exact := by
  let S := pairHomologyShortComplex X A
  have hS : S.ShortExact := pairHomologyShortExact X A
  refine ⟨?_, ?_⟩
  · exact hS.δ_comp (n + 1) n (by simp)
  · exact hS.homology_exact₁ (n + 1) n (by simp)

/-- The absolute-to-relative map is an isomorphism when the adjacent
subspace homology groups vanish. -/
theorem homologyToRelative_isIso_of_subspace_zero
    (X : Type) [TopologicalSpace X] (A : Set X) (k : ℕ)
    (hnow : IsZero (H A (k + 1))) (hprev : IsZero (H A k)) :
    IsIso (homologyToRelative X A (k + 1)) := by
  let S := pairHomologyShortComplex X A
  have hS : S.ShortExact := pairHomologyShortExact X A
  have hmono : Mono (homologyToRelative X A (k + 1)) := by
    have h := (hS.homology_exact₂ (k + 1)).mono_g (hnow.eq_of_src _ _)
    exact h
  have hepi : Epi (homologyToRelative X A (k + 1)) := by
    have h := (hS.homology_exact₃ (k + 1) k (by simp)).epi_f
      (hprev.eq_of_tgt _ _)
    exact h
  exact isIso_of_mono_of_epi _

/-- Positive-degree acyclicity yields the isomorphism in degrees at least two.
Degree one requires the separate condition that `H₀(A)` vanish. -/
theorem homologyToRelative_isIso_of_positive_acyclic
    (X : Type) [TopologicalSpace X] (A : Set X)
    (h : ∀ j : ℕ, 0 < j → IsZero (H A j))
    (k : ℕ) (hk : 0 < k) :
    IsIso (homologyToRelative X A (k + 1)) :=
  homologyToRelative_isIso_of_subspace_zero X A k
    (h (k + 1) (by omega)) (h k hk)

#print axioms pairHomology_exact_at_absolute
#print axioms pairHomology_exact_at_relative
#print axioms pairHomology_exact_at_subspace
#print axioms homologyToRelative_isIso_of_subspace_zero
#print axioms homologyToRelative_isIso_of_positive_acyclic

end CurveComplexGenusTwo.CWHurewicz
