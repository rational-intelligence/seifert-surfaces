import CurveComplexGenusTwo.CWHurewicz.RelativeQuotientComparison
import CurveComplexGenusTwo.CWHurewicz.ExcisionClean

namespace CurveComplexGenusTwo.CWHurewicz
open CategoryTheory
open scoped Simplicial

/-- Actual singular-simplex map induced by the inclusion of the excised space. -/
noncomputable def excisedSimplexPush (X : TopCat) (U : Set X) (n : ℕ) :=
  (TopCat.toSSet.map (excisionInclusionX X U)).app (.op ⦋n⦌)

noncomputable def excisedChainPush (X : TopCat) (U : Set X) (n : ℕ) :=
  Finsupp.lmapDomain ℤ ℤ (excisedSimplexPush X U n)

theorem excisedSimplexPush_injective (X : TopCat) (U : Set X) (n : ℕ) :
    Function.Injective (excisedSimplexPush X U n) := by
  intro x y h
  apply (TopCat.toSSetObjEquiv _ (.op ⦋n⦌)).injective
  ext t
  exact congrArg (fun z => TopCat.toSSetObjEquiv X (.op ⦋n⦌) z t) h

theorem excisedSimplexPush_range (X : TopCat) (U : Set X) (n : ℕ) :
    Set.range (excisedSimplexPush X U n) =
      {x | Set.range (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x) ⊆ Uᶜ} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ z ⟨t, rfl⟩
    exact (TopCat.toSSetObjEquiv _ (.op ⦋n⦌) y t).property
  · intro hx
    let f := TopCat.toSSetObjEquiv X (.op ⦋n⦌) x
    let g : C(Convexity.StdSimplex ℝ (Fin (n + 1)), Excised X U) :=
      ⟨fun t => ⟨f t, hx ⟨t, rfl⟩⟩, f.continuous.subtype_mk _⟩
    refine ⟨(TopCat.toSSetObjEquiv _ (.op ⦋n⦌)).symm g, ?_⟩
    apply (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).injective
    ext t
    change ((TopCat.toSSetObjEquiv (TopCat.of (Excised X U)) (.op ⦋n⦌))
      ((TopCat.toSSetObjEquiv (TopCat.of (Excised X U)) (.op ⦋n⦌)).symm g) t).val = f t
    simp [g]

theorem excisedChainPush_injective (X : TopCat) (U : Set X) (n : ℕ) :
    Function.Injective (excisedChainPush X U n) := by
  exact Finsupp.mapDomain_injective (excisedSimplexPush_injective X U n)

theorem excisedChainPush_range (X : TopCat) (U : Set X) (n : ℕ) :
    LinearMap.range (excisedChainPush X U n) = excisionSubspaceChains X Uᶜ n := by
  have h := Finsupp.lmapDomain_supported ℤ ℤ (excisedSimplexPush X U n) Set.univ
  simpa [Finsupp.supported_univ, Submodule.map_top, Set.image_univ,
    excisedSimplexPush_range, excisedChainPush, excisionSubspaceChains] using h

theorem excisedChainPush_boundary (X : TopCat) (U : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of (Excised X U))) _⦋n + 1⦌ →₀ ℤ) :
    singularBoundaryFinsupp X n (excisedChainPush X U (n + 1) c) =
      excisedChainPush X U n
        (singularBoundaryFinsupp (TopCat.of (Excised X U)) n c) := by
  classical
  have hsingle (x : (TopCat.toSSet.obj (TopCat.of (Excised X U))) _⦋n + 1⦌) :
      singularBoundaryFinsupp X n (excisedChainPush X U (n + 1) (Finsupp.single x 1)) =
        excisedChainPush X U n
          (singularBoundaryFinsupp (TopCat.of (Excised X U)) n (Finsupp.single x 1)) := by
    simp only [excisedChainPush, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      singularBoundaryFinsupp_single]
    rw [Finsupp.mapDomain_finset_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finsupp.mapDomain_smul, Finsupp.mapDomain_single]
    congr 2
  have hrepr : c = ∑ x ∈ c.support, c x • Finsupp.single x 1 := by
    conv_lhs => rw [← Finsupp.sum_single c]
    simp [Finsupp.sum, Finsupp.smul_single]
  rw [hrepr]
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl (fun x hx => congrArg (fun y => c x • y) (hsingle x))

theorem excisedChainPush_subspace_iff (X : TopCat) (A U : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of (Excised X U))) _⦋n⦌ →₀ ℤ) :
    excisedChainPush X U n c ∈ excisionSubspaceChains X A n ↔
      c ∈ excisionSubspaceChains (TopCat.of (Excised X U)) (excisedSubspace A U) n := by
  classical
  change (∀ x ∈ (Finsupp.mapDomain (excisedSimplexPush X U n) c).support,
      Set.range (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x) ⊆ A) ↔ _
  rw [Finsupp.mapDomain_support_of_injective (excisedSimplexPush_injective X U n)]
  constructor
  · intro h
    change ∀ x ∈ c.support, Set.range
      (TopCat.toSSetObjEquiv (TopCat.of (Excised X U)) (.op ⦋n⦌) x) ⊆ _
    intro x hx z hz
    obtain ⟨t, rfl⟩ := hz
    exact h _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩) ⟨t, rfl⟩
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rintro z ⟨t, rfl⟩
    exact h hy ⟨t, rfl⟩

theorem smallSingularChains_eq_sup (X : TopCat) (A U : Set X) (n : ℕ) :
    smallSingularChains X A U n =
      excisionSubspaceChains X Uᶜ n ⊔ excisionSubspaceChains X A n := by
  exact Finsupp.supported_union _ _

end CurveComplexGenusTwo.CWHurewicz
