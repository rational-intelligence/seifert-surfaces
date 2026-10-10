/- Local import and naming adapter for barycentric_mesh_wave11/SmallSingularChains.lean.
   The copied proof bodies are unchanged; the iterate name is made distinct
   from the verified linear-map iterate in SingularCarrierIteration. -/
import CurveComplexGenusTwo.CWHurewicz.SingularCarrierIteration
import CurveComplexGenusTwo.CWHurewicz.SmallSimplexCover
import CurveComplexGenusTwo.CWHurewicz.BarycentricMesh

namespace CurveComplexGenusTwo.CWHurewicz

open Classical Convexity CategoryTheory
open scoped Simplicial

noncomputable local instance (n : ℕ) : MetricSpace (StdSimplex ℝ (Fin (n + 1))) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).comapMetricSpace
    (fun t => (t.weights : Fin (n + 1) → ℝ))

private abbrev Sing (X : TopCat) (n : ℕ) := (TopCat.toSSet.obj X) _⦋n⦌

/-- A singular simplex resulting from a specified list of subdivision flags. -/
noncomputable def singularFlagIterate (X : TopCat) (n : ℕ)
    (ss : List (Equiv.Perm (Fin (n + 1)))) (x : Sing X n) : Sing X n :=
  match ss with
  | [] => x
  | σ :: tail => barycentricFlagSingular X n σ (singularFlagIterate X n tail x)

theorem singularFlagIterate_eval (X : TopCat) (n : ℕ)
    (ss : List (Equiv.Perm (Fin (n + 1)))) (x : Sing X n)
    (t : StdSimplex ℝ (Fin (n + 1))) :
    (TopCat.toSSetObjEquiv X (.op ⦋n⦌) (singularFlagIterate X n ss x)) t =
      (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x)
        (barycentricFlagIterate n ss t) := by
  induction ss generalizing t with
  | nil => simp [singularFlagIterate, barycentricFlagIterate]
  | cons σ ss ih =>
      simp only [singularFlagIterate, barycentricFlagIterate, Function.comp_apply]
      simp only [barycentricFlagSingular, Equiv.apply_symm_apply,
        ContinuousMap.comp_apply]
      exact ih (barycentricFlag n σ t)

/-- Repeated application of the actual signed singular barycentric operator. -/
noncomputable def singularBarycentricIterateList (X : TopCat) (n : ℕ)
    (k : ℕ) (c : Sing X n →₀ ℤ) : Sing X n →₀ ℤ :=
  match k with
  | 0 => c
  | k + 1 => singularBarycentricFinsupp X n (singularBarycentricIterateList X n k c)

theorem singularBarycentricFinsupp_support (X : TopCat) (n : ℕ)
    (c : Sing X n →₀ ℤ) (y : Sing X n)
    (hy : y ∈ (singularBarycentricFinsupp X n c).support) :
    ∃ x ∈ c.support, ∃ σ : Equiv.Perm (Fin (n + 1)),
      y = barycentricFlagSingular X n σ x := by
  classical
  have hrepr : c = ∑ x ∈ c.support, Finsupp.single x (c x) := by
    simpa [Finsupp.sum] using (Finsupp.sum_single c).symm
  rw [hrepr, map_sum] at hy
  obtain ⟨x, hx, hyx⟩ := Finsupp.mem_support_finsetSum y hy
  have hsingle : Finsupp.single x (c x) = c x • Finsupp.single x 1 := by
    ext z
    by_cases hz : z = x <;> simp [hz]
  rw [hsingle, LinearMap.map_smul] at hyx
  have hy' : y ∈ (singularBarycentricFinsupp X n (Finsupp.single x 1)).support :=
    Finsupp.support_smul hyx
  rw [singularBarycentricFinsupp_single] at hy'
  obtain ⟨σ, -, hσ⟩ := Finsupp.mem_support_finsetSum y hy'
  have hσ' : y = barycentricFlagSingular X n σ x := by
    have hσ'' := Finsupp.support_smul hσ
    simpa using hσ''
  exact ⟨x, hx, σ, hσ'⟩

theorem singularBarycentricIterateList_support (X : TopCat) (n k : ℕ)
    (c : Sing X n →₀ ℤ) (y : Sing X n)
    (hy : y ∈ (singularBarycentricIterateList X n k c).support) :
    ∃ x ∈ c.support, ∃ ss : List (Equiv.Perm (Fin (n + 1))),
      ss.length = k ∧ y = singularFlagIterate X n ss x := by
  induction k generalizing y with
  | zero =>
      exact ⟨y, by simpa [singularBarycentricIterateList] using hy,
        [], rfl, by simp [singularFlagIterate]⟩
  | succ k ih =>
      have hy' : y ∈ (singularBarycentricFinsupp X n
          (singularBarycentricIterateList X n k c)).support := by
        simpa [singularBarycentricIterateList] using hy
      obtain ⟨z, hz, σ, rfl⟩ := singularBarycentricFinsupp_support X n _ y hy'
      obtain ⟨x, hx, ss, hlen, rfl⟩ := ih z hz
      exact ⟨x, hx, σ :: ss, by simp [hlen], rfl⟩

/-- Every finite singular chain becomes subordinate to the excision cover after
an actual iterated barycentric subdivision. -/
theorem singularBarycentricIterateList_eventually_small
    (X : TopCat) (A U : Set X) (hU : closure U ⊆ interior A)
    (n : ℕ) (c : Sing X n →₀ ℤ) :
    ∃ k : ℕ, ∀ y ∈ (singularBarycentricIterateList X n k c).support,
      ((TopCat.toSSetObjEquiv X (.op ⦋n⦌) y) '' Set.univ ⊆ Uᶜ) ∨
        ((TopCat.toSSetObjEquiv X (.op ⦋n⦌) y) '' Set.univ ⊆ A) := by
  let fs : List C(StdSimplex ℝ (Fin (n + 1)), X) :=
    c.support.toList.map (fun x => TopCat.toSSetObjEquiv X (.op ⦋n⦌) x)
  obtain ⟨δ, hδ, hcover⟩ :=
    singularSimplices_excision_lebesgue_number A U hU n fs
  obtain ⟨k, hk⟩ :=
    barycentricFlagIterate_finite_family_eventually_subordinate n A U fs δ hδ hcover
  refine ⟨k, ?_⟩
  intro y hy
  obtain ⟨x, hx, ss, hlen, rfl⟩ :=
    singularBarycentricIterateList_support X n k c y hy
  have hfx : (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x) ∈ fs := by
    exact List.mem_map.mpr ⟨x, by simpa using hx, rfl⟩
  rcases hk _ hfx ss hlen with h | h
  · left
    rintro z ⟨t, -, rfl⟩
    rw [singularFlagIterate_eval]
    exact h ⟨t, Set.mem_univ _, rfl⟩
  · right
    rintro z ⟨t, -, rfl⟩
    rw [singularFlagIterate_eval]
    exact h ⟨t, Set.mem_univ _, rfl⟩

end CurveComplexGenusTwo.CWHurewicz
