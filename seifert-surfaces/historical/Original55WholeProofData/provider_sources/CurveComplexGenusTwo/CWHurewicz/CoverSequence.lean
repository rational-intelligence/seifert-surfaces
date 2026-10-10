import CurveComplexGenusTwo.CWHurewicz.ExcisedChainIdentification

namespace CurveComplexGenusTwo.CWHurewicz
open CategoryTheory
open scoped Simplicial

theorem excisionSubspaceChains_boundary (X : TopCat) (A : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ)
    (hc : c ∈ excisionSubspaceChains X A (n + 1)) :
    singularBoundaryFinsupp X n c ∈ excisionSubspaceChains X A n := by
  have hm : c ∈ smallSingularChains X A Set.univ (n + 1) := by
    intro x hx
    exact Or.inr (hc hx)
  have hb := smallSingularChains_boundary X A Set.univ n c hm
  intro x hx
  rcases hb hx with h | h
  · intro z hz
    exact False.elim (h hz (Set.mem_univ _))
  · exact h


/-- Small chains for the two-set cover, in the existing excision model. -/
noncomputable abbrev coverSmallChains (X : TopCat) (U V : Set X) (n : ℕ) :=
  smallSingularChains X V Uᶜ n

theorem coverSmallChains_eq_sup (X : TopCat) (U V : Set X) (n : ℕ) :
    coverSmallChains X U V n =
      excisionSubspaceChains X U n ⊔ excisionSubspaceChains X V n := by
  simpa using smallSingularChains_eq_sup X V Uᶜ n

theorem coverSubspaceChains_inter (X : TopCat) (U V : Set X) (n : ℕ) :
    excisionSubspaceChains X (U ∩ V) n =
      excisionSubspaceChains X U n ⊓ excisionSubspaceChains X V n := by
  ext c
  constructor
  · intro h
    exact ⟨fun x hx y hy => (h hx hy).1, fun x hx y hy => (h hx hy).2⟩
  · rintro ⟨hu, hv⟩ x hx y hy
    exact ⟨hu hx hy, hv hx hy⟩

noncomputable def coverChainSum (X : TopCat) (U V : Set X) (n : ℕ) :
    (excisionSubspaceChains X U n × excisionSubspaceChains X V n) →ₗ[ℤ]
      coverSmallChains X U V n where
  toFun c := ⟨c.1.1 + c.2.1, by
    rw [coverSmallChains_eq_sup]
    exact Submodule.add_mem_sup c.1.2 c.2.2⟩
  map_add' a b := by ext; simp; abel
  map_smul' a b := by ext; simp [smul_add]

noncomputable def coverChainDifference (X : TopCat) (U V : Set X) (n : ℕ) :
    excisionSubspaceChains X (U ∩ V) n →ₗ[ℤ]
      (excisionSubspaceChains X U n × excisionSubspaceChains X V n) where
  toFun c := (⟨c.1, fun x hx y hy => (c.2 hx hy).1⟩,
    ⟨-c.1, (excisionSubspaceChains X V n).neg_mem
      (fun x hx y hy => (c.2 hx hy).2)⟩)
  map_add' a b := by ext <;> simp <;> abel
  map_smul' a b := by ext <;> simp

theorem coverChainDifference_injective (X : TopCat) (U V : Set X) (n : ℕ) :
    Function.Injective (coverChainDifference X U V n) := by
  intro a b h
  exact Subtype.ext (congrArg (fun c => c.1.1) h)

theorem coverChainSum_surjective (X : TopCat) (U V : Set X) (n : ℕ) :
    Function.Surjective (coverChainSum X U V n) := by
  intro c
  have hc : c.1 ∈ excisionSubspaceChains X U n ⊔ excisionSubspaceChains X V n :=
    (congrArg (fun S : Submodule ℤ ((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) => c.1 ∈ S)
      (coverSmallChains_eq_sup X U V n)).mp c.2
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hc
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

theorem coverChainSum_difference (X : TopCat) (U V : Set X) (n : ℕ)
    (c : excisionSubspaceChains X (U ∩ V) n) :
    coverChainSum X U V n (coverChainDifference X U V n c) = 0 := by
  apply Subtype.ext
  exact add_neg_cancel c.1

theorem coverChainSum_ker (X : TopCat) (U V : Set X) (n : ℕ) :
    LinearMap.ker (coverChainSum X U V n) =
      LinearMap.range (coverChainDifference X U V n) := by
  ext c
  constructor
  · intro hc
    have hsum : c.1.1 + c.2.1 = 0 := congrArg Subtype.val hc
    have heq : c.2.1 = -c.1.1 := eq_neg_of_add_eq_zero_right hsum
    have hv : c.1.1 ∈ excisionSubspaceChains X V n := by
      have := (excisionSubspaceChains X V n).neg_mem c.2.2
      simpa [heq] using this
    refine ⟨⟨c.1.1, ?_⟩, ?_⟩
    · rw [coverSubspaceChains_inter]
      exact ⟨c.1.2, hv⟩
    · apply Prod.ext
      · rfl
      · exact Subtype.ext heq.symm
  · rintro ⟨c, rfl⟩
    exact coverChainSum_difference X U V n c

noncomputable def coverSubspaceBoundary (X : TopCat) (U : Set X) (n : ℕ) :
    excisionSubspaceChains X U (n + 1) →ₗ[ℤ] excisionSubspaceChains X U n :=
  ((singularBoundaryFinsupp X n).comp (excisionSubspaceChains X U (n + 1)).subtype).codRestrict _ (fun c => excisionSubspaceChains_boundary X U n c.1 c.2)

noncomputable def coverPairBoundary (X : TopCat) (U V : Set X) (n : ℕ) :
    (excisionSubspaceChains X U (n + 1) × excisionSubspaceChains X V (n + 1)) →ₗ[ℤ]
      (excisionSubspaceChains X U n × excisionSubspaceChains X V n) :=
  (coverSubspaceBoundary X U n).prodMap (coverSubspaceBoundary X V n)

theorem coverChainSum_boundary (X : TopCat) (U V : Set X) (n : ℕ)
    (c : excisionSubspaceChains X U (n + 1) × excisionSubspaceChains X V (n + 1)) :
    smallSingularBoundary X V Uᶜ n (coverChainSum X U V (n + 1) c) =
      coverChainSum X U V n (coverPairBoundary X U V n c) := by
  apply Subtype.ext
  exact map_add (singularBoundaryFinsupp X n) c.1.1 c.2.1

theorem coverChainDifference_boundary (X : TopCat) (U V : Set X) (n : ℕ)
    (c : excisionSubspaceChains X (U ∩ V) (n + 1)) :
    coverPairBoundary X U V n (coverChainDifference X U V (n + 1) c) =
      coverChainDifference X U V n (coverSubspaceBoundary X (U ∩ V) n c) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact map_neg (singularBoundaryFinsupp X n) c.1

theorem coverSubspaceBoundary_square (X : TopCat) (U : Set X) (n : ℕ)
    (c : excisionSubspaceChains X U (n + 2)) :
    coverSubspaceBoundary X U n (coverSubspaceBoundary X U (n + 1) c) = 0 := by
  apply Subtype.ext
  exact singularBoundaryFinsupp_comp_zero X n c.1



/-- Ordinary singular chains of the subspace U. -/
abbrev coverOrdinaryChains (X : TopCat) (U : Set X) (n : ℕ) :=
  (TopCat.toSSet.obj (TopCat.of U)) _⦋n⦌ →₀ ℤ

noncomputable def coverSimplexPush (X : TopCat) (U : Set X) (n : ℕ) :=
  (TopCat.toSSet.map (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))).app
    (.op ⦋n⦌)

noncomputable def coverOrdinaryPush (X : TopCat) (U : Set X) (n : ℕ) :=
  Finsupp.lmapDomain ℤ ℤ (coverSimplexPush X U n)

theorem coverSimplexPush_injective (X : TopCat) (U : Set X) (n : ℕ) :
    Function.Injective (coverSimplexPush X U n) := by
  intro a b h
  apply (TopCat.toSSetObjEquiv _ (.op ⦋n⦌)).injective
  ext t
  exact congrArg (fun z => TopCat.toSSetObjEquiv X (.op ⦋n⦌) z t) h

theorem coverSimplexPush_range (X : TopCat) (U : Set X) (n : ℕ) :
    Set.range (coverSimplexPush X U n) =
      {x | Set.range (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x) ⊆ U} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ z ⟨t, rfl⟩
    exact (TopCat.toSSetObjEquiv _ (.op ⦋n⦌) y t).property
  · intro hx
    let f := TopCat.toSSetObjEquiv X (.op ⦋n⦌) x
    let g : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U) :=
      ⟨fun t => ⟨f t, hx ⟨t, rfl⟩⟩, f.continuous.subtype_mk _⟩
    refine ⟨(TopCat.toSSetObjEquiv _ (.op ⦋n⦌)).symm g, ?_⟩
    apply (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).injective
    ext t
    change ((TopCat.toSSetObjEquiv (TopCat.of U) (.op ⦋n⦌))
      ((TopCat.toSSetObjEquiv (TopCat.of U) (.op ⦋n⦌)).symm g) t).val = f t
    simp [g]

theorem coverOrdinaryPush_injective (X : TopCat) (U : Set X) (n : ℕ) :
    Function.Injective (coverOrdinaryPush X U n) :=
  Finsupp.mapDomain_injective (coverSimplexPush_injective X U n)

theorem coverOrdinaryPush_range (X : TopCat) (U : Set X) (n : ℕ) :
    LinearMap.range (coverOrdinaryPush X U n) = excisionSubspaceChains X U n := by
  have h := Finsupp.lmapDomain_supported ℤ ℤ (coverSimplexPush X U n) Set.univ
  simpa [Finsupp.supported_univ, Submodule.map_top, Set.image_univ,
    coverSimplexPush_range, coverOrdinaryPush, excisionSubspaceChains] using h

/-- The support model is canonically equivalent to the ordinary subspace chains. -/
noncomputable def coverOrdinaryEquiv (X : TopCat) (U : Set X) (n : ℕ) :
    coverOrdinaryChains X U n ≃ₗ[ℤ] excisionSubspaceChains X U n :=
  (LinearEquiv.ofInjective (coverOrdinaryPush X U n)
    (coverOrdinaryPush_injective X U n)).trans
      (LinearEquiv.ofEq _ _ (coverOrdinaryPush_range X U n))

theorem coverOrdinaryEquiv_val (X : TopCat) (U : Set X) (n : ℕ)
    (c : coverOrdinaryChains X U n) :
    (coverOrdinaryEquiv X U n c).1 = coverOrdinaryPush X U n c := rfl

noncomputable def coverOrdinaryPairEquiv (X : TopCat) (U V : Set X) (n : ℕ) :
    (coverOrdinaryChains X U n × coverOrdinaryChains X V n) ≃ₗ[ℤ]
      (excisionSubspaceChains X U n × excisionSubspaceChains X V n) :=
  (coverOrdinaryEquiv X U n).prodCongr (coverOrdinaryEquiv X V n)

noncomputable def coverOrdinarySum (X : TopCat) (U V : Set X) (n : ℕ) :
    (coverOrdinaryChains X U n × coverOrdinaryChains X V n) →ₗ[ℤ]
      coverSmallChains X U V n :=
  (coverChainSum X U V n).comp (coverOrdinaryPairEquiv X U V n).toLinearMap

noncomputable def coverOrdinaryDifference (X : TopCat) (U V : Set X) (n : ℕ) :
    coverOrdinaryChains X (U ∩ V) n →ₗ[ℤ]
      (coverOrdinaryChains X U n × coverOrdinaryChains X V n) :=
  (coverOrdinaryPairEquiv X U V n).symm.toLinearMap.comp
    ((coverChainDifference X U V n).comp (coverOrdinaryEquiv X (U ∩ V) n).toLinearMap)

theorem coverOrdinarySum_val (X : TopCat) (U V : Set X) (n : ℕ)
    (c : coverOrdinaryChains X U n × coverOrdinaryChains X V n) :
    (coverOrdinarySum X U V n c).1 =
      coverOrdinaryPush X U n c.1 + coverOrdinaryPush X V n c.2 := rfl

theorem coverOrdinaryDifference_injective (X : TopCat) (U V : Set X) (n : ℕ) :
    Function.Injective (coverOrdinaryDifference X U V n) :=
  (coverOrdinaryPairEquiv X U V n).symm.injective.comp
    ((coverChainDifference_injective X U V n).comp
      (coverOrdinaryEquiv X (U ∩ V) n).injective)

theorem coverOrdinarySum_surjective (X : TopCat) (U V : Set X) (n : ℕ) :
    Function.Surjective (coverOrdinarySum X U V n) :=
  (coverChainSum_surjective X U V n).comp (coverOrdinaryPairEquiv X U V n).surjective

theorem coverOrdinarySum_difference (X : TopCat) (U V : Set X) (n : ℕ)
    (c : coverOrdinaryChains X (U ∩ V) n) :
    coverOrdinarySum X U V n (coverOrdinaryDifference X U V n c) = 0 := by
  simp only [coverOrdinarySum, coverOrdinaryDifference, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact coverChainSum_difference X U V n _

theorem coverOrdinarySum_ker (X : TopCat) (U V : Set X) (n : ℕ) :
    LinearMap.ker (coverOrdinarySum X U V n) =
      LinearMap.range (coverOrdinaryDifference X U V n) := by
  ext c
  constructor
  · intro hc
    have h : coverOrdinaryPairEquiv X U V n c ∈
        LinearMap.ker (coverChainSum X U V n) := hc
    rw [coverChainSum_ker] at h
    obtain ⟨b, hb⟩ := h
    refine ⟨(coverOrdinaryEquiv X (U ∩ V) n).symm b, ?_⟩
    apply (coverOrdinaryPairEquiv X U V n).injective
    simpa only [coverOrdinaryDifference, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hb
  · rintro ⟨b, rfl⟩
    exact coverOrdinarySum_difference X U V n b


theorem coverOrdinaryPush_boundary (X : TopCat) (U : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of U)) _⦋n + 1⦌ →₀ ℤ) :
    singularBoundaryFinsupp X n (coverOrdinaryPush X U (n + 1) c) =
      coverOrdinaryPush X U n
        (singularBoundaryFinsupp (TopCat.of U) n c) := by
  classical
  have hsingle (x : (TopCat.toSSet.obj (TopCat.of U)) _⦋n + 1⦌) :
      singularBoundaryFinsupp X n (coverOrdinaryPush X U (n + 1) (Finsupp.single x 1)) =
        coverOrdinaryPush X U n
          (singularBoundaryFinsupp (TopCat.of U) n (Finsupp.single x 1)) := by
    simp only [coverOrdinaryPush, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      singularBoundaryFinsupp_single]
    rw [Finsupp.mapDomain_finsetSum]
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


theorem coverOrdinaryEquiv_boundary (X : TopCat) (U : Set X) (n : ℕ)
    (c : coverOrdinaryChains X U (n + 1)) :
    coverSubspaceBoundary X U n (coverOrdinaryEquiv X U (n + 1) c) =
      coverOrdinaryEquiv X U n (singularBoundaryFinsupp (TopCat.of U) n c) := by
  apply Subtype.ext
  exact coverOrdinaryPush_boundary X U n c

noncomputable def coverOrdinaryPairBoundary (X : TopCat) (U V : Set X) (n : ℕ) :
    (coverOrdinaryChains X U (n + 1) × coverOrdinaryChains X V (n + 1)) →ₗ[ℤ]
      (coverOrdinaryChains X U n × coverOrdinaryChains X V n) :=
  (singularBoundaryFinsupp (TopCat.of U) n).prodMap
    (singularBoundaryFinsupp (TopCat.of V) n)

theorem coverOrdinaryPairEquiv_boundary (X : TopCat) (U V : Set X) (n : ℕ)
    (c : coverOrdinaryChains X U (n + 1) × coverOrdinaryChains X V (n + 1)) :
    coverPairBoundary X U V n (coverOrdinaryPairEquiv X U V (n + 1) c) =
      coverOrdinaryPairEquiv X U V n (coverOrdinaryPairBoundary X U V n c) := by
  exact Prod.ext (coverOrdinaryEquiv_boundary X U n c.1)
    (coverOrdinaryEquiv_boundary X V n c.2)

theorem coverOrdinarySum_boundary (X : TopCat) (U V : Set X) (n : ℕ)
    (c : coverOrdinaryChains X U (n + 1) × coverOrdinaryChains X V (n + 1)) :
    smallSingularBoundary X V Uᶜ n (coverOrdinarySum X U V (n + 1) c) =
      coverOrdinarySum X U V n (coverOrdinaryPairBoundary X U V n c) := by
  change smallSingularBoundary X V Uᶜ n
    (coverChainSum X U V (n + 1) (coverOrdinaryPairEquiv X U V (n + 1) c)) = _
  rw [coverChainSum_boundary, coverOrdinaryPairEquiv_boundary]
  rfl

theorem coverOrdinaryDifference_equiv (X : TopCat) (U V : Set X) (n : ℕ)
    (c : coverOrdinaryChains X (U ∩ V) n) :
    coverOrdinaryPairEquiv X U V n (coverOrdinaryDifference X U V n c) =
      coverChainDifference X U V n (coverOrdinaryEquiv X (U ∩ V) n c) := by
  exact (coverOrdinaryPairEquiv X U V n).apply_symm_apply _

theorem coverOrdinaryDifference_push_fst (X : TopCat) (U V : Set X) (n : ℕ)
    (c : coverOrdinaryChains X (U ∩ V) n) :
    coverOrdinaryPush X U n (coverOrdinaryDifference X U V n c).1 =
      coverOrdinaryPush X (U ∩ V) n c :=
  congrArg (fun p => p.1.1) (coverOrdinaryDifference_equiv X U V n c)

theorem coverOrdinaryDifference_push_snd (X : TopCat) (U V : Set X) (n : ℕ)
    (c : coverOrdinaryChains X (U ∩ V) n) :
    coverOrdinaryPush X V n (coverOrdinaryDifference X U V n c).2 =
      -coverOrdinaryPush X (U ∩ V) n c :=
  congrArg (fun p => p.2.1) (coverOrdinaryDifference_equiv X U V n c)

theorem coverOrdinaryDifference_boundary (X : TopCat) (U V : Set X) (n : ℕ)
    (c : coverOrdinaryChains X (U ∩ V) (n + 1)) :
    coverOrdinaryPairBoundary X U V n (coverOrdinaryDifference X U V (n + 1) c) =
      coverOrdinaryDifference X U V n
        (singularBoundaryFinsupp (TopCat.of ↥(U ∩ V)) n c) := by
  apply (coverOrdinaryPairEquiv X U V n).injective
  rw [← coverOrdinaryPairEquiv_boundary, coverOrdinaryDifference_equiv,
    coverChainDifference_boundary, coverOrdinaryEquiv_boundary,
    coverOrdinaryDifference_equiv]

/-- Degreewise short exactness of the two-set singular-chain cover sequence. -/
theorem coverOrdinary_shortExact (X : TopCat) (U V : Set X) (n : ℕ) :
    Function.Injective (coverOrdinaryDifference X U V n) ∧
      LinearMap.ker (coverOrdinarySum X U V n) =
        LinearMap.range (coverOrdinaryDifference X U V n) ∧
      Function.Surjective (coverOrdinarySum X U V n) :=
  ⟨coverOrdinaryDifference_injective X U V n, coverOrdinarySum_ker X U V n,
    coverOrdinarySum_surjective X U V n⟩



/-- Chain map of the actual inclusion of one subspace in another. -/
noncomputable def coverSubsetPush (X : TopCat) (A B : Set X) (h : A ⊆ B) (n : ℕ) :
    coverOrdinaryChains X A n →ₗ[ℤ] coverOrdinaryChains X B n :=
  Finsupp.lmapDomain ℤ ℤ
    ((TopCat.toSSet.map (TopCat.ofHom
      (⟨fun a => ⟨a.1, h a.2⟩, continuous_subtype_val.subtype_mk _⟩ : C(A, B)))).app
      (.op ⦋n⦌))

theorem coverSubsetPush_ambient (X : TopCat) (A B : Set X) (h : A ⊆ B) (n : ℕ)
    (c : coverOrdinaryChains X A n) :
    coverOrdinaryPush X B n (coverSubsetPush X A B h n c) =
      coverOrdinaryPush X A n c := by
  simp only [coverOrdinaryPush, coverSubsetPush, Finsupp.lmapDomain_apply,
    ← Finsupp.mapDomain_comp]
  rfl

/-- The transported difference is precisely the two actual inclusions with signs + and -. -/
theorem coverOrdinaryDifference_inclusions (X : TopCat) (U V : Set X) (n : ℕ)
    (c : coverOrdinaryChains X (U ∩ V) n) :
    coverOrdinaryDifference X U V n c =
      (coverSubsetPush X (U ∩ V) U Set.inter_subset_left n c,
        -coverSubsetPush X (U ∩ V) V Set.inter_subset_right n c) := by
  apply Prod.ext
  · apply coverOrdinaryPush_injective X U n
    rw [coverOrdinaryDifference_push_fst, coverSubsetPush_ambient]
  · apply coverOrdinaryPush_injective X V n
    rw [coverOrdinaryDifference_push_snd, map_neg, coverSubsetPush_ambient]

theorem coverSubsetPush_boundary (X : TopCat) (A B : Set X) (h : A ⊆ B) (n : ℕ)
    (c : coverOrdinaryChains X A (n + 1)) :
    singularBoundaryFinsupp (TopCat.of B) n (coverSubsetPush X A B h (n + 1) c) =
      coverSubsetPush X A B h n (singularBoundaryFinsupp (TopCat.of A) n c) := by
  apply coverOrdinaryPush_injective X B n
  rw [← coverOrdinaryPush_boundary, coverSubsetPush_ambient, coverSubsetPush_ambient,
    coverOrdinaryPush_boundary]

theorem coverSmallBoundary_square (X : TopCat) (U V : Set X) (n : ℕ)
    (c : coverSmallChains X U V (n + 2)) :
    smallSingularBoundary X V Uᶜ n (smallSingularBoundary X V Uᶜ (n + 1) c) = 0 := by
  apply Subtype.ext
  exact singularBoundaryFinsupp_comp_zero X n c.1

theorem coverOrdinaryPairBoundary_square (X : TopCat) (U V : Set X) (n : ℕ)
    (c : coverOrdinaryChains X U (n + 2) × coverOrdinaryChains X V (n + 2)) :
    coverOrdinaryPairBoundary X U V n (coverOrdinaryPairBoundary X U V (n + 1) c) = 0 :=
  Prod.ext (singularBoundaryFinsupp_comp_zero (TopCat.of U) n c.1)
    (singularBoundaryFinsupp_comp_zero (TopCat.of V) n c.2)

end CurveComplexGenusTwo.CWHurewicz
