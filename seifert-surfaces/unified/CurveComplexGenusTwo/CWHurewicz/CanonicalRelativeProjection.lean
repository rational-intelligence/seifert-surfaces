import CurveComplexGenusTwo.CWHurewicz.ExcisedQuotientIdentification

namespace CurveComplexGenusTwo.CWHurewicz
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

/-- The canonical cokernel projection after identifying free singular chains. -/
noncomputable def canonicalRelativeProjection (X : TopCat) (A : Set X) (n : ℕ) :
    ((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) →ₗ[ℤ] (relativeSingularChains X A).X n :=
  ((singularChainsFinsuppIso X n).inv ≫
    (cokernel.π (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (pairInclusion X A))).f n).hom

theorem canonicalRelativeProjection_surjective (X : TopCat) (A : Set X) (n : ℕ) :
    Function.Surjective (canonicalRelativeProjection X A n) := by
  have hi := (ModuleCat.epi_iff_surjective (singularChainsFinsuppIso X n).inv).mp
    (inferInstance : Epi (singularChainsFinsuppIso X n).inv)
  have hp := (ModuleCat.epi_iff_surjective
    ((cokernel.π (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (pairInclusion X A))).f n)).mp inferInstance
  exact hp.comp hi

theorem canonicalRelativeProjection_kernel (X : TopCat) (A : Set X) (n : ℕ) :
    LinearMap.ker (canonicalRelativeProjection X A n) = excisionSubspaceChains X A n := by
  let F := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ))
  let inc := F.map (pairInclusion X A)
  have exactAt := (ShortComplex.cokernelSequence_exact inc).map
    (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)
  have hrange := exactAt.moduleCat_range_eq_ker
  change LinearMap.range (inc.f n).hom = LinearMap.ker ((cokernel.π inc).f n).hom at hrange
  have hgen (Y : TopCat) (x : (TopCat.toSSet.obj Y) _⦋n⦌) :
      (singularChainsFinsuppIso Y n).inv (Finsupp.single x 1) =
        ((TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom 1 := by
    rw [← singularChainsFinsuppIso_generator Y n x]
    exact (singularChainsFinsuppIso Y n).hom_inv_id_apply _
  have hmap (c : (TopCat.toSSet.obj (TopCat.of ↥A)) _⦋n⦌ →₀ ℤ) :
      inc.f n ((singularChainsFinsuppIso (TopCat.of ↥A) n).inv c) =
        (singularChainsFinsuppIso X n).inv
          (Finsupp.lmapDomain ℤ ℤ ((TopCat.toSSet.map (pairInclusion X A)).app (.op ⦋n⦌)) c) := by
    classical
    have hs (x : (TopCat.toSSet.obj (TopCat.of ↥A)) _⦋n⦌) :
        inc.f n ((singularChainsFinsuppIso (TopCat.of ↥A) n).inv (Finsupp.single x 1)) =
          (singularChainsFinsuppIso X n).inv
            (Finsupp.lmapDomain ℤ ℤ ((TopCat.toSSet.map (pairInclusion X A)).app (.op ⦋n⦌))
              (Finsupp.single x 1)) := by
      simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hgen]
      exact congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ _ => f.hom 1)
        (SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map (pairInclusion X A))
          (ModuleCat.of ℤ ℤ) x)
    have hc : c = ∑ x ∈ c.support, c x • Finsupp.single x 1 := by
      conv_lhs => rw [← Finsupp.sum_single c]
      simp [Finsupp.sum, Finsupp.smul_single]
    change (inc.f n).hom ((singularChainsFinsuppIso (TopCat.of ↥A) n).inv.hom c) =
      (singularChainsFinsuppIso X n).inv.hom
        (Finsupp.lmapDomain ℤ ℤ ((TopCat.toSSet.map (pairInclusion X A)).app (.op ⦋n⦌)) c)
    rw [hc]
    change ((SSet.chainComplexMap (TopCat.toSSet.map (pairInclusion X A))
      (ModuleCat.of ℤ ℤ)).f n).hom _ = _
    simp only [map_sum, LinearMap.map_smul]
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    exact hs x
  have hsrange : Set.range ((TopCat.toSSet.map (pairInclusion X A)).app (.op ⦋n⦌)) =
      {x | Set.range (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x) ⊆ A} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩ z ⟨t, rfl⟩
      exact (TopCat.toSSetObjEquiv _ (.op ⦋n⦌) y t).property
    · intro hx
      let f := TopCat.toSSetObjEquiv X (.op ⦋n⦌) x
      let g : C(Convexity.StdSimplex ℝ (Fin (n + 1)), ↥A) :=
        ⟨fun t => ⟨f t, hx ⟨t, rfl⟩⟩, f.continuous.subtype_mk _⟩
      refine ⟨(TopCat.toSSetObjEquiv (TopCat.of ↥A) (.op ⦋n⦌)).symm g, ?_⟩
      apply (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).injective
      ext t
      change ((TopCat.toSSetObjEquiv (TopCat.of ↥A) (.op ⦋n⦌))
        ((TopCat.toSSetObjEquiv (TopCat.of ↥A) (.op ⦋n⦌)).symm g) t).val = f t
      simp [g]
  have hfreeRange : LinearMap.range (Finsupp.lmapDomain ℤ ℤ
      ((TopCat.toSSet.map (pairInclusion X A)).app (.op ⦋n⦌))) =
      excisionSubspaceChains X A n := by
    have h := Finsupp.lmapDomain_supported ℤ ℤ
      ((TopCat.toSSet.map (pairInclusion X A)).app (.op ⦋n⦌)) Set.univ
    simpa [Finsupp.supported_univ, Submodule.map_top, Set.image_univ,
      hsrange, excisionSubspaceChains] using h
  ext c
  change canonicalRelativeProjection X A n c = 0 ↔ _
  rw [← hfreeRange]
  constructor
  · intro hc
    have hp : (singularChainsFinsuppIso X n).inv c ∈
        LinearMap.ker ((cokernel.π inc).f n).hom := hc
    rw [← hrange] at hp
    obtain ⟨b, hb⟩ := hp
    let d := (singularChainsFinsuppIso (TopCat.of ↥A) n).hom b
    refine ⟨d, ?_⟩
    apply (ModuleCat.mono_iff_injective (singularChainsFinsuppIso X n).inv).mp inferInstance
    rw [← hmap]
    change inc.f n ((singularChainsFinsuppIso (TopCat.of ↥A) n).inv
      ((singularChainsFinsuppIso (TopCat.of ↥A) n).hom b)) = _
    exact (congrArg (fun y => inc.f n y)
      ((singularChainsFinsuppIso (TopCat.of ↥A) n).hom_inv_id_apply b)).trans hb
  · rintro ⟨d, rfl⟩
    change (cokernel.π inc).f n ((singularChainsFinsuppIso X n).inv _) = 0
    rw [← hmap]
    have hz := congrArg (fun f => f.f n) (cokernel.condition inc)
    exact congrArg (fun f : (F.obj (TopCat.of ↥A)).X n ⟶ _ =>
      f.hom ((singularChainsFinsuppIso (TopCat.of ↥A) n).inv d)) hz

theorem canonicalRelativeProjection_boundary (X : TopCat) (A : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ) :
    (relativeSingularChains X A).d (n + 1) n
      (canonicalRelativeProjection X A (n + 1) c) =
      canonicalRelativeProjection X A n (singularBoundaryFinsupp X n c) := by
  let p := cokernel.π
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (pairInclusion X A))
  change (p.f (n + 1) ≫ (relativeSingularChains X A).d (n + 1) n)
    ((singularChainsFinsuppIso X (n + 1)).inv c) = _
  dsimp only [relativeSingularChains]
  rw [p.comm]
  change p.f n _ = p.f n ((singularChainsFinsuppIso X n).inv
    ((singularChainsFinsuppIso X n).hom
      (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d
        (n + 1) n ((singularChainsFinsuppIso X (n + 1)).inv c))))
  exact congrArg (fun z => p.f n z)
    ((singularChainsFinsuppIso X n).hom_inv_id_apply _).symm

theorem canonicalRelativeProjection_excision (X : TopCat) (A U : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of (Excised X U))) _⦋n⦌ →₀ ℤ) :
    (excisionRelativeChainMap A U).f n
      (canonicalRelativeProjection (TopCat.of (Excised X U)) (excisedSubspace A U) n c) =
      canonicalRelativeProjection X A n (excisedChainPush X U n c) := by
  classical
  let Y := TopCat.of (Excised X U)
  let F := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ))
  let f := F.map (excisionInclusionX X U)
  have hgen (Z : TopCat) (x : (TopCat.toSSet.obj Z) _⦋n⦌) :
      (singularChainsFinsuppIso Z n).inv (Finsupp.single x 1) =
        ((TopCat.toSSet.obj Z).ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom 1 := by
    rw [← singularChainsFinsuppIso_generator Z n x]
    exact (singularChainsFinsuppIso Z n).hom_inv_id_apply _
  have hmap : f.f n ((singularChainsFinsuppIso Y n).inv c) =
      (singularChainsFinsuppIso X n).inv (excisedChainPush X U n c) := by
    have hs (x : (TopCat.toSSet.obj Y) _⦋n⦌) :
        f.f n ((singularChainsFinsuppIso Y n).inv (Finsupp.single x 1)) =
          (singularChainsFinsuppIso X n).inv (excisedChainPush X U n (Finsupp.single x 1)) := by
      simp only [excisedChainPush, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hgen]
      exact congrArg (fun g : ModuleCat.of ℤ ℤ ⟶ _ => g.hom 1)
        (SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map (excisionInclusionX X U))
          (ModuleCat.of ℤ ℤ) x)
    have hc : c = ∑ x ∈ c.support, c x • Finsupp.single x 1 := by
      conv_lhs => rw [← Finsupp.sum_single c]
      simp [Finsupp.sum, Finsupp.smul_single]
    change ((SSet.chainComplexMap (TopCat.toSSet.map (excisionInclusionX X U))
      (ModuleCat.of ℤ ℤ)).f n).hom ((singularChainsFinsuppIso Y n).inv.hom c) =
      (singularChainsFinsuppIso X n).inv.hom (excisedChainPush X U n c)
    rw [hc]
    simp only [map_sum, LinearMap.map_smul]
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    exact hs x
  have hπ : cokernel.π (F.map (pairInclusion (Excised X U) (excisedSubspace A U))) ≫
      excisionRelativeChainMap A U = f ≫ cokernel.π (F.map (pairInclusion X A)) :=
    cokernel.π_desc _ _ _
  have hn := congrArg (fun g => g.f n) hπ
  have he := congrArg (fun g : (F.obj Y).X n ⟶ _ =>
    g.hom ((singularChainsFinsuppIso Y n).inv c)) hn
  change (excisionRelativeChainMap A U).f n
    ((cokernel.π (F.map (pairInclusion (Excised X U) (excisedSubspace A U)))).f n
      ((singularChainsFinsuppIso Y n).inv c)) = _
  change (cokernel.π (F.map (pairInclusion (Excised X U) (excisedSubspace A U)))).f n ≫
    (excisionRelativeChainMap A U).f n = _ at hn
  change ((cokernel.π (F.map (pairInclusion (Excised X U) (excisedSubspace A U)))).f n ≫
    (excisionRelativeChainMap A U).f n) ((singularChainsFinsuppIso Y n).inv c) = _
  rw [hn]
  change (cokernel.π (F.map (pairInclusion X A))).f n
    (f.f n ((singularChainsFinsuppIso Y n).inv c)) = _
  rw [hmap]
  rfl

end CurveComplexGenusTwo.CWHurewicz
