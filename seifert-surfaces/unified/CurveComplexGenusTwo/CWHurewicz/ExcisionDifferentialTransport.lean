import CurveComplexGenusTwo.CWHurewicz.ExcisedQuotientIdentification
import CurveComplexGenusTwo.CWHurewicz.CanonicalRelativeProjection

set_option backward.isDefEq.respectTransparency false

namespace CurveComplexGenusTwo.CWHurewicz
open CategoryTheory
open scoped Simplicial
 theorem excisionChain_reflects_boundary
    (X : Type) [TopologicalSpace X] (A U : Set X)
    (hU : closure U ⊆ interior A) (n : ℕ)
    (x : (relativeSingularChains (Excised X U) (excisedSubspace A U)).X (n+1))
    (hx : (relativeSingularChains (Excised X U) (excisedSubspace A U)).d (n+1) n x = 0)
    (b : (relativeSingularChains X A).X (n+2))
    (hb : (excisionRelativeChainMap A U).f (n+1) x = (relativeSingularChains X A).d (n+2) (n+1) b) :
    ∃ d : (relativeSingularChains (Excised X U) (excisedSubspace A U)).X (n+2),
      (relativeSingularChains (Excised X U) (excisedSubspace A U)).d (n+2) (n+1) d = x := by
  let Y := TopCat.of (Excised X U)
  let B := excisedSubspace A U
  have pzero (Z : TopCat) (C : Set Z) (i : ℕ) (c : (TopCat.toSSet.obj Z) _⦋i⦌ →₀ ℤ) :
      canonicalRelativeProjection Z C i c = 0 ↔ c ∈ excisionSubspaceChains Z C i := by
    change c ∈ LinearMap.ker (canonicalRelativeProjection Z C i) ↔ _
    rw [canonicalRelativeProjection_kernel]
  obtain ⟨c, rfl⟩ := canonicalRelativeProjection_surjective Y B (n+1) x
  obtain ⟨a, rfl⟩ := canonicalRelativeProjection_surjective (TopCat.of X) A (n+2) b
  rw [canonicalRelativeProjection_boundary Y B n] at hx
  rw [canonicalRelativeProjection_excision (TopCat.of X) A U (n+1),
    canonicalRelativeProjection_boundary (TopCat.of X) A (n+1)] at hb
  have hz := (excisedChainPushToSmall (TopCat.of X) A U (n+1) c).2
  have hcy : singularBoundaryFinsupp (TopCat.of X) n
      (excisedChainPush (TopCat.of X) U (n+1) c) ∈ excisionSubspaceChains (TopCat.of X) A n := by
    rw [excisedChainPush_boundary]
    exact (excisedChainPush_subspace_iff (TopCat.of X) A U n _).mpr ((pzero Y B n _).mp hx)
  have hres := (pzero (TopCat.of X) A (n+1)
    (excisedChainPush (TopCat.of X) U (n+1) c - singularBoundaryFinsupp (TopCat.of X) (n+1) a)).mp (by rw [map_sub, hb, sub_self])
  obtain ⟨a', ha', he⟩ := relativeSmallCycle_has_small_filling (TopCat.of X) A U hU n _ hz
    (fun s hs => hcy hs) a (fun s hs => hres hs)
  rw [smallSingularChains_eq_sup] at ha'
  obtain ⟨v, hv, w, hw, heq⟩ := Submodule.mem_sup.mp ha'
  rw [← excisedChainPush_range] at hv
  obtain ⟨d, rfl⟩ := hv
  have hde : a' - excisedChainPush (TopCat.of X) U (n+2) d ∈ excisionSubspaceChains (TopCat.of X) A (n+2) := by
    have e : a' - excisedChainPush (TopCat.of X) U (n+2) d = w := by rw [← heq]; abel
    rw [e]; exact hw
  have hp : canonicalRelativeProjection (TopCat.of X) A (n+2) a' =
      canonicalRelativeProjection (TopCat.of X) A (n+2) (excisedChainPush (TopCat.of X) U (n+2) d) := by
    simpa only [map_sub, sub_eq_zero] using (pzero (TopCat.of X) A (n+2) _).mpr hde
  refine ⟨canonicalRelativeProjection Y B (n+2) d, ?_⟩
  rw [canonicalRelativeProjection_boundary Y B (n+1)]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (pzero Y B (n+1) _).mpr
  apply (excisedChainPush_subspace_iff (TopCat.of X) A U (n+1) _).mp
  apply (pzero (TopCat.of X) A (n+1) _).mp
  rw [map_sub, ← excisedChainPush_boundary, map_sub]
  have hr := (pzero (TopCat.of X) A (n+1) _).mpr (show _ ∈ excisionSubspaceChains (TopCat.of X) A (n+1) from fun s hs => he s hs)
  rw [map_sub, sub_eq_zero] at hr
  rw [← canonicalRelativeProjection_boundary (TopCat.of X) A (n+1), ← hp,
    canonicalRelativeProjection_boundary (TopCat.of X) A (n+1), ← hr]
  exact sub_self _


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

noncomputable def excisedRelativeQuotientBoundary
    (X : TopCat) (A U : Set X) (n : ℕ) :
    excisedRelativeChainQuotient X A U (n + 1) →ₗ[ℤ]
      excisedRelativeChainQuotient X A U n :=
  Submodule.mapQ _ _ (singularBoundaryFinsupp (TopCat.of (Excised X U)) n) (by
    intro c hc
    exact excisionSubspaceChains_boundary _ _ n c hc)

noncomputable def smallRelativeQuotientBoundary
    (X : TopCat) (A U : Set X) (n : ℕ) :
    smallRelativeChainQuotient X A U (n + 1) →ₗ[ℤ]
      smallRelativeChainQuotient X A U n :=
  Submodule.mapQ _ _ (smallSingularBoundary X A U n) (by
    intro c hc
    exact excisionSubspaceChains_boundary X A n c.1 hc)

theorem excisedRelativeQuotientBoundary_square
    (X : TopCat) (A U : Set X) (n : ℕ)
    (q : excisedRelativeChainQuotient X A U (n + 2)) :
    excisedRelativeQuotientBoundary X A U n
      (excisedRelativeQuotientBoundary X A U (n + 1) q) = 0 := by
  obtain ⟨c, rfl⟩ := (excisionSubspaceChains (TopCat.of (Excised X U))
    (excisedSubspace A U) (n + 2)).mkQ_surjective q
  change Submodule.Quotient.mk (singularBoundaryFinsupp _ n
    (singularBoundaryFinsupp _ (n + 1) c)) = _
  rw [singularBoundaryFinsupp_comp_zero]
  rfl

theorem smallRelativeQuotientBoundary_square
    (X : TopCat) (A U : Set X) (n : ℕ)
    (q : smallRelativeChainQuotient X A U (n + 2)) :
    smallRelativeQuotientBoundary X A U n
      (smallRelativeQuotientBoundary X A U (n + 1) q) = 0 := by
  obtain ⟨c, rfl⟩ := ((excisionSubspaceChains X A (n + 2)).comap
    (smallSingularChains X A U (n + 2)).subtype).mkQ_surjective q
  change Submodule.Quotient.mk
    (smallSingularBoundary X A U n (smallSingularBoundary X A U (n + 1) c)) = _
  have hc : smallSingularBoundary X A U n
      (smallSingularBoundary X A U (n + 1) c) = 0 := by
    apply Subtype.ext
    exact singularBoundaryFinsupp_comp_zero X n c.1
  rw [hc]
  rfl

theorem excisedRelativeChainQuotientMap_boundary
    (X : TopCat) (A U : Set X) (n : ℕ)
    (q : excisedRelativeChainQuotient X A U (n + 1)) :
    smallRelativeQuotientBoundary X A U n
      (excisedRelativeChainQuotientMap X A U (n + 1) q) =
    excisedRelativeChainQuotientMap X A U n
      (excisedRelativeQuotientBoundary X A U n q) := by
  obtain ⟨c, rfl⟩ := (excisionSubspaceChains (TopCat.of (Excised X U))
    (excisedSubspace A U) (n + 1)).mkQ_surjective q
  change Submodule.Quotient.mk (smallSingularBoundary X A U n
    (excisedChainPushToSmall X A U (n + 1) c)) =
    Submodule.Quotient.mk (excisedChainPushToSmall X A U n
      (singularBoundaryFinsupp (TopCat.of (Excised X U)) n c))
  congr 1
  apply Subtype.ext
  exact excisedChainPush_boundary X U n c

/-- The canonical homology map induced by the actual excision inclusion,
in every positive degree. No comparison equivalence is a hypothesis. -/
theorem canonicalExcisionHomologyMap_isIso
    (X : Type) [TopologicalSpace X] (A U : Set X)
    (hU : closure U ⊆ interior A) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (excisionRelativeChainMap A U) (n + 1)) := by
  let projection (Y : TopCat) (B : Set Y) (i : ℕ) :=
    ((singularChainsFinsuppIso Y i).inv ≫
      (CategoryTheory.Limits.cokernel.π
        (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (pairInclusion Y B))).f i)
  have projection_surjective (Y : TopCat) (B : Set Y) (i : ℕ) :
      Function.Surjective (projection Y B i) := by
    have : CategoryTheory.Epi
        ((CategoryTheory.Limits.cokernel.π
          (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
            (ModuleCat.of ℤ ℤ)).map (pairInclusion Y B))).f i) := by
      infer_instance
    have hi := (ModuleCat.epi_iff_surjective (singularChainsFinsuppIso Y i).inv).mp
      (inferInstance : Epi (singularChainsFinsuppIso Y i).inv)
    have hp := (ModuleCat.epi_iff_surjective
      ((CategoryTheory.Limits.cokernel.π
          (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
            (ModuleCat.of ℤ ℤ)).map (pairInclusion Y B))).f i)).mp inferInstance
    exact hp.comp hi
  have projection_boundary (Y : TopCat) (B : Set Y) (i : ℕ)
      (c : (TopCat.toSSet.obj Y) _⦋i + 1⦌ →₀ ℤ) :
      (relativeSingularChains Y B).d (i + 1) i (projection Y B (i + 1) c) =
        projection Y B i (singularBoundaryFinsupp Y i c) := by
    let p := CategoryTheory.Limits.cokernel.π
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (pairInclusion Y B))
    have h := p.comm (i + 1) i
    have hc := congrArg (fun f => f ((singularChainsFinsuppIso Y (i + 1)).inv c)) h
    change (p.f (i + 1) ≫ (relativeSingularChains Y B).d (i + 1) i)
      ((singularChainsFinsuppIso Y (i + 1)).inv c) = _
    dsimp only [relativeSingularChains]
    rw [p.comm]
    change p.f i (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ ℤ)).d
      (i + 1) i ((singularChainsFinsuppIso Y (i + 1)).inv c)) = _
    change p.f i _ = p.f i ((singularChainsFinsuppIso Y i).inv
      ((singularChainsFinsuppIso Y i).hom
        (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ ℤ)).d
          (i + 1) i ((singularChainsFinsuppIso Y (i + 1)).inv c))))
    exact congrArg (fun z => p.f i z)
      ((singularChainsFinsuppIso Y i).hom_inv_id_apply _).symm
  let Y := TopCat.of (Excised X U)
  let B := excisedSubspace A U
  let K := relativeSingularChains (Excised X U) B
  let L := relativeSingularChains X A
  let f := excisionRelativeChainMap A U
  have pzero (Z : TopCat) (C : Set Z) (i : ℕ) (c : (TopCat.toSSet.obj Z) _⦋i⦌ →₀ ℤ) :
      canonicalRelativeProjection Z C i c = 0 ↔ c ∈ excisionSubspaceChains Z C i := by
    change c ∈ LinearMap.ker (canonicalRelativeProjection Z C i) ↔ _
    rw [canonicalRelativeProjection_kernel]
  have splitSmall (i : ℕ) (c : (TopCat.toSSet.obj (TopCat.of X)) _⦋i⦌ →₀ ℤ)
      (hc : c ∈ smallSingularChains (TopCat.of X) A U i) :
      ∃ d : (TopCat.toSSet.obj Y) _⦋i⦌ →₀ ℤ,
        c - excisedChainPush (TopCat.of X) U i d ∈ excisionSubspaceChains (TopCat.of X) A i := by
    rw [smallSingularChains_eq_sup] at hc
    obtain ⟨v, hv, a, ha, heq⟩ := Submodule.mem_sup.mp hc
    rw [← excisedChainPush_range] at hv
    obtain ⟨d, rfl⟩ := hv
    refine ⟨d, ?_⟩
    have h : c - excisedChainPush (TopCat.of X) U i d = a := by rw [← heq]; abel
    rw [h]
    exact ha
  have chainSurj (y : L.X (n + 1)) (hy : L.d (n + 1) n y = 0) :
      ∃ x : K.X (n + 1), K.d (n + 1) n x = 0 ∧
        ∃ b : L.X (n + 2), f.f (n + 1) x - y = L.d (n + 2) (n + 1) b := by
    obtain ⟨c, rfl⟩ := canonicalRelativeProjection_surjective (TopCat.of X) A (n + 1) y
    dsimp only [L] at hy
    rw [canonicalRelativeProjection_boundary (TopCat.of X) A n] at hy
    have hc := (pzero (TopCat.of X) A n _).mp hy
    obtain ⟨z, hz, hcycle, b, hb⟩ := relativeCycle_has_small_representative
      (TopCat.of X) A U hU n c (fun x hx => hc hx)
    obtain ⟨d, hd⟩ := splitSmall (n + 1) z hz
    have hdproj : canonicalRelativeProjection (TopCat.of X) A (n + 1)
        (excisedChainPush (TopCat.of X) U (n + 1) d) =
        canonicalRelativeProjection (TopCat.of X) A (n + 1) z := by
      have := (pzero (TopCat.of X) A (n + 1) _).mpr hd
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    refine ⟨canonicalRelativeProjection Y B (n + 1) d, ?_,
      canonicalRelativeProjection (TopCat.of X) A (n + 2) b, ?_⟩
    · dsimp only [K]
      rw [canonicalRelativeProjection_boundary Y B n]
      apply (pzero Y B n _).mpr
      apply (excisedChainPush_subspace_iff (TopCat.of X) A U n _).mp
      rw [← excisedChainPush_boundary]
      apply (pzero (TopCat.of X) A n _).mp
      rw [← canonicalRelativeProjection_boundary (TopCat.of X) A n, hdproj,
        canonicalRelativeProjection_boundary (TopCat.of X) A n]
      exact (pzero (TopCat.of X) A n _).mpr (fun x hx => hcycle x hx)
    · dsimp only [f, L, Y, B]
      rw [canonicalRelativeProjection_excision (TopCat.of X) A U (n + 1), hdproj,
        canonicalRelativeProjection_boundary (TopCat.of X) A (n + 1)]
      have hh := (pzero (TopCat.of X) A (n + 1) _).mpr (fun x hx => hb x hx)
      simpa only [map_sub, sub_eq_zero] using hh
  have cycleLift (M : ChainComplex (ModuleCat.{0} ℤ) ℕ)
      (x : M.X (n + 1)) (hx : M.d (n + 1) n x = 0) :
      ∃ z : M.cycles (n + 1), M.iCycles (n + 1) z = x := by
    let v : (M.sc (n + 1)).moduleCatLeftHomologyData.K := ⟨x, by
      change M.d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) x = 0
      rw [(ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (n+1) n from rfl)]
      exact hx⟩
    refine ⟨(M.sc (n + 1)).moduleCatCyclesIso.inv v, ?_⟩
    exact congrArg (fun q => q v) ((M.sc (n + 1)).moduleCatCyclesIso_inv_iCycles)
  have classEq (M : ChainComplex (ModuleCat.{0} ℤ) ℕ)
      (z w : M.cycles (n + 1)) :
      M.homologyπ (n + 1) z = M.homologyπ (n + 1) w ↔
      ∃ b : M.X (n + 2), M.d (n + 2) (n + 1) b =
        M.iCycles (n + 1) z - M.iCycles (n + 1) w := by
    rw [← (ModuleCat.mono_iff_injective (M.homologyι (n + 1))).mp
      inferInstance |>.eq_iff]
    have hh := M.homology_π_ι (n + 1)
    change (M.homologyπ (n + 1) ≫ M.homologyι (n + 1)) z =
      (M.homologyπ (n + 1) ≫ M.homologyι (n + 1)) w ↔ _
    rw [hh]
    have h := (M.sc (n + 1)).moduleCat_pOpcycles_eq_iff
      (M.iCycles (n + 1) z) (M.iCycles (n + 1) w)
    change _ ↔ ∃ b : M.X ((ComplexShape.down ℕ).prev (n + 1)),
      M.d _ (n + 1) b = M.iCycles (n + 1) z - M.iCycles (n + 1) w at h
    rw [(ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n+2) (n+1) from rfl)] at h
    exact h
  have homSurj : Function.Surjective (HomologicalComplex.homologyMap f (n + 1)) := by
    intro y
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (L.homologyπ (n + 1))).mp inferInstance y
    have hz : L.d (n + 1) n (L.iCycles (n + 1) z) = 0 :=
      congrArg (fun q => q z) (L.iCycles_d (n + 1) n)
    obtain ⟨x, hx, b, hb⟩ := chainSurj (L.iCycles (n + 1) z) hz
    obtain ⟨w, hw⟩ := cycleLift K x hx
    refine ⟨K.homologyπ (n + 1) w, ?_⟩
    change (K.homologyπ (n + 1) ≫ HomologicalComplex.homologyMap f (n + 1)) w = _
    rw [HomologicalComplex.homologyπ_naturality]
    apply (classEq L _ z).mpr
    refine ⟨b, ?_⟩
    have hh := congrArg (fun q => q w) (HomologicalComplex.cyclesMap_i f (n + 1))
    change L.iCycles (n + 1) (HomologicalComplex.cyclesMap f (n + 1) w) =
      f.f (n + 1) (K.iCycles (n + 1) w) at hh
    erw [hh, hw]
    exact hb.symm
  have homInj : Function.Injective (HomologicalComplex.homologyMap f (n + 1)) := by
    intro a a' he
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ (n + 1))).mp inferInstance a
    obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ (n + 1))).mp inferInstance a'
    have hn := HomologicalComplex.homologyπ_naturality f (n + 1)
    change (K.homologyπ (n + 1) ≫ HomologicalComplex.homologyMap f (n + 1)) z =
      (K.homologyπ (n + 1) ≫ HomologicalComplex.homologyMap f (n + 1)) w at he
    rw [hn] at he
    obtain ⟨b, hb⟩ := (classEq L _ _).mp he
    have hz := congrArg (fun q => q z) (HomologicalComplex.cyclesMap_i f (n + 1))
    have hw := congrArg (fun q => q w) (HomologicalComplex.cyclesMap_i f (n + 1))
    change L.iCycles (n + 1) (HomologicalComplex.cyclesMap f (n + 1) z) =
      f.f (n + 1) (K.iCycles (n + 1) z) at hz
    change L.iCycles (n + 1) (HomologicalComplex.cyclesMap f (n + 1) w) =
      f.f (n + 1) (K.iCycles (n + 1) w) at hw
    erw [hz, hw, ← map_sub] at hb
    apply (classEq K z w).mpr
    apply excisionChain_reflects_boundary X A U hU n _ _ b hb.symm
    rw [map_sub]
    have hcz := congrArg (fun q => q z) (K.iCycles_d (n + 1) n)
    have hcw := congrArg (fun q => q w) (K.iCycles_d (n + 1) n)
    change K.d (n + 1) n (K.iCycles (n + 1) z) = 0 at hcz
    change K.d (n + 1) n (K.iCycles (n + 1) w) = 0 at hcw
    rw [hcz, hcw, sub_self]
  have : Epi (HomologicalComplex.homologyMap f (n + 1)) :=
    (ModuleCat.epi_iff_surjective _).mpr homSurj
  have : Mono (HomologicalComplex.homologyMap f (n + 1)) :=
    (ModuleCat.mono_iff_injective _).mpr homInj
  exact CategoryTheory.isIso_of_mono_of_epi _

end CurveComplexGenusTwo.CWHurewicz
