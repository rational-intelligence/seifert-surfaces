import CurveComplexGenusTwo.CWHurewicz.AffineConeFaces
import CurveComplexGenusTwo.CWHurewicz.BarycentricFlag

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace CurveComplexGenusTwo.CWHurewicz

open Convexity

noncomputable def singularChainsFinsuppIso (X : TopCat) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X n ≅
      ModuleCat.of ℤ ((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan
    (ModuleCat.of ℤ ℤ) n).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit ℤ ℤ
        ((TopCat.toSSet.obj X) _⦋n⦌))

theorem singularChainsFinsuppIso_generator (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    ((TopCat.toSSet.obj X).ιChainComplex x ≫
      (singularChainsFinsuppIso X n).hom).hom 1 = Finsupp.single x 1 := by
  have h := ((TopCat.toSSet.obj X).isColimitChainComplexXCofan
    (ModuleCat.of ℤ ℤ) n).comp_coconePointUniqueUpToIso_hom
      (ModuleCat.finsuppCoconeIsColimit ℤ ℤ
        ((TopCat.toSSet.obj X) _⦋n⦌)) ⟨x⟩
  exact congrArg (fun f : ModuleCat.of ℤ ℤ ⟶
    ModuleCat.of ℤ ((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) => f.hom 1) h

private theorem affineSimplex_continuous {n m : ℕ}
    (f : affineSimplex n m) : Continuous f := by
  obtain ⟨g, rfl⟩ := StdSimplex.affineMapMk_surjective f
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (m + 1))).continuous_iff]
  change Continuous (fun t : StdSimplex ℝ (Fin (n + 1)) =>
    ((StdSimplex.affineMapMk g t).weights : Fin (m + 1) → ℝ))
  simp only [StdSimplex.affineMapMk_apply]
  apply continuous_pi
  intro i
  change Continuous (fun t : StdSimplex ℝ (Fin (n + 1)) =>
    ((iConvexComb t g).weights) i)
  rw [show (fun t : StdSimplex ℝ (Fin (n + 1)) =>
      ((iConvexComb t g).weights) i) =
      (fun t => (t.weights.sum (fun j r => r • (g j).weights)) i) by
    funext t; simp [iConvexComb, StdSimplex.weights_sConvexComb,
      Finsupp.sum_mapDomain_index, add_smul]]
  have h (t : StdSimplex ℝ (Fin (n + 1))) :
      (t.weights.sum (fun j r => r • (g j).weights)) i =
        ∑ j : Fin (n + 1), t.weights j * (g j).weights i := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp
  rw [show (fun t : StdSimplex ℝ (Fin (n + 1)) =>
      (t.weights.sum (fun j r => r • (g j).weights)) i) =
      (fun t => ∑ j : Fin (n + 1), t.weights j * (g j).weights i) by
    funext t; exact h t]
  fun_prop

noncomputable def affineAsSingular (n m : ℕ)
    (f : affineSimplex n m) :
    (TopCat.toSSet.obj (TopCat.of (StdSimplex ℝ (Fin (m + 1))))) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv
    (TopCat.of (StdSimplex ℝ (Fin (m + 1)))) (.op ⦋n⦌)).symm
      ⟨f, affineSimplex_continuous f⟩

theorem affineAsSingular_injective (n m : ℕ) :
    Function.Injective (affineAsSingular n m) := by
  intro f g h
  apply ConvexSpace.AffineMap.ext
  have heq := congrArg
    (TopCat.toSSetObjEquiv
      (TopCat.of (StdSimplex ℝ (Fin (m + 1)))) (.op ⦋n⦌)) h
  funext x
  exact ContinuousMap.congr_fun heq x

theorem affineAsSingular_face {n m : ℕ}
    (f : affineSimplex (n + 1) m) (i : Fin (n + 2)) :
    affineAsSingular n m (affineFace f i) =
      (TopCat.toSSet.obj
        (TopCat.of (StdSimplex ℝ (Fin (m + 1))))).δ i
          (affineAsSingular (n + 1) m f) := by
  apply (TopCat.toSSetObjEquiv
    (TopCat.of (StdSimplex ℝ (Fin (m + 1)))) (.op ⦋n⦌)).injective
  ext z
  rfl

theorem affineAsSingular_comp_flag (n m : ℕ)
    (f : affineSimplex n m) (σ : Equiv.Perm (Fin (n + 1))) :
    affineAsSingular n m (f.comp (barycentricFlagAffine n σ)) =
      barycentricFlagSingular
        (TopCat.of (StdSimplex ℝ (Fin (m + 1)))) n σ
        (affineAsSingular n m f) := by
  apply (TopCat.toSSetObjEquiv
    (TopCat.of (StdSimplex ℝ (Fin (m + 1)))) (.op ⦋n⦌)).injective
  ext z
  rfl

noncomputable def affineCarrier (n m : ℕ) :
    (affineSimplex n m →₀ ℤ) →ₗ[ℤ]
      ((TopCat.toSSet.obj
        (TopCat.of (StdSimplex ℝ (Fin (m + 1))))) _⦋n⦌ →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (affineAsSingular n m)

noncomputable def affineBarycentricDegree (n m : ℕ) :
    (affineSimplex n m →₀ ℤ) →ₗ[ℤ] (affineSimplex n m →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun f =>
    ∑ σ : Equiv.Perm (Fin (n + 1)),
      (σ.sign : ℤ) • Finsupp.single (f.comp (barycentricFlagAffine n σ)) 1)

noncomputable def singularBoundaryFinsupp (X : TopCat) (n : ℕ) :
    (((TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ) →ₗ[ℤ]
      ((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ)) :=
  ((singularChainsFinsuppIso X (n + 1)).inv ≫
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫
      (singularChainsFinsuppIso X n).hom).hom

theorem singularBoundaryFinsupp_single (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    singularBoundaryFinsupp X n (Finsupp.single x 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        Finsupp.single ((TopCat.toSSet.obj X).δ i x) 1 := by
  rw [← singularChainsFinsuppIso_generator X (n + 1) x]
  change (((TopCat.toSSet.obj X).ιChainComplex x ≫
    (singularChainsFinsuppIso X (n + 1)).hom ≫
    (singularChainsFinsuppIso X (n + 1)).inv ≫
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫
    (singularChainsFinsuppIso X n).hom).hom 1) = _
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp, ModuleCat.hom_sum, LinearMap.sum_apply,
    ModuleCat.hom_comp, LinearMap.comp_apply]
  congr 1
  funext i
  rcases neg_one_pow_eq_or ℤ i.val with h | h
  · simp only [h, one_smul]
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      singularChainsFinsuppIso_generator X n ((TopCat.toSSet.obj X).δ i x)
  · simp only [h, neg_smul, one_smul, ModuleCat.hom_neg, LinearMap.neg_apply,
      map_neg]
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      congrArg Neg.neg (singularChainsFinsuppIso_generator X n
        ((TopCat.toSSet.obj X).δ i x))

theorem affineCarrier_injective (n m : ℕ) :
    Function.Injective (affineCarrier n m) := by
  exact Finsupp.mapDomain_injective (affineAsSingular_injective n m)

theorem affineCarrier_boundary_single (n m : ℕ)
    (f : affineSimplex (n + 1) m) :
    affineCarrier n m (affineBoundaryMap n m (Finsupp.single f 1)) =
      singularBoundaryFinsupp
        (TopCat.of (StdSimplex ℝ (Fin (m + 1)))) n
        (Finsupp.single (affineAsSingular (n + 1) m f) 1) := by
  rw [singularBoundaryFinsupp_single]
  simp only [affineBoundaryMap, Finsupp.linearCombination_single]
  unfold affineBoundary
  simp only [one_smul]
  rw [map_sum]
  simp only [map_smul, affineCarrier, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← affineAsSingular_face]

theorem affineCarrier_boundary_compat (n m : ℕ)
    (c : affineSimplex (n + 1) m →₀ ℤ) :
    affineCarrier n m (affineBoundaryMap n m c) =
      singularBoundaryFinsupp
        (TopCat.of (StdSimplex ℝ (Fin (m + 1)))) n
        (affineCarrier (n + 1) m c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single f a =>
      have hs : Finsupp.single f a = a • Finsupp.single f 1 := by
        ext x
        by_cases hx : x = f <;> simp [hx]
      rw [hs]
      simp only [LinearMap.map_smul]
      simpa [affineCarrier, Finsupp.lmapDomain_apply] using
        congrArg (fun z => a • z) (affineCarrier_boundary_single n m f)

theorem singularBoundaryFinsupp_comp_zero (X : TopCat) (n : ℕ)
    (c : ((TopCat.toSSet.obj X) _⦋n + 2⦌ →₀ ℤ)) :
    singularBoundaryFinsupp X n
      (singularBoundaryFinsupp X (n + 1) c) = 0 := by
  unfold singularBoundaryFinsupp
  change (((singularChainsFinsuppIso X (n + 2)).inv ≫
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 2) (n + 1) ≫
    (singularChainsFinsuppIso X (n + 1)).hom ≫
    (singularChainsFinsuppIso X (n + 1)).inv ≫
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫
    (singularChainsFinsuppIso X n).hom).hom c) = 0
  simp only [Iso.hom_inv_id_assoc]
  have hd := ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d_comp_d
    (n + 2) (n + 1) n
  change ((singularChainsFinsuppIso X (n + 2)).inv ≫
    ((((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 2) (n + 1)) ≫
      (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n)) ≫
    (singularChainsFinsuppIso X n).hom).hom c = 0
  rw [hd]
  simp

theorem affineBoundaryMap_comp_zero (n m : ℕ)
    (c : affineSimplex (n + 2) m →₀ ℤ) :
    affineBoundaryMap n m (affineBoundaryMap (n + 1) m c) = 0 := by
  apply affineCarrier_injective n m
  rw [affineCarrier_boundary_compat, affineCarrier_boundary_compat]
  exact singularBoundaryFinsupp_comp_zero
    (TopCat.of (StdSimplex ℝ (Fin (m + 1)))) n (affineCarrier (n + 2) m c)



end CurveComplexGenusTwo.CWHurewicz
