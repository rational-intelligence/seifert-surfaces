import CurveComplexGenusTwo.CWHurewicz.AffineCarrier

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace CurveComplexGenusTwo.CWHurewicz

open Convexity

private noncomputable abbrev singularChains' (X : TopCat) :=
  (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)

private theorem mapDomain_finset_sum {α β ι : Type*} [DecidableEq β]
    (f : α → β) (s : Finset ι) (g : ι → α →₀ ℤ) :
    Finsupp.mapDomain f (∑ i ∈ s, g i) =
      ∑ i ∈ s, Finsupp.mapDomain f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finsupp.mapDomain_add, ih]

noncomputable def singularBarycentricFinsupp (X : TopCat) (n : ℕ) :
    (((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) →ₗ[ℤ]
      ((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ)) :=
  ((singularChainsFinsuppIso X n).inv ≫ barycentricDegree X n ≫
    (singularChainsFinsuppIso X n).hom).hom

theorem singularBarycentricFinsupp_single (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularBarycentricFinsupp X n (Finsupp.single x 1) =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        (σ.sign : ℤ) • Finsupp.single (barycentricFlagSingular X n σ x) 1 := by
  rw [← singularChainsFinsuppIso_generator X n x]
  change (((TopCat.toSSet.obj X).ιChainComplex x ≫
    (singularChainsFinsuppIso X n).hom ≫
    (singularChainsFinsuppIso X n).inv ≫ barycentricDegree X n ≫
    (singularChainsFinsuppIso X n).hom).hom 1) = _
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, barycentricDegree_generator]
  simp only [Preadditive.sum_comp, Linear.smul_comp, ModuleCat.hom_sum,
    LinearMap.sum_apply]
  congr 1
  funext σ
  rw [← singularChainsFinsuppIso_generator X n
    (barycentricFlagSingular X n σ x)]
  simp

theorem affineCarrier_barycentric (n m : ℕ)
    (c : affineSimplex n m →₀ ℤ) :
    affineCarrier n m (affineBarycentricDegree n m c) =
      singularBarycentricFinsupp
        (TopCat.of (StdSimplex ℝ (Fin (m + 1)))) n
        (affineCarrier n m c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single f a =>
      have hs : Finsupp.single f a = a • Finsupp.single f 1 := by
        ext z
        by_cases hz : z = f <;> simp [hz]
      rw [hs]
      simp only [LinearMap.map_smul]
      rw [affineBarycentricDegree, Finsupp.linearCombination_single]
      simp only [affineCarrier, Finsupp.lmapDomain_apply]
      simp only [one_smul]
      rw [mapDomain_finset_sum]
      simp_rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single]
      rw [singularBarycentricFinsupp_single]
      simp only [affineAsSingular_comp_flag]

theorem singularBarycentric_boundary_compat (X : TopCat) (n : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ) :
    singularBoundaryFinsupp X n
        (singularBarycentricFinsupp X (n + 1) c) =
      singularBarycentricFinsupp X n
        (singularBoundaryFinsupp X n c) := by
  have h := congrArg
    (fun q => (singularChainsFinsuppIso X (n + 1)).inv ≫ q ≫
      (singularChainsFinsuppIso X n).hom)
    (barycentricDegree_chain_identity X n)
  simp only [Category.assoc] at h
  simpa [singularBarycentricFinsupp, singularBoundaryFinsupp,
    singularChains',
    ModuleCat.hom_comp, LinearMap.comp_apply] using congrArg (fun q => q.hom c) h

theorem affineBarycentric_boundary_compat (n m : ℕ)
    (c : affineSimplex (n + 1) m →₀ ℤ) :
    affineBoundaryMap n m (affineBarycentricDegree (n + 1) m c) =
      affineBarycentricDegree n m (affineBoundaryMap n m c) := by
  apply affineCarrier_injective
  calc
    _ = singularBoundaryFinsupp
        (TopCat.of (StdSimplex ℝ (Fin (m + 1)))) n
        (affineCarrier (n + 1) m
          (affineBarycentricDegree (n + 1) m c)) :=
          affineCarrier_boundary_compat n m _
    _ = singularBoundaryFinsupp
        (TopCat.of (StdSimplex ℝ (Fin (m + 1)))) n
        (singularBarycentricFinsupp
          (TopCat.of (StdSimplex ℝ (Fin (m + 1)))) (n + 1)
          (affineCarrier (n + 1) m c)) := by rw [affineCarrier_barycentric]
    _ = singularBarycentricFinsupp
        (TopCat.of (StdSimplex ℝ (Fin (m + 1)))) n
        (singularBoundaryFinsupp
          (TopCat.of (StdSimplex ℝ (Fin (m + 1)))) n
          (affineCarrier (n + 1) m c)) :=
          singularBarycentric_boundary_compat _ n _
    _ = singularBarycentricFinsupp
        (TopCat.of (StdSimplex ℝ (Fin (m + 1)))) n
        (affineCarrier n m (affineBoundaryMap n m c)) := by
          rw [affineCarrier_boundary_compat]
    _ = affineCarrier n m
        (affineBarycentricDegree n m (affineBoundaryMap n m c)) :=
          (affineCarrier_barycentric n m _).symm

theorem affineBarycentricDegree_zero (m : ℕ)
    (c : affineSimplex 0 m →₀ ℤ) :
    affineBarycentricDegree 0 m c = c := by
  classical
  apply affineCarrier_injective
  rw [affineCarrier_barycentric]
  simp [singularBarycentricFinsupp, barycentricDegree_zero]

noncomputable def standardAffineIdentity (n : ℕ) : affineSimplex n n :=
  StdSimplex.affineMap (R := ℝ) (Equiv.refl (Fin (n + 1)))

noncomputable def affineFaceInclusion (n : ℕ) (i : Fin (n + 2)) :
    affineSimplex n (n + 1) :=
  StdSimplex.affineMap (R := ℝ) i.succAbove

noncomputable def affinePostcompose (k m l : ℕ)
    (g : affineSimplex m l) :
    (affineSimplex k m →₀ ℤ) →ₗ[ℤ] (affineSimplex k l →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun f => g.comp f)

theorem affinePostcompose_boundary (n m l : ℕ)
    (g : affineSimplex m l) (c : affineSimplex (n + 1) m →₀ ℤ) :
    affineBoundaryMap n l (affinePostcompose (n + 1) m l g c) =
      affinePostcompose n m l g (affineBoundaryMap n m c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single f a =>
      simp only [affinePostcompose, affineBoundaryMap,
        Finsupp.lmapDomain_apply, Finsupp.linearCombination_single,
        LinearMap.map_smul]
      unfold affineBoundary
      simp only [Finsupp.mapDomain_single,
        Finsupp.linearCombination_single]
      rw [mapDomain_finset_sum]
      simp_rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single]
      congr 1

theorem affinePostcompose_comp (k m l r : ℕ)
    (g : affineSimplex l r) (h : affineSimplex m l)
    (c : affineSimplex k m →₀ ℤ) :
    affinePostcompose k l r g (affinePostcompose k m l h c) =
      affinePostcompose k m r (g.comp h) c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single f a =>
      simp only [affinePostcompose, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single]
      congr 1

theorem affinePostcompose_barycentric (n m l : ℕ)
    (g : affineSimplex m l) (c : affineSimplex n m →₀ ℤ) :
    affineBarycentricDegree n l (affinePostcompose n m l g c) =
      affinePostcompose n m l g (affineBarycentricDegree n m c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single f a =>
      simp only [affinePostcompose, affineBarycentricDegree,
        Finsupp.lmapDomain_apply, Finsupp.linearCombination_single,
        LinearMap.map_smul, Finsupp.mapDomain_single]
      rw [mapDomain_finset_sum]
      simp_rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single]
      congr 1

noncomputable def universalCarrierHomotopy (n : ℕ) :
    affineSimplex (n + 1) n →₀ ℤ :=
  Nat.rec (motive := fun k => affineSimplex (k + 1) k →₀ ℤ) 0
    (fun k prev => affineConeMap (k + 1) (k + 1)
        (StdSimplex.barycenter : StdSimplex ℝ (Fin (k + 2)))
        (affineBarycentricDegree (k + 1) (k + 1)
            (Finsupp.single (standardAffineIdentity (k + 1)) 1) -
          Finsupp.single (standardAffineIdentity (k + 1)) 1 -
          ∑ i : Fin (k + 2), (-1 : ℤ) ^ i.val •
            affinePostcompose (k + 1) k (k + 1)
              (affineFaceInclusion k i) prev)) n

noncomputable def universalCarrierObstruction (n : ℕ) :
    affineSimplex (n + 1) (n + 1) →₀ ℤ :=
  affineBarycentricDegree (n + 1) (n + 1)
      (Finsupp.single (standardAffineIdentity (n + 1)) 1) -
    Finsupp.single (standardAffineIdentity (n + 1)) 1 -
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
      affinePostcompose (n + 1) n (n + 1)
        (affineFaceInclusion n i) (universalCarrierHomotopy n)

noncomputable def affineUniversalHomotopy (n m : ℕ) :
    (affineSimplex n m →₀ ℤ) →ₗ[ℤ] (affineSimplex (n + 1) m →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun f =>
    affinePostcompose (n + 1) n m f (universalCarrierHomotopy n))

private theorem affineUniversalHomotopy_single (n m : ℕ)
    (f : affineSimplex n m) :
    affineUniversalHomotopy n m (Finsupp.single f 1) =
      affinePostcompose (n + 1) n m f (universalCarrierHomotopy n) := by
  simp [affineUniversalHomotopy]

private theorem affineBoundaryMap_single_identity (n : ℕ) :
    affineBoundaryMap n (n + 1)
        (Finsupp.single (standardAffineIdentity (n + 1)) 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        Finsupp.single (affineFaceInclusion n i) 1 := by
  simp only [affineBoundaryMap, Finsupp.linearCombination_single,
    affineBoundary, one_smul]
  congr 1
  funext i
  have hface : affineFace (standardAffineIdentity (n + 1)) i =
      affineFaceInclusion n i := by
    apply StdSimplex.affineMap_ext
    intro j
    simp [affineFace, affineFaceInclusion, standardAffineIdentity]
  rw [hface]

private theorem affineUniversalHomotopy_boundary_single (n m : ℕ)
    (f : affineSimplex (n + 1) m) :
    affineUniversalHomotopy n m
      (affineBoundaryMap n m (Finsupp.single f 1)) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        affinePostcompose (n + 1) n m (affineFace f i)
          (universalCarrierHomotopy n) := by
  classical
  simp only [affineBoundaryMap, Finsupp.linearCombination_single,
    affineBoundary, one_smul, map_sum, map_smul,
    affineUniversalHomotopy_single]

private theorem affinePostcompose_identity (k n : ℕ)
    (c : affineSimplex k n →₀ ℤ) :
    affinePostcompose k n n (standardAffineIdentity n) c = c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single f a =>
      simp only [affinePostcompose, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single]
      congr 1
      apply StdSimplex.affineMap_ext
      intro j
      simp [standardAffineIdentity]

private theorem affinePostcompose_face (k n m : ℕ)
    (f : affineSimplex (n + 1) m) (i : Fin (n + 2))
    (c : affineSimplex k n →₀ ℤ) :
    affinePostcompose k n m (affineFace f i) c =
      affinePostcompose k (n + 1) m f
        (affinePostcompose k n (n + 1) (affineFaceInclusion n i) c) := by
  rw [affinePostcompose_comp]
  rfl

private theorem affineUniversalHomotopy_boundary_succ_of (n m : ℕ)
    (h : affineBoundaryMap (n + 1) (n + 1)
      (universalCarrierHomotopy (n + 1)) = universalCarrierObstruction n)
    (c : affineSimplex (n + 1) m →₀ ℤ) :
    affineBoundaryMap (n + 1) m (affineUniversalHomotopy (n + 1) m c) +
      affineUniversalHomotopy n m (affineBoundaryMap n m c) =
      affineBarycentricDegree (n + 1) m c - c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      simp only [map_add]
      calc
        _ = ((affineBoundaryMap (n + 1) m)
              ((affineUniversalHomotopy (n + 1) m) c) +
              (affineUniversalHomotopy n m) ((affineBoundaryMap n m) c)) +
            ((affineBoundaryMap (n + 1) m)
              ((affineUniversalHomotopy (n + 1) m) d) +
              (affineUniversalHomotopy n m) ((affineBoundaryMap n m) d)) := by abel
        _ = ((affineBarycentricDegree (n + 1) m) c - c) +
              ((affineBarycentricDegree (n + 1) m) d - d) := by rw [hc, hd]
        _ = _ := by abel
  | single f a =>
      have hs : Finsupp.single f a = a • Finsupp.single f 1 := by
        ext q
        by_cases hq : q = f <;> simp [hq]
      rw [hs]
      simp only [LinearMap.map_smul, ← smul_add, ← smul_sub]
      congr 1
      rw [affineUniversalHomotopy_single,
        affinePostcompose_boundary, h,
        affineUniversalHomotopy_boundary_single]
      have hf : ∀ i : Fin (n + 2),
          affineFace f i = f.comp (affineFaceInclusion n i) := by
        intro i
        rfl
      simp_rw [affinePostcompose_face]
      calc
        _ = affinePostcompose (n + 1) (n + 1) m f
          (universalCarrierObstruction n +
            ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
              affinePostcompose (n + 1) n (n + 1)
                (affineFaceInclusion n i) (universalCarrierHomotopy n)) := by
                  simp only [map_add, map_sum, map_smul]
        _ = _ := by
          rw [show universalCarrierObstruction n +
          (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
            affinePostcompose (n + 1) n (n + 1)
              (affineFaceInclusion n i) (universalCarrierHomotopy n)) =
          affineBarycentricDegree (n + 1) (n + 1)
            (Finsupp.single (standardAffineIdentity (n + 1)) 1) -
          Finsupp.single (standardAffineIdentity (n + 1)) 1 by
              unfold universalCarrierObstruction
              abel]
          rw [map_sub, ← affinePostcompose_barycentric]
          simp [affinePostcompose, Finsupp.lmapDomain_apply,
            standardAffineIdentity]

private theorem universalCarrierObstruction_as_chain (n : ℕ) :
    universalCarrierObstruction n =
      affineBarycentricDegree (n + 1) (n + 1)
        (Finsupp.single (standardAffineIdentity (n + 1)) 1) -
      Finsupp.single (standardAffineIdentity (n + 1)) 1 -
      affineUniversalHomotopy n (n + 1)
        (affineBoundaryMap n (n + 1)
          (Finsupp.single (standardAffineIdentity (n + 1)) 1)) := by
  rw [affineBoundaryMap_single_identity]
  simp only [map_sum, map_smul, affineUniversalHomotopy_single]
  rfl

theorem universalCarrierHomotopy_succ (n : ℕ) :
    universalCarrierHomotopy (n + 1) =
      affineConeMap (n + 1) (n + 1)
        (StdSimplex.barycenter : StdSimplex ℝ (Fin (n + 2)))
        (universalCarrierObstruction n) := by
  rfl

theorem universalCarrierHomotopy_zero :
    universalCarrierHomotopy 0 =
      (0 : affineSimplex 1 0 →₀ ℤ) := by
  rfl

theorem universalCarrierHomotopy_boundary_zero :
    affineBoundaryMap 0 0 (universalCarrierHomotopy 0) = 0 := by
  simp [universalCarrierHomotopy]

theorem universalCarrierObstruction_cycle_zero :
    affineBoundaryMap 0 1 (universalCarrierObstruction 0) = 0 := by
  have hzero : universalCarrierHomotopy 0 = 0 := universalCarrierHomotopy_zero
  simp only [universalCarrierObstruction, hzero,
    map_zero, smul_zero, Finset.sum_const_zero, sub_zero]
  rw [map_sub, affineBarycentric_boundary_compat]
  rw [affineBarycentricDegree_zero]
  simp

theorem universalCarrierObstruction_cycle (n : ℕ) :
    affineBoundaryMap n (n + 1)
      (universalCarrierObstruction n) = 0 := by
  induction n with
  | zero => exact universalCarrierObstruction_cycle_zero
  | succ n ih =>
      have hboundary :
          affineBoundaryMap (n + 1) (n + 1)
            (universalCarrierHomotopy (n + 1)) =
              universalCarrierObstruction n := by
        rw [universalCarrierHomotopy_succ, affineBoundaryMap_cone,
          ih, map_zero]
        simp
      let e : affineSimplex (n + 2) (n + 2) →₀ ℤ :=
        Finsupp.single (standardAffineIdentity (n + 2)) 1
      have hdd : affineBoundaryMap n (n + 2)
          (affineBoundaryMap (n + 1) (n + 2) e) = 0 :=
        affineBoundaryMap_comp_zero n (n + 2) e
      have hh := affineUniversalHomotopy_boundary_succ_of n (n + 2)
        hboundary (affineBoundaryMap (n + 1) (n + 2) e)
      rw [hdd, map_zero, add_zero] at hh
      rw [universalCarrierObstruction_as_chain]
      change affineBoundaryMap (n + 1) (n + 2)
        (affineBarycentricDegree (n + 2) (n + 2) e - e -
          affineUniversalHomotopy (n + 1) (n + 2)
            (affineBoundaryMap (n + 1) (n + 2) e)) = 0
      simp only [map_sub, affineBarycentric_boundary_compat]
      rw [hh]
      abel

theorem universalCarrierHomotopy_boundary_succ (n : ℕ) :
    affineBoundaryMap (n + 1) (n + 1) (universalCarrierHomotopy (n + 1)) =
      universalCarrierObstruction n := by
  rw [universalCarrierHomotopy_succ,
    affineBoundaryMap_cone]
  rw [universalCarrierObstruction_cycle, map_zero]
  simp

theorem affineCarrierHomotopy_boundary_zero (m : ℕ)
    (c : affineSimplex 0 m →₀ ℤ) :
    affineBoundaryMap 0 m (affineUniversalHomotopy 0 m c) =
      affineBarycentricDegree 0 m c - c := by
  rw [affineBarycentricDegree_zero]
  have h : affineUniversalHomotopy 0 m c = 0 := by
    classical
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp [hc, hd]
    | single f a => simp [affineUniversalHomotopy, universalCarrierHomotopy]
  simp [h]

theorem affineCarrierHomotopy_boundary_succ (n m : ℕ)
    (c : affineSimplex (n + 1) m →₀ ℤ) :
    affineBoundaryMap (n + 1) m (affineUniversalHomotopy (n + 1) m c) +
      affineUniversalHomotopy n m (affineBoundaryMap n m c) =
      affineBarycentricDegree (n + 1) m c - c := by
  exact affineUniversalHomotopy_boundary_succ_of n m
    (universalCarrierHomotopy_boundary_succ n) c

noncomputable def singularAffinePushforward (X : TopCat) (k n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    (affineSimplex k n →₀ ℤ) →ₗ[ℤ]
      ((TopCat.toSSet.obj X) _⦋k⦌ →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun a =>
    (TopCat.toSSet.map
      (TopCat.ofHom (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x))).app (.op ⦋k⦌)
        (affineAsSingular k n a))

theorem singularAffinePushforward_single (X : TopCat) (k n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌)
    (a : affineSimplex k n) :
    singularAffinePushforward X k n x (Finsupp.single a 1) =
      Finsupp.single
        ((TopCat.toSSet.map
          (TopCat.ofHom (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x))).app (.op ⦋k⦌)
          (affineAsSingular k n a)) 1 := by
  simp [singularAffinePushforward, Finsupp.lmapDomain_apply]

theorem singularAffinePushforward_boundary (X : TopCat) (k n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌)
    (c : affineSimplex (k + 1) n →₀ ℤ) :
    singularBoundaryFinsupp X k
      (singularAffinePushforward X (k + 1) n x c) =
    singularAffinePushforward X k n x (affineBoundaryMap k n c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single a z =>
      have hs : Finsupp.single a z = z • Finsupp.single a 1 := by
        ext q
        by_cases hq : q = a <;> simp [hq]
      rw [hs]
      simp only [LinearMap.map_smul]
      rw [singularAffinePushforward_single, singularBoundaryFinsupp_single]
      simp only [affineBoundaryMap, Finsupp.linearCombination_single,
        affineBoundary, one_smul, map_sum, map_smul,
        singularAffinePushforward_single]
      congr 1

noncomputable def singularCarrierHomotopy (X : TopCat) (n : ℕ) :
    (((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) →ₗ[ℤ]
      ((TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ)) :=
  Finsupp.linearCombination ℤ (fun x =>
    singularAffinePushforward X (n + 1) n x
      (universalCarrierHomotopy n))

theorem singularCarrierHomotopy_zero (X : TopCat)
    (c : (TopCat.toSSet.obj X) _⦋0⦌ →₀ ℤ) :
    singularCarrierHomotopy X 0 c = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single x a =>
      simp [singularCarrierHomotopy, universalCarrierHomotopy_zero]

theorem singularCarrierHomotopy_boundary_zero (X : TopCat)
    (c : (TopCat.toSSet.obj X) _⦋0⦌ →₀ ℤ) :
    singularBoundaryFinsupp X 0 (singularCarrierHomotopy X 0 c) =
      singularBarycentricFinsupp X 0 c - c := by
  rw [singularCarrierHomotopy_zero]
  have hzero : singularBarycentricFinsupp X 0 c = c := by
    simp [singularBarycentricFinsupp, barycentricDegree_zero]
  simp [hzero]

private theorem singularAffinePushforward_face (X : TopCat) (n k : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n + 1⦌) (i : Fin (n + 2))
    (c : affineSimplex k n →₀ ℤ) :
    singularAffinePushforward X k n ((TopCat.toSSet.obj X).δ i x) c =
      singularAffinePushforward X k (n + 1) x
        (affinePostcompose k n (n + 1) (affineFaceInclusion n i) c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single a z =>
      simp only [singularAffinePushforward, affinePostcompose,
        Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      congr 1

private theorem singularAffinePushforward_identity (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularAffinePushforward X n n x
      (Finsupp.single (standardAffineIdentity n) 1) = Finsupp.single x 1 := by
  rw [singularAffinePushforward_single]
  congr 1
  apply (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).injective
  ext z
  change (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x) (standardAffineIdentity n z) = _
  simp [standardAffineIdentity]

private theorem singularAffinePushforward_barycentric_identity (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularAffinePushforward X n n x
      (affineBarycentricDegree n n
        (Finsupp.single (standardAffineIdentity n) 1)) =
      singularBarycentricFinsupp X n (Finsupp.single x 1) := by
  classical
  rw [affineBarycentricDegree, Finsupp.linearCombination_single]
  simp only [map_sum, map_smul, singularAffinePushforward_single, one_smul]
  rw [singularBarycentricFinsupp_single]
  congr 1
  funext σ
  congr 1
  congr 1
  apply (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).injective
  ext z
  change (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x)
    ((standardAffineIdentity n).comp (barycentricFlagAffine n σ) z) =
    (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x) (barycentricFlag n σ z)
  simp [standardAffineIdentity, barycentricFlag, barycentricFlagAffine]

private theorem singularCarrierHomotopy_single (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularCarrierHomotopy X n (Finsupp.single x 1) =
      singularAffinePushforward X (n + 1) n x
        (universalCarrierHomotopy n) := by
  simp [singularCarrierHomotopy]

private theorem singularCarrierHomotopy_boundary_single (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    singularCarrierHomotopy X n
        (singularBoundaryFinsupp X n (Finsupp.single x 1)) =
      singularAffinePushforward X (n + 1) (n + 1) x
        (affineUniversalHomotopy n (n + 1)
          (affineBoundaryMap n (n + 1)
            (Finsupp.single (standardAffineIdentity (n + 1)) 1))) := by
  classical
  rw [singularBoundaryFinsupp_single, affineBoundaryMap_single_identity]
  simp only [map_sum, map_smul, singularCarrierHomotopy_single,
    affineUniversalHomotopy_single]
  congr 1
  funext i
  exact congrArg ((-1 : ℤ) ^ i.val • ·)
    (singularAffinePushforward_face X n (n + 1) x i
      (universalCarrierHomotopy n))

/-- Barycentric subdivision is chain homotopic to the identity on singular
chains, with the homotopy induced by the universal affine carrier. -/
theorem singularCarrierHomotopy_boundary_succ (X : TopCat) (n : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ) :
    singularBoundaryFinsupp X (n + 1)
        (singularCarrierHomotopy X (n + 1) c) +
      singularCarrierHomotopy X n (singularBoundaryFinsupp X n c) =
      singularBarycentricFinsupp X (n + 1) c - c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      simp only [map_add]
      calc
        _ = (singularBoundaryFinsupp X (n + 1) (singularCarrierHomotopy X (n + 1) c) +
              singularCarrierHomotopy X n (singularBoundaryFinsupp X n c)) +
            (singularBoundaryFinsupp X (n + 1) (singularCarrierHomotopy X (n + 1) d) +
              singularCarrierHomotopy X n (singularBoundaryFinsupp X n d)) := by abel
        _ = (singularBarycentricFinsupp X (n + 1) c - c) +
              (singularBarycentricFinsupp X (n + 1) d - d) := by rw [hc, hd]
        _ = _ := by abel
  | single x a =>
      have hs : Finsupp.single x a = a • Finsupp.single x 1 := by
        ext q
        by_cases hq : q = x <;> simp [hq]
      rw [hs]
      simp only [LinearMap.map_smul, ← smul_add, ← smul_sub]
      congr 1
      let e : affineSimplex (n + 1) (n + 1) →₀ ℤ :=
        Finsupp.single (standardAffineIdentity (n + 1)) 1
      have he : affineUniversalHomotopy (n + 1) (n + 1) e =
          universalCarrierHomotopy (n + 1) := by
        dsimp [e]
        rw [affineUniversalHomotopy_single, affinePostcompose_identity]
      calc
        _ = singularAffinePushforward X (n + 1) (n + 1) x
              (affineBoundaryMap (n + 1) (n + 1)
                (universalCarrierHomotopy (n + 1))) +
            singularAffinePushforward X (n + 1) (n + 1) x
              (affineUniversalHomotopy n (n + 1)
                (affineBoundaryMap n (n + 1) e)) := by
                rw [singularCarrierHomotopy_single,
                  singularAffinePushforward_boundary,
                  singularCarrierHomotopy_boundary_single]
        _ = singularAffinePushforward X (n + 1) (n + 1) x
              (affineBoundaryMap (n + 1) (n + 1)
                (universalCarrierHomotopy (n + 1)) +
               affineUniversalHomotopy n (n + 1)
                (affineBoundaryMap n (n + 1) e)) := by rw [map_add]
        _ = singularAffinePushforward X (n + 1) (n + 1) x
              (affineBarycentricDegree (n + 1) (n + 1) e - e) := by
                rw [← he, affineCarrierHomotopy_boundary_succ]
        _ = singularBarycentricFinsupp X (n + 1) (Finsupp.single x 1) -
              Finsupp.single x 1 := by
                rw [map_sub, singularAffinePushforward_barycentric_identity,
                  singularAffinePushforward_identity]

end CurveComplexGenusTwo.CWHurewicz
