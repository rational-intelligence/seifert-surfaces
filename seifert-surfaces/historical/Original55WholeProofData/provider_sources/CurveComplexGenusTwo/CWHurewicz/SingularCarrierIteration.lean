import CurveComplexGenusTwo.CWHurewicz.CarrierHomotopy

open CategoryTheory
open scoped Simplicial

namespace CurveComplexGenusTwo.CWHurewicz

/-- A singular chain is carried by `S` when every simplex with nonzero
coefficient has its entire geometric image in `S`. -/
def SingularChainImageSupported (X : TopCat) (n : ℕ) (S : Set X)
    (c : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) : Prop :=
  ∀ x ∈ c.support, Set.range (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x) ⊆ S

private theorem imageSupported_zero (X : TopCat) (n : ℕ) (S : Set X) :
    SingularChainImageSupported X n S 0 := by
  simp [SingularChainImageSupported]

private theorem imageSupported_add (X : TopCat) (n : ℕ) (S : Set X)
    {c d : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ}
    (hc : SingularChainImageSupported X n S c)
    (hd : SingularChainImageSupported X n S d) :
    SingularChainImageSupported X n S (c + d) := by
  classical
  intro x hx
  rcases Finset.mem_union.mp (Finset.mem_of_subset Finsupp.support_add hx) with h | h
  · exact hc x h
  · exact hd x h

private theorem imageSupported_smul (X : TopCat) (n : ℕ) (S : Set X)
    (a : ℤ) {c : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ}
    (hc : SingularChainImageSupported X n S c) :
    SingularChainImageSupported X n S (a • c) := by
  classical
  intro x hx
  exact hc x (Finset.mem_of_subset Finsupp.support_smul hx)

private theorem imageSupported_mono (X : TopCat) (n : ℕ)
    {S T : Set X} (hST : S ⊆ T)
    {c : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ}
    (hc : SingularChainImageSupported X n S c) :
    SingularChainImageSupported X n T c := by
  intro x hx
  exact (hc x hx).trans hST

private theorem imageSupported_single (X : TopCat) (n : ℕ) (S : Set X)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) (a : ℤ)
    (hx : Set.range (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x) ⊆ S) :
    SingularChainImageSupported X n S (Finsupp.single x a) := by
  classical
  intro y hy
  have hxy : y = x := (Finsupp.mem_support_single y x a).mp hy |>.1
  simpa [hxy] using hx

private theorem imageSupported_mapDomain {α β : Type*} [DecidableEq β]
    (P : β → Prop) (g : α → β) (c : α →₀ ℤ)
    (hc : ∀ x ∈ c.support, P (g x)) :
    ∀ y ∈ (Finsupp.mapDomain g c).support, P y := by
  intro y hy
  have hy' : y ∈ g '' (c.support : Set α) := by
    by_contra h
    have hz := Finsupp.mapDomain_of_not_mem_image_support (f := g) (x := c) h
    exact (Finsupp.mem_support_iff.mp hy) hz
  obtain ⟨x, hx, rfl⟩ := hy'
  exact hc x hx

private theorem singularAffinePushforward_range (X : TopCat) (k n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌)
    (c : affineSimplex k n →₀ ℤ) :
    SingularChainImageSupported X k
      (Set.range (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x))
      (singularAffinePushforward X k n x c) := by
  classical
  change ∀ y ∈ (Finsupp.mapDomain (fun a : affineSimplex k n =>
    (TopCat.toSSet.map
      (TopCat.ofHom (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x))).app (.op ⦋k⦌)
        (affineAsSingular k n a)) c).support,
    Set.range (TopCat.toSSetObjEquiv X (.op ⦋k⦌) y) ⊆
      Set.range (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x)
  apply imageSupported_mapDomain
  intro a ha z hz
  obtain ⟨t, rfl⟩ := hz
  exact ⟨a t, rfl⟩

private theorem barycentricFlagSingular_range (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌)
    (σ : Equiv.Perm (Fin (n + 1))) :
    Set.range (TopCat.toSSetObjEquiv X (.op ⦋n⦌)
      (barycentricFlagSingular X n σ x)) ⊆
    Set.range (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x) := by
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  exact ⟨barycentricFlag n σ t, rfl⟩

private theorem barycentric_single_supported (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) (S : Set X)
    (hx : Set.range (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x) ⊆ S) :
    SingularChainImageSupported X n S
      (singularBarycentricFinsupp X n (Finsupp.single x 1)) := by
  rw [singularBarycentricFinsupp_single]
  have aux (t : Finset (Equiv.Perm (Fin (n + 1)))) :
      SingularChainImageSupported X n S
        (∑ σ ∈ t, (σ.sign : ℤ) •
          Finsupp.single (barycentricFlagSingular X n σ x) 1) := by
    induction t using Finset.induction_on with
    | empty => simpa using imageSupported_zero X n S
    | @insert σ t h ih =>
        rw [Finset.sum_insert h]
        exact imageSupported_add X n S
          (imageSupported_smul X n S (σ.sign : ℤ)
            (imageSupported_single X n S (barycentricFlagSingular X n σ x) 1
              ((barycentricFlagSingular_range X n x σ).trans hx))) ih
  simpa using aux Finset.univ

private theorem imageSupported_linearMap (X : TopCat) (n m : ℕ) (S : Set X)
    (F : ((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) →ₗ[ℤ]
      ((TopCat.toSSet.obj X) _⦋m⦌ →₀ ℤ))
    (hF : ∀ x : (TopCat.toSSet.obj X) _⦋n⦌,
      Set.range (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x) ⊆ S →
      SingularChainImageSupported X m S (F (Finsupp.single x 1)))
    (c : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ)
    (hc : SingularChainImageSupported X n S c) :
    SingularChainImageSupported X m S (F c) := by
  classical
  have hrepr : c = ∑ x ∈ c.support, c x • Finsupp.single x 1 := by
    conv_lhs => rw [← Finsupp.sum_single c]
    simp [Finsupp.sum, Finsupp.smul_single]
  rw [hrepr]
  simp only [map_sum, map_smul]
  have aux (t : Finset ((TopCat.toSSet.obj X) _⦋n⦌))
      (ht : t ⊆ c.support) :
      SingularChainImageSupported X m S
        (∑ x ∈ t, c x • F (Finsupp.single x 1)) := by
    induction t using Finset.induction_on with
    | empty => simpa using imageSupported_zero X m S
    | @insert x t h ih =>
        rw [Finset.sum_insert h]
        exact imageSupported_add X m S
          (imageSupported_smul X m S (c x) (hF x (hc x (ht (by simp)))))
          (ih (fun y hy => ht (Finset.mem_insert_of_mem hy)))
  exact aux c.support (Finset.Subset.rfl)

/-- Barycentric subdivision preserves the geometric carrier of a singular
chain, with no convexity or openness assumption on the carrier. -/
theorem singularBarycentricFinsupp_supported (X : TopCat) (n : ℕ)
    (S : Set X) (c : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ)
    (hc : SingularChainImageSupported X n S c) :
    SingularChainImageSupported X n S (singularBarycentricFinsupp X n c) := by
  exact imageSupported_linearMap X n n S (singularBarycentricFinsupp X n)
    (fun x hx => barycentric_single_supported X n x S hx) c hc

/-- The singular carrier homotopy preserves each input chain's geometric
carrier. -/
theorem singularCarrierHomotopy_supported (X : TopCat) (n : ℕ)
    (S : Set X) (c : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ)
    (hc : SingularChainImageSupported X n S c) :
    SingularChainImageSupported X (n + 1) S (singularCarrierHomotopy X n c) := by
  apply imageSupported_linearMap X n (n + 1) S (singularCarrierHomotopy X n)
    ?_ c hc
  intro x hx
  rw [singularCarrierHomotopy, Finsupp.linearCombination_single, one_smul]
  exact imageSupported_mono X (n + 1) hx
    (singularAffinePushforward_range X (n + 1) n x
      (universalCarrierHomotopy n))

/-- The `k`-fold barycentric subdivision map on singular chains. -/
noncomputable def singularBarycentricIterate (X : TopCat) (n k : ℕ) :
    (((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) →ₗ[ℤ]
      ((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ)) :=
  k.rec LinearMap.id (fun _ prev => (singularBarycentricFinsupp X n).comp prev)

/-- The telescoping carrier homotopy from `Sd^k` to the identity. -/
noncomputable def singularCarrierHomotopyIterate (X : TopCat) (n k : ℕ) :
    (((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) →ₗ[ℤ]
      ((TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ)) :=
  k.rec 0 (fun j prev => prev +
    (singularCarrierHomotopy X n).comp (singularBarycentricIterate X n j))

@[simp] theorem singularBarycentricIterate_zero (X : TopCat) (n : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) :
    singularBarycentricIterate X n 0 c = c := rfl

@[simp] theorem singularBarycentricIterate_succ (X : TopCat) (n k : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) :
    singularBarycentricIterate X n (k + 1) c =
      singularBarycentricFinsupp X n (singularBarycentricIterate X n k c) := rfl

@[simp] theorem singularCarrierHomotopyIterate_zero (X : TopCat) (n : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) :
    singularCarrierHomotopyIterate X n 0 c = 0 := rfl

@[simp] theorem singularCarrierHomotopyIterate_succ (X : TopCat) (n k : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) :
    singularCarrierHomotopyIterate X n (k + 1) c =
      singularCarrierHomotopyIterate X n k c +
        singularCarrierHomotopy X n (singularBarycentricIterate X n k c) := rfl

theorem singularBarycentricIterate_boundary (X : TopCat) (n k : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ) :
    singularBoundaryFinsupp X n (singularBarycentricIterate X (n + 1) k c) =
      singularBarycentricIterate X n k (singularBoundaryFinsupp X n c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [singularBarycentricIterate_succ]
      rw [singularBarycentric_boundary_compat, ih]

theorem singularBarycentricIterate_supported (X : TopCat) (n k : ℕ)
    (S : Set X) (c : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ)
    (hc : SingularChainImageSupported X n S c) :
    SingularChainImageSupported X n S (singularBarycentricIterate X n k c) := by
  induction k with
  | zero => simpa using hc
  | succ k ih =>
      rw [singularBarycentricIterate_succ]
      exact singularBarycentricFinsupp_supported X n S _ ih

theorem singularCarrierHomotopyIterate_supported (X : TopCat) (n k : ℕ)
    (S : Set X) (c : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ)
    (hc : SingularChainImageSupported X n S c) :
    SingularChainImageSupported X (n + 1) S
      (singularCarrierHomotopyIterate X n k c) := by
  induction k with
  | zero => simpa using imageSupported_zero X (n + 1) S
  | succ k ih =>
      rw [singularCarrierHomotopyIterate_succ]
      exact imageSupported_add X (n + 1) S ih
        (singularCarrierHomotopy_supported X n S _
          (singularBarycentricIterate_supported X n k S c hc))

theorem singularCarrierHomotopyIterate_boundary_succ (X : TopCat) (n k : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ) :
    singularBoundaryFinsupp X (n + 1)
        (singularCarrierHomotopyIterate X (n + 1) k c) +
      singularCarrierHomotopyIterate X n k (singularBoundaryFinsupp X n c) =
      singularBarycentricIterate X (n + 1) k c - c := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [singularCarrierHomotopyIterate_succ,
        singularBarycentricIterate_succ, map_add]
      have h := singularCarrierHomotopy_boundary_succ X n
        (singularBarycentricIterate X (n + 1) k c)
      rw [singularBarycentricIterate_boundary X n k c] at h
      calc
        _ = (singularBoundaryFinsupp X (n + 1)
              (singularCarrierHomotopyIterate X (n + 1) k c) +
              singularCarrierHomotopyIterate X n k
                (singularBoundaryFinsupp X n c)) +
            (singularBoundaryFinsupp X (n + 1)
              (singularCarrierHomotopy X (n + 1)
                (singularBarycentricIterate X (n + 1) k c)) +
              singularCarrierHomotopy X n
                (singularBarycentricIterate X n k
                  (singularBoundaryFinsupp X n c))) := by abel
        _ = (singularBarycentricIterate X (n + 1) k c - c) +
              (singularBarycentricFinsupp X (n + 1)
                (singularBarycentricIterate X (n + 1) k c) -
                singularBarycentricIterate X (n + 1) k c) := by rw [ih, h]
        _ = _ := by abel

theorem singularBarycentricFinsupp_degree_zero (X : TopCat)
    (c : (TopCat.toSSet.obj X) _⦋0⦌ →₀ ℤ) :
    singularBarycentricFinsupp X 0 c = c := by
  simp [singularBarycentricFinsupp, barycentricDegree_zero]

theorem singularBarycentricIterate_degree_zero (X : TopCat) (k : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋0⦌ →₀ ℤ) :
    singularBarycentricIterate X 0 k c = c := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [singularBarycentricIterate_succ,
        singularBarycentricFinsupp_degree_zero]
      exact ih

theorem singularCarrierHomotopyIterate_degree_zero (X : TopCat) (k : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋0⦌ →₀ ℤ) :
    singularCarrierHomotopyIterate X 0 k c = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [singularCarrierHomotopyIterate_succ, ih,
        singularCarrierHomotopy_zero]
      simp

theorem singularCarrierHomotopyIterate_boundary_zero (X : TopCat) (k : ℕ)
    (c : (TopCat.toSSet.obj X) _⦋0⦌ →₀ ℤ) :
    singularBoundaryFinsupp X 0
      (singularCarrierHomotopyIterate X 0 k c) =
        singularBarycentricIterate X 0 k c - c := by
  rw [singularCarrierHomotopyIterate_degree_zero,
    singularBarycentricIterate_degree_zero]
  simp

end CurveComplexGenusTwo.CWHurewicz
