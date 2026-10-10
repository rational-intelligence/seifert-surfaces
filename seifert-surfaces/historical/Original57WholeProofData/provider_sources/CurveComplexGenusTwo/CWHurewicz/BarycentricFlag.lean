import Mathlib

/-! Geometric flags of a barycentric subdivision of a standard simplex. -/

namespace CurveComplexGenusTwo.CWHurewicz

open Convexity
open Classical
open CategoryTheory
open CategoryTheory.Limits
open scoped Simplicial

private def flagVertices (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => σ.symm i ≤ k)

private theorem flagVertices_nonempty (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    (flagVertices n σ k).Nonempty := by
  refine ⟨σ 0, ?_⟩
  simp [flagVertices]

/-- A flag simplex has the barycenters of the successive initial sets of
vertices under `σ` as its vertices. -/
noncomputable def barycentricFlagAffine (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1)))
      (StdSimplex ℝ (Fin (n + 1))) :=
  StdSimplex.affineMapMk (fun k =>
    StdSimplex.subBarycenter (flagVertices n σ k)
      (flagVertices_nonempty n σ k))

theorem barycentricFlagAffine_vertex (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    barycentricFlagAffine n σ (.single k) =
      StdSimplex.subBarycenter (flagVertices n σ k)
        (flagVertices_nonempty n σ k) := by
  simp [barycentricFlagAffine]

theorem barycentricFlagAffine_continuous (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    Continuous (barycentricFlagAffine n σ) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff]
  change Continuous (fun t : StdSimplex ℝ (Fin (n + 1)) =>
    ((barycentricFlagAffine n σ t).weights : Fin (n + 1) → ℝ))
  simp only [barycentricFlagAffine, StdSimplex.affineMapMk_apply,
    StdSimplex.weights_iConvexComb]
  apply continuous_pi
  intro i
  have h (t : StdSimplex ℝ (Fin (n + 1))) :
      (t.weights.sum (fun j r =>
        r • (StdSimplex.subBarycenter (flagVertices n σ j)
          (flagVertices_nonempty n σ j)).weights)) i =
      ∑ j : Fin (n + 1), t.weights j *
        (StdSimplex.subBarycenter (flagVertices n σ j)
          (flagVertices_nonempty n σ j)).weights i := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp_rw [h]
  fun_prop

/-- The continuous affine simplex corresponding to one barycentric flag. -/
noncomputable def barycentricFlag (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (n + 1))) :=
  ⟨barycentricFlagAffine n σ, barycentricFlagAffine_continuous n σ⟩

theorem barycentricFlag_vertex (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    barycentricFlag n σ (.single k) =
      StdSimplex.subBarycenter (flagVertices n σ k)
        (flagVertices_nonempty n σ k) :=
  barycentricFlagAffine_vertex n σ k

/-- Apply one barycentric flag to a singular simplex. -/
noncomputable def barycentricFlagSingular (X : TopCat) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1)))
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).symm
    ((TopCat.toSSetObjEquiv X (.op ⦋n⦌) x).comp
      (barycentricFlag n σ))

private noncomputable abbrev singularChains (X : TopCat) :=
  (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)

/-- Signed sum of all barycentric flag simplices in a fixed degree.
The chain-map identity is a separate combinatorial obligation. -/
noncomputable def barycentricDegree (X : TopCat) (n : ℕ) :
    (singularChains X).X n ⟶ (singularChains X).X n :=
  Sigma.desc (fun x : (TopCat.toSSet.obj X) _⦋n⦌ =>
    (∑ σ : Equiv.Perm (Fin (n + 1)),
      (σ.sign : ℤ) • (TopCat.toSSet.obj X).ιChainComplex
        (barycentricFlagSingular X n σ x) :
      (ModuleCat.of ℤ ℤ) ⟶ (singularChains X).X n))

theorem barycentricDegree_generator (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) x ≫
      barycentricDegree X n =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        (σ.sign : ℤ) • (TopCat.toSSet.obj X).ιChainComplex
          (barycentricFlagSingular X n σ x) := by
  simp [barycentricDegree, SSet.ιChainComplex]

theorem barycentricFlagSingular_zero (X : TopCat)
    (σ : Equiv.Perm (Fin 1))
    (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    barycentricFlagSingular X 0 σ x = x := by
  apply (TopCat.toSSetObjEquiv X (.op ⦋0⦌)).injective
  ext t
  have ht : barycentricFlag 0 σ t = t := Subsingleton.elim _ _
  simp [barycentricFlagSingular, ht]

theorem barycentricDegree_zero (X : TopCat) :
    barycentricDegree X 0 = 𝟙 (singularChains X).X 0 := by
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro x
  rw [barycentricDegree_generator]
  simp [barycentricFlagSingular_zero]

private theorem permFinTwo_univ :
    (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by
  decide

private theorem flag_one_id_zero :
    barycentricFlag 1 (1 : Equiv.Perm (Fin 2)) (.single 0) =
      (StdSimplex.single 0 : StdSimplex ℝ (Fin 2)) := by
  rw [barycentricFlag_vertex]
  have hs : flagVertices 1 (1 : Equiv.Perm (Fin 2)) 0 = {0} := by decide
  simpa only [hs] using (StdSimplex.subBarycenter_singleton (K := ℝ) (0 : Fin 2))

private theorem flag_one_id_one :
    barycentricFlag 1 (1 : Equiv.Perm (Fin 2)) (.single 1) =
      (StdSimplex.barycenter : StdSimplex ℝ (Fin 2)) := by
  rw [barycentricFlag_vertex]
  have hs : flagVertices 1 (1 : Equiv.Perm (Fin 2)) 1 = Finset.univ := by decide
  cases hs
  rfl

private theorem flag_one_swap_zero :
    barycentricFlag 1 (Equiv.swap 0 1) (.single 0) =
      (StdSimplex.single 1 : StdSimplex ℝ (Fin 2)) := by
  rw [barycentricFlag_vertex]
  have hs : flagVertices 1 (Equiv.swap 0 1) 0 = {1} := by decide
  simpa only [hs] using (StdSimplex.subBarycenter_singleton (K := ℝ) (1 : Fin 2))

private theorem flag_one_swap_one :
    barycentricFlag 1 (Equiv.swap 0 1) (.single 1) =
      (StdSimplex.barycenter : StdSimplex ℝ (Fin 2)) := by
  rw [barycentricFlag_vertex]
  have hs : flagVertices 1 (Equiv.swap 0 1) 1 = Finset.univ := by decide
  cases hs
  rfl

private theorem flag_one_faces_midpoint (X : TopCat)
    (x : (TopCat.toSSet.obj X) _⦋1⦌) :
    (TopCat.toSSet.obj X).δ (0 : Fin 2)
        (barycentricFlagSingular X 1 1 x) =
      (TopCat.toSSet.obj X).δ (0 : Fin 2)
        (barycentricFlagSingular X 1 (Equiv.swap 0 1) x) := by
  apply (TopCat.toSSetObjEquiv X (.op ⦋0⦌)).injective
  ext t
  simp only [TopCat.toSSetObjEquiv_δ_apply]
  have ht : t = (StdSimplex.single 0 : StdSimplex ℝ (Fin 1)) := Subsingleton.elim _ _
  subst t
  simp [barycentricFlagSingular, flag_one_id_one, flag_one_swap_one]

private theorem flag_one_id_face_start (X : TopCat)
    (x : (TopCat.toSSet.obj X) _⦋1⦌) :
    (TopCat.toSSet.obj X).δ (1 : Fin 2)
        (barycentricFlagSingular X 1 1 x) =
      (TopCat.toSSet.obj X).δ (1 : Fin 2) x := by
  apply (TopCat.toSSetObjEquiv X (.op ⦋0⦌)).injective
  ext t
  simp only [TopCat.toSSetObjEquiv_δ_apply]
  have ht : t = (StdSimplex.single 0 : StdSimplex ℝ (Fin 1)) := Subsingleton.elim _ _
  subst t
  simp [barycentricFlagSingular, flag_one_id_zero]

private theorem flag_one_swap_face_end (X : TopCat)
    (x : (TopCat.toSSet.obj X) _⦋1⦌) :
    (TopCat.toSSet.obj X).δ (1 : Fin 2)
        (barycentricFlagSingular X 1 (Equiv.swap 0 1) x) =
      (TopCat.toSSet.obj X).δ (0 : Fin 2) x := by
  apply (TopCat.toSSetObjEquiv X (.op ⦋0⦌)).injective
  ext t
  simp only [TopCat.toSSetObjEquiv_δ_apply]
  have ht : t = (StdSimplex.single 0 : StdSimplex ℝ (Fin 1)) := Subsingleton.elim _ _
  subst t
  simp [barycentricFlagSingular, flag_one_swap_zero]

/-- The first nontrivial boundary identity for the signed barycentric sum. -/
theorem barycentricDegree_one_chain_identity (X : TopCat) :
    barycentricDegree X 1 ≫ (singularChains X).d 1 0 =
      (singularChains X).d 1 0 ≫ barycentricDegree X 0 := by
  simp only [barycentricDegree_zero]
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro x
  rw [← Category.assoc, barycentricDegree_generator]
  rw [permFinTwo_univ]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [SSet.ιChainComplex_d, flag_one_faces_midpoint,
    flag_one_id_face_start, flag_one_swap_face_end]
  abel

private theorem flag_one_id_coordinate (t : StdSimplex ℝ (Fin 2)) :
    (barycentricFlag 1 (1 : Equiv.Perm (Fin 2)) t).weights 1 =
      t.weights 1 / 2 := by
  change (StdSimplex.iConvexComb t
    (fun k => StdSimplex.subBarycenter (flagVertices 1 1 k)
      (flagVertices_nonempty 1 1 k))).weights 1 = _
  rw [StdSimplex.weights_iConvexComb]
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, add_zero,
    smul_eq_mul]
  have h0 := congrArg (fun s : StdSimplex ℝ (Fin 2) => s.weights 1) flag_one_id_zero
  have h1 := congrArg (fun s : StdSimplex ℝ (Fin 2) => s.weights 1) flag_one_id_one
  rw [barycentricFlag_vertex] at h0 h1
  simp at h0 h1
  simp only [show (Fin.succ (0 : Fin 1)) = (1 : Fin 2) from rfl]
  rw [h0, h1]
  norm_num [StdSimplex.weights_barycenter_apply]
  ring

private theorem flag_one_swap_coordinate (t : StdSimplex ℝ (Fin 2)) :
    (barycentricFlag 1 (Equiv.swap 0 1) t).weights 1 =
      1 - t.weights 1 / 2 := by
  change (StdSimplex.iConvexComb t
    (fun k => StdSimplex.subBarycenter (flagVertices 1 (Equiv.swap 0 1) k)
      (flagVertices_nonempty 1 (Equiv.swap 0 1) k))).weights 1 = _
  rw [StdSimplex.weights_iConvexComb]
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero,
    Finsupp.add_apply, Finsupp.smul_apply, add_zero, smul_eq_mul]
  have h0 := congrArg (fun s : StdSimplex ℝ (Fin 2) => s.weights 1) flag_one_swap_zero
  have h1 := congrArg (fun s : StdSimplex ℝ (Fin 2) => s.weights 1) flag_one_swap_one
  rw [barycentricFlag_vertex] at h0 h1
  simp at h0 h1
  simp only [show (Fin.succ (0 : Fin 1)) = (1 : Fin 2) from rfl]
  rw [h0, h1]
  norm_num [StdSimplex.weights_barycenter_apply]
  have ht : t.weights 0 + t.weights 1 = 1 := by
    simp
  linear_combination ht

theorem barycentricFlag_one_shrinks_coordinate
    (σ : Equiv.Perm (Fin 2)) (t u : StdSimplex ℝ (Fin 2)) :
    |(barycentricFlag 1 σ t).weights 1 -
      (barycentricFlag 1 σ u).weights 1| =
      |t.weights 1 - u.weights 1| / 2 := by
  have hσ : σ = 1 ∨ σ = Equiv.swap 0 1 := by
    have := Finset.mem_univ σ
    rw [permFinTwo_univ] at this
    simpa using this
  rcases hσ with rfl | rfl
  · rw [flag_one_id_coordinate, flag_one_id_coordinate]
    rw [show t.weights 1 / 2 - u.weights 1 / 2 =
      (t.weights 1 - u.weights 1) / 2 by ring, abs_div]
    norm_num
  · rw [flag_one_swap_coordinate, flag_one_swap_coordinate]
    rw [show (1 - t.weights 1 / 2) - (1 - u.weights 1 / 2) =
      -(t.weights 1 - u.weights 1) / 2 by ring, abs_div, abs_neg]
    norm_num

/-- Compose a sequence of one-dimensional barycentric flag maps. -/
noncomputable def flagIterate (ss : List (Equiv.Perm (Fin 2))) :
    StdSimplex ℝ (Fin 2) → StdSimplex ℝ (Fin 2) :=
  match ss with
  | [] => id
  | σ :: tail => flagIterate tail ∘ barycentricFlag 1 σ

theorem flagIterate_coordinate_contraction
    (ss : List (Equiv.Perm (Fin 2)))
    (t u : StdSimplex ℝ (Fin 2)) :
    |(flagIterate ss t).weights 1 - (flagIterate ss u).weights 1| =
      ((1 : ℝ) / 2) ^ ss.length * |t.weights 1 - u.weights 1| := by
  induction ss generalizing t u with
  | nil => simp [flagIterate]
  | cons σ ss ih =>
      simp only [flagIterate, Function.comp_apply, List.length_cons]
      rw [ih, barycentricFlag_one_shrinks_coordinate]
      rw [pow_succ]
      ring

theorem exists_one_dimensional_subdivision_depth
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, ((1 : ℝ) / 2) ^ k < δ := by
  exact exists_pow_lt_of_lt_one hδ (by norm_num)

theorem flagIterate_coordinate_mesh
    (ss : List (Equiv.Perm (Fin 2)))
    (t u : StdSimplex ℝ (Fin 2)) :
    |(flagIterate ss t).weights 1 - (flagIterate ss u).weights 1| ≤
      ((1 : ℝ) / 2) ^ ss.length := by
  rw [flagIterate_coordinate_contraction]
  have htu : |t.weights 1 - u.weights 1| ≤ 1 := by
    have ht := t.weights_apply_le_one 1
    have hu := u.weights_apply_le_one 1
    have ht0 := t.weights_nonneg 1
    have hu0 := u.weights_nonneg 1
    rw [abs_le]
    constructor <;> linarith
  exact mul_le_of_le_one_right (pow_nonneg (by norm_num) _) htu

theorem flagIterate_coordinate_small
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, ∀ ss : List (Equiv.Perm (Fin 2)), ss.length = k →
      ∀ t u : StdSimplex ℝ (Fin 2),
        |(flagIterate ss t).weights 1 -
          (flagIterate ss u).weights 1| < δ := by
  obtain ⟨k, hk⟩ := exists_one_dimensional_subdivision_depth δ hδ
  refine ⟨k, ?_⟩
  intro ss hss t u
  exact (flagIterate_coordinate_mesh ss t u).trans_lt (hss ▸ hk)

private noncomputable instance : MetricSpace (StdSimplex ℝ (Fin 2)) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 2)).comapMetricSpace
    (fun t => (t.weights : Fin 2 → ℝ))

theorem simplex_one_dist_eq_coordinate
    (t u : StdSimplex ℝ (Fin 2)) :
    dist t u = |t.weights 1 - u.weights 1| := by
  have hsumt : t.weights 0 + t.weights 1 = 1 := by simp
  have hsumu : u.weights 0 + u.weights 1 = 1 := by simp
  change dist (t.weights : Fin 2 → ℝ) (u.weights : Fin 2 → ℝ) = _
  simp only [dist_pi_def, Real.nndist_eq]
  have hzero : |t.weights 0 - u.weights 0| = |t.weights 1 - u.weights 1| := by
    have hdiff : t.weights 0 - u.weights 0 = -(t.weights 1 - u.weights 1) := by
      linarith
    rw [hdiff, abs_neg]
  rw [← Real.coe_nnabs (t.weights 1 - u.weights 1)]
  norm_cast
  apply le_antisymm
  · rw [Finset.sup_le_iff]
    intro b _
    fin_cases b
    · exact_mod_cast hzero.le
    · exact le_refl _
  · exact (Finset.le_sup (f := fun b : Fin 2 =>
      Real.nnabs (t.weights b - u.weights b))
        (Finset.mem_univ (1 : Fin 2)))

theorem flagIterate_mesh
    (ss : List (Equiv.Perm (Fin 2)))
    (t u : StdSimplex ℝ (Fin 2)) :
    dist (flagIterate ss t) (flagIterate ss u) ≤
      ((1 : ℝ) / 2) ^ ss.length := by
  rw [simplex_one_dist_eq_coordinate]
  exact flagIterate_coordinate_mesh ss t u

theorem flagIterate_image_small
    {X : Type*} [TopologicalSpace X] (A U : Set X)
    (f : C(StdSimplex ℝ (Fin 2), X))
    (δ : ℝ)
    (hcover : ∀ z : StdSimplex ℝ (Fin 2),
      f '' Metric.ball z δ ⊆ Uᶜ ∨ f '' Metric.ball z δ ⊆ A)
    (ss : List (Equiv.Perm (Fin 2)))
    (hdepth : ((1 : ℝ) / 2) ^ ss.length < δ) :
    (f ∘ flagIterate ss) '' Set.univ ⊆ Uᶜ ∨
      (f ∘ flagIterate ss) '' Set.univ ⊆ A := by
  let t : StdSimplex ℝ (Fin 2) := .single 0
  rcases hcover (flagIterate ss t) with h | h
  · left
    rintro y ⟨u, -, rfl⟩
    apply h
    refine ⟨flagIterate ss u, ?_, rfl⟩
    exact Metric.mem_ball.mpr ((flagIterate_mesh ss u t).trans_lt hdepth)

  · right
    rintro y ⟨u, -, rfl⟩
    apply h
    refine ⟨flagIterate ss u, ?_, rfl⟩
    exact Metric.mem_ball.mpr ((flagIterate_mesh ss u t).trans_lt hdepth)

theorem flagIterate_image_eventually_small
    {X : Type*} [TopologicalSpace X] (A U : Set X)
    (f : C(StdSimplex ℝ (Fin 2), X))
    (δ : ℝ) (hδ : 0 < δ)
    (hcover : ∀ z : StdSimplex ℝ (Fin 2),
      f '' Metric.ball z δ ⊆ Uᶜ ∨ f '' Metric.ball z δ ⊆ A) :
    ∃ k : ℕ, ∀ ss : List (Equiv.Perm (Fin 2)), ss.length = k →
      (f ∘ flagIterate ss) '' Set.univ ⊆ Uᶜ ∨
        (f ∘ flagIterate ss) '' Set.univ ⊆ A := by
  obtain ⟨k, hk⟩ := exists_one_dimensional_subdivision_depth δ hδ
  exact ⟨k, fun ss hss => flagIterate_image_small A U f δ hcover ss (hss ▸ hk)⟩

theorem flagIterate_finite_family_eventually_small
    {X : Type*} [TopologicalSpace X] (A U : Set X)
    (fs : List C(StdSimplex ℝ (Fin 2), X))
    (δ : ℝ) (hδ : 0 < δ)
    (hcover : ∀ f ∈ fs, ∀ z : StdSimplex ℝ (Fin 2),
      f '' Metric.ball z δ ⊆ Uᶜ ∨ f '' Metric.ball z δ ⊆ A) :
    ∃ k : ℕ, ∀ f ∈ fs, ∀ ss : List (Equiv.Perm (Fin 2)), ss.length = k →
      (f ∘ flagIterate ss) '' Set.univ ⊆ Uᶜ ∨
        (f ∘ flagIterate ss) '' Set.univ ⊆ A := by
  obtain ⟨k, hk⟩ := exists_one_dimensional_subdivision_depth δ hδ
  refine ⟨k, ?_⟩
  intro f hf ss hss
  exact flagIterate_image_small A U f δ (hcover f hf) ss (hss ▸ hk)

private theorem adjacent_swap_preserves_initial_segment
    {n : ℕ} (j : Fin (n + 1)) (k p : Fin (n + 2))
    (hk : k ≠ j.castSucc) :
    Equiv.swap j.castSucc j.succ p ≤ k ↔ p ≤ k := by
  have hkv : k.val ≠ j.val := by
    intro heq
    exact hk (Fin.ext heq)
  have hsucc : j.succ.val = j.val + 1 := rfl
  have hcast : j.castSucc.val = j.val := rfl
  simp only [Equiv.swap_apply_def]
  split_ifs with hp hq
  · subst p
    omega
  · subst p
    omega
  · rfl

private theorem flagVertices_adjacent_swap_eq
    {n : ℕ} (σ : Equiv.Perm (Fin (n + 2)))
    (j : Fin (n + 1)) (k : Fin (n + 2))
    (hk : k ≠ j.castSucc) :
    flagVertices (n + 1)
        (σ * Equiv.swap j.castSucc j.succ) k =
      flagVertices (n + 1) σ k := by
  ext i
  simp only [flagVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsym : (σ * Equiv.swap j.castSucc j.succ).symm i =
      Equiv.swap j.castSucc j.succ (σ.symm i) := by
    simp [Equiv.Perm.mul_def, Equiv.symm_swap]
  rw [hsym]
  exact adjacent_swap_preserves_initial_segment j k (σ.symm i) hk

private theorem adjacent_swap_changes_sign
    {n : ℕ} (σ : Equiv.Perm (Fin (n + 2)))
    (j : Fin (n + 1)) :
    ((σ * Equiv.swap j.castSucc j.succ).sign : ℤ) =
      -(σ.sign : ℤ) := by
  have hne : (j.castSucc : Fin (n + 2)) ≠ j.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]

private theorem barycentricFlag_adjacent_swap_face
    {n : ℕ} (σ : Equiv.Perm (Fin (n + 2)))
    (j : Fin (n + 1)) (t : StdSimplex ℝ (Fin (n + 1))) :
    barycentricFlag (n + 1) (σ * Equiv.swap j.castSucc j.succ)
        (StdSimplex.map j.castSucc.succAbove t) =
      barycentricFlag (n + 1) σ
        (StdSimplex.map j.castSucc.succAbove t) := by
  let f := StdSimplex.affineMap (R := ℝ) j.castSucc.succAbove
  have heq : (barycentricFlagAffine (n + 1)
      (σ * Equiv.swap j.castSucc j.succ)).comp f =
      (barycentricFlagAffine (n + 1) σ).comp f := by
    apply StdSimplex.affineMap_ext
    intro i
    change barycentricFlagAffine (n + 1)
        (σ * Equiv.swap j.castSucc j.succ)
          (StdSimplex.map j.castSucc.succAbove (.single i)) =
      barycentricFlagAffine (n + 1) σ
          (StdSimplex.map j.castSucc.succAbove (.single i))
    simp only [StdSimplex.map_single, barycentricFlagAffine_vertex]
    simp only [flagVertices_adjacent_swap_eq σ j (j.castSucc.succAbove i)
      (Fin.succAbove_ne _ _)]
  exact congrArg (fun g : ConvexSpace.AffineMap ℝ
      (StdSimplex ℝ (Fin (n + 1)))
      (StdSimplex ℝ (Fin (n + 2))) => g t) heq

theorem barycentricFlagSingular_adjacent_swap_face
    (X : TopCat) {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (σ : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 1)) :
    (TopCat.toSSet.obj X).δ j.castSucc
        (barycentricFlagSingular X (n + 1)
          (σ * Equiv.swap j.castSucc j.succ) x) =
      (TopCat.toSSet.obj X).δ j.castSucc
        (barycentricFlagSingular X (n + 1) σ x) := by
  apply (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).injective
  ext t
  simp only [TopCat.toSSetObjEquiv_δ_apply]
  simp only [barycentricFlagSingular, Equiv.apply_symm_apply,
    ContinuousMap.comp_apply]
  rw [barycentricFlag_adjacent_swap_face]

theorem barycentricFlag_interior_face_sum_zero
    (X : TopCat) {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (j : Fin (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)),
      (σ.sign : ℤ) • (TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).δ j.castSucc
          (barycentricFlagSingular X (n + 1) σ x)) :
        (ModuleCat.of ℤ ℤ) ⟶ (singularChains X).X n) = 0 := by
  let g (σ : Equiv.Perm (Fin (n + 2))) :=
    σ * Equiv.swap j.castSucc j.succ
  apply Finset.sum_ninvolution g
  · intro σ
    simp only [g, adjacent_swap_changes_sign,
      barycentricFlagSingular_adjacent_swap_face]
    simp
  · intro σ _ h
    have heq := congrArg (fun τ : Equiv.Perm (Fin (n + 2)) => τ j.castSucc) h
    simp [g, Equiv.Perm.mul_apply] at heq
    have hv := congrArg Fin.val heq
    simp at hv
  · intro σ
    exact Finset.mem_univ _
  · intro σ
    simp [g, mul_assoc]

private theorem barycentricFlag_weighted_interior_face_sum_zero
    (X : TopCat) {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (j : Fin (n + 1)) (c : ℤ) :
    (∑ σ : Equiv.Perm (Fin (n + 2)),
      ((σ.sign : ℤ) * c) • (TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).δ j.castSucc
          (barycentricFlagSingular X (n + 1) σ x)) :
        (ModuleCat.of ℤ ℤ) ⟶ (singularChains X).X n) = 0 := by
  calc
    _ = c • (∑ σ : Equiv.Perm (Fin (n + 2)),
        (σ.sign : ℤ) • (TopCat.toSSet.obj X).ιChainComplex
          ((TopCat.toSSet.obj X).δ j.castSucc
            (barycentricFlagSingular X (n + 1) σ x))) := by
          simp [Finset.smul_sum, mul_smul, mul_comm]
    _ = 0 := by rw [barycentricFlag_interior_face_sum_zero]; simp

theorem barycentricDegree_boundary_last
    (X : TopCat) {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    (TopCat.toSSet.obj X).ιChainComplex x ≫
        barycentricDegree X (n + 1) ≫ (singularChains X).d (n + 1) n =
      ∑ σ : Equiv.Perm (Fin (n + 2)),
        ((σ.sign : ℤ) * (-1 : ℤ) ^ (Fin.last (n + 1)).val) •
          (TopCat.toSSet.obj X).ιChainComplex
            ((TopCat.toSSet.obj X).δ (Fin.last (n + 1))
              (barycentricFlagSingular X (n + 1) σ x)) := by
  rw [← Category.assoc, barycentricDegree_generator]
  simp only [Preadditive.sum_comp, Linear.smul_comp,
    SSet.ιChainComplex_d, Finset.smul_sum, smul_smul]
  simp_rw [Fin.sum_univ_castSucc]
  simp only [Finset.sum_add_distrib]
  have hfirst : (∑ σ : Equiv.Perm (Fin (n + 2)),
      ∑ i : Fin n,
        ((σ.sign : ℤ) * (-1 : ℤ) ^ i.castSucc.castSucc.val) •
          (TopCat.toSSet.obj X).ιChainComplex
            ((TopCat.toSSet.obj X).δ i.castSucc.castSucc
              (barycentricFlagSingular X (n + 1) σ x)) :
        (ModuleCat.of ℤ ℤ) ⟶ (singularChains X).X n) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    exact barycentricFlag_weighted_interior_face_sum_zero X x i.castSucc
      ((-1 : ℤ) ^ i.castSucc.castSucc.val)
  rw [hfirst, zero_add]
  have hsecond := barycentricFlag_weighted_interior_face_sum_zero
    X x (Fin.last n) ((-1 : ℤ) ^ (Fin.last n).castSucc.val)
  rw [hsecond, zero_add]

private noncomputable def lastPermutation (n : ℕ)
    (i : Fin (n + 2)) (ρ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin (n + 2)) :=
  Equiv.Perm.decomposeFin'Symm i ρ * finRotate (n + 2)

private theorem lastPermutation_last (n : ℕ)
    (i : Fin (n + 2)) (ρ : Equiv.Perm (Fin (n + 1))) :
    lastPermutation n i ρ (Fin.last (n + 1)) = i := by
  simp [lastPermutation, Equiv.Perm.mul_apply,
    Equiv.Perm.decomposeFin'Symm_zero]

private theorem lastPermutation_castSucc (n : ℕ)
    (i : Fin (n + 2)) (ρ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    lastPermutation n i ρ k.castSucc = i.succAbove (ρ k) := by
  simp [lastPermutation, Equiv.Perm.mul_apply,
    Equiv.Perm.decomposeFin'Symm_succ]

private theorem lastPermutation_sign (n : ℕ)
    (i : Fin (n + 2)) (ρ : Equiv.Perm (Fin (n + 1))) :
    ((lastPermutation n i ρ).sign : ℤ) *
        (-1 : ℤ) ^ (Fin.last (n + 1)).val =
      ((-1 : ℤ) ^ i.val) * (ρ.sign : ℤ) := by
  simp only [lastPermutation, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_decomposeFin'Symm, sign_finRotate,
    Fin.val_last]
  rw [show n + 2 - 1 = n + 1 by omega, pow_add]
  norm_num [pow_succ]
  have hn : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by
    rw [← pow_add]
    rw [show n + n = 2 * n by omega, pow_mul]
    norm_num
  calc
    _ = ((-1 : ℤ) ^ i.val * (ρ.sign : ℤ)) *
        ((-1 : ℤ) ^ n * (-1 : ℤ) ^ n) := by ring
    _ = _ := by rw [hn]; ring

private noncomputable def lastPermutationEquiv (n : ℕ) :
    (Fin (n + 2) × Equiv.Perm (Fin (n + 1))) ≃
      Equiv.Perm (Fin (n + 2)) :=
  Equiv.Perm.decomposeFin'.symm.trans (Equiv.mulRight (finRotate (n + 2)))

private theorem lastPermutationEquiv_apply (n : ℕ)
    (i : Fin (n + 2)) (ρ : Equiv.Perm (Fin (n + 1))) :
    lastPermutationEquiv n (i, ρ) = lastPermutation n i ρ := by
  rfl

private theorem sum_over_lastPermutation (n : ℕ)
    {M : Type*} [AddCommMonoid M]
    (f : Equiv.Perm (Fin (n + 2)) → M) :
    ∑ σ, f σ = ∑ i : Fin (n + 2),
      ∑ ρ : Equiv.Perm (Fin (n + 1)), f (lastPermutation n i ρ) := by
  rw [← Fintype.sum_prod_type' (fun i ρ => f (lastPermutation n i ρ))]
  change ∑ σ, f σ = ∑ p, f (lastPermutationEquiv n p)
  exact (Equiv.sum_comp (lastPermutationEquiv n) f).symm

private theorem lastPermutation_symm_succAbove (n : ℕ)
    (i : Fin (n + 2)) (ρ : Equiv.Perm (Fin (n + 1)))
    (a : Fin (n + 1)) :
    (lastPermutation n i ρ).symm (i.succAbove a) =
      (ρ.symm a).castSucc := by
  apply (lastPermutation n i ρ).injective
  simp [lastPermutation_castSucc]

private theorem lastPermutation_symm_last (n : ℕ)
    (i : Fin (n + 2)) (ρ : Equiv.Perm (Fin (n + 1))) :
    (lastPermutation n i ρ).symm i = Fin.last (n + 1) := by
  apply (lastPermutation n i ρ).injective
  simp [lastPermutation_last]

private theorem flagVertices_lastPermutation_castSucc (n : ℕ)
    (i : Fin (n + 2)) (ρ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    flagVertices (n + 1) (lastPermutation n i ρ) k.castSucc =
      (flagVertices n ρ k).image i.succAbove := by
  ext z
  constructor
  · intro hz
    have hzi : z ≠ i := by
      intro heq
      subst z
      have h := (Finset.mem_filter.mp hz).2
      rw [lastPermutation_symm_last] at h
      have hv := Fin.le_def.mp h
      simp only [Fin.val_castSucc, Fin.val_last] at hv
      omega
    obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hzi
    rw [Finset.mem_image]
    refine ⟨a, ?_, rfl⟩
    have h := (Finset.mem_filter.mp hz).2
    rw [lastPermutation_symm_succAbove] at h
    simpa [flagVertices] using h
  · intro hz
    rw [Finset.mem_image] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    simp only [flagVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [lastPermutation_symm_succAbove]
    simpa [flagVertices] using ha

private theorem subBarycenter_image_succAbove
    {n : ℕ} (S : Finset (Fin (n + 1))) (hS : S.Nonempty)
    (i : Fin (n + 2)) :
    StdSimplex.map i.succAbove
        (StdSimplex.subBarycenter (K := ℝ) S hS) =
      StdSimplex.subBarycenter (K := ℝ) (S.image i.succAbove) (hS.image _) := by
  ext z
  rw [StdSimplex.weights_map, StdSimplex.weights_subBarycenter,
    StdSimplex.weights_subBarycenter]
  rw [Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single]
  rw [Finset.card_image_of_injective S i.succAbove_right_injective]
  have hsum :
      (∑ m ∈ Finset.image i.succAbove S, Finsupp.single m (S.card : ℝ)⁻¹) =
        ∑ m ∈ S, Finsupp.single (i.succAbove m) (S.card : ℝ)⁻¹ := by
    rw [Finset.sum_image (Set.injOn_of_injective i.succAbove_right_injective)]
  rw [hsum]

private theorem barycentricFlag_lastPermutation_face
    (n : ℕ) (i : Fin (n + 2))
    (ρ : Equiv.Perm (Fin (n + 1)))
    (t : StdSimplex ℝ (Fin (n + 1))) :
    barycentricFlag (n + 1) (lastPermutation n i ρ)
        (StdSimplex.map (Fin.last (n + 1)).succAbove t) =
      StdSimplex.map i.succAbove (barycentricFlag n ρ t) := by
  let f := StdSimplex.affineMap (R := ℝ) (Fin.last (n + 1)).succAbove
  let g := StdSimplex.affineMap (R := ℝ) i.succAbove
  have heq : (barycentricFlagAffine (n + 1)
      (lastPermutation n i ρ)).comp f =
      g.comp (barycentricFlagAffine n ρ) := by
    apply StdSimplex.affineMap_ext
    intro k
    change barycentricFlagAffine (n + 1) (lastPermutation n i ρ)
        (StdSimplex.map (Fin.last (n + 1)).succAbove (.single k)) =
      StdSimplex.map i.succAbove
        (barycentricFlagAffine n ρ (.single k))
    simp only [Fin.succAbove_last, StdSimplex.map_single,
      barycentricFlagAffine_vertex]
    simp only [flagVertices_lastPermutation_castSucc]
    exact (subBarycenter_image_succAbove _ _ _).symm
  exact congrArg (fun q : ConvexSpace.AffineMap ℝ
      (StdSimplex ℝ (Fin (n + 1)))
      (StdSimplex ℝ (Fin (n + 2))) => q t) heq

theorem barycentricFlagSingular_lastPermutation_face
    (X : TopCat) {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (i : Fin (n + 2)) (ρ : Equiv.Perm (Fin (n + 1))) :
    (TopCat.toSSet.obj X).δ (Fin.last (n + 1))
        (barycentricFlagSingular X (n + 1) (lastPermutation n i ρ) x) =
      barycentricFlagSingular X n ρ
        ((TopCat.toSSet.obj X).δ i x) := by
  apply (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).injective
  ext t
  simp only [TopCat.toSSetObjEquiv_δ_apply]
  simp only [barycentricFlagSingular, Equiv.apply_symm_apply,
    ContinuousMap.comp_apply]
  rw [barycentricFlag_lastPermutation_face]
  rfl

theorem barycentricDegree_chain_identity (X : TopCat) (n : ℕ) :
    barycentricDegree X (n + 1) ≫ (singularChains X).d (n + 1) n =
      (singularChains X).d (n + 1) n ≫ barycentricDegree X n := by
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro x
  rw [barycentricDegree_boundary_last]
  rw [sum_over_lastPermutation]
  simp only [lastPermutation_sign,
    barycentricFlagSingular_lastPermutation_face]
  rw [← Category.assoc, SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp, Linear.smul_comp]
  simp_rw [barycentricDegree_generator]
  simp only [Finset.smul_sum, smul_smul]

noncomputable def barycentricChainMap (X : TopCat) :
    singularChains X ⟶ singularChains X where
  f n := barycentricDegree X n
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    exact barycentricDegree_chain_identity X j

end CurveComplexGenusTwo.CWHurewicz
