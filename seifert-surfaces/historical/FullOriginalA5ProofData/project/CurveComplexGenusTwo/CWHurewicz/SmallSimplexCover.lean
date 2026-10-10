import Mathlib

/-!
The compactness input for singular excision: every continuous singular simplex
has a uniform scale at which its pieces land in one member of the excision cover.
-/

namespace CurveComplexGenusTwo.CWHurewicz

open Convexity Topology

noncomputable local instance (n : ℕ) : MetricSpace (StdSimplex ℝ (Fin (n + 1))) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).comapMetricSpace
    (fun t => (t.weights : Fin (n + 1) → ℝ))

theorem singularSimplex_excision_lebesgue_number
    {X : Type*} [TopologicalSpace X] (A U : Set X)
    (hU : closure U ⊆ interior A) (n : ℕ)
    (f : C(StdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : StdSimplex ℝ (Fin (n + 1)),
        (f '' Metric.ball x δ ⊆ Uᶜ ∨ f '' Metric.ball x δ ⊆ A) := by
  let c : Fin 2 → Set (StdSimplex ℝ (Fin (n + 1))) :=
    fun i => if i = 0 then f ⁻¹' (closure U)ᶜ else f ⁻¹' interior A
  have hcopen : ∀ i, IsOpen (c i) := by
    intro i
    fin_cases i
    · exact isClosed_closure.isOpen_compl.preimage f.continuous
    · exact isOpen_interior.preimage f.continuous
  have hcover : (Set.univ : Set (StdSimplex ℝ (Fin (n + 1)))) ⊆ ⋃ i, c i := by
    intro x _
    by_cases hx : f x ∈ closure U
    · exact Set.mem_iUnion.mpr ⟨1, by simpa [c] using hU hx⟩
    · exact Set.mem_iUnion.mpr ⟨0, by simpa [c] using hx⟩
  obtain ⟨δ, hδ, hδball⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hcopen hcover
  refine ⟨δ, hδ, fun x => ?_⟩
  obtain ⟨i, hi⟩ := hδball x (Set.mem_univ x)
  fin_cases i
  · left
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact fun hyU => (hi hz) (subset_closure hyU)
  · right
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact interior_subset (hi hz)

/-- A finite family of singular simplices admits one common excision scale.
This is the compactness step needed for the finite support of a singular chain. -/
theorem singularSimplices_excision_lebesgue_number
    {X : Type*} [TopologicalSpace X] (A U : Set X)
    (hU : closure U ⊆ interior A) (n : ℕ)
    (fs : List C(StdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ f ∈ fs, ∀ x : StdSimplex ℝ (Fin (n + 1)),
        (f '' Metric.ball x δ ⊆ Uᶜ ∨ f '' Metric.ball x δ ⊆ A) := by
  induction fs with
  | nil =>
      exact ⟨1, by norm_num, by simp⟩
  | cons f fs ih =>
      obtain ⟨δf, hδf, hf⟩ := singularSimplex_excision_lebesgue_number A U hU n f
      obtain ⟨δs, hδs, hs⟩ := ih
      refine ⟨min δf δs, lt_min hδf hδs, ?_⟩
      intro g hg x
      rcases List.mem_cons.mp hg with rfl | hg
      · rcases hf x with h | h
        · exact Or.inl (Set.image_mono (Metric.ball_subset_ball (min_le_left _ _)) |>.trans h)
        · exact Or.inr (Set.image_mono (Metric.ball_subset_ball (min_le_left _ _)) |>.trans h)
      · rcases hs g hg x with h | h
        · exact Or.inl (Set.image_mono (Metric.ball_subset_ball (min_le_right _ _)) |>.trans h)
        · exact Or.inr (Set.image_mono (Metric.ball_subset_ball (min_le_right _ _)) |>.trans h)

end CurveComplexGenusTwo.CWHurewicz
