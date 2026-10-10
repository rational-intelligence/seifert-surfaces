import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
namespace CurveComplex
 theorem position_interval_subdivision
    {S I : Type*} [TopologicalSpace S]
    (f : C(CurveComplex.Interval, S)) (U : I → Set S)
    (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ t, ∃ i, f t ∈ U i) :
    ∃ n : ℕ, 0 < n ∧ ∃ chart : Fin n → I,
      ∀ k : Fin n, ∀ t : CurveComplex.Interval,
        (k.val : ℝ) / n ≤ (t : ℝ) →
        (t : ℝ) ≤ (k.val + 1 : ℝ) / n → f t ∈ U (chart k) := by
  classical
  let V : I → Set Interval := fun i => f ⁻¹' U i
  have hV : ∀ i, IsOpen (V i) := fun i => (hU i).preimage f.continuous
  have hcov : (Set.univ : Set Interval) ⊆ ⋃ i, V i := by
    intro t _
    obtain ⟨i, hi⟩ := hcover t
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hV hcov
  obtain ⟨n, hn, hmesh⟩ := Real.exists_nat_pos_inv_lt hδ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let a : Fin n → Interval := fun k => ⟨(k.val : ℝ) / n, by
    constructor
    · positivity
    · apply (div_le_one hnR).mpr
      have hk : (k.val : ℝ) < n := by exact_mod_cast k.isLt
      exact hk.le⟩
  have ha : ∀ k : Fin n, ∃ i, Metric.ball (a k) δ ⊆ V i :=
    fun k => hball (a k) (Set.mem_univ _)
  choose chart hc using ha
  refine ⟨n, hn, chart, ?_⟩
  intro k t hlo hhi
  apply hc k
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
  change |(t : ℝ) - (k.val : ℝ) / n| < δ
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  calc
    (t : ℝ) - (k.val : ℝ) / n ≤ (n : ℝ)⁻¹ := by
      have heq : (k.val + 1 : ℝ) / n = (k.val : ℝ) / n + (n : ℝ)⁻¹ := by
        rw [add_div, one_div]
      rw [heq] at hhi
      linarith
    _ < δ := hmesh
end CurveComplex
