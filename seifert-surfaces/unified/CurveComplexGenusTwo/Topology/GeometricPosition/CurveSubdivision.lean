import CurveComplexGenusTwo.Topology.GeometricPosition.IntervalSubdivision
namespace CurveComplex
/-- Concrete embedded parameter arcs covering the unchanged embedded circle,
with each whole closed arc in one member of the specified open cover. -/
theorem position_curve_chart_subdivision
    {S I : Type*} [TopologicalSpace S]
    (c : Curve S) (U : I → Set S)
    (hU : ∀ i, IsOpen (U i))
    (hcover : c.image ⊆ ⋃ i, U i) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ chart : Fin n → I,
      ∃ arc : Fin n → C(Interval, S),
        (∀ k, Topology.IsEmbedding (arc k)) ∧
        (∀ k t, arc k t = c.map (Circle.exp
          (-Real.pi + 2 * Real.pi * (((k.val : ℝ) + (t : ℝ)) / n)))) ∧
        c.image = ⋃ k, Set.range (arc k) ∧
        (∀ k, Set.range (arc k) ⊆ U (chart k)) := by
  classical
  let f : C(Interval, S) := ⟨fun t => c.map (Circle.exp
      (-Real.pi + 2 * Real.pi * (t : ℝ))),
    c.embedded.continuous.comp (Circle.exp.continuous.comp (by fun_prop))⟩
  let V : (I × Interval) → Set Interval := fun j =>
    f ⁻¹' U j.1 ∩ Metric.ball j.2 (1/4)
  have hV : ∀ j, IsOpen (V j) := fun j =>
    ((hU j.1).preimage f.continuous).inter Metric.isOpen_ball
  have hcov : ∀ t : Interval, ∃ j, t ∈ V j := by
    intro t
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_range_self _))
    exact ⟨(i, t), hi, by simp⟩
  obtain ⟨n, hn, chart, hc⟩ := position_interval_subdivision
    ⟨id, continuous_id⟩ V hV hcov
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn1 : n = 1 := by omega
    let k : Fin n := ⟨0, hn⟩
    let z : Interval := ⟨0, by norm_num⟩
    let o : Interval := ⟨1, by norm_num⟩
    have hz := (hc k z (by simp [k, z]) (by simp [k, z, hn1])).2
    have ho := (hc k o (by simp [k, o]) (by simp [k, o, hn1])).2
    have hzo : dist z o = 1 := by simp [z, o, Subtype.dist_eq, Real.dist_eq]
    have hd := dist_triangle z (chart k).2 o
    rw [hzo, dist_comm (chart k).2 o] at hd
    have hz' := Metric.mem_ball.mp hz
    have ho' := Metric.mem_ball.mp ho
    change dist z (chart k).2 < 1/4 at hz'
    change dist o (chart k).2 < 1/4 at ho'
    linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnR2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  let q : Fin n → Interval → Interval := fun k t => ⟨((k.val : ℝ) + (t : ℝ)) / n, by
    constructor
    · exact div_nonneg (add_nonneg (Nat.cast_nonneg _) t.property.1) hnR.le
    · apply (div_le_one hnR).mpr
      have hk : (k.val : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt k.isLt
      linarith [t.property.2]⟩
  let g : Fin n → C(Interval, Circle) := fun k =>
    ⟨fun t => Circle.exp (-Real.pi + 2 * Real.pi * (q k t : ℝ)),
      Circle.exp.continuous.comp (by dsimp [q]; fun_prop)⟩
  let arc : Fin n → C(Interval, S) := fun k =>
    ⟨fun t => c.map (g k t), c.embedded.continuous.comp (g k).continuous⟩
  have hbound (k : Fin n) (t : Interval) :
      -Real.pi + 2 * Real.pi * (q k t : ℝ) ∈ Set.Icc
        (-Real.pi + 2 * Real.pi * ((k.val : ℝ) / n))
        (-Real.pi + 2 * Real.pi * ((k.val + 1 : ℝ) / n)) := by
    have hlo : (k.val : ℝ) / n ≤ (q k t : ℝ) := by
      dsimp [q]
      exact div_le_div_of_nonneg_right (by linarith [t.property.1]) hnR.le
    have hhi : (q k t : ℝ) ≤ (k.val + 1 : ℝ) / n := by
      dsimp [q]
      exact div_le_div_of_nonneg_right (by linarith [t.property.2]) hnR.le
    constructor <;> nlinarith [Real.pi_pos]
  have hi (k : Fin n) : Function.Injective (g k) := by
    intro t u heq
    have hwidth :
        (-Real.pi + 2 * Real.pi * ((k.val + 1 : ℝ) / n)) -
          (-Real.pi + 2 * Real.pi * ((k.val : ℝ) / n)) < 2 * Real.pi := by
      have hw : 2 * Real.pi / (n : ℝ) < 2 * Real.pi := by
        apply (div_lt_iff₀ hnR).mpr
        nlinarith [Real.pi_pos]
      convert hw using 1 <;> ring
    have hh := Circle.exp_injOn_Icc hwidth (hbound k t) (hbound k u) heq
    apply Subtype.ext
    have hq : (q k t : ℝ) = (q k u : ℝ) := by nlinarith [Real.pi_pos]
    change ((k.val : ℝ) + (t : ℝ)) / n = ((k.val : ℝ) + (u : ℝ)) / n at hq
    have ht := (div_left_inj' hnR.ne').mp hq
    linarith
  refine ⟨n, hn2, fun k => (chart k).1, arc, ?_, ?_, ?_, ?_⟩
  · intro k
    exact c.embedded.comp ((g k).continuous.isClosedEmbedding (hi k)).isEmbedding
  · intro k t
    rfl
  · have hmeshCover (s : Interval) : ∃ k : Fin n, ∃ t : Interval, q k t = s := by
      by_cases hs : (s : ℝ) = 1
      · let k : Fin n := ⟨n-1, Nat.sub_lt hn (by decide)⟩
        let t : Interval := ⟨1, by norm_num⟩
        refine ⟨k, t, Subtype.ext ?_⟩
        have hk : ((n-1 : ℕ) : ℝ) + 1 = n := by
          exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ n by omega))
        change (((n-1 : ℕ) : ℝ) + 1) / n = (s : ℝ)
        rw [hk, div_self hnR.ne', hs]
      · have hs1 : (s : ℝ) < 1 := lt_of_le_of_ne s.property.2 hs
        let k : Fin n := ⟨⌊(n : ℝ) * s⌋₊, (Nat.floor_lt
          (mul_nonneg hnR.le s.property.1)).mpr
            (by nlinarith)⟩
        let t : Interval := ⟨(n : ℝ) * s - k.val, by
          constructor
          · exact sub_nonneg.mpr (Nat.floor_le (mul_nonneg hnR.le s.property.1))
          · have hh := Nat.lt_floor_add_one ((n : ℝ) * s)
            change (n : ℝ) * s - (⌊(n : ℝ) * s⌋₊ : ℝ) ≤ 1
            linarith⟩
        refine ⟨k, t, Subtype.ext ?_⟩
        change ((k.val : ℝ) + ((n : ℝ) * s - k.val)) / n = (s : ℝ)
        field_simp
        ring
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨θ, hθ, hθz⟩ := Circle.surjOn_exp_neg_pi_pi (Set.mem_univ z)
      let s : Interval := ⟨(θ + Real.pi) / (2 * Real.pi), by
        constructor
        · exact div_nonneg (by linarith [hθ.1]) (by positivity)
        · apply (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr
          linarith [hθ.2]⟩
      obtain ⟨k, t, hqt⟩ := hmeshCover s
      apply Set.mem_iUnion.mpr
      refine ⟨k, t, ?_⟩
      change c.map (Circle.exp (-Real.pi + 2 * Real.pi * (q k t : ℝ))) = c.map z
      rw [hqt]
      have hangle : -Real.pi + 2 * Real.pi * (s : ℝ) = θ := by
        dsimp [s]
        field_simp
        ring
      rw [hangle, hθz]
    · intro hy
      obtain ⟨k, t, rfl⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_range_self _
  · intro k y hy
    obtain ⟨t, rfl⟩ := hy
    exact (hc k (q k t)
      (div_le_div_of_nonneg_right (by linarith [t.property.1]) hnR.le)
      (div_le_div_of_nonneg_right (by linarith [t.property.2]) hnR.le)).1
end CurveComplex
