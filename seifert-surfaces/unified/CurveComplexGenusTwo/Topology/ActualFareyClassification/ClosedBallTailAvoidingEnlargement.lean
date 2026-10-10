import CurveComplexGenusTwo.Topology.ActualFareyClassification.VariableDirectionRadialHomeomorph

open Set Topology Filter Metric

/-- A closed forbidden set determines a concrete variable-width expansion of
an actual closed ball. The expansion creates interior room away from forbidden
points and introduces NO new forbidden contacts, even at its fixed endpoints. -/
theorem closed_ball_actual_forbidden_avoiding_enlargement
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (B U : Set E) (hB : IsClosed B) (hBn : B.Nonempty)
    (hU : IsOpen U) (hQU : closedBall (0:E) 1⊆U) :
    ∃ H : E ≃ₜ E,
      H '' closedBall (0:E) 1⊆U ∧
      (H '' closedBall (0:E) 1)∩B=closedBall (0:E) 1∩B ∧
      closedBall (0:E) 1\B⊆H '' ball (0:E) 1 ∧
      (∀ z, ‖z‖=1 → z∈B → H.symm z=z) := by
  obtain ⟨delta,hdelta,hDU⟩ := (isCompact_closedBall (0:E) 1).exists_cthickening_subset_open hU hQU
  let w : E→ℝ := fun z => min delta (infDist z B/2)
  have hw : Continuous w := continuous_const.min ((continuous_infDist_pt B).div_const 2)
  have hb (z : E) : 0 ≤ w z ∧ w z ≤ delta :=
    ⟨le_min hdelta.le (div_nonneg infDist_nonneg (by norm_num)),min_le_left _ _⟩
  obtain ⟨H,hH,hHi⟩ := bounded_direction_width_radial_homeomorph w hw delta hdelta.le hb
  let n : E→E := fun z => ‖z‖⁻¹ • z
  have hn (z : E) (hz : z≠0) : ‖n z‖=1 := by
    dsimp [n]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hz)),inv_mul_cancel₀ (norm_pos_iff.mpr hz).ne']
  have hc (z : E) : 0<1+w (n z) := by linarith [(hb (n z)).1]
  have hnormi (z : E) : ‖H.symm z‖=(1+w (n z))⁻¹*‖z‖ := by
    rw [hHi,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hc z))]
  have hQ (z : E) (hz : z∈H '' closedBall (0:E) 1) : ‖z‖ ≤ 1+w (n z) := by
    obtain ⟨x,hx,he⟩ := hz
    have hi : ‖H.symm z‖ ≤ 1 := by rw [←he,H.symm_apply_apply]; simpa using hx
    rw [hnormi] at hi
    have hh := (mul_le_mul_of_nonneg_left hi (hc z).le)
    rw [←mul_assoc,mul_inv_cancel₀ (hc z).ne',one_mul,mul_one] at hh
    exact hh
  have hdist (z : E) (hz : 1<‖z‖) : dist z (n z)=‖z‖-1 := by
    have hnpos : 0<‖z‖ := by linarith
    rw [dist_eq_norm,show z-n z=(1-‖z‖⁻¹) • z by dsimp [n]; module,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (by have hh := (inv_le_one₀ hnpos).mpr hz.le; linarith)]
    rw [sub_mul,one_mul,inv_mul_cancel₀ hnpos.ne']
  have hold : closedBall (0:E) 1⊆H '' closedBall (0:E) 1 := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa using hz
    refine ⟨H.symm z,?_,H.apply_symm_apply z⟩
    have hh : ‖H.symm z‖ ≤ ‖z‖ := by
      rw [hnormi]
      have hc1 : (1+w (n z))⁻¹ ≤ 1 := (inv_le_one₀ (hc z)).mpr (by linarith [(hb (n z)).1])
      simpa using mul_le_mul_of_nonneg_right hc1 (norm_nonneg z)
    simpa using hh.trans hz1
  have hNoNew (z : E) (hz : z∈H '' closedBall (0:E) 1) (hzB : z∈B) : z∈closedBall (0:E) 1 := by
    by_contra hnQ
    have hz1 : 1<‖z‖ := by simpa using hnQ
    have hq := hQ z hz
    have hd : infDist (n z) B ≤ w (n z) := by
      apply (infDist_le_dist_of_mem hzB).trans
      rw [dist_comm,hdist z hz1]
      linarith
    have hwD : w (n z) ≤ infDist (n z) B/2 := min_le_right _ _
    have hw0 : w (n z)=0 := by linarith [infDist_nonneg (x:=n z) (s:=B),(hb (n z)).1]
    rw [hw0] at hq
    linarith
  refine ⟨H,?_,?_,?_,?_⟩
  · intro z hz
    apply hDU
    by_cases hzQ : z∈closedBall (0:E) 1
    · exact self_subset_cthickening _ hzQ
    · have hz1 : 1<‖z‖ := by simpa using hzQ
      have hz0 : z≠0 := by intro he; simp [he] at hz1; linarith
      have hnQ : n z∈closedBall (0:E) 1 := by simp [hn z hz0]
      apply mem_cthickening_of_dist_le z (n z) delta (closedBall (0:E) 1) hnQ
      rw [hdist z hz1]
      linarith [hQ z hz,(hb (n z)).2]
  · ext z
    constructor
    · rintro ⟨hz,hzB⟩; exact ⟨hNoNew z hz hzB,hzB⟩
    · rintro ⟨hz,hzB⟩; exact ⟨hold hz,hzB⟩
  · intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa using hz.1
    refine ⟨H.symm z,?_,H.apply_symm_apply z⟩
    have hh : ‖H.symm z‖<1 := by
      rw [hnormi]
      rcases lt_or_eq_of_le hz1 with hlt|heq
      · have hc1 : (1+w (n z))⁻¹ ≤ 1 := (inv_le_one₀ (hc z)).mpr (by linarith [(hb (n z)).1])
        exact (mul_le_mul_of_nonneg_right hc1 (norm_nonneg z)).trans_lt (by simpa using hlt)
      · have hnz : n z=z := by dsimp [n]; rw [heq]; simp
        have hwpos : 0<w (n z) := by
          rw [hnz]
          exact lt_min hdelta (div_pos ((hB.notMem_iff_infDist_pos hBn).mp hz.2) (by norm_num))
        rw [heq,mul_one]
        exact (inv_lt_one₀ (hc z)).mpr (by linarith)
    simpa using hh
  · intro z hz hzB
    have hnz : n z=z := by dsimp [n]; rw [hz]; simp
    have hw0 : w (n z)=0 := by
      rw [hnz]
      dsimp [w]
      rw [infDist_zero_of_mem hzB,zero_div,min_eq_right hdelta.le]
    rw [hHi]
    change (1+w (n z))⁻¹ • z=z
    rw [hw0]; simp

#print axioms closed_ball_actual_forbidden_avoiding_enlargement
