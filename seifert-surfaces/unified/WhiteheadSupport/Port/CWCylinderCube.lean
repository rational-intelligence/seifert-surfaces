import WhiteheadSupport.Port.CWBasic

namespace SeifertSurfaces.WhiteheadSupport.Port.CW

universe u v

open _root_.Topology Metric

private def cylinderCoords (n : ℕ)
    (p : unitInterval × CellDisk n) : Fin (n + 1) → ℝ :=
  Fin.cons (2 * p.1.val - 1) p.2.val

private theorem cylinderCoords_mem (n : ℕ)
    (p : unitInterval × CellDisk n) :
    cylinderCoords n p ∈ closedBall (0 : Fin (n + 1) → ℝ) 1 := by
  rw [mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
  intro j
  cases j using Fin.cases with
  | zero =>
    change |2 * p.1.val - 1| ≤ 1
    rw [abs_le]
    have ht : 0 ≤ p.1.val ∧ p.1.val ≤ 1 := p.1.property
    constructor <;> linarith [ht.1, ht.2]
  | succ j =>
    have hw : ‖p.2.val‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right] using p.2.property
    have hj := (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).1 hw j
    simpa [cylinderCoords] using hj

/-- The interval-cylinder over an `n`-disk sits in the sup-norm
`(n+1)`-disk via the first coordinate `2t-1`. -/
def cylinderToDisk (n : ℕ) :
    C(unitInterval × CellDisk n, CellDisk (n + 1)) :=
  ⟨fun p => ⟨cylinderCoords n p, cylinderCoords_mem n p⟩, by
    apply Continuous.subtype_mk
    unfold cylinderCoords
    fun_prop⟩

private noncomputable def diskTime (n : ℕ) (z : CellDisk (n + 1)) : unitInterval :=
  ⟨(z.val 0 + 1) / 2, by
    have hz : ‖z.val‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right] using z.property
    have h0 := (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).1 hz (0 : Fin (n + 1))
    have habs : |z.val 0| ≤ 1 := by simpa only [Real.norm_eq_abs] using h0
    rcases (abs_le.mp habs) with ⟨hl, hr⟩
    constructor <;> linarith⟩

private def diskTail (n : ℕ) (z : CellDisk (n + 1)) : CellDisk n :=
  ⟨Fin.tail z.val, by
    rw [mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
    intro j
    have hz : ‖z.val‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right] using z.property
    exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).1 hz j.succ⟩

/-- Inverse coordinates: the first disk coordinate records time, while the
remaining coordinates record the original disk point. -/
noncomputable def diskToCylinder (n : ℕ) :
    C(CellDisk (n + 1), unitInterval × CellDisk n) :=
  ⟨fun z => (diskTime n z, diskTail n z), by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact (((continuous_apply (0 : Fin (n + 1))).comp continuous_subtype_val).add
        continuous_const).div_const 2
    · apply Continuous.subtype_mk
      fun_prop⟩

theorem diskToCylinder_left_inverse (n : ℕ) :
    Function.LeftInverse (diskToCylinder n) (cylinderToDisk n) := by
  intro p
  apply Prod.ext
  · apply Subtype.ext
    change ((2 * p.1.val - 1) + 1) / 2 = p.1.val
    ring
  · apply Subtype.ext
    simp [diskToCylinder, diskTail, cylinderToDisk, cylinderCoords]

theorem diskToCylinder_right_inverse (n : ℕ) :
    Function.RightInverse (diskToCylinder n) (cylinderToDisk n) := by
  intro z
  apply Subtype.ext
  ext j
  cases j using Fin.cases with
  | zero => simp [cylinderToDisk, cylinderCoords, diskToCylinder, diskTime]; ring
  | succ j => simp [cylinderToDisk, cylinderCoords, diskToCylinder, diskTail, Fin.tail]

noncomputable def cylinderDiskHomeomorph (n : ℕ) :
    unitInterval × CellDisk n ≃ₜ CellDisk (n + 1) where
  toFun := cylinderToDisk n
  invFun := diskToCylinder n
  left_inv := diskToCylinder_left_inverse n
  right_inv := diskToCylinder_right_inverse n
  continuous_toFun := (cylinderToDisk n).continuous
  continuous_invFun := (diskToCylinder n).continuous

/-- Boundary of a cylinder, represented by its explicit disk coordinates. -/
def cylinderBoundary (n : ℕ) : Set (unitInterval × CellDisk n) :=
  {p | (cylinderToDisk n p).val ∈
    sphere (0 : Fin (n + 1) → ℝ) 1}

theorem isClosed_cylinderBoundary (n : ℕ) :
    IsClosed (cylinderBoundary n) := by
  exact isClosed_sphere.preimage
    (continuous_subtype_val.comp (cylinderToDisk n).continuous)

/-- The cylinder boundary is the next-dimensional sphere. The map is the
coordinate homeomorphism restricted to the boundary. -/
noncomputable def cylinderBoundarySphereHomeomorph (n : ℕ) :
    ↥(cylinderBoundary n) ≃ₜ CellSphere (n + 1) where
  toFun p := ⟨(cylinderToDisk n p.val).val, p.property⟩
  invFun z := ⟨diskToCylinder n
      ⟨z.val, sphere_subset_closedBall z.property⟩, by
    change ((cylinderToDisk n) ((diskToCylinder n)
      ⟨z.val, sphere_subset_closedBall z.property⟩)).val ∈
      sphere (0 : Fin (n + 1) → ℝ) 1
    rw [diskToCylinder_right_inverse]
    exact z.property⟩
  left_inv p := by
    apply Subtype.ext
    exact diskToCylinder_left_inverse n p.val
  right_inv z := by
    apply Subtype.ext
    change ((cylinderToDisk n) ((diskToCylinder n)
      ⟨z.val, sphere_subset_closedBall z.property⟩)).val = z.val
    exact congrArg Subtype.val
      (diskToCylinder_right_inverse n
        ⟨z.val, sphere_subset_closedBall z.property⟩)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp
      ((cylinderToDisk n).continuous.comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (diskToCylinder n).continuous.comp
      (continuous_subtype_val.subtype_mk _)

theorem cylinderBoundary_zero (n : ℕ) (w : CellDisk n) :
    ((0 : unitInterval), w) ∈ cylinderBoundary n := by
  simp only [cylinderBoundary, Set.mem_ofPred_eq, mem_sphere, dist_zero_right]
  change ‖cylinderCoords n ((0 : unitInterval), w)‖ = 1
  have hle : ‖cylinderCoords n ((0 : unitInterval), w)‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_zero_right] using
      cylinderCoords_mem n ((0 : unitInterval), w)
  have hfirst := norm_le_pi_norm
    (cylinderCoords n ((0 : unitInterval), w)) (0 : Fin (n + 1))
  have hge : 1 ≤ ‖cylinderCoords n ((0 : unitInterval), w)‖ := by
    simpa [cylinderCoords] using hfirst
  exact le_antisymm hle hge

theorem cylinderBoundary_one (n : ℕ) (w : CellDisk n) :
    ((1 : unitInterval), w) ∈ cylinderBoundary n := by
  simp only [cylinderBoundary, Set.mem_ofPred_eq, mem_sphere, dist_zero_right]
  change ‖cylinderCoords n ((1 : unitInterval), w)‖ = 1
  have hle : ‖cylinderCoords n ((1 : unitInterval), w)‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_zero_right] using
      cylinderCoords_mem n ((1 : unitInterval), w)
  have hfirst := norm_le_pi_norm
    (cylinderCoords n ((1 : unitInterval), w)) (0 : Fin (n + 1))
  have hge : 1 ≤ ‖cylinderCoords n ((1 : unitInterval), w)‖ := by
    have : |2 - (1 : ℝ)| ≤ ‖cylinderCoords n ((1 : unitInterval), w)‖ := by
      simpa [cylinderCoords] using hfirst
    norm_num at this
    exact this
  exact le_antisymm hle hge

theorem cylinderBoundary_side (n : ℕ) (t : unitInterval)
    (w : CellSphere n) :
    (t, (⟨w.val, sphere_subset_closedBall w.property⟩ : CellDisk n)) ∈
      cylinderBoundary n := by
  simp only [cylinderBoundary, Set.mem_ofPred_eq, mem_sphere, dist_zero_right]
  change ‖cylinderCoords n
    (t, (⟨w.val, sphere_subset_closedBall w.property⟩ : CellDisk n))‖ = 1
  have hle : ‖cylinderCoords n
      (t, (⟨w.val, sphere_subset_closedBall w.property⟩ : CellDisk n))‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_zero_right] using
      cylinderCoords_mem n
        (t, (⟨w.val, sphere_subset_closedBall w.property⟩ : CellDisk n))
  have hw : ‖w.val‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using w.property
  have hge : 1 ≤ ‖cylinderCoords n
      (t, (⟨w.val, sphere_subset_closedBall w.property⟩ : CellDisk n))‖ := by
    calc
      1 = ‖w.val‖ := hw.symm
      _ ≤ ‖cylinderCoords n
          (t, (⟨w.val, sphere_subset_closedBall w.property⟩ : CellDisk n))‖ := by
        apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
        intro j
        have hj := norm_le_pi_norm
          (cylinderCoords n
            (t, (⟨w.val, sphere_subset_closedBall w.property⟩ : CellDisk n)))
          j.succ
        simpa [cylinderCoords] using hj
  exact le_antisymm hle hge

/-- A point of the cylinder boundary lies on an endpoint face or on the
lateral sphere. -/
theorem cylinderBoundary_cases (n : ℕ)
    (p : unitInterval × CellDisk n) (hp : p ∈ cylinderBoundary n) :
    p.1 = 0 ∨ p.1 = 1 ∨
      p.2.val ∈ sphere (0 : Fin n → ℝ) 1 := by
  by_contra h
  push Not at h
  obtain ⟨ht0, ht1, hw⟩ := h
  have ht : 0 < p.1.val ∧ p.1.val < 1 := by
    have hb := p.1.property
    constructor
    · exact lt_of_le_of_ne hb.1 (Ne.symm (by
        intro heq
        apply ht0
        exact Subtype.ext heq))
    · exact lt_of_le_of_ne hb.2 (by
        intro heq
        apply ht1
        exact Subtype.ext heq)
  have hwnorm : ‖p.2.val‖ < 1 := by
    have hle : ‖p.2.val‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right] using p.2.property
    have hne : ‖p.2.val‖ ≠ 1 := by
      intro heq
      apply hw
      simpa only [mem_sphere, dist_zero_right] using heq
    exact lt_of_le_of_ne hle hne
  have hc : ‖cylinderCoords n p‖ < 1 := by
    apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).2
    intro j
    cases j using Fin.cases with
    | zero =>
      change |2 * p.1.val - 1| < 1
      rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    | succ j =>
      have hj := norm_le_pi_norm p.2.val j
      have : ‖p.2.val j‖ < 1 := lt_of_le_of_lt hj hwnorm
      simpa [cylinderCoords] using this
  have hnorm : ‖cylinderCoords n p‖ = 1 := by
    change (cylinderToDisk n p).val ∈ sphere (0 : Fin (n + 1) → ℝ) 1 at hp
    change ‖(cylinderToDisk n p).val‖ = 1
    simpa only [mem_sphere, dist_zero_right] using hp
  exact (ne_of_lt hc) hnorm

end SeifertSurfaces.WhiteheadSupport.Port.CW
