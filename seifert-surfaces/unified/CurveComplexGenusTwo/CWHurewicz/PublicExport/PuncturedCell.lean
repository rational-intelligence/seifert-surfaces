import CurveComplexGenusTwo.CWHurewicz.CWBasic

namespace CurveComplexGenusTwo.CWHurewicz
open Topology
open scoped unitInterval ContinuousMap

/-- The punctured characteristic disk, with the actual subspace topology. -/
abbrev PuncturedCellDisk (n : ℕ) := {z : CellDisk n // z.val ≠ 0}

noncomputable def puncturedCellInclusion (n : ℕ) :
    C(PuncturedCellDisk n, CellDisk n) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Radial projection to the characteristic sphere. -/
noncomputable def puncturedCellRadial (n : ℕ) :
    C(PuncturedCellDisk n, CellSphere n) :=
  ⟨fun z => ⟨‖z.val.val‖⁻¹ • z.val.val, by
      rw [Metric.mem_sphere, dist_zero_right]
      exact norm_smul_inv_norm z.property⟩,
    by
      apply Continuous.subtype_mk
      have hv : Continuous (fun z : PuncturedCellDisk n => z.val.val) :=
        continuous_subtype_val.comp continuous_subtype_val
      exact (hv.norm.inv₀ (fun z => norm_ne_zero_iff.mpr z.property)).smul hv⟩

noncomputable def puncturedCellRadialToDisk (n : ℕ) :
    C(PuncturedCellDisk n, CellDisk n) :=
  ⟨fun z => ⟨(puncturedCellRadial n z).val,
      Metric.sphere_subset_closedBall (puncturedCellRadial n z).property⟩,
    (continuous_subtype_val.comp (puncturedCellRadial n).continuous).subtype_mk _⟩

/-- Radial cell removal fixes the boundary pointwise. -/
noncomputable def puncturedCellRadialHomotopy (n : ℕ) :
    ContinuousMap.HomotopyRel (puncturedCellInclusion n)
      (puncturedCellRadialToDisk n)
      {z : PuncturedCellDisk n | ‖z.val.val‖ = 1} where
  toFun p := ⟨(1 - (p.1 : ℝ)) • p.2.val.val +
      (p.1 : ℝ) • (puncturedCellRadial n p.2).val,
    (convex_closedBall (0 : Fin n → ℝ) (1 : ℝ)) p.2.val.property
      (Metric.sphere_subset_closedBall (puncturedCellRadial n p.2).property)
      (sub_nonneg.mpr p.1.property.2) p.1.property.1 (by ring)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hv : Continuous (fun p : I × PuncturedCellDisk n => p.2.val.val) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    have ht : Continuous (fun p : I × PuncturedCellDisk n => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hr : Continuous (fun p : I × PuncturedCellDisk n =>
        (puncturedCellRadial n p.2).val) :=
      continuous_subtype_val.comp ((puncturedCellRadial n).continuous.comp continuous_snd)
    exact ((continuous_const.sub ht).smul hv).add (ht.smul hr)
  map_zero_left z := by apply Subtype.ext; simp [puncturedCellInclusion]
  map_one_left z := by apply Subtype.ext; simp [puncturedCellRadialToDisk]
  prop' t z hz := by
    apply Subtype.ext
    change (1 - (t : ℝ)) • z.val.val +
      (t : ℝ) • (‖z.val.val‖⁻¹ • z.val.val) = z.val.val
    change ‖z.val.val‖ = 1 at hz
    rw [hz]
    simp only [inv_one, one_smul, ← add_smul]
    simp

/-- The deformation never crosses the removed cell center. -/
theorem puncturedCellRadialHomotopy_ne_zero (n : ℕ)
    (t : I) (z : PuncturedCellDisk n) :
    ((puncturedCellRadialHomotopy n) (t, z)).val ≠ 0 := by
  change (1 - (t : ℝ)) • z.val.val +
    (t : ℝ) • (‖z.val.val‖⁻¹ • z.val.val) ≠ 0
  rw [smul_smul, ← add_smul]
  apply smul_ne_zero _ z.property
  have hn : 0 < ‖z.val.val‖ := norm_pos_iff.mpr z.property
  have ht := t.property
  have hi : 0 < ‖z.val.val‖⁻¹ := inv_pos.mpr hn
  have hp : 0 < 1 - (t : ℝ) + (t : ℝ) * ‖z.val.val‖⁻¹ := by
    by_cases h : (t : ℝ) = 0
    · simp [h]
    · have : 0 < (t : ℝ) := lt_of_le_of_ne ht.1 (Ne.symm h)
      exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2) (mul_pos this hi)
  exact ne_of_gt hp

/-- Composing the radial homotopy with a genuine CW characteristic map
pushes a punctured cell into the lower skeleton, relative to its frontier. -/
noncomputable def characteristicRadialHomotopy
    {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (n : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set X) n) :
    ContinuousMap.HomotopyRel
      ((characteristic n i).comp (puncturedCellInclusion n))
      ((characteristic n i).comp (puncturedCellRadialToDisk n))
      {z : PuncturedCellDisk n | ‖z.val.val‖ = 1} where
  toFun p := characteristic n i (puncturedCellRadialHomotopy n p)
  continuous_toFun := (characteristic n i).continuous.comp
    (puncturedCellRadialHomotopy n).continuous
  map_zero_left z := by exact congrArg (characteristic n i) ((puncturedCellRadialHomotopy n).map_zero_left z)
  map_one_left z := by exact congrArg (characteristic n i) ((puncturedCellRadialHomotopy n).map_one_left z)
  prop' t z hz := by exact congrArg (characteristic n i) ((puncturedCellRadialHomotopy n).prop t z hz)

theorem characteristicRadialHomotopy_endpoint_mem
    {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (n : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set X) n)
    (z : PuncturedCellDisk n) :
    characteristicRadialHomotopy n i (1, z) ∈ skeletonBelow X n := by
  have he : characteristicRadialHomotopy n i (1, z) =
      characteristic n i (puncturedCellRadialToDisk n z) :=
    (characteristicRadialHomotopy n i).map_one_left z
  rw [he]
  exact (attaching n i (puncturedCellRadial n z)).property

/-- The characteristic sphere includes in the punctured disk. -/
noncomputable def cellSphereToPunctured (n : ℕ) :
    C(CellSphere n, PuncturedCellDisk n) :=
  ⟨fun z => ⟨⟨z.val, Metric.sphere_subset_closedBall z.property⟩, by
      have hz : ‖z.val‖ = 1 := by simp
      exact norm_ne_zero_iff.mp (by rw [hz]; norm_num)⟩,
    (continuous_subtype_val.subtype_mk _).subtype_mk _⟩

/-- The radial homotopy is a deformation through the punctured disk itself. -/
noncomputable def puncturedCellDeformation (n : ℕ) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (PuncturedCellDisk n))
      ((cellSphereToPunctured n).comp (puncturedCellRadial n))
      {z : PuncturedCellDisk n | ‖z.val.val‖ = 1} where
  toFun p := ⟨puncturedCellRadialHomotopy n p,
    puncturedCellRadialHomotopy_ne_zero n p.1 p.2⟩
  continuous_toFun := (puncturedCellRadialHomotopy n).continuous.subtype_mk _
  map_zero_left z := by
    apply Subtype.ext
    exact (puncturedCellRadialHomotopy n).map_zero_left z
  map_one_left z := by
    apply Subtype.ext
    exact (puncturedCellRadialHomotopy n).map_one_left z
  prop' t z hz := by
    apply Subtype.ext
    exact (puncturedCellRadialHomotopy n).prop t z hz

@[simp] theorem puncturedCellRadial_sphere (n : ℕ) (z : CellSphere n) :
    puncturedCellRadial n (cellSphereToPunctured n z) = z := by
  apply Subtype.ext
  change ‖z.val‖⁻¹ • z.val = z.val
  have hz : ‖z.val‖ = 1 := by simp
  simp [hz]

/-- A punctured characteristic disk has the homotopy type of its actual
boundary sphere. No Hurewicz, cellular approximation, or homology input. -/
noncomputable def puncturedCellSphereHomotopyEquiv (n : ℕ) :
    PuncturedCellDisk n ≃ₕ CellSphere n where
  toFun := puncturedCellRadial n
  invFun := cellSphereToPunctured n
  left_inv := ⟨(puncturedCellDeformation n).toHomotopy.symm⟩
  right_inv := by
    have h : (puncturedCellRadial n).comp (cellSphereToPunctured n) =
        ContinuousMap.id (CellSphere n) := by
      apply ContinuousMap.ext
      intro z
      exact puncturedCellRadial_sphere n z
    rw [h]

end CurveComplexGenusTwo.CWHurewicz
