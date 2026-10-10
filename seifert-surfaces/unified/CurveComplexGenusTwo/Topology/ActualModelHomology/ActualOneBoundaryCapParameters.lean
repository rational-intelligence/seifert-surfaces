import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualBoundaryCapRayGeometry

namespace CurveComplex.Hyperbolic.OneBoundaryRay

noncomputable def modelSideCount (p : ℕ) : ℝ := 4*(p : ℝ)+3
noncomputable def modelCapAngle (p : ℕ) : ℝ := Real.pi/modelSideCount p
noncomputable def modelRayOrigin (p : ℕ) : ℝ := 1/Real.cos (modelCapAngle p)

 theorem modelSideCount_pos (p : ℕ) : 0 < modelSideCount p := by
  unfold modelSideCount
  positivity

 theorem modelCapAngle_pos (p : ℕ) : 0 < modelCapAngle p := by
  exact div_pos Real.pi_pos (modelSideCount_pos p)

 theorem modelCapAngle_lt_half_pi (p : ℕ) : modelCapAngle p<Real.pi/2 := by
  unfold modelCapAngle
  apply (div_lt_div_iff₀ (modelSideCount_pos p) (by norm_num : (0:ℝ)<2)).mpr
  unfold modelSideCount
  nlinarith [Real.pi_pos, show 0≤(p:ℝ) by positivity]

 theorem modelCapCos_pos (p : ℕ) : 0<Real.cos (modelCapAngle p) := by
  apply Real.cos_pos_of_mem_Ioo
  exact ⟨by linarith [modelCapAngle_pos p,Real.pi_pos],modelCapAngle_lt_half_pi p⟩

 theorem modelCapCos_lt_one (p : ℕ) : Real.cos (modelCapAngle p)<1 := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi
    (show (0:ℝ)≤0 by rfl)
    (show modelCapAngle p≤Real.pi by linarith [modelCapAngle_lt_half_pi p,Real.pi_pos])
    (modelCapAngle_pos p)
  simpa using h

 theorem modelRayOrigin_gt_one (p : ℕ) : 1 < modelRayOrigin p := by
  unfold modelRayOrigin
  exact (lt_div_iff₀ (modelCapCos_pos p)).mpr (by simpa using modelCapCos_lt_one p)

noncomputable def modelCapDeletedDiskHomotopyEquivBoundary (p : ℕ) :=
  deletedCapDiskHomotopyEquivBoundary (modelRayOrigin p) (modelRayOrigin_gt_one p)

end CurveComplex.Hyperbolic.OneBoundaryRay
