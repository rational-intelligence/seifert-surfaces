import InitialBoundaryHoleFilling_v463

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 800000
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

private theorem unit_circle_parameter_surjective_v463
    (b:E2) (hb:‖b‖=1) : ∃ s:ℝ,unitCircleParameter s=b := by
  let z:ℂ := ⟨b 0,b 1⟩
  have hs : (b 0)^2+(b 1)^2=1 := by
    have he := EuclideanSpace.real_norm_sq_eq b
    rw [hb] at he
    simpa only [Fin.sum_univ_two,one_pow] using he.symm
  have hz : ‖z‖=1 := by
    have hzsq : ‖z‖^2=1 := by
      rw [←Complex.normSq_eq_norm_sq]
      simpa [z,Complex.normSq_apply,pow_two] using hs
    nlinarith [norm_nonneg z]
  have hne : z ≠ 0 := by intro he; simp [he] at hz
  refine ⟨Complex.arg z,?_⟩
  ext j
  fin_cases j
  · change Real.cos (Complex.arg z)=b 0
    rw [Complex.cos_arg hne,hz]
    simp [z]
  · change Real.sin (Complex.arg z)=b 1
    rw [Complex.sin_arg,hz]
    simp [z]

private theorem original_disc_center_ball_or_boundary_near_v463
    (x:E2) (hx:x∈closedDisc 1) (r:ℝ) (hr:0 < r) (hrhalf:r ≤ 1/2) :
    Metric.closedBall x (r/16)⊆disc 1 ∨
      ∃ s:ℝ,dist x (unitCircleParameter s) < r/8 := by
  classical
  have hxn : ‖x‖ ≤ 1 := by simpa only [closedDisc,Metric.mem_closedBall,dist_zero_right] using hx
  by_cases hgap : r/8 ≤ 1-‖x‖
  · left
    intro z hz
    have hzx : ‖z-x‖ ≤ r/16 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    have hn : ‖z‖ ≤ ‖z-x‖+‖x‖ := by
      simpa only [sub_add_cancel] using norm_add_le (z-x) x
    have hlt : ‖z‖ < 1 := by linarith
    simpa only [disc,Metric.mem_ball,dist_zero_right] using hlt
  · right
    have hnx : 0 < ‖x‖ := by linarith [lt_of_not_ge hgap]
    let b:E2 := ‖x‖⁻¹•x
    have hbn : ‖b‖=1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hnx),inv_mul_cancel₀ hnx.ne']
    obtain ⟨s,hs⟩ := unit_circle_parameter_surjective_v463 b hbn
    refine ⟨s,?_⟩
    rw [hs]
    have hsub : x-b=((‖x‖-1)/‖x‖)•x := by
      dsimp only [b]
      rw [div_eq_mul_inv,sub_mul,mul_inv_cancel₀ hnx.ne',one_mul,sub_smul,one_smul]
    have hdist : dist x b=1-‖x‖ := by
      rw [dist_eq_norm,hsub,norm_smul,
        Real.norm_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxn) hnx.le)]
      field_simp
      ring
    rw [hdist]
    exact lt_of_not_ge hgap

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
