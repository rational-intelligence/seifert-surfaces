import InitialSeparableTestAE_v457

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

private def original_disc_clamp_v457 (x : E2) : closedDisc 1 :=
  ⟨(max 1 ‖x‖)⁻¹•x,by
    change dist ((max 1 ‖x‖)⁻¹•x) 0≤1
    rw [dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (le_max_left 1 ‖x‖ |>.trans' (by norm_num)))]
    have hp : 0 < max 1 ‖x‖ := lt_of_lt_of_le (by norm_num) (le_max_left 1 ‖x‖)
    simpa only [div_eq_mul_inv,mul_comm] using (div_le_one hp).mpr (le_max_right 1 ‖x‖)⟩

private theorem continuous_original_disc_clamp_v457 : Continuous original_disc_clamp_v457 := by
  apply Continuous.subtype_mk
  have hp : ∀ x:E2,max 1 ‖x‖≠0 := fun x=>(lt_of_lt_of_le (by norm_num) (le_max_left 1 ‖x‖)).ne'
  exact (continuous_const.max continuous_norm).inv₀ hp |>.smul continuous_id

private theorem original_disc_clamp_eq_v457 (x:E2) (hx:x∈closedDisc 1) :
    (original_disc_clamp_v457 x:E2)=x := by
  have hn : ‖x‖≤1 := by simpa [closedDisc,dist_zero_right] using hx
  simp only [original_disc_clamp_v457,max_eq_left hn,inv_one,one_smul]

private theorem original_circle_in_closed_disc_v457 (t:ℝ) : unitCircleParameter t∈closedDisc 1 := by
  have hn : ‖unitCircleParameter t‖^2=1 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
    exact Real.cos_sq_add_sin_sq t
  change dist (unitCircleParameter t) 0≤1
  rw [dist_zero_right]
  nlinarith [norm_nonneg (unitCircleParameter t)]

private def original_closed_disc_test_jet_v457
    (psi:E2→ℝ) (hpsi:ContDiff ℝ ∞ psi) :
    C(closedDisc 1,ℝ) × (Fin 2 → C(closedDisc 1,ℝ)) :=
  (⟨fun x=>psi x,(hpsi.continuous.comp continuous_subtype_val)⟩,
    fun j=>⟨fun x=>fderiv ℝ psi x (coordinateVector 2 j),
      ((hpsi.continuous_fderiv (by simp)).clm_apply continuous_const).comp continuous_subtype_val⟩)

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
