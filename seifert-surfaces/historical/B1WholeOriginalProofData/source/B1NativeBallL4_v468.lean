import B1BoundaryH3Step_v468
import DifferentialGeometry.External.DeGiorgi.SobolevPoincare
import DifferentialGeometry.External.DeGiorgi.UnitBallApproximationCore.Rescaling
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
set_option maxHeartbeats 1000000

/-- In dimension two, the paid subcritical Sobolev inequality turns native
H1 on a ball into L4. No regular representative is supplied as an input. -/
theorem native_ball_H1_L4_v468 (R : ℝ) (hR : 0<R) (u : E2 → ℝ)
    (hu : DeGiorgi.MemW1p 2 u (Metric.ball (0:E2) R)) :
    MemLp u 4 (volume.restrict (Metric.ball (0:E2) R)) := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0:E2) R)) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  let hw := hu.someWitness
  let hwsmall : DeGiorgi.MemW1pWitness (ENNReal.ofReal (4/3:ℝ)) u (Metric.ball (0:E2) R) :=
    { memLp := hw.memLp.mono_exponent (by norm_num)
      weakGrad := hw.weakGrad
      weakGrad_component_memLp := fun i => (hw.weakGrad_component_memLp i).mono_exponent (by norm_num)
      isWeakGrad := hw.isWeakGrad }
  let hv := hwsmall.rescaleToUnitBall hR
  have hineq := DeGiorgi.sobolev_poincare_unitBall (by norm_num : 1<(4/3:ℝ))
    (by norm_num : (4/3:ℝ)<(2:ℝ)) hv
  norm_num at hineq
  let v : E2 → ℝ := fun z => u ((0:E2)+R • z)
  let avg : ℝ := ⨍ y in Metric.ball (0:E2) 1, v y ∂volume
  have hfin : eLpNorm (fun z => v z-avg) 4 (volume.restrict (Metric.ball (0:E2) 1))<⊤ := by
    have hC : DeGiorgi.CSobolevPoincare 2 (4/3:ℝ)<⊤ := by
      have hCG : DeGiorgi.CUnitBallExtensionGrad 2 (4/3:ℝ)≠⊤ := by
        unfold DeGiorgi.CUnitBallExtensionGrad
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by simp))
      change ENNReal.ofReal (DeGiorgi.CGns 2 (4/3:ℝ)) *
        (1+DeGiorgi.CUnitBallExtensionGrad 2 (4/3:ℝ)*
          (ENNReal.ofReal (DeGiorgi.CPoincVal 2)+1))<⊤
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨by norm_num,
        ENNReal.mul_lt_top hCG.lt_top (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,by norm_num⟩)⟩)
    have hh := hineq.trans_lt (ENNReal.mul_lt_top hC hv.weakGrad_norm_memLp.eLpNorm_lt_top)
    simpa only [v,avg,zero_add] using hh
  have hvLp : MemLp v 4 (volume.restrict (Metric.ball (0:E2) 1)) := by
    have hsub : MemLp (fun z => v z-avg) 4 (volume.restrict (Metric.ball (0:E2) 1)) := hfin
    have hconst : MemLp (fun _ : E2 => avg) 4 (volume.restrict (Metric.ball (0:E2) 1)) := memLp_const _
    convert hsub.add hconst using 1
    funext z
    simp only [Pi.add_apply,sub_add_cancel]
  have he := DeGiorgi.eLpNorm_rescale_to_unitBall (d:=2) (x₀:=(0:E2)) (f:=u) hR
    (by norm_num : (4:ℝ≥0∞)≠0) (by norm_num : (4:ℝ≥0∞)≠⊤)
  have hmul : ENNReal.ofReal (R⁻¹ ^ ((2:ℝ)/4))*eLpNorm u 4
      (volume.restrict (Metric.ball (0:E2) R))<⊤ := by
    have hh := hvLp.eLpNorm_lt_top
    change eLpNorm (fun z => u ((0:E2)+R • z)) 4 (volume.restrict (Metric.ball (0:E2) 1))<⊤ at hh
    rw [he] at hh
    norm_num at hh
    convert hh using 1 <;> norm_num
  have hfactor : ENNReal.ofReal (R⁻¹ ^ ((2:ℝ)/4))≠0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (inv_pos.mpr hR) _)).ne'
  by_contra hn
  have htop : eLpNorm u 4 (volume.restrict (Metric.ball (0:E2) R))=⊤ :=
    top_unique (not_lt.mp hn)
  rw [htop,ENNReal.mul_top hfactor] at hmul
  exact lt_irrefl _ hmul
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_ball_H1_L4_v468
