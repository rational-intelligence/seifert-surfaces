import CapArtificialTrace
import CapOpenLensGraph
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def capBaseMap (s : ℝ) (b : ℝ→E2) (z : E2) : E2 := b (s+Real.arcsin (capTangent s z))
def capBaseJet (s : ℝ) (b : ℝ→E2) (i : Fin 2) (z : E2) : E2 :=
  (deriv b (s+Real.arcsin (capTangent s z)) i/Real.sqrt (1-(capTangent s z)^2)) •
    rotateQuarter (unitCircleParameter s)

theorem cap_rotate_quarter_norm (s : ℝ) : ‖rotateQuarter (unitCircleParameter s)‖=1 := by
  have hh := frame_norm_sq 0 1 s
  simp only [zero_smul,one_smul,zero_add,zero_pow (by decide : 2≠0),one_pow,zero_add] at hh
  nlinarith [norm_nonneg (rotateQuarter (unitCircleParameter s))]

theorem capTangent_continuous (s : ℝ) : Continuous (capTangent s) := continuous_const.inner continuous_id

theorem capBaseMap_continuous (s : ℝ) (b : ℝ→E2) (hb : Continuous b) : Continuous (capBaseMap s b) :=
  hb.comp (continuous_const.add ((capTangent_continuous s).arcsin))

theorem capBaseJet_measurable (s : ℝ) (b : ℝ→E2) (hb : ContDiff ℝ ∞ b) (i : Fin 2) : Measurable (capBaseJet s b i) := by
  unfold capBaseJet
  have hc : Continuous (fun z:E2 => deriv b (s+Real.arcsin (capTangent s z)) i) :=
    (EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp ((hb.continuous_deriv (by simp)).comp
      (continuous_const.add ((capTangent_continuous s).arcsin)))
  exact (hc.measurable.div ((continuous_const.sub ((capTangent_continuous s).pow 2)).sqrt.measurable)).smul measurable_const

theorem cap_base_coordinate_energy (s : ℝ) (b : ℝ→E2) (p : ℝ×ℝ) (hp : |p.2|<1) :
    euclideanJetDensity (capBaseJet s b) (capCoordinateEquiv s p) =
      ‖deriv b (s+Real.arcsin p.2)‖^2/(1-p.2^2) := by
  have hs : Real.sqrt (1-p.2^2)^2=1-p.2^2 := Real.sq_sqrt (by
    have hh := (sq_lt_sq₀ (abs_nonneg p.2) (show 0≤(1:ℝ) by norm_num)).mpr hp
    simpa [sq_abs] using le_of_lt (sub_pos.mpr (show p.2^2<1 by simpa [sq_abs] using hh)))
  simp only [euclideanJetDensity,capBaseJet,capCoordinateEquiv_tangent,norm_smul,Real.norm_eq_abs,
    cap_rotate_quarter_norm,mul_one,div_pow,sq_abs,hs]
  rw [← Finset.sum_div,← EuclideanSpace.real_norm_sq_eq]

theorem cap_coordinate_tangent_range (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2) (z : E2)
    (hz : z∈planarCap (unitCircleParameter s) q) : |capTangent s z|<capLensReach q := by
  let p := (capCoordinateEquiv s).symm z
  have he : capCoordinateEquiv s p=z := (capCoordinateEquiv s).apply_symm_apply z
  have hp := (cap_coordinate_graph_iff s q hq hq1 p).mp (by rw [he];exact hz)
  have hy := abs_lt.mpr hp.1
  rw [← capCoordinateEquiv_tangent s p,he] at hy
  exact hy

theorem cap_coordinate_rectangle (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2) :
    (capCoordinateEquiv s) ⁻¹' planarCap (unitCircleParameter s) q ⊆
      Icc (1-q) 1 ×ˢ Icc (-capLensReach q) (capLensReach q) := by
  intro p hp
  have hg := (cap_coordinate_graph_iff s q hq hq1 p).mp hp
  have hL : Real.sqrt (q^2-p.2^2)≤q := by
    have hh := Real.sqrt_le_sqrt (sub_le_self (q^2) (sq_nonneg p.2))
    rwa [Real.sqrt_sq hq.le] at hh
  have hU : Real.sqrt (1-p.2^2)≤1 := by
    have hh := Real.sqrt_le_sqrt (sub_le_self (1:ℝ) (sq_nonneg p.2))
    simpa using hh
  exact ⟨⟨by have hh:=hg.2.1;change 1-Real.sqrt (q^2-p.2^2)<p.1 at hh;linarith,
    hg.2.2.le.trans hU⟩,⟨hg.1.1.le,hg.1.2.le⟩⟩
end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
