import CapBaseNativeL2
import CapUpperBoundaryGreen
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def capCoordinateLinear (s : ℝ) : (ℝ×ℝ)→L[ℝ]E2 :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (unitCircleParameter s) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (rotateQuarter (unitCircleParameter s))

theorem capCoordinateLinear_apply (s : ℝ) (p : ℝ×ℝ) : capCoordinateLinear s p=capCoordinateEquiv s p := rfl

theorem capCoordinate_contDiff (s : ℝ) : ContDiff ℝ ∞ (capCoordinateEquiv s) :=
  (capCoordinateLinear s).contDiff

def capScalarProfile (s : ℝ) (b : ℝ→E2) (i : Fin 2) (y : ℝ) : ℝ := b (s+Real.arcsin y) i
def capCoordinateProduct (s : ℝ) (b : ℝ→E2) (psi : E2→ℝ) (i : Fin 2) (p : ℝ×ℝ) : ℝ :=
  capScalarProfile s b i p.2 * psi (capCoordinateEquiv s p)
def capCoordinateFluxX (s : ℝ) (b : ℝ→E2) (psi : E2→ℝ) (i j : Fin 2) (p : ℝ×ℝ) : ℝ :=
  capCoordinateProduct s b psi i p * unitCircleParameter s j
def capCoordinateFluxY (s : ℝ) (b : ℝ→E2) (psi : E2→ℝ) (i j : Fin 2) (p : ℝ×ℝ) : ℝ :=
  capCoordinateProduct s b psi i p * rotateQuarter (unitCircleParameter s) j

theorem capScalarProfile_deriv (s y : ℝ) (b : ℝ→E2) (hb : ContDiff ℝ ∞ b) (i : Fin 2)
    (hy : |y|<1) : HasDerivAt (capScalarProfile s b i)
      (deriv b (s+Real.arcsin y) i/Real.sqrt (1-y^2)) y := by
  have hd := (hb.differentiable (by simp) (s+Real.arcsin y)).hasDerivAt
  have hp := (EuclideanSpace.proj (𝕜:=ℝ) i).hasFDerivAt.comp_hasDerivAt (s+Real.arcsin y) hd
  have ha := (Real.hasDerivAt_arcsin (ne_of_gt (abs_lt.mp hy).1) (ne_of_lt (abs_lt.mp hy).2)).const_add s
  convert hp.comp y ha using 1
  · rfl
  · simp only [EuclideanSpace.coe_proj]
    ring

theorem capScalarProfile_smoothAt (s y : ℝ) (b : ℝ→E2) (hb : ContDiff ℝ ∞ b) (i : Fin 2)
    (hy : |y|<1) : ContDiffAt ℝ ∞ (capScalarProfile s b i) y := by
  have ha : ContDiffAt ℝ ∞ Real.arcsin y := Real.contDiffAt_arcsin (ne_of_gt (abs_lt.mp hy).1) (ne_of_lt (abs_lt.mp hy).2)
  have hθ : ContDiffAt ℝ ∞ (fun y:ℝ => s+Real.arcsin y) y := contDiffAt_const.add ha
  exact ((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp hb).contDiffAt.comp y hθ

theorem cap_coordinate_product_fderiv (s : ℝ) (b : ℝ→E2) (hb : ContDiff ℝ ∞ b)
    (psi : E2→ℝ) (hpsi : ContDiff ℝ ∞ psi) (i : Fin 2) (p : ℝ×ℝ) (hp : |p.2|<1) :
    HasFDerivAt (capCoordinateProduct s b psi i)
      ((psi (capCoordinateEquiv s p) * (deriv b (s+Real.arcsin p.2) i/Real.sqrt (1-p.2^2))) •
        ContinuousLinearMap.snd ℝ ℝ ℝ +
        capScalarProfile s b i p.2 • ((fderiv ℝ psi (capCoordinateEquiv s p)).comp (capCoordinateLinear s))) p := by
  have hβ := (capScalarProfile_deriv s p.2 b hb i hp).hasFDerivAt.comp p (hasFDerivAt_snd (p:=p))
  have hφ := (hpsi.differentiable (by simp) (capCoordinateEquiv s p)).hasFDerivAt.comp p (capCoordinateLinear s).hasFDerivAt
  convert hβ.mul hφ using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro z
    simp [ContinuousLinearMap.comp_apply,Function.comp_apply]
    ring

theorem cap_frame_coordinate_vector (s : ℝ) (j : Fin 2) :
    unitCircleParameter s j • unitCircleParameter s +
      rotateQuarter (unitCircleParameter s) j • rotateQuarter (unitCircleParameter s) = coordinateVector 2 j := by
  apply PiLp.ext
  intro k
  fin_cases j <;> fin_cases k <;>
    simp [unitCircleParameter,rotateQuarter,coordinateVector,EuclideanSpace.equiv] <;>
    nlinarith [Real.cos_sq_add_sin_sq s]

theorem cap_coordinate_divergence (s : ℝ) (b : ℝ→E2) (hb : ContDiff ℝ ∞ b)
    (psi : E2→ℝ) (hpsi : ContDiff ℝ ∞ psi) (i j : Fin 2) (p : ℝ×ℝ) (hp : |p.2|<1) :
    (fderiv ℝ (capCoordinateFluxX s b psi i j) p) (1,0) +
      (fderiv ℝ (capCoordinateFluxY s b psi i j) p) (0,1) =
      capBaseMap s b (capCoordinateEquiv s p) i *
        fderiv ℝ psi (capCoordinateEquiv s p) (coordinateVector 2 j) +
        capBaseJet s b i (capCoordinateEquiv s p) j * psi (capCoordinateEquiv s p) := by
  have hd := cap_coordinate_product_fderiv s b hb psi hpsi i p hp
  have hx := hd.mul_const (unitCircleParameter s j)
  have hy := hd.mul_const (rotateQuarter (unitCircleParameter s) j)
  rw [show fderiv ℝ (capCoordinateFluxX s b psi i j) p = _ from hx.fderiv,
    show fderiv ℝ (capCoordinateFluxY s b psi i j) p = _ from hy.fderiv]
  have hframe := congrArg (fderiv ℝ psi (capCoordinateEquiv s p)) (cap_frame_coordinate_vector s j)
  simp only [map_add,map_smul,smul_eq_mul] at hframe
  simp [capBaseMap,capBaseJet,capCoordinateEquiv_tangent,capScalarProfile,
    ContinuousLinearMap.comp_apply,capCoordinateLinear,PiLp.smul_apply,smul_eq_mul] at *
  linear_combination b (s+Real.arcsin p.2) i * hframe

theorem cap_coordinate_flux_smooth (s : ℝ) (b : ℝ→E2) (hb : ContDiff ℝ ∞ b)
    (psi : E2→ℝ) (hpsi : ContDiff ℝ ∞ psi) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (capCoordinateFluxX s b psi i j) {p : ℝ×ℝ | |p.2|<1} ∧
      ContDiffOn ℝ ∞ (capCoordinateFluxY s b psi i j) {p : ℝ×ℝ | |p.2|<1} := by
  have hprod : ContDiffOn ℝ ∞ (capCoordinateProduct s b psi i) {p : ℝ×ℝ | |p.2|<1} := by
    intro p hp
    have hβ := (capScalarProfile_smoothAt s p.2 b hb i hp).comp p contDiffAt_snd
    have hφ := (hpsi.comp (capCoordinate_contDiff s)).contDiffAt (x:=p)
    exact (hβ.mul hφ).contDiffWithinAt
  exact ⟨hprod.mul contDiffOn_const,hprod.mul contDiffOn_const⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
