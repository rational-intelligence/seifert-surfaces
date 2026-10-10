import Section5GeometricDefinitions
import OriginalA4GeometryBridges

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N]

/-- The actual supplied warped collar has this literal coordinate Hessian.
Proof extracted from the already compiled A.4 calculation, without a Hessian premise. -/
theorem warped_coordinate_hessian
    {h : AmbientMetric N} {M : Set N} (C : WarpedBoundaryCollar h M)
    (y : E3) (hy : y ∈ C.coordinates.chart.target) (v : E3) :
    hessianQuadratic (actualChartTensor h C.coordinates)
      (fun z : E3 => z 0) y v = C.phi (y 0) * deriv C.phi (y 0) *
        (∑ i : Fin 2, ∑ j : Fin 2,
          C.levelMetric (levelCoordinates y) i j * levelVector v i * levelVector v j) := by
  have hentries : ∀ z ∈ C.coordinates.chart.target,
      actualChartTensor h C.coordinates z =
        !![1, 0, 0;
          0, C.phi (z 0)^2 * C.levelMetric (levelCoordinates z) 0 0,
             C.phi (z 0)^2 * C.levelMetric (levelCoordinates z) 0 1;
          0, C.phi (z 0)^2 * C.levelMetric (levelCoordinates z) 1 0,
             C.phi (z 0)^2 * C.levelMetric (levelCoordinates z) 1 1] := by
    intro z hz
    ext i j
    have hm := C.warped_metric z hz (coordinateVector 3 i) (coordinateVector 3 j)
    fin_cases i <;> fin_cases j <;>
      simpa [coordinateInner, coordinateVector, EuclideanSpace.single, PiLp.single_apply,
        Fin.sum_univ_succ, levelVector, levelCoordinates] using hm
  have hinvrow : ∀ j : Fin 3, (actualChartTensor h C.coordinates y)⁻¹ 0 j =
      if j = 0 then 1 else 0 := by
    have hLpos : (C.levelMetric (levelCoordinates y)).PosDef := by
      apply Matrix.PosDef.of_dotProduct_mulVec_pos
      · ext i j
        simpa only [Matrix.conjTranspose_apply, star_trivial] using
          C.levelMetric_symmetric (levelCoordinates y) j i
      · intro ξ hξ
        let v : E2 := WithLp.toLp 2 ξ
        have hv : v ≠ 0 := by
          intro hv
          exact hξ (WithLp.toLp_injective 2 hv)
        have hp := C.levelMetric_positive (levelCoordinates y) v hv
        convert hp using 1
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, v, Fin.sum_univ_succ]
        ring
    have hphi : 0 < C.phi (y 0) :=
      C.phi_positive _ (abs_lt.mp (C.target_radial_range y hy))
    have hdet : 0 < (actualChartTensor h C.coordinates y).det := by
      have heq : (actualChartTensor h C.coordinates y).det =
          C.phi (y 0)^4 * (C.levelMetric (levelCoordinates y)).det := by
        rw [hentries y hy, Matrix.det_fin_three, Matrix.det_fin_two]
        simp
        ring
      rw [heq]
      exact mul_pos (pow_pos hphi _) hLpos.det_pos
    have hmul := Matrix.mul_nonsing_inv (actualChartTensor h C.coordinates y)
      (isUnit_iff_ne_zero.mpr (ne_of_gt hdet))
    intro j
    have hrow := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 0 j) hmul
    simpa [Matrix.mul_apply, hentries y hy, Fin.sum_univ_succ, Matrix.one_apply, eq_comm] using hrow
  have hpartial : ∀ i j : Fin 2,
      partial3 (fun z => actualChartTensor h C.coordinates z i.succ j.succ) y 0 =
        2 * C.phi (y 0) * deriv C.phi (y 0) * C.levelMetric (levelCoordinates y) i j := by
    have hentry (z : E3) (hz : z ∈ C.coordinates.chart.target) (i j : Fin 2) :
        actualChartTensor h C.coordinates z i.succ j.succ =
          C.phi (z 0)^2 * C.levelMetric (levelCoordinates z) i j := by
      rw [hentries z hz]
      fin_cases i <;> fin_cases j <;> rfl
    let P : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0
    let L : E3 →L[ℝ] E2 :=
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1).smulRight (coordinateVector 2 0) +
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2).smulRight (coordinateVector 2 1)
    have hL : ∀ z, L z = levelCoordinates z := fun _ => rfl
    have hLzero : L (coordinateVector 3 0) = 0 := by
      simp [L, coordinateVector, EuclideanSpace.single, PiLp.single_apply]
    intro i j
    have hgerm : (fun z => actualChartTensor h C.coordinates z i.succ j.succ) =ᶠ[𝓝 y]
        (fun z => C.phi (z 0)^2 * C.levelMetric (levelCoordinates z) i j) := by
      filter_upwards [C.coordinates.chart.open_target.mem_nhds hy] with z hz
      exact hentry z hz i j
    have hphi := ((C.phi_smooth.differentiable (by simp)) (y 0)).hasDerivAt.comp_hasFDerivAt y
      P.hasFDerivAt
    have hlevel := (((C.levelMetric_smooth i j).differentiable (by simp)) (L y)).hasFDerivAt.comp y
      L.hasFDerivAt
    have hprod := (hphi.pow 2).mul hlevel
    dsimp only [Function.comp_def, Pi.mul_apply] at hprod
    change fderiv ℝ (fun z => actualChartTensor h C.coordinates z i.succ j.succ) y
      (coordinateVector 3 0) = _
    rw [hgerm.fderiv_eq]
    change fderiv ℝ (fun z => C.phi (P z)^2 * C.levelMetric (L z) i j) y
      (coordinateVector 3 0) = _
    have heq := hprod.fderiv
    change fderiv ℝ (fun z => C.phi (P z)^2 * C.levelMetric (L z) i j) y = _ at heq
    rw [heq]
    simp [hLzero, ContinuousLinearMap.comp_apply, P, hL, levelCoordinates, coordinateVector,
      EuclideanSpace.single, PiLp.single_apply]
    ring
  have hrow (z : E3) (hz : z ∈ C.coordinates.chart.target) (j : Fin 3) :
      actualChartTensor h C.coordinates z 0 j = if j = 0 then 1 else 0 := by
    rw [hentries z hz]
    fin_cases j <;> rfl
  have hcol (z : E3) (hz : z ∈ C.coordinates.chart.target) (i : Fin 3) :
      actualChartTensor h C.coordinates z i 0 = if i = 0 then 1 else 0 := by
    rw [hentries z hz]
    fin_cases i <;> rfl
  have hdrow (i j : Fin 3) :
      partial3 (fun z => actualChartTensor h C.coordinates z 0 j) y i = 0 := by
    have hgerm : (fun z => actualChartTensor h C.coordinates z 0 j) =ᶠ[𝓝 y]
        (fun _ => if j = 0 then 1 else 0) := by
      filter_upwards [C.coordinates.chart.open_target.mem_nhds hy] with z hz
      exact hrow z hz j
    unfold partial3
    rw [hgerm.fderiv_eq]
    simp
  have hdcol (i j : Fin 3) :
      partial3 (fun z => actualChartTensor h C.coordinates z j 0) y i = 0 := by
    have hgerm : (fun z => actualChartTensor h C.coordinates z j 0) =ᶠ[𝓝 y]
        (fun _ => if j = 0 then 1 else 0) := by
      filter_upwards [C.coordinates.chart.open_target.mem_nhds hy] with z hz
      exact hcol z hz j
    unfold partial3
    rw [hgerm.fderiv_eq]
    simp
  have hChrist (a b : Fin 3) : christoffel (actualChartTensor h C.coordinates) y a b 0 =
      -(1 / 2 : ℝ) * partial3 (fun z => actualChartTensor h C.coordinates z a b) y 0 := by
    simp only [christoffel, hinvrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, hdrow]
    ring
  have hp (z : E3) (a : Fin 3) :
      partial3 (fun z : E3 => z 0) z a = if a = 0 then 1 else 0 := by
    change fderiv ℝ (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0) z (coordinateVector 3 a) = _
    rw [ContinuousLinearMap.fderiv]
    simp [coordinateVector, EuclideanSpace.single, PiLp.single_apply, eq_comm]
  have hsecond (a b : Fin 3) :
      partial3 (fun z => partial3 (fun z : E3 => z 0) z b) y a = 0 := by
    simp only [hp]
    simp [partial3]
  unfold hessianQuadratic hessianCoefficient
  simp only [hsecond]
  simp only [hp]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [hChrist, zero_sub, neg_mul, neg_neg]
  simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hpartial ⊢
  simp only [hdrow, hdcol, mul_zero, zero_mul, zero_add, add_zero]
  have hp00 := hpartial 0 0
  have hp01 := hpartial 0 1
  have hp10 := hpartial 1 0
  have hp11 := hpartial 1 1
  norm_num at hp00 hp01 hp10 hp11
  simp only [hp00, hp01, hp10, hp11]
  simp [levelVector, levelCoordinates, coordinateVector, EuclideanSpace.single,
    PiLp.single_apply, PiLp.add_apply, PiLp.smul_apply]
  ring
/-- Strict negativity on every nonzero tangent vector at the actual boundary. -/
theorem warped_coordinate_boundary_strict
    {h : AmbientMetric N} {M : Set N} (C : WarpedBoundaryCollar h M)
    (y : E3) (hy : y ∈ C.coordinates.chart.target) (hy0 : y 0 = 0)
    (v : E3) (hv : v ≠ 0) (hv0 : v 0 = 0) :
    hessianQuadratic (actualChartTensor h C.coordinates)
      (fun z : E3 => z 0) y v < 0 := by
  rw [warped_coordinate_hessian C y hy v, hy0, C.phi_zero, one_mul]
  have hlevel : levelVector v ≠ 0 := by
    intro hz
    apply hv
    ext i
    fin_cases i
    · exact hv0
    · have he := congrArg (fun w : E2 => w 0) hz
      simpa [levelVector, levelCoordinates, coordinateVector, EuclideanSpace.single, PiLp.single_apply] using he
    · have he := congrArg (fun w : E2 => w 1) hz
      simpa [levelVector, levelCoordinates, coordinateVector, EuclideanSpace.single, PiLp.single_apply] using he
  exact mul_neg_of_neg_of_pos C.phi_strict_at_boundary
    (C.levelMetric_positive (levelCoordinates y) (levelVector v) hlevel)

end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
