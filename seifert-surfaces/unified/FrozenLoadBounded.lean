import ApprovedDataClosure

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder

def matrixActionLinear (A : Mat) : V →L[ℝ] V :=
  ({ toFun := DeGiorgi.matMulE A
     map_add' := by
       intro x y
       ext i
       simp [DeGiorgi.matMulE_apply, Matrix.mulVec_add]
     map_smul' := by
       intro c x
       ext i
       simp [DeGiorgi.matMulE_apply, Matrix.mulVec_smul] } : V →ₗ[ℝ] V).toContinuousLinearMap

def pairGradientLinear (Ω : Set V) : H01Space Ω →L[ℝ] Lp V 2 (volume.restrict Ω) :=
  (WithLp.sndL 2 ℝ (Lp ℝ 2 (volume.restrict Ω)) (Lp V 2 (volume.restrict Ω))).comp
    (H01Space Ω).subtypeL

lemma frozenLoad_eq_inner (A : Mat) {Ω : Set V} {v : V → ℝ}
    (hv : H1Witness v Ω) (p : H01Space Ω) :
    frozenLoad A hv p = -inner ℝ
      ((matrixActionLinear A).compLp ((weak_gradient_memLp Ω v hv).toLp hv.weakGrad))
      (pairGradientLinear Ω p) := by
  unfold frozenLoad
  rw [L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [(matrixActionLinear A).coeFn_compLp
      ((weak_gradient_memLp Ω v hv).toLp hv.weakGrad),
    (weak_gradient_memLp Ω v hv).coeFn_toLp] with x hx hvx
  rw [hx, hvx]
  rfl

theorem frozenLoad_bounded_linear (center : V) (R κ Λ : ℝ)
    (hR : 0 < R) (hκ : 0 < κ) (hΛ : κ ≤ Λ) (A : Mat)
    (hA : CoefficientBounds (fun _ => A) (Metric.ball center R) κ Λ)
    (v : V → ℝ) (hv : H1Witness v (Metric.ball center R)) :
    IsBoundedLinearMap ℝ (frozenLoad A hv) := by
  let Ω := Metric.ball center R
  let f := (matrixActionLinear A).compLp ((weak_gradient_memLp Ω v hv).toLp hv.weakGrad)
  let L := -((innerSL ℝ f).comp (pairGradientLinear Ω))
  have heq : frozenLoad A hv = L := by
    funext p
    exact frozenLoad_eq_inner A hv p
  rw [heq]
  exact L.isBoundedLinearMap

end SeifertSurfaces.WeakSchauder
