import GeometricArea
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.NormDet

open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory Bundle

namespace SeifertSurfaces.MetricFoundations
open Foundations
universe u v
noncomputable section

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

theorem coordinateDifferential_injective {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (p : S) {y : Euc 2}
    (hy : y ∈ (extChartAt (𝓡∂ 2) p).target) :
    Function.Injective
      (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) (f.toFun ∘ (extChartAt (𝓡∂ 2) p).symm)
        (extChartAt (𝓡∂ 2) p).target y) := by
  have he := mdifferentiableWithinAt_extChartAt_symm hy
  have hu := (uniqueDiffOn_extChartAt_target (I := 𝓡∂ 2) p y hy).uniqueMDiffWithinAt
  rw [mfderiv_comp_mfderivWithin y (f.smooth.mdifferentiable (by simp) _)
    (mdifferentiableOn_extChartAt_symm y hy) hu]
  apply (f.differential_injective _).comp
  rw [he.mfderivWithin_mono hu (extChartAt_target_subset_range p)]
  intro a b hab
  have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hy
  have hab' := congrArg (mfderiv (𝓡∂ 2) 𝓘(ℝ, Euc 2) (extChartAt (𝓡∂ 2) p)
    ((extChartAt (𝓡∂ 2) p).symm y)) hab
  change ((mfderiv (𝓡∂ 2) 𝓘(ℝ, Euc 2) (extChartAt (𝓡∂ 2) p)
      ((extChartAt (𝓡∂ 2) p).symm y)) ∘L
      mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) (extChartAt (𝓡∂ 2) p).symm
        (range (𝓡∂ 2)) y) a =
    ((mfderiv (𝓡∂ 2) 𝓘(ℝ, Euc 2) (extChartAt (𝓡∂ 2) p)
      ((extChartAt (𝓡∂ 2) p).symm y)) ∘L
      mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) (extChartAt (𝓡∂ 2) p).symm
        (range (𝓡∂ 2)) y) b at hab'
  rw [h] at hab'
  exact hab'

set_option backward.isDefEq.respectTransparency false in
theorem coordinateGram_det_pos (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (p : S) {y : Euc 2}
    (hy : y ∈ (extChartAt (𝓡∂ 2) p).target) :
    0 < Matrix.det (coordinateGram g f.toFun p y) := by
  let d := mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3)
    (f.toFun ∘ (extChartAt (𝓡∂ 2) p).symm) (extChartAt (𝓡∂ 2) p).target y
  let c := (tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm
  let v : Fin 2 → TangentSpace (𝓡∂ 3) (f.toFun ((extChartAt (𝓡∂ 2) p).symm y)) :=
    fun i => d (c (EuclideanSpace.single i 1))
  have hv : LinearIndependent ℝ v := by
    have hb := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.linearIndependent
    have hc := hb.map' c.toLinearMap (LinearMap.ker_eq_bot.mpr c.injective)
    have hd := hc.map' d.toLinearMap
      (LinearMap.ker_eq_bot.mpr (coordinateDifferential_injective f p hy))
    have hvfun : d.toLinearMap ∘ c.toLinearMap ∘
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis = v := by
      funext i
      change d (c ((EuclideanSpace.basisFun (Fin 2) ℝ) i)) =
        d (c (EuclideanSpace.single i 1))
      rw [EuclideanSpace.basisFun_apply]
    rw [hvfun] at hd
    convert hd using 0 <;> rfl
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ 3) x) :=
    ⟨g.toRiemannianMetric⟩
  have hG : coordinateGram g f.toFun p y = Matrix.gram ℝ v := by
    rfl
  rw [hG]
  exact (Matrix.posDef_gram_of_linearIndependent hv).det_pos

theorem coordinateAreaDensity_pos (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (p : S) {y : Euc 2}
    (hy : y ∈ (extChartAt (𝓡∂ 2) p).target) :
    0 < coordinateAreaDensity g f.toFun p y :=
  Real.sqrt_pos.2 (coordinateGram_det_pos g f p hy)

theorem linearMapGramDensity_eq_normDet {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (d : Euc 2 →ₗ[ℝ] F) :
    Real.sqrt (Matrix.det (Matrix.gram ℝ (fun i : Fin 2 =>
      d (EuclideanSpace.single i 1)))) = (d.normDet : ℝ) := by
  have h := d.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin 2) ℝ)
  simp only [EuclideanSpace.basisFun_apply] at h
  rw [← h]
  exact Real.sqrt_sq (by exact d.normDet_nonneg)

theorem linearMapGramDensity_comp {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (d : Euc 2 →ₗ[ℝ] F) (A : Euc 2 →ₗ[ℝ] Euc 2) :
    Real.sqrt (Matrix.det (Matrix.gram ℝ (fun i : Fin 2 =>
      d (A (EuclideanSpace.single i 1))))) =
    |A.det| * Real.sqrt (Matrix.det (Matrix.gram ℝ (fun i : Fin 2 =>
      d (EuclideanSpace.single i 1)))) := by
  change Real.sqrt (Matrix.det (Matrix.gram ℝ (fun i : Fin 2 =>
    (d ∘ₗ A) (EuclideanSpace.single i 1)))) = _
  rw [linearMapGramDensity_eq_normDet, linearMapGramDensity_eq_normDet,
    LinearMap.normDet_comp_of_finrank_eq A d rfl,
    LinearMap.normDet_eq_abs_det, mul_comm]

theorem coordinateAreaDensity_eq_normDet (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (f : S → M) (p : S) (y : Euc 2) :
    coordinateAreaDensity g f p y =
      letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ 3) x) :=
        ⟨g.toRiemannianMetric⟩
      ((mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) (f ∘ (extChartAt (𝓡∂ 2) p).symm)
        (extChartAt (𝓡∂ 2) p).target y).toLinearMap.comp
          (tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm.toLinearMap).normDet := by
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ 3) x) :=
    ⟨g.toRiemannianMetric⟩
  exact linearMapGramDensity_eq_normDet
    (F := TangentSpace (𝓡∂ 3) (f ((extChartAt (𝓡∂ 2) p).symm y)))
    ((mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) (f ∘ (extChartAt (𝓡∂ 2) p).symm)
        (extChartAt (𝓡∂ 2) p).target y).toLinearMap.comp
      (tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm.toLinearMap)

end
end SeifertSurfaces.MetricFoundations
