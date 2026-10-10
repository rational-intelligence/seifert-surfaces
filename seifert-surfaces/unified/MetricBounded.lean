import Mathlib

noncomputable section
open scoped Topology

namespace SeifertSurfaces.AppendixC

lemma positive_bilinear_unitBall_bounded
    {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [FiniteDimensional ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hs : ∀ v w, B v w = B w v)
    (hp : ∀ v, v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v : V | B v v < 1} := by
  let W := ULift.{0} V
  let coreW : InnerProductSpace.Core ℝ W :=
    { inner := fun v w => B v.down w.down
      conj_inner_symm := by intro v w; exact hs w.down v.down
      re_inner_nonneg := by
        intro v
        by_cases hv : v.down = 0
        · simp [hv]
        · exact (hp v.down hv).le
      add_left := by
        intro v w x
        change B (v.down + w.down) x.down = _
        simp
      smul_left := by
        intro v w c
        change B (c • v.down) w.down = _
        simp
      definite := by
        intro v hv
        apply ULift.ext
        change v.down = 0
        by_contra h
        exact (hp v.down h).ne' hv }
  letI : Module ℝ W := inferInstance
  letI : FiniteDimensional ℝ W := inferInstance
  letI : PreInnerProductSpace.Core ℝ W := coreW.toCore
  letI : NormedAddCommGroup W := coreW.toNormedAddCommGroup
  letI : SeminormedAddCommGroup W := coreW.toNormedAddCommGroup.toSeminormedAddCommGroup
  letI : Norm W := coreW.toNormedAddCommGroup.toNorm
  letI : Dist W := coreW.toNormedAddCommGroup.toMetricSpace.toDist
  letI : MetricSpace W := coreW.toNormedAddCommGroup.toMetricSpace
  letI : PseudoMetricSpace W := coreW.toNormedAddCommGroup.toMetricSpace.toPseudoMetricSpace
  letI : UniformSpace W := coreW.toNormedAddCommGroup.toMetricSpace.toUniformSpace
  letI : TopologicalSpace W :=
    coreW.toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedSpace ℝ W := InnerProductSpace.Core.toNormedSpace
  letI : InnerProductSpace ℝ W := InnerProductSpace.ofCore coreW.toCore
  let e : W →ₗ[ℝ] V := ULift.moduleEquiv.toLinearMap
  have he : Continuous e := e.continuous_of_finiteDimensional
  have hb : Bornology.IsVonNBounded ℝ {w : W | B w.down w.down < 1} := by
    apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
    refine ⟨1, ?_⟩
    intro w hw
    have hn : ‖w‖ * ‖w‖ = B w.down w.down :=
      (InnerProductSpace.Core.inner_self_eq_norm_mul_norm w).symm
    change B w.down w.down < 1 at hw
    nlinarith [norm_nonneg w]
  convert hb.image (⟨e, he⟩ : W →L[ℝ] V) using 1
  ext v
  simp [e, W]

end SeifertSurfaces.AppendixC
