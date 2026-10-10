import NativePlaneRotation
import NativeBallGreenDirection

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def ballRotationEquiv (x : E2) (R : E2 ≃ₗᵢ[ℝ] E2) : E2 ≃ᵐ E2 :=
  R.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.addLeft x)

@[simp] theorem ballRotationEquiv_apply (x : E2) (R : E2 ≃ₗᵢ[ℝ] E2) (z : E2) :
    ballRotationEquiv x R z = x + R z := rfl

@[simp] theorem ballRotationEquiv_symm_apply (x : E2) (R : E2 ≃ₗᵢ[ℝ] E2) (z : E2) :
    (ballRotationEquiv x R).symm z = R.symm (z - x) := by
  change R.symm (-x + z) = _
  congr 1
  abel

theorem ballRotationEquiv_preserves (x : E2) (R : E2 ≃ₗᵢ[ℝ] E2) (q : ℝ) :
    MeasurePreserving (ballRotationEquiv x R)
      (volume.restrict (Metric.ball (0 : E2) q)) (volume.restrict (Metric.ball x q)) := by
  have he : MeasurePreserving (ballRotationEquiv x R) volume volume :=
    (measurePreserving_add_left volume x).comp R.measurePreserving
  have hpre : ballRotationEquiv x R ⁻¹' Metric.ball x q = Metric.ball (0 : E2) q := by
    ext z
    simp [Metric.mem_ball, dist_eq_norm]
  have hh := he.restrict_preimage (s := Metric.ball x q) measurableSet_ball
  rw [hpre] at hh
  exact hh

theorem rotated_scalar_cone (x : E2) (R : E2 ≃ₗᵢ[ℝ] E2) (q k : ℝ) (hq : 0 < q)
    (g : ℝ → ℝ) (hg : Periodic g (2 * Real.pi)) (hgc : Continuous g)
    (hga : AbsolutelyContinuousOnInterval g (-Real.pi) Real.pi)
    (hgd : MemLp (deriv g) 2 (volume.restrict (Icc (-Real.pi) Real.pi))) :
    let h : E2 → ℝ := fun z => scalarCone 0 q k g (R.symm (z - x))
    let d : E2 → E2 := fun z => R (scalarConeGrad 0 q g (R.symm (z - x)))
    MemLp h 2 (volume.restrict (Metric.ball x q)) ∧
    MemLp d 2 (volume.restrict (Metric.ball x q)) ∧
    (∫ z in Metric.ball x q, ‖d z‖ ^ 2) =
      (1 / 2 : ℝ) * ∫ t in Icc (-Real.pi) Real.pi, (g t ^ 2 + deriv g t ^ 2) ∧
    (∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → ∀ j : Fin 2,
      IntegrableOn (fun z => h z * fderiv ℝ psi z (coordinateVector 2 j) + d z j * psi z)
        (Metric.ball x q) ∧
      IntegrableOn (fun t => (k + g t) * psi (x + q • R (unitCircleParameter t)) *
        R (unitCircleParameter t) j) (Icc (-Real.pi) Real.pi) ∧
      (∫ z in Metric.ball x q, h z * fderiv ℝ psi z (coordinateVector 2 j) + d z j * psi z) =
        q * ∫ t in Icc (-Real.pi) Real.pi,
          (k + g t) * psi (x + q • R (unitCircleParameter t)) * R (unitCircleParameter t) j) := by
  dsimp only
  let e := ballRotationEquiv x R
  have he := ballRotationEquiv_preserves x R q
  have hei := he.symm e
  have hf := scalarCone_memLp 0 q k hq g hg hgc
  have hd := scalarConeGrad_energy 0 q hq g hg hgc hgd
  have hfm : MemLp (fun z => scalarCone 0 q k g (R.symm (z - x))) 2
      (volume.restrict (Metric.ball x q)) := by
    simpa only [e, Function.comp_def, ballRotationEquiv_symm_apply] using hf.comp_measurePreserving hei
  have hdm : MemLp (fun z => R (scalarConeGrad 0 q g (R.symm (z - x)))) 2
      (volume.restrict (Metric.ball x q)) := by
    have hdp : MemLp (fun z => scalarConeGrad 0 q g (R.symm (z - x))) 2
        (volume.restrict (Metric.ball x q)) := by
      simpa only [e, Function.comp_def, ballRotationEquiv_symm_apply] using hd.1.comp_measurePreserving hei
    exact hdp.continuousLinearMap_comp R.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨hfm, hdm, ?_, ?_⟩
  · have hi := he.integral_comp' (fun z => ‖R (scalarConeGrad 0 q g (R.symm (z - x)))‖ ^ 2)
    simpa only [ballRotationEquiv_apply, add_sub_cancel_left, R.symm_apply_apply, R.norm_map] using
      hi.symm.trans (by simpa only [ballRotationEquiv_apply, add_sub_cancel_left,
        R.symm_apply_apply, R.norm_map] using hd.2)
  · intro psi hs j
    let Ψ : E2 → ℝ := fun z => psi (x + R z)
    have hΨ : ContDiff ℝ ∞ Ψ :=
      hs.comp (contDiff_const.add R.toContinuousLinearEquiv.contDiff)
    have hchain (z : E2) : fderiv ℝ Ψ z (R.symm (coordinateVector 2 j)) =
        fderiv ℝ psi (x + R z) (coordinateVector 2 j) := by
      have ha : HasFDerivAt (fun y : E2 => x + R y)
          R.toContinuousLinearEquiv.toContinuousLinearMap z :=
        R.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.const_add x
      have hb := (hs.differentiable (by simp) (x + R z)).hasFDerivAt.comp z ha
      change fderiv ℝ (psi ∘ (fun y : E2 => x + R y)) z (R.symm (coordinateVector 2 j)) = _
      rw [hb.fderiv]
      simp
    have hinner (v : E2) : inner ℝ v (R.symm (coordinateVector 2 j)) = R v j := by
      rw [← R.inner_map_eq_flip, inner_coordinateVector]
    have hgr := scalarCone_green_direction 0 q k hq g hg hgc hga Ψ hΨ
      (R.symm (coordinateVector 2 j))
    simp only [zero_add, hchain, hinner] at hgr
    have hb (t : ℝ) : Ψ (q • unitCircleParameter t) =
        psi (x + q • R (unitCircleParameter t)) := by dsimp [Ψ]; rw [map_smul]
    simp only [hb] at hgr
    have heq : (fun z => scalarCone 0 q k g (R.symm (z - x)) *
        fderiv ℝ psi z (coordinateVector 2 j) + R (scalarConeGrad 0 q g (R.symm (z - x))) j * psi z) ∘ e =
        (fun z => scalarCone 0 q k g z * fderiv ℝ psi (x + R z) (coordinateVector 2 j) +
          R (scalarConeGrad 0 q g z) j * Ψ z) := by
      funext z
      simp only [e, Function.comp_def, ballRotationEquiv_apply, add_sub_cancel_left, R.symm_apply_apply, Ψ]
    refine ⟨(he.integrable_comp_emb e.measurableEmbedding).mp (by rw [heq]; exact hgr.1), hgr.2.1, ?_⟩
    have hi := he.integral_comp' (fun z => scalarCone 0 q k g (R.symm (z - x)) *
        fderiv ℝ psi z (coordinateVector 2 j) + R (scalarConeGrad 0 q g (R.symm (z - x))) j * psi z)
    change (∫ z in Metric.ball (0 : E2) q, ((fun z => scalarCone 0 q k g (R.symm (z - x)) *
        fderiv ℝ psi z (coordinateVector 2 j) + R (scalarConeGrad 0 q g (R.symm (z - x))) j * psi z) ∘ e) z) = _ at hi
    rw [heq] at hi
    exact hi.symm.trans hgr.2.2

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
