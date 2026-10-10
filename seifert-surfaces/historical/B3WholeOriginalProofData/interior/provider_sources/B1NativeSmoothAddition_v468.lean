import B1NativeOffsetTruncation_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Addition of a smooth L2 datum preserves the literal supplied native weak gradient. -/
theorem native_h1_add_smooth_v468 (U : Set E2) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On U u du) (w : E2 → ℝ) (hw : ContDiff ℝ ∞ w)
    (hwLp : MemLp w 2 (volume.restrict U))
    (hdwLp : MemLp (planarGradient w) 2 (volume.restrict U)) :
    H1On U (fun x => u x + w x) (fun x => du x + planarGradient w x) := by
  have hweak := smooth_native_weak_gradient_v468 U w hw
  have hv := hu.2.1.add hwLp
  have hd := hu.2.2.add hdwLp
  refine ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hv.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hd.locallyIntegrable (by norm_num)),?_⟩,hv,hd⟩
  intro φ hs hc ht i
  have hφ : MemLp φ 2 (volume.restrict U) :=
    (hs.continuous.memLp_of_hasCompactSupport (μ := volume) hc).restrict U
  have hdφ : MemLp (fun x => fderiv ℝ φ x (coordinateVector 2 i)) 2 (volume.restrict U) :=
    (((hs.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (μ := volume) (hc.fderiv_apply ℝ (coordinateVector 2 i))).restrict U
  have hiu := hu.2.1.integrable_mul hdφ
  have hiw := hwLp.integrable_mul hdφ
  have hidu := (hu.2.2.eval_piLp i).integrable_mul hφ
  have hidw := (hdwLp.eval_piLp i).integrable_mul hφ
  have hleft := integral_add hiu hiw
  have hright := integral_add hidu hidw
  simp only [Pi.add_apply,Pi.mul_apply] at hleft hright
  simp only [add_mul,PiLp.add_apply]
  rw [hleft,hright,hu.1.2.2 φ hs hc ht i,hweak.2.2 φ hs hc ht i]
  ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency
