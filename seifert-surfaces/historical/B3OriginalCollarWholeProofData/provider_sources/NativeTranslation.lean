import NativeBoundaryRestriction
set_option maxHeartbeats 6000000
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open SeifertSurfaces.AppendixACoordinates BoundaryPotentialLower

lemma native_h1_translation (U : Set E2) (hU : MeasurableSet U) (c : E2)
    (v : E2 → ℝ) (dv : E2 → E2) (hu : H1On U v dv) :
    H1On ((fun z : E2 => z+c) ⁻¹' U) (fun z => v (z+c)) (fun z => dv (z+c)) := by
  let W := (fun z : E2 => z+c) ⁻¹' U
  have hT : MeasurePreserving (fun z : E2 => z+c) (volume.restrict W) (volume.restrict U) :=
    (measurePreserving_add_right volume c).restrict_preimage hU
  have hEmb : MeasurableEmbedding (fun z : E2 => z+c) := (Homeomorph.addRight c).measurableEmbedding
  have hInt (f : E2 → ℝ) : (∫ z in W, f (z+c)) = ∫ y in U, f y := hT.integral_comp hEmb f
  have hv := hu.2.1.comp_measurePreserving hT
  have hdv := hu.2.2.comp_measurePreserving hT
  refine ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hv.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hdv.locallyIntegrable (by norm_num)),?_⟩,hv,hdv⟩
  intro phi hp hc ht i
  let psi := fun y : E2 => phi (y+(-c))
  have hps : ContDiff ℝ ∞ psi := hp.comp (contDiff_id.add contDiff_const)
  have hpc : HasCompactSupport psi := hc.comp_homeomorph (Homeomorph.addRight (-c))
  have hpt : tsupport psi ⊆ U := by
    intro y hy
    have hh := ht (tsupport_comp_subset_preimage phi (continuous_id.add continuous_const) hy)
    change y+(-c)+c ∈ U at hh
    simpa only [neg_add_cancel_right] using hh
  have heq := hu.1.2.2 psi hps hpc hpt i
  rw [← hInt (fun y => v y*fderiv ℝ psi y (coordinateVector 2 i)),← hInt (fun y => dv y i*psi y)] at heq
  simpa only [psi,fderiv_comp_add_right,add_neg_cancel_right] using heq

lemma planar_gradient_translation (phi : E2 → ℝ) (c z : E2) :
    planarGradient (fun y => phi (y+c)) z = planarGradient phi (z+c) := by
  unfold planarGradient
  rw [fderiv_comp_add_right]

lemma native_weak_divergence_translation (U : Set E2) (hU : MeasurableSet U) (c : E2)
    (a : E2 → Mat2) (e : E2 → E2) (v : E2 → ℝ) (dv : E2 → E2)
    (hw : WeakDivergenceWithData U a e (fun _ => 0) v dv) :
    WeakDivergenceWithData ((fun z : E2 => z+c) ⁻¹' U)
      (fun z => a (z+c)) (fun z => e (z+c)) (fun _ => 0) (fun z => v (z+c)) (fun z => dv (z+c)) := by
  refine ⟨native_h1_translation U hU c v dv hw.1,?_⟩
  intro phi hp hc ht
  let W := (fun z : E2 => z+c) ⁻¹' U
  let psi := fun y : E2 => phi (y+(-c))
  have hps : ContDiff ℝ ∞ psi := hp.comp (contDiff_id.add contDiff_const)
  have hpc : HasCompactSupport psi := hc.comp_homeomorph (Homeomorph.addRight (-c))
  have hpt : tsupport psi ⊆ U := by
    intro y hy
    have hh := ht (tsupport_comp_subset_preimage phi (continuous_id.add continuous_const) hy)
    change y+(-c)+c ∈ U at hh
    simpa only [neg_add_cancel_right] using hh
  have hg (z : E2) : planarGradient psi (z+c) = planarGradient phi z := by
    rw [planar_gradient_translation]
    simp only [add_neg_cancel_right]
  obtain ⟨hi1,hi2,heq⟩ := hw.2 psi hps hpc hpt
  have hT : MeasurePreserving (fun z : E2 => z+c) (volume.restrict W) (volume.restrict U) :=
    (measurePreserving_add_right volume c).restrict_preimage hU
  have hEmb : MeasurableEmbedding (fun z : E2 => z+c) := (Homeomorph.addRight c).measurableEmbedding
  have hInt (f : E2 → ℝ) : (∫ z in W, f (z+c)) = ∫ y in U, f y := hT.integral_comp hEmb f
  have hi1' := (hT.integrable_comp_emb hEmb).mpr hi1
  have hi2' := (hT.integrable_comp_emb hEmb).mpr hi2
  dsimp only [Function.comp_def] at hi1' hi2'
  simp_rw [hg] at hi1'
  simp_rw [hg,zero_mul,add_zero] at hi2'
  refine ⟨hi1',by simpa only [W,IntegrableOn,zero_mul,add_zero] using hi2',?_⟩
  rw [← hInt (fun y => inner ℝ (matrixAction (a y) (dv y)) (planarGradient psi y)),
    ← hInt (fun y => inner ℝ (e y) (planarGradient psi y)+(0:ℝ)*psi y)] at heq
  simpa only [hg,zero_mul,add_zero] using heq

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
