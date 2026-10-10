import InitialLocalCapGreen_v457
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

private theorem ae_simultaneous_continuous_tests_v457
    {X J : Type*} [MeasurableSpace X] [TopologicalSpace J] [SecondCountableTopology J]
    (mu : Measure X) (S : Set J) (L : X → J → ℝ)
    (hc : ∀ᵐ x ∂mu,Continuous (L x))
    (htests : ∀ u∈S,∀ᵐ x ∂mu,L x u=0) :
    ∀ᵐ x ∂mu,∀ u∈S,L x u=0 := by
  obtain ⟨T,hTc,hTS,hST⟩ := TopologicalSpace.exists_countable_dense_subset S
  have hzero : ∀ᵐ x ∂mu,∀ u∈T,L x u=0 := (ae_ball_iff hTc).mpr
    (fun u hu=>htests u (hTS hu))
  filter_upwards [hc,hzero] with x hcx hzx
  have hclosed : IsClosed {u | L x u=0} := isClosed_eq hcx continuous_const
  intro u hu
  apply hclosed.closure_subset_iff.mpr hzx
  exact hST hu

private theorem weighted_continuous_map_integrable_v457
    {X K : Type*} [MeasurableSpace X] [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    (mu : Measure X) (tau : X → K) (htau : Measurable tau)
    (g : X → ℝ) (hg : Integrable g mu) (u : C(K,ℝ)) :
    Integrable (fun x=>g x*u (tau x)) mu :=
  hg.mul_bdd (u.continuous.measurable.comp htau |>.aestronglyMeasurable)
    (Eventually.of_forall fun x=>u.norm_coe_le_norm (tau x))

private theorem weighted_continuous_map_integral_v457
    {X K : Type*} [MeasurableSpace X] [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    (mu : Measure X) (tau : X → K) (htau : Measurable tau)
    (g : X → ℝ) (hg : Integrable g mu) :
    Continuous (fun u:C(K,ℝ)=>∫ x,g x*u (tau x) ∂mu) := by
  have hi (u : C(K,ℝ)) : Integrable (fun x=>g x*u (tau x)) mu :=
    hg.mul_bdd (u.continuous.measurable.comp htau |>.aestronglyMeasurable)
      (Eventually.of_forall fun x=>u.norm_coe_le_norm (tau x))
  let c : ℝ≥0 := ⟨∫ x,‖g x‖ ∂mu,integral_nonneg fun _=>norm_nonneg _⟩
  apply LipschitzWith.continuous (K:=c)
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro u v
  rw [dist_eq_norm,← integral_sub (hi u) (hi v)]
  have he : (fun x=>g x*u (tau x)-g x*v (tau x))=
      (fun x=>g x*(u-v) (tau x)) := by
    funext x
    simp only [ContinuousMap.sub_apply]
    ring
  rw [he]
  calc
    ‖∫ x,g x*(u-v) (tau x) ∂mu‖ ≤ ∫ x,‖g x*(u-v) (tau x)‖ ∂mu := norm_integral_le_integral_norm _
    _ ≤ ∫ x,‖g x‖*‖u-v‖ ∂mu := by
      apply integral_mono (hi (u-v)).norm (hg.norm.mul_const ‖u-v‖)
      intro x
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((u-v).norm_coe_le_norm (tau x)) (norm_nonneg _)
    _ = (c:ℝ)*dist u v := by rw [integral_mul_const,dist_eq_norm];rfl

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
