import A5HalfspaceImmersionCancellation

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u v

theorem smooth_halfspace_map_coordinate_extension
    {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    (f : EuclideanHalfSpace 2 → M) (V : Set (EuclideanHalfSpace 2))
    (hV : IsOpen V) (hf : ContMDiffOn (𝓡∂ 2) (𝓡∂ 3) ∞ f V)
    (z : EuclideanHalfSpace 2) (hz : z ∈ V) :
    ∃ U : Set (Euc 2), IsOpen U ∧ (𝓡∂ 2) z ∈ U ∧
      ContDiffOn ℝ ∞ (extChartAt (𝓡∂ 3) (f z) ∘ f ∘ (𝓡∂ 2).symm)
        (U ∩ range (𝓡∂ 2)) := by
  let d := extChartAt (𝓡∂ 3) (f z)
  let W := V ∩ f ⁻¹' d.source
  have hW : IsOpen W := hf.continuousOn.isOpen_inter_preimage hV (isOpen_extChartAt_source _)
  have hzW : z ∈ W := ⟨hz, mem_extChartAt_source (f z)⟩
  let U := (𝓡∂ 2).symm ⁻¹' W
  have hzU : (𝓡∂ 2) z ∈ U := by
    simpa only [U, mem_preimage, ModelWithCorners.left_inv] using hzW
  refine ⟨U, hW.preimage (𝓡∂ 2).continuous_symm, hzU, ?_⟩
  have hs : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ, Euc 3) ∞ (d ∘ f) W :=
    (contMDiffOn_iff_target.mp hf).2 (f z)
  exact (hs.comp ((𝓡∂ 2).contMDiffOn_symm.mono inter_subset_right)
    (fun y hy => hy.1)).contDiffOn

/-- Smooth immersion cancellation into a half-space chart works for any
source model, including a quadrant prism. Only continuity of the lift is
required; no source derivative or boundary transversality is assumed. -/
theorem contMDiffAt_lift_through_regular_halfspace_map
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    {H₁ : Type*} [TopologicalSpace H₁] (I : ModelWithCorners ℝ E₁ H₁)
    {X : Type u} [TopologicalSpace X] [ChartedSpace H₁ X]
    {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    (f : EuclideanHalfSpace 2 → M) (V : Set (EuclideanHalfSpace 2))
    (hV : IsOpen V) (hf : ContMDiffOn (𝓡∂ 2) (𝓡∂ 3) ∞ f V)
    (k : X → EuclideanHalfSpace 2) (x : X) (hk : ContinuousAt k x) (hkV : k x ∈ V)
    (hinj : Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) f (k x)))
    (n : ℕ∞ω) (hn : n ≤ ∞) (hcomp : ContMDiffAt I (𝓡∂ 3) n (f ∘ k) x) :
    ContMDiffAt I (𝓡∂ 2) n k x := by
  let g : Euc 2 → Euc 3 := extChartAt (𝓡∂ 3) (f (k x)) ∘ f ∘ (𝓡∂ 2).symm
  let q : E₁ → Euc 2 := (𝓡∂ 2) ∘ k ∘ (extChartAt I x).symm
  let y := extChartAt I x x
  have hqy : q y = (𝓡∂ 2) (k x) := by
    dsimp only [q, y, Function.comp_apply]
    rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
  obtain ⟨U, hU, hzU, hg⟩ := smooth_halfspace_map_coordinate_extension f V hV hf (k x) hkV
  have hfd := ((hf.contMDiffAt (hV.mem_nhds hkV)).mdifferentiableAt (by simp)).hasMFDerivAt.2
  change HasFDerivWithinAt g
    ((tangentSpaceCastModel (𝓡∂ 3) (f (k x))).toContinuousLinearMap.comp
      ((mfderiv (𝓡∂ 2) (𝓡∂ 3) f (k x)).comp
        (tangentSpaceCastModel (𝓡∂ 2) (k x)).symm.toContinuousLinearMap))
    (range (𝓡∂ 2)) ((𝓡∂ 2) (k x)) at hfd
  have hi : Function.Injective (fderivWithin ℝ g (range (𝓡∂ 2)) ((𝓡∂ 2) (k x))) := by
    rw [hfd.fderivWithin ((𝓡∂ 2).uniqueDiffOn _ (mem_range_self _))]
    exact (tangentSpaceCastModel (𝓡∂ 3) (f (k x))).injective.comp
      (hinj.comp (tangentSpaceCastModel (𝓡∂ 2) (k x)).symm.injective)
  have hq : ContinuousAt q y := by
    apply (𝓡∂ 2).continuousAt.comp
    have hk' : ContinuousAt k ((extChartAt I x).symm y) := by
      dsimp only [y]
      rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
      exact hk
    exact hk'.comp (continuousAt_extChartAt_symm x)
  have hgq : g ∘ q = extChartAt (𝓡∂ 3) ((f ∘ k) x) ∘ (f ∘ k) ∘ (extChartAt I x).symm := by
    funext z
    simp only [g, q, Function.comp_apply, ModelWithCorners.left_inv]
  have hqsm : ContDiffWithinAt ℝ n q (range I) y := by
    apply halfspace_immersion_cancel_on_relative_source g q (range I) y
      (mem_extChartAt_target x |> extChartAt_target_subset_range x) U hU
    · rwa [hqy]
    · rw [hqy]; exact mem_range_self _
    · exact hg
    · rwa [hqy]
    · exact hq.continuousWithinAt
    · exact Filter.Eventually.of_forall (fun z => mem_range_self _)
    · exact hn
    · rw [hgq]
      exact (contMDiffAt_iff.mp hcomp).2
  apply contMDiffAt_iff.mpr
  refine ⟨hk, ?_⟩
  simpa [q, y, Function.comp_def] using hqsm

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
