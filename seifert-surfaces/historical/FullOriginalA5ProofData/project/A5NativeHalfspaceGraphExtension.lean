import A5RectangleLocalExtension
import A5MetricGraphConstruction
import NativeBoundaryPreliminaries

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.LongitudeProducers
open SeifertSurfaces.LongitudeProducers.DiagramRemainingHelpers
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

/-- A genuine closed half-disc C1 map admits a local ambient C1 extension.
The actual values on the original relative domain are retained. -/
theorem C1_closed_halfdisc_local_extension
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : ℝ) (hρ : 0 < ρ) (f : E2 → V)
    (hf : ContDiffOn ℝ 1 f (closedHalfDisc ρ)) :
    ∃ g : E2 → V, ContDiffAt ℝ 1 g 0 ∧
      g =ᶠ[𝓝[closedHalfDisc ρ] (0 : E2)] f := by
  let δ := ρ / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let a : E2 := !₂[0,-δ]
  let b : E2 := !₂[δ,δ]
  let T := euclideanRectangle a b
  have hab : ∀ i, a i < b i := by
    intro i
    fin_cases i
    · exact hδ
    · change -δ < δ; linarith
  have hzero : (0 : E2) ∈ T := by
    intro i
    fin_cases i
    · exact ⟨le_rfl,hδ.le⟩
    · exact ⟨neg_nonpos.mpr hδ.le,hδ.le⟩
  have hsub : T ⊆ closedHalfDisc ρ := by
    intro z hz
    have hz0 : 0 ≤ z 0 ∧ z 0 ≤ δ := hz 0
    have hz1 : -δ ≤ z 1 ∧ z 1 ≤ δ := hz 1
    refine ⟨?_,hz0.1⟩
    have hsq : ‖z‖ ^ 2 = (z 0) ^ 2 + (z 1) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [Fin.sum_univ_two]
    have hb0 := sq_le_sq₀ hz0.1 hδ.le |>.mpr hz0.2
    have hb1 := sq_le_sq₀ (abs_nonneg (z 1)) hδ.le |>.mpr (abs_le.mpr hz1)
    rw [sq_abs] at hb1
    rw [Metric.mem_closedBall,dist_zero_right]
    dsimp [δ] at hb0 hb1
    nlinarith [norm_nonneg z]
  obtain ⟨g,hg,he,_⟩ := C1_rectangle_local_extension a b hab f 0 hzero
    ((hf 0 (hsub hzero)).mono hsub)
  have hnear : ∀ᶠ z in 𝓝[closedHalfDisc ρ] (0 : E2), z ∈ T := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : E2) hδ),
      self_mem_nhdsWithin] with z hz hzS
    have hn : ‖z‖ < δ := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    have hb (i : Fin 2) : |z i| < δ := (PiLp.norm_apply_le z i).trans_lt hn
    intro i
    fin_cases i
    · exact ⟨hzS.2,(abs_lt.mp (hb 0)).2.le⟩
    · exact ⟨(abs_lt.mp (hb 1)).1.le,(abs_lt.mp (hb 1)).2.le⟩
  have ht : Tendsto id (𝓝[closedHalfDisc ρ] (0 : E2)) (𝓝[T] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds,hnear⟩
  exact ⟨g,hg,ht.eventually he⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
