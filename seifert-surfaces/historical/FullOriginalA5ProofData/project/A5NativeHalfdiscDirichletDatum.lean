import A5NativeHalfspaceMetricGraph
import A5NativeBoundaryMetricEquation

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
universe u

/-- A straightened native C1 section with its actual smooth boundary trace
constructs the metric graph and the precise smooth scalar Dirichlet datum.
The graph height and the boundary height agree by the separating linear
coordinates, including the translation by the actual graph origin. -/
theorem native_halfdisc_metric_graph_with_smooth_dirichlet_datum
    {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ,E3) ∞ N]
    (h : AmbientMetric N) (c : SmoothAmbientChart N)
    (ρ : ℝ) (hρ : 0 < ρ) (f : E2 → E3)
    (hf : ContDiffOn ℝ 1 f (closedHalfDisc ρ))
    (hchart : MapsTo f (closedHalfDisc ρ) c.chart.target)
    (P : E3 →L[ℝ] E2) (height : E3 →L[ℝ] ℝ)
    (hsep : Function.Injective (fun z => (P z,height z)))
    (hsection : ∀ z ∈ closedHalfDisc ρ, P (f z) = z)
    (γ : ℝ → E3) (I : Set ℝ) (hI : IsOpen I) (hI0 : (0 : ℝ) ∈ I)
    (hγ : ContDiffOn ℝ ∞ γ I)
    (htrace : ∀ z ∈ closedHalfDisc ρ, z 0 = 0 → f z = γ (z 1)) :
    ∃ G : NativeMetricGraph h, ∃ r : ℝ, ∃ g : SmoothDirichletDatum r,
      0 < r ∧ r < G.radius ∧ r < ρ ∧ G.coordinates = c ∧ G.origin = f 0 ∧
      P G.origin = 0 ∧ (∀ v, P (G.plane v) = v ∧ height (G.plane v) = 0) ∧
      P G.normal = 0 ∧ height G.normal = 1 ∧
      (∀ t, g.value t = height (γ t) - height (f 0)) ∧
      (∀ z ∈ closedHalfDisc r,
        graphMap G.origin G.plane G.normal G.height z = f z) ∧
      (∀ z ∈ flatBoundary r, G.height z = g.value (z 1)) := by
  obtain ⟨G,hGc,hGo,hGp,hGn,hGh,_,hGρ,hGf⟩ :=
    native_metric_graph_of_C1_halfspace_section h c ρ hρ f hf hchart P height hsep hsection
  obtain ⟨ε,hε,hεI⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hI0)
  let r : ℝ := min G.radius ε / 2
  have hr : 0 < r := div_pos (lt_min G.radius_pos hε) (by norm_num)
  have hrG : r < G.radius := by dsimp [r]; linarith [min_le_left G.radius ε,lt_min G.radius_pos hε]
  have hrε : r < ε := by dsimp [r]; linarith [min_le_right G.radius ε,lt_min G.radius_pos hε]
  have h2 : r ≤ 2 * G.radius := by linarith [G.radius_pos]
  have hγr : ContDiffOn ℝ ∞ (fun t => height (γ t) - height (f 0)) (Ioo (-r) r) := by
    apply ((height.contDiff.comp_contDiffOn hγ).sub contDiffOn_const).mono
    intro t ht
    apply hεI
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using (abs_lt.mpr ht).trans hrε
  let g : SmoothDirichletDatum r := ⟨fun t => height (γ t) - height (f 0),hγr⟩
  have hrρ : r < ρ := by
    let z : E2 := r • coordinateVector 2 0
    have hzn : ‖z‖ = r := by
      simp [z,norm_smul,Real.norm_of_nonneg hr.le,coordinateVector]
    have hh := hGρ z (by simpa only [Metric.mem_closedBall,dist_zero_right,hzn] using h2)
    simpa only [Metric.mem_ball,dist_zero_right,hzn] using hh
  have hGfr (z : E2) (hz : z ∈ closedHalfDisc r) :
      graphMap G.origin G.plane G.normal G.height z = f z :=
    hGf z (closedHalfDisc_mono h2 hz)
  refine ⟨G,r,g,hr,hrG,hrρ,hGc,hGo,?_,hGp,hGn,hGh,fun _ => rfl,hGfr,?_⟩
  · rw [hGo]
    exact hsection 0 ⟨Metric.mem_closedBall_self hρ.le,by simp⟩
  · intro z hz
    have hzH : z ∈ closedHalfDisc r := ⟨Metric.ball_subset_closedBall hz.1,hz.2.ge⟩
    have hh := congrArg height ((hGfr z hzH).trans (htrace z (closedHalfDisc_mono hrρ.le hzH) hz.2))
    simp only [graphMap,map_add,map_smul,(hGp z).2,hGh,smul_eq_mul,mul_one,add_zero,hGo] at hh
    exact eq_sub_of_add_eq' hh

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
