import A5NativeMetricGraphOperator
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N]

/-- Construct the exact metric graph, its splitting, height, and closed
double-radius control from a C1 section of a separating linear projection.
The native graph formula agrees with the original section throughout that
closed double-radius disc. -/
theorem native_metric_graph_of_C1_section
    (h : AmbientMetric N) (c : SmoothAmbientChart N)
    (U : Set E2) (hU : IsOpen U) (a : E2) (ha : a ∈ U)
    (f : E2 → E3) (hf : ContDiffOn ℝ 1 f U)
    (hchart : MapsTo f U c.chart.target)
    (P : E3 →L[ℝ] E2) (height : E3 →L[ℝ] ℝ)
    (hsep : Function.Injective (fun z => (P z, height z)))
    (hsection : ∀ z ∈ U, P (f z) = z) :
    ∃ G : NativeMetricGraph h,
      G.coordinates = c ∧ G.origin = f a ∧
      (∀ v, P (G.plane v) = v ∧ height (G.plane v) = 0) ∧
      P G.normal = 0 ∧ height G.normal = 1 ∧
      G.height 0 = 0 ∧
      ∀ z ∈ Metric.closedBall 0 (2 * G.radius),
        a + z ∈ U ∧ graphMap G.origin G.plane G.normal G.height z = f (a + z) := by
  let A : E3 →L[ℝ] E2 × ℝ := P.prod height
  have hA : Function.Bijective A := by
    refine ⟨hsep, ?_⟩
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := A.toLinearMap) (by simp [E2, E3, Module.finrank_prod])).mp
    exact hsep
  let e : E3 ≃L[ℝ] E2 × ℝ := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hA.1) (LinearMap.range_eq_top.mpr hA.2)
  let L : E2 →L[ℝ] E3 := e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E2 ℝ)
  let n : E3 := e.symm (0, 1)
  let u : E2 → ℝ := fun z => height (f (a + z) - f a)
  have hsplit (z : E2 × ℝ) : L z.1 + z.2 • n = e.symm z := by
    change e.symm (z.1, 0) + z.2 • e.symm (0, 1) = e.symm z
    rw [← map_smul, ← map_add]
    congr 1
    ext <;> simp
  have hLP (v : E2) : P (L v) = v ∧ height (L v) = 0 := by
    have he := e.apply_symm_apply (v, 0)
    change (P (L v), height (L v)) = (v, 0) at he
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  have hn : P n = 0 ∧ height n = 1 := by
    have he := e.apply_symm_apply (0, 1)
    change (P n, height n) = (0, 1) at he
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  have hgraph (z : E2) (hz : a + z ∈ U) : graphMap (f a) L n u z = f (a + z) := by
    have he : e (f (a + z) - f a) = (z, u z) := by
      apply Prod.ext
      · change P (f (a + z) - f a) = z
        rw [map_sub, hsection _ hz, hsection _ ha]
        abel
      · rfl
    have hi : L z + u z • n = f (a + z) - f a := by
      rw [hsplit (z, u z), ← he, e.symm_apply_apply]
    change f a + L z + u z • n = f (a + z)
    rw [add_assoc, hi]
    abel
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let r := δ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hball : MapsTo (fun z : E2 => a + z) (Metric.closedBall 0 (2 * r)) U := by
    intro z hz
    apply hδU
    have hh : ‖z‖ ≤ 2 * r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    change dist (a + z) a < δ
    rw [dist_eq_norm]
    have he : a + z - a = z := by abel
    rw [he]
    dsimp [r] at hh
    linarith
  have hu : ContDiffOn ℝ 1 u (Metric.closedBall 0 (2 * r)) :=
    height.contDiff.comp_contDiffOn
      ((hf.comp (contDiffOn_const.add contDiffOn_id) hball).sub contDiffOn_const)
  let G : NativeMetricGraph h := {
    coordinates := c
    origin := f a
    plane := L
    normal := n
    splitting := by
      have he : (fun z : E2 × ℝ => L z.1 + z.2 • n) = e.symm := funext hsplit
      rw [he]
      exact e.symm.bijective
    height := u
    radius := r
    radius_pos := hr
    height_C1 := hu
    graph_in_chart := fun z hz => (hgraph z (hball hz)).symm ▸ hchart (hball hz)
  }
  refine ⟨G, rfl, rfl, hLP, hn.1, hn.2, ?_, ?_⟩
  · change height (f (a + 0) - f a) = 0
    simp
  · intro z hz
    exact ⟨hball hz, hgraph z (hball hz)⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
