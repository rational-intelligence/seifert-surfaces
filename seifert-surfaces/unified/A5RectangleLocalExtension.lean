import DiagramExtensionRemaining

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.LongitudeProducers
open SeifertSurfaces.LongitudeProducers.DiagramRemainingHelpers

/-- The certified rectangle extension applies to genuinely local C1 data at
any point of the closed rectangle, including corners. -/
theorem C1_rectangle_local_extension
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (a b : Euc 2) (hab : ∀ i, a i < b i) (F : Euc 2 → V)
    (x : Euc 2) (hx : x ∈ euclideanRectangle a b)
    (hF : ContDiffWithinAt ℝ 1 F (euclideanRectangle a b) x) :
    ∃ g : Euc 2 → V, ContDiffAt ℝ 1 g x ∧
      g =ᶠ[𝓝[euclideanRectangle a b] x] F ∧
      fderiv ℝ g x = fderivWithin ℝ F (euclideanRectangle a b) x := by
  obtain ⟨U, hU, hxU, hFU⟩ := hF.contDiffOn' le_rfl (by simp)
  rw [insert_eq_of_mem hx] at hFU
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hxU
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let c : Euc 2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => max (a i) (x i - δ))
  let d : Euc 2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => min (b i) (x i + δ))
  have hc (i : Fin 2) : c i = max (a i) (x i - δ) := rfl
  have hd (i : Fin 2) : d i = min (b i) (x i + δ) := rfl
  have hcd : ∀ i, c i < d i := by
    intro i
    rw [hc, hd, max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨hab i, by linarith [(hx i).1]⟩,
      ⟨by linarith [(hx i).2], by linarith⟩⟩
  have hxT : x ∈ euclideanRectangle c d := by
    intro i
    rw [hc, hd]
    exact ⟨max_le (hx i).1 (by linarith), le_min (hx i).2 (by linarith)⟩
  have hsub : euclideanRectangle c d ⊆ euclideanRectangle a b ∩ U := by
    intro y hy
    have hys : y ∈ euclideanRectangle a b := by
      intro i
      exact ⟨(le_max_left _ _).trans (hy i).1, (hy i).2.trans (min_le_left _ _)⟩
    refine ⟨hys, hεU ?_⟩
    have hb (i : Fin 2) : |(y - x) i| ≤ δ := by
      rw [abs_le]
      have hl := (le_max_right (a i) (x i - δ)).trans (hy i).1
      have hu := (hy i).2.trans (min_le_right (b i) (x i + δ))
      change -δ ≤ y i - x i ∧ y i - x i ≤ δ
      constructor <;> linarith
    have hsq : ‖y - x‖ ^ 2 ≤ 2 * δ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [Fin.sum_univ_two]
      have h0 := sq_le_sq₀ (abs_nonneg ((y - x) 0)) hδ.le |>.mpr (hb 0)
      have h1 := sq_le_sq₀ (abs_nonneg ((y - x) 1)) hδ.le |>.mpr (hb 1)
      rw [sq_abs] at h0 h1
      linarith
    rw [Metric.mem_ball, dist_eq_norm]
    dsimp [δ] at hsq
    nlinarith [norm_nonneg (y - x)]
  obtain ⟨e⟩ := finite_c1_closed_rectangle_extension c d hcd F (hFU.mono hsub)
  have he : ContDiffAt ℝ 1 e.map x :=
    (e.c1 x (e.rectangle_inside hxT)).contDiffAt
      (e.neighborhood_open.mem_nhds (e.rectangle_inside hxT))
  let W : Set (Euc 2) := ⋂ i : Fin 2, {y | x i - δ < y i ∧ y i < x i + δ}
  have hW : IsOpen W := isOpen_iInter_of_finite fun i =>
    (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).inter
      (isOpen_lt (EuclideanSpace.proj i).continuous continuous_const)
  have hxW : x ∈ W := mem_iInter.mpr (fun i => by change x i - δ < x i ∧ x i < x i + δ; constructor <;> linarith)
  have heq : e.map =ᶠ[𝓝[euclideanRectangle a b] x] F := by
    filter_upwards [nhdsWithin_le_nhds (hW.mem_nhds hxW),
      self_mem_nhdsWithin] with y hyW hys
    apply e.values
    intro i
    have hy := mem_iInter.mp hyW i
    rw [hc, hd]
    exact ⟨max_le (hys i).1 hy.1.le, le_min (hys i).2 hy.2.le⟩
  refine ⟨e.map, he, heq, ?_⟩
  exact ((he.differentiableAt (by norm_num)).fderivWithin
    (nondegenerate_rectangle_unique_diff a b hab x hx)).symm.trans
    (heq.fderivWithin_eq (heq.self_of_nhdsWithin hx))

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
