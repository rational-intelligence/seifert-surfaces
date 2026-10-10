import FlatBoundaryClockProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

/-- Internal construction data for every sufficiently shortened original
clock. The scale remains free so a finite set of native pieces can share it. -/
structure SectorHalfStripTemplate (A : SectorModel) (q : ℝ → Euc 2) where
  scaleBound : ℝ
  scaleBound_pos : 0 < scaleBound
  scaleBound_lt_one : scaleBound < 1
  height : ℝ
  height_pos : 0 < height
  tangent : Euc 2
  inward : Euc 2
  tangent_unit : ‖tangent‖ = 1
  inward_unit : ‖inward‖ = 1
  orthogonal : inner ℝ tangent inward = 0
  clock : ℝ → ℝ
  clock_center : clock 0 = 0
  exact_lift : ∀ d : ℝ, 0 < d → d ≤ scaleBound → ∀ t ∈ Ioo (-1 : ℝ) 1,
    q (d * t) = q 0 + clock (d * t) • tangent
  clock_c1 : ∀ d : ℝ, 0 < d → d ≤ scaleBound →
    ContDiffOn ℝ 1 (fun t => clock (d * t)) (Ioo (-1 : ℝ) 1)
  clock_regular : ∀ d : ℝ, 0 < d → d ≤ scaleBound →
    ∀ t ∈ Ioo (-1 : ℝ) 1, deriv (fun t => clock (d * t)) t ≠ 0
  clock_embedding : ∀ d : ℝ, 0 < d → d ≤ scaleBound →
    IsEmbedding (fun t : Ioo (-1 : ℝ) 1 => clock (d * t))
  maps_to_sector : ∀ d : ℝ, 0 < d → d ≤ scaleBound →
    MapsTo (affineSeamCoordinates (q 0) tangent inward (fun t => clock (d * t)))
      (seamHalfstrip height) A.domain
  positive_interior : ∀ d : ℝ, 0 < d → d ≤ scaleBound →
    MapsTo (affineSeamCoordinates (q 0) tangent inward (fun t => clock (d * t)))
      (Ioo (-1 : ℝ) 1 ×ˢ Ioo (0 : ℝ) height) (interior A.domain)
  boundary_halfplane : ∀ d : ℝ, 0 < d → d ≤ scaleBound → ∀ t ∈ Ioo (-1 : ℝ) 1,
    ∀ᶠ z in 𝓝 (q (d * t)), z ∈ A.domain ↔ 0 ≤ inner ℝ inward (z - q (d * t))

/-- The actual regular sector boundary germ produces uniform positive
height affine halfstrips, with all clock regularity and embeddings proved. -/
theorem regular_sector_boundary_halfstrip_template
    (A : SectorModel) (q : ℝ → Euc 2) (U : Set ℝ) (hU : IsOpen U) (h0 : 0 ∈ U)
    (hq : MapsTo q U (A.domain ∩ frontier A.domain))
    (hqc : ContDiffOn ℝ 1 q U) (hqr : ∀ t ∈ U, deriv q t ≠ 0)
    (hqemb : IsEmbedding (fun t : U => q t))
    (hregular : q 0 ≠ 0 ∨ A.angle = Real.pi) :
    Nonempty (SectorHalfStripTemplate A q) := by
  obtain ⟨e, m, he, hm, hem, hmx, hside, V, hV, hVU, h0V, clock, hc0, hc, hcr, hline⟩ :=
    regular_sector_boundary_straight_clock A q U hU h0 hq hqc hqr hregular
  obtain ⟨ε, hε, hεside⟩ := Metric.mem_nhds_iff.mp hside
  have hqc0 := ((hqc 0 h0).contDiffAt (hU.mem_nhds h0)).continuousAt
  have hqnear : ∀ᶠ t in 𝓝 (0 : ℝ), q t ∈ Metric.ball (q 0) (ε / 4) :=
    hqc0.eventually (Metric.ball_mem_nhds (q 0) (by positivity))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (hV.mem_nhds h0V) hqnear)
  let η := min δ 1 / 2
  have hη : 0 < η := half_pos (lt_min hδ zero_lt_one)
  have hηδ : η < δ := by dsimp [η]; linarith [min_le_left δ 1]
  have hη1 : η < 1 := by dsimp [η]; linarith [min_le_right δ 1]
  have hsmall (d : ℝ) (hd : 0 < d) (hdη : d ≤ η) (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) :
      d * t ∈ V ∧ q (d * t) ∈ Metric.ball (q 0) (ε / 4) := by
    apply hδsub
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos hd]
    have hat : |t| < 1 := abs_lt.mpr ht
    nlinarith [mul_lt_mul_of_pos_left hat hd]
  have hclockemb : IsEmbedding (fun t : V => clock t) :=
    scalar_clock_embedding_of_straight_lift V (q 0) e clock q hc.continuousOn
      (hqemb.comp (IsEmbedding.inclusion hVU)) hline
  have hinnerq (d : ℝ) (hd : 0 < d) (hdη : d ≤ η) (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) :
      inner ℝ m (q (d * t)) = 0 := by
    have hme : inner ℝ m e = 0 := by rw [real_inner_comm]; exact hem
    rw [hline _ (hsmall d hd hdη t ht).1, inner_add_right, inner_smul_right, hmx,
      hme, mul_zero, add_zero]
  have hdist (d : ℝ) (hd : 0 < d) (hdη : d ≤ η) (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1)
      (b : ℝ) (hb : |b| < ε / 4) : q (d * t) + b • m ∈ Metric.ball (q 0) ε := by
    have hqd : dist (q (d * t)) (q 0) < ε / 4 := (hsmall d hd hdη t ht).2
    have hbd : dist (q (d * t) + b • m) (q (d * t)) = |b| := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hm, mul_one, Real.norm_eq_abs]
    exact lt_of_le_of_lt (dist_triangle _ (q (d * t)) _) (by rw [hbd]; linarith)
  have hcoord (d t b : ℝ) (hd : 0 < d) (hdη : d ≤ η) (ht : t ∈ Ioo (-1 : ℝ) 1) :
      affineSeamCoordinates (q 0) e m (fun t => clock (d * t)) (t, b) = q (d * t) + b • m := by
    unfold affineSeamCoordinates
    rw [hline _ (hsmall d hd hdη t ht).1]
  have hinner (d t b : ℝ) (hd : 0 < d) (hdη : d ≤ η) (ht : t ∈ Ioo (-1 : ℝ) 1) :
      inner ℝ m (q (d * t) + b • m) = b := by
    rw [inner_add_right, hinnerq d hd hdη t ht, inner_smul_right,
      real_inner_self_eq_norm_sq, hm, one_pow, mul_one, zero_add]
  have hposinterior (z : Euc 2) (hzB : z ∈ Metric.ball (q 0) ε) (hz : 0 < inner ℝ m z) :
      z ∈ interior A.domain := by
    let O := Metric.ball (q 0) ε ∩ {z : Euc 2 | 0 < inner ℝ m z}
    have hO : IsOpen O := Metric.isOpen_ball.inter (isOpen_lt continuous_const (innerSL ℝ m).continuous)
    have hOS : O ⊆ A.domain := fun y hy => (hεside hy.1).mpr hy.2.le
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hO.mem_nhds ⟨hzB, hz⟩) hOS)
  refine ⟨{
    scaleBound := η
    scaleBound_pos := hη
    scaleBound_lt_one := hη1
    height := ε / 4
    height_pos := by positivity
    tangent := e
    inward := m
    tangent_unit := he
    inward_unit := hm
    orthogonal := hem
    clock := clock
    clock_center := hc0
    exact_lift := fun d hd hdη t ht => hline _ (hsmall d hd hdη t ht).1
    clock_c1 := ?_
    clock_regular := ?_
    clock_embedding := ?_
    maps_to_sector := ?_
    positive_interior := ?_
    boundary_halfplane := ?_
  }⟩
  · intro d hd hdη
    exact hc.comp (contDiff_const.mul contDiff_id).contDiffOn
      (fun t ht => (hsmall d hd hdη t ht).1)
  · intro d hd hdη t ht
    have hca := (hc (d * t) (hsmall d hd hdη t ht).1).contDiffAt
      (hV.mem_nhds (hsmall d hd hdη t ht).1)
    have hder := (hca.differentiableAt (by norm_num)).hasDerivAt.comp t
      ((hasDerivAt_id t).const_mul d)
    have hform : deriv (fun t => clock (d * t)) t = deriv clock (d * t) * d := by
      convert! hder.deriv using 1 <;> simp [Function.comp_def]
    rw [hform]
    exact mul_ne_zero (hcr _ (hsmall d hd hdη t ht).1) hd.ne'
  · intro d hd hdη
    let D := Homeomorph.mulLeft₀ d hd.ne'
    have hemb : IsEmbedding (fun t : Ioo (-1 : ℝ) 1 => D t) :=
      D.isEmbedding.comp IsEmbedding.subtypeVal
    exact hclockemb.comp (hemb.codRestrict V (fun t => (hsmall d hd hdη t t.property).1))
  · intro d hd hdη z hz
    rw [show z = (z.1, z.2) from rfl, hcoord d z.1 z.2 hd hdη hz.1]
    apply (hεside (hdist d hd hdη z.1 hz.1 z.2 (by rw [abs_of_nonneg hz.2.1]; exact hz.2.2))).mpr
    rw [hinner d z.1 z.2 hd hdη hz.1]
    exact hz.2.1
  · intro d hd hdη z hz
    rw [show z = (z.1, z.2) from rfl, hcoord d z.1 z.2 hd hdη hz.1]
    apply hposinterior _ (hdist d hd hdη z.1 hz.1 z.2 (by rw [abs_of_pos hz.2.1]; exact hz.2.2))
    rw [hinner d z.1 z.2 hd hdη hz.1]
    exact hz.2.1
  · intro d hd hdη t ht
    have hball : q (d * t) ∈ Metric.ball (q 0) ε := by
      apply Metric.mem_ball.mpr
      exact lt_of_lt_of_le (hsmall d hd hdη t ht).2 (by linarith [hε])
    filter_upwards [Metric.isOpen_ball.mem_nhds hball] with z hz
    have hziff : z ∈ A.domain ↔ 0 ≤ inner ℝ m z := hεside hz
    rw [hziff, inner_sub_right, hinnerq d hd hdη t ht, sub_zero]

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
