import NativeMetricFormProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped Manifold ContDiff Bundle
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- Continuous outward metric unit conormals are constructed from the
actual native closed-side differential and its inward Euclidean frame.
No conormal section, unit condition or edge orthogonality is an input. -/
theorem native_metric_unit_outward_section
    (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    {P : Type*} [TopologicalSpace P] (q : P → Euc 2) (p : P → ThreeSphere)
    (hq : Continuous q) (hqm : ∀ t, q t ∈ ((F.domain i).chart j).map.target)
    (heq : ∀ t, pieceSphereCoordinate E F i j (q t) = p t)
    (e m : Euc 2) (he : ‖e‖ = 1) (hm : ‖m‖ = 1) (hem : inner ℝ e m = 0) :
    ∃ v : P → Euc 2, Continuous v ∧ (∀ t, inner ℝ m (v t) < 0) ∧
      (∀ t, G.extension.inner (p t)
        (actualPieceConormal E F i j (q t) (v t) (p t) (heq t))
        (actualPieceConormal E F i j (q t) (v t) (p t) (heq t)) = 1) ∧
      (∀ t, G.extension.inner (p t)
        (actualPieceConormal E F i j (q t) (v t) (p t) (heq t))
        (actualPieceConormal E F i j (q t) e (p t) (heq t)) = 0) ∧
      Continuous (fun t => Bundle.TotalSpace.mk' (Euc 3) (p t)
        (actualPieceConormal E F i j (q t) (v t) (p t) (heq t))) := by
  let B := fun t => nativePieceMetricForm E G F i j (q t) (p t) (heq t)
  have hBpos (t : P) := native_piece_metric_form_positive E G F i j (q t) (hqm t) (p t) (heq t)
  have hBE : Continuous (fun t => B t e e) := native_piece_metric_pair_continuous E G F i j
    q (fun _ => e) (fun _ => e) p hq continuous_const continuous_const hqm heq
  have hBME : Continuous (fun t => B t m e) := native_piece_metric_pair_continuous E G F i j
    q (fun _ => m) (fun _ => e) p hq continuous_const continuous_const hqm heq
  have hen : e ≠ 0 := by intro hz; simpa [hz] using he
  have hBEne : ∀ t, B t e e ≠ 0 := fun t => (hBpos t e hen).ne'
  let n := fun t => seamMetricOrthogonalOutward (B t) e m
  have hncont : Continuous n := (hBME.div hBE hBEne).smul continuous_const |>.sub continuous_const
  have hnne (t : P) : n t ≠ 0 := by
    have hme : inner ℝ m e = 0 := by rw [real_inner_comm, hem]
    have hninner : inner ℝ m (n t) = -1 := by
      dsimp [n, seamMetricOrthogonalOutward]
      rw [inner_sub_right, inner_smul_right, hme, mul_zero,
        real_inner_self_eq_norm_sq, hm, one_pow]
      norm_num
    intro hz
    rw [hz, inner_zero_right] at hninner
    norm_num at hninner
  have hBN : Continuous (fun t => B t (n t) (n t)) :=
    native_piece_metric_pair_continuous E G F i j q n n p hq hncont hncont hqm heq
  have hBNpos : ∀ t, 0 < B t (n t) (n t) := fun t => hBpos t (n t) (hnne t)
  have hdcont : Continuous (fun t => (Real.sqrt (B t (n t) (n t)))⁻¹) :=
    hBN.sqrt.inv₀ (fun t => (Real.sqrt_pos.mpr (hBNpos t)).ne')
  let v := fun t => seamMetricUnitOutward (B t) e m
  have hvcont : Continuous v := hdcont.smul hncont
  have hprop (t : P) := seam_metric_unit_outward_properties (B t) e m (hBpos t) he hm hem
  refine ⟨v, hvcont, fun t => (hprop t).2.2, ?_, ?_, ?_⟩
  · intro t
    exact (nativePieceMetricForm_apply E G F i j _ _ _ _ _).symm.trans (hprop t).1
  · intro t
    exact (nativePieceMetricForm_apply E G F i j _ _ _ _ _).symm.trans (hprop t).2.1
  · exact native_actual_differential_section_continuous E F i j q v p hq hvcont hqm heq

/-- The local flat inward halfplane proves the literal original outward
direction condition for every source vector with negative inward component. -/
theorem local_halfplane_outward_direction
    (D : Set (Euc 2)) (y m v : Euc 2)
    (hside : ∀ᶠ z in 𝓝 y, z ∈ D ↔ 0 ≤ inner ℝ m (z - y))
    (hv : inner ℝ m v < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ Ioo (0 : ℝ) ε,
      y - b • v ∈ interior D ∧ y + b • v ∉ D := by
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hside
  let ε := δ / (‖v‖ + 1)
  have hden : 0 < ‖v‖ + 1 := by positivity
  have hε : 0 < ε := div_pos hδ hden
  have hdist (b : ℝ) (hb : b ∈ Ioo (0 : ℝ) ε) : b * ‖v‖ < δ := by
    have hd := (lt_div_iff₀ hden).mp hb.2
    nlinarith [norm_nonneg v, hb.1]
  have hplus (b : ℝ) (hb : b ∈ Ioo (0 : ℝ) ε) : y + b • v ∈ Metric.ball y δ := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hb.1]
    exact hdist b hb
  have hminus (b : ℝ) (hb : b ∈ Ioo (0 : ℝ) ε) : y - b • v ∈ Metric.ball y δ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos hb.1]
    exact hdist b hb
  refine ⟨ε, hε, ?_⟩
  intro b hb
  constructor
  · let O := Metric.ball y δ ∩ {z : Euc 2 | 0 < inner ℝ m (z - y)}
    have hO : IsOpen O := Metric.isOpen_ball.inter
      (isOpen_lt continuous_const ((innerSL ℝ m).continuous.comp (continuous_id.sub continuous_const)))
    have hOS : O ⊆ D := fun z hz => (hδsub hz.1).mpr hz.2.le
    have hp : y - b • v ∈ O := by
      refine ⟨hminus b hb, ?_⟩
      change 0 < inner ℝ m (y - b • v - y)
      rw [sub_sub_cancel_left, inner_neg_right, inner_smul_right]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg hb.1 hv)
    exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hO.mem_nhds hp) hOS)
  · intro hd
    have ht : 0 ≤ inner ℝ m (y + b • v - y) := (hδsub (hplus b hb)).mp hd
    rw [add_sub_cancel_left, inner_smul_right] at ht
    exact (not_le_of_gt (mul_neg_of_pos_of_neg hb.1 hv)) ht

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
