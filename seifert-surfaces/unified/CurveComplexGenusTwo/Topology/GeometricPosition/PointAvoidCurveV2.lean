import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChartV2
import CurveComplexGenusTwo.Topology.ChartLift

open Schoenflies
open scoped NNReal
universe u
namespace CurveComplex.PositionUniverseV2
theorem position_point_off_curve
    (S : Type u) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (c : Curve S) (p : S) (hp : p ∈ c.image)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ H : AmbientIsotopy S, H.finalMap p ∉ c.image ∧
      ∀ t x, x ∉ W → H.map (t, x) = x := by
  classical
  have hsmall (f : Plane → Plane)
        (c : ℝ≥0) (hc : (c : ℝ) < 1) (hf : LipschitzWith c f) :
        ∃ H : AmbientIsotopy Plane,
          (∀ t x, H.map (t, x) = x + (t : ℝ) • f x) ∧
          (∀ t x, f x = 0 → H.map (t, x) = x) := by
    classical
    let F : Interval × Plane → Plane :=
      fun p => p.2 + (p.1 : ℝ) • f p.2
    have hF : Continuous F := continuous_snd.add
      ((continuous_subtype_val.comp continuous_fst).smul
        (hf.continuous.comp continuous_snd))
    refine ⟨{ map := ⟨F, hF⟩, homeomorphism_at := ?_, at_zero := ?_ },
      fun t x => rfl, ?_⟩
    · intro t
      have happ : ApproximatesLinearOn (fun x => F (t, x))
          (ContinuousLinearEquiv.refl ℝ Plane : Plane →L[ℝ] Plane)
          Set.univ c := by
        intro x _ y _
        have heq : F (t, x) - F (t, y) - (x - y) =
            (t : ℝ) • (f x - f y) := by dsimp [F]; module
        change ‖F (t, x) - F (t, y) - (x - y)‖ ≤ _
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
        calc
          (t : ℝ) * ‖f x - f y‖ ≤ 1 * ‖f x - f y‖ :=
            mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)
          _ ≤ c * ‖x - y‖ := by simpa [dist_eq_norm] using hf.dist_le_mul x y
      let e := happ.toHomeomorph (fun x => F (t, x)) (Or.inr (by simpa using hc))
      exact ⟨e, fun x => rfl⟩
    · intro x
      simp [F]
    · intro t x hx
      change x + (t : ℝ) • f x = x
      simp [hx]
  
  have hpush (p v : Plane) (R : ℝ) (hR : 0 < R) (hv : ‖v‖ < 1) :
        ∃ H : AmbientIsotopy Plane,
          (∀ x, H.finalMap x = x + max (R - dist x p) 0 • v) ∧
          ∀ t x, R ≤ dist x p → H.map (t, x) = x := by
    classical
    let b : Plane → ℝ := fun x => max (R - dist x p) 0
    have hb0 : LipschitzWith 1 (fun x : Plane => R - dist x p) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
        sub_sub_sub_cancel_left, abs_sub_comm] using abs_dist_sub_le x y p
    have hb : LipschitzWith 1 b := hb0.max_const 0
    let f : Plane → Plane := fun x => b x • v
    have hf : LipschitzWith ‖v‖₊ f := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      change ‖b x • v - b y • v‖ ≤ ‖v‖ * dist x y
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      have h := hb.dist_le_mul x y
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
      calc
        |b x - b y| * ‖v‖ ≤ dist x y * ‖v‖ :=
          mul_le_mul_of_nonneg_right h (norm_nonneg _)
        _ = ‖v‖ * dist x y := mul_comm _ _
    obtain ⟨H, hH, hfix⟩ := hsmall f ‖v‖₊ hv hf
    refine ⟨H, ?_, ?_⟩
    · intro x
      unfold AmbientIsotopy.finalMap
      rw [hH]
      simp [f, b]
    · intro t x hx
      apply hfix
      simp [f, b, max_eq_right (sub_nonpos.mpr hx)]
  obtain ⟨E, hpE, hEp, hEW, hSquare, hcurve⟩ :=
    position_curve_crosscut_chart S c p hp W hW hpW
  have hC : IsCompact (Metric.closedBall (0 : Plane) (1/2)) := isCompact_closedBall _ _
  have hCV : Metric.closedBall (0 : Plane) (1/2) ⊆ E.target := by
    intro z hz
    apply hSquare
    rw [mem_closedSquare_zero_one]
    have hn : ‖z‖ ≤ 1/2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact (Plane.supNorm_le_norm z).trans (by linarith)
  let v : Plane := Plane.mk 0 (1/2)
  have hv : ‖v‖ < 1 := by
    norm_num [v, EuclideanSpace.norm_eq, Fin.sum_univ_two, Plane.mk]
  obtain ⟨H, hmove, hfix⟩ := hpush 0 v (1/2) (by norm_num) hv
  obtain ⟨K, G, hcoord, hGU, hGfix⟩ := position_surface_chart_lift S
    E.source E.target E.open_source E.toHomeomorphSourceTarget
    (Metric.closedBall 0 (1/2)) hC hCV H (by
      intro t x hx
      apply hfix
      have hh : ¬ dist x (0 : Plane) ≤ 1/2 := hx
      exact (lt_of_not_ge hh).le)
  refine ⟨G, ?_, ?_⟩
  · let q : E.source := K.finalMap ⟨p, hpE⟩
    have hq : G.finalMap p = q.val := hGU ⟨1, by norm_num⟩ ⟨p, hpE⟩
    have hEq : E q.val = (1/2 : ℝ) • v := by
      have hh := hcoord (⟨1, by norm_num⟩ : Interval) ⟨p, hpE⟩
      change E q.val = H.finalMap (E p) at hh
      rw [hEp, hmove] at hh
      simpa using hh
    intro hm
    rw [hq] at hm
    have hz := (hcurve q.val q.property).mp hm
    rw [hEq] at hz
    norm_num [v, Plane.mk] at hz
  · intro t x hx
    exact hGfix t x (fun h => hx (hEW h))
end CurveComplex.PositionUniverseV2
