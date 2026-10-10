import CurveComplexGenusTwo.Topology.CrosscutFull
import CurveComplexGenusTwo.Foundations.Definitions

namespace CurveComplex
open Schoenflies Metric Set

private theorem position_alexander_radius (R : ℝ) (hR : 0 < R)
    (F : Plane ≃ₜ Plane) (hFfix : ∀ x, R ≤ ‖x‖ → F x = x)
    (C : Set Plane) (hFC : ∀ x, x ∉ C → F x = x)
    (hscale : ∀ (t : ℝ), 0 < t → t ≤ 1 → ∀ x, x ∉ C → t⁻¹ • x ∉ C) :
    ∃ H : AmbientIsotopy Plane, H.finalMap = F ∧
      (∀ t x, R ≤ ‖x‖ → H.map (t, x) = x) ∧
      ∀ t x, x ∉ C → H.map (t, x) = x := by
  have hFbound (x : Plane) (hx : ‖x‖ ≤ R) : ‖F x‖ ≤ R := by
    by_contra hn
    have heq : F x = x := F.injective (hFfix (F x) (le_of_not_ge hn))
    exact hn (by rw [heq]; exact hx)
  have hdisp (x : Plane) : ‖F x - x‖ ≤ 2 * R := by
    by_cases hx : ‖x‖ ≤ R
    · exact (norm_sub_le _ _).trans (by linarith [hFbound x hx])
    · rw [hFfix x (le_of_not_ge hx), sub_self, norm_zero]
      linarith
  let G : Interval × Plane → Plane := fun z =>
    if (z.1 : ℝ) = 0 then z.2 else (z.1 : ℝ) • F ((z.1 : ℝ)⁻¹ • z.2)
  have hGbound (z : Interval × Plane) :
      dist (G z) z.2 ≤ (2 * R) * (z.1 : ℝ) := by
    by_cases ht : (z.1 : ℝ) = 0
    · simp only [G, ht, ite_true, dist_self, mul_zero, le_refl]
    · dsimp only [G]
      rw [if_neg ht, dist_eq_norm]
      have heq : (z.1 : ℝ) • F ((z.1 : ℝ)⁻¹ • z.2) - z.2 =
          (z.1 : ℝ) • (F ((z.1 : ℝ)⁻¹ • z.2) - (z.1 : ℝ)⁻¹ • z.2) := by
        rw [smul_sub, smul_smul, mul_inv_cancel₀ ht, one_smul]
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg z.1.property.1]
      calc
        (z.1 : ℝ) * ‖F ((z.1 : ℝ)⁻¹ • z.2) - (z.1 : ℝ)⁻¹ • z.2‖ ≤
            (z.1 : ℝ) * (2 * R) :=
          mul_le_mul_of_nonneg_left (hdisp _) z.1.property.1
        _ = (2 * R) * (z.1 : ℝ) := mul_comm _ _
  have hGc : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases ht : (z.1 : ℝ) = 0
    · have hGz : G z = z.2 := by simp only [G, ht, ite_true]
      change Filter.Tendsto G (nhds z) (nhds (G z))
      rw [hGz, tendsto_iff_dist_tendsto_zero]
      have hlim : Filter.Tendsto
          (fun w : Interval × Plane => (2 * R) * (w.1 : ℝ) + dist w.2 z.2)
          (nhds z) (nhds 0) := by
        have hc : Continuous (fun w : Interval × Plane =>
            (2 * R) * (w.1 : ℝ) + dist w.2 z.2) := by fun_prop
        simpa only [ContinuousAt, ht, mul_zero, dist_self, add_zero] using hc.continuousAt (x := z)
      exact squeeze_zero (fun w => dist_nonneg) (fun w =>
        (dist_triangle (G w) w.2 z.2).trans (add_le_add (hGbound w) le_rfl)) hlim
    · have hc : ContinuousAt
          (fun w : Interval × Plane => (w.1 : ℝ) • F ((w.1 : ℝ)⁻¹ • w.2)) z := by
        fun_prop (disch := assumption)
      apply hc.congr_of_eventuallyEq
      have hevent : ∀ᶠ w : Interval × Plane in nhds z, (w.1 : ℝ) ≠ 0 :=
        (continuous_subtype_val.comp continuous_fst).continuousAt.eventually_ne ht
      exact hevent.mono (fun w hw => if_neg hw)
  refine ⟨{ map := ⟨G, hGc⟩, homeomorphism_at := ?_, at_zero := ?_ }, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : (t : ℝ) = 0
    · exact ⟨Homeomorph.refl _, fun x => by
        change x = G (t, x)
        simp only [G, ht, ite_true]⟩
    · let u : ℝˣ := Units.mk0 (t : ℝ) ht
      let e := ((Homeomorph.smul u⁻¹).trans F).trans (Homeomorph.smul u)
      refine ⟨e, ?_⟩
      intro x
      change (t : ℝ) • F ((t : ℝ)⁻¹ • x) = G (t, x)
      dsimp only [G]
      rw [if_neg ht]
  · intro x
    simp [G]
  · funext x
    simp [AmbientIsotopy.finalMap, G]
  · intro t x hx
    change G (t, x) = x
    by_cases ht : (t : ℝ) = 0
    · simp only [G, ht, ite_true]
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      have hlarge : R ≤ ‖(t : ℝ)⁻¹ • x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos), inv_mul_eq_div]
        apply (le_div_iff₀ htpos).mpr
        nlinarith [t.property.2]
      simp only [G, if_neg ht, hFfix _ hlarge, smul_smul, mul_inv_cancel₀ ht, one_smul]
  · intro t x hx
    change G (t, x) = x
    by_cases ht : (t : ℝ) = 0
    · simp only [G, ht, ite_true]
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      have hout := hscale (t : ℝ) htpos t.property.2 x hx
      simp only [G, if_neg ht, hFC _ hout, smul_smul, mul_inv_cancel₀ ht, one_smul]

theorem position_crosscut_supported_isotopy
    (A B : Set Plane) (a b : Plane)
    (hA : IsArcBetween A a b) (hB : IsArcBetween B a b)
    (ha : a ∈ modelCurve) (hb : b ∈ modelCurve)
    (hAi : A \ {a, b} ⊆ Plane.openSquare 0 1)
    (hBi : B \ {a, b} ⊆ Plane.openSquare 0 1) :
    ∃ (R : ℝ) (H : AmbientIsotopy Plane),
      0 < R ∧ H.finalMap '' A = B ∧
      (∀ t x, R ≤ ‖x‖ → H.map (t, x) = x) ∧
      ∀ t x, x ∉ Plane.openSquare 0 1 → H.map (t, x) = x := by
  obtain ⟨F, hFA, hFfix⟩ :=
    position_relative_crosscut_replacement A B a b hA hB ha hb hAi hBi
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_ball (0 : Plane)).mp (Plane.isBounded_closedSquare 0 1)
  have hRpos : 0 < R := by
    have hz : (0 : Plane) ∈ Plane.closedSquare 0 1 := by
      exact mem_closedSquare_zero_one.mpr (by simp [Plane.supNorm])
    have hb := hR hz
    simpa using hb
  have hFball : ∀ x : Plane, R ≤ ‖x‖ → F x = x := by
    intro x hx
    apply hFfix x
    intro hxs
    have hb : x ∈ Metric.ball (0 : Plane) R :=
      hR (mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hxs).le)
    exact not_lt_of_ge hx (by simpa using hb)
  have hscale : ∀ (t : ℝ), 0 < t → t ≤ 1 →
      ∀ x : Plane, x ∉ Plane.openSquare 0 1 → t⁻¹ • x ∉ Plane.openSquare 0 1 := by
    intro t ht ht1 x hx hxin
    have hs : 1 ≤ Plane.supNorm x :=
      le_of_not_gt (fun h => hx (mem_openSquare_zero_one.mpr h))
    have hti : 1 ≤ t⁻¹ := by
      apply (one_le_inv₀ ht).mpr
      exact ht1
    have hs' : 1 ≤ Plane.supNorm (t⁻¹ • x) := by
      rw [Plane.supNorm_smul, abs_of_pos (inv_pos.mpr ht)]
      calc
        1 ≤ t⁻¹ := hti
        _ = t⁻¹ * 1 := by ring
        _ ≤ t⁻¹ * Plane.supNorm x :=
          mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr ht.le)
    exact not_lt_of_ge hs' (mem_openSquare_zero_one.mp hxin)
  obtain ⟨H, hHF, hHfix, hHsq⟩ :=
    position_alexander_radius R hRpos F hFball (Plane.openSquare 0 1) hFfix hscale
  refine ⟨R, H, hRpos, ?_, hHfix, hHsq⟩
  rw [hHF]
  exact hFA

#print axioms position_crosscut_supported_isotopy

end CurveComplex
