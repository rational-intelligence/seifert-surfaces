import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Tactic

set_option autoImplicit false
open Set MeasureTheory
open scoped ContDiff

namespace SeifertSurfaces.GraphGreenTransport
noncomputable section

def transport (L U : ℝ → ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (L z.2 + z.1 * (U z.2 - L z.2), z.2)

def slope (a b : ℝ) (L U : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  derivWithin L (Icc a b) z.2 +
    z.1 * (derivWithin U (Icc a b) z.2 - derivWithin L (Icc a b) z.2)

def transportDerivative (a b : ℝ) (L U : ℝ → ℝ) (z : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![U z.2 - L z.2, slope a b L U z; 0, 1]).toContinuousLinearMap

theorem width_nonneg {a b : ℝ} {L U : ℝ → ℝ}
    (ha : L a = U a) (hb : L b = U b)
    (hLU : ∀ y ∈ Ioo a b, L y < U y) {y : ℝ} (hy : y ∈ Icc a b) :
    0 ≤ U y - L y := by
  rcases hy.1.eq_or_lt with h | h
  · subst y; simp [ha]
  rcases hy.2.eq_or_lt with h' | h'
  · subst y; simp [hb]
  exact sub_nonneg.mpr (hLU y ⟨h, h'⟩).le

theorem transport_closed {a b : ℝ} {L U : ℝ → ℝ}
    (ha : L a = U a) (hb : L b = U b)
    (hLU : ∀ y ∈ Ioo a b, L y < U y) {z : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc a b) :
    (transport L U z).2 ∈ Icc a b ∧
      (transport L U z).1 ∈ Icc (L (transport L U z).2) (U (transport L U z).2) := by
  have hw := width_nonneg ha hb hLU hz.2
  dsimp [transport]
  exact ⟨hz.2, by constructor <;> nlinarith [hz.1.1, hz.1.2]⟩

theorem transport_inj {a b : ℝ} {L U : ℝ → ℝ}
    (hLU : ∀ y ∈ Ioo a b, L y < U y) :
    InjOn (transport L U) (Ioo (0 : ℝ) 1 ×ˢ Ioo a b) := by
  intro z hz w hw he
  have hy : z.2 = w.2 := by simpa only [transport] using congrArg Prod.snd he
  have hx := congrArg Prod.fst he
  dsimp [transport] at hx
  rw [← hy] at hx
  have hwidth : U z.2 - L z.2 ≠ 0 := ne_of_gt (sub_pos.mpr (hLU z.2 hz.2))
  exact Prod.ext (mul_right_cancel₀ hwidth (add_left_cancel hx)) hy

theorem transport_image {a b : ℝ} {L U : ℝ → ℝ}
    (hLU : ∀ y ∈ Ioo a b, L y < U y) :
    transport L U '' (Ioo (0 : ℝ) 1 ×ˢ Ioo a b) =
      {z | z.2 ∈ Ioo a b ∧ z.1 ∈ Ioo (L z.2) (U z.2)} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwidth := sub_pos.mpr (hLU w.2 hw.2)
    exact ⟨hw.2, by dsimp [transport]; constructor <;> nlinarith [hw.1.1, hw.1.2]⟩
  · intro hz
    have hwidth := sub_pos.mpr (hLU z.2 hz.1)
    refine ⟨((z.1 - L z.2) / (U z.2 - L z.2), z.2), ⟨?_, hz.1⟩, ?_⟩
    · exact ⟨div_pos (sub_pos.mpr hz.2.1) hwidth,
        (div_lt_one hwidth).mpr (by linarith [hz.2.2])⟩
    · ext <;> simp [transport, div_mul_cancel₀ _ (ne_of_gt hwidth)]

theorem graph_hasDerivAt {a b : ℝ} {H : ℝ → ℝ}
    (hH : ContDiffOn ℝ 2 H (Icc a b)) {y : ℝ} (hy : y ∈ Ioo a b) :
    HasDerivAt H (derivWithin H (Icc a b) y) y := by
  exact ((hH.differentiableOn (by norm_num)) y ⟨hy.1.le, hy.2.le⟩).hasDerivWithinAt.hasDerivAt
    (Icc_mem_nhds hy.1 hy.2)

theorem hasFDerivAt_transport {a b : ℝ} {L U : ℝ → ℝ}
    (hL : ContDiffOn ℝ 2 L (Icc a b)) (hU : ContDiffOn ℝ 2 U (Icc a b))
    {z : ℝ × ℝ} (hz : z.2 ∈ Ioo a b) :
    HasFDerivAt (transport L U) (transportDerivative a b L U z) z := by
  have hs : HasFDerivAt (fun z : ℝ × ℝ => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) z :=
    hasFDerivAt_snd
  have hLd := (graph_hasDerivAt hL hz).comp_hasFDerivAt z hs
  have hUd := (graph_hasDerivAt hU hz).comp_hasFDerivAt z hs
  unfold transportDerivative
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert (hLd.add (hasFDerivAt_fst.mul (hUd.sub hLd))).prodMk hasFDerivAt_snd using 1
  · rfl
  · ext <;> simp [slope, smul_eq_mul]

theorem det_transportDerivative (a b : ℝ) (L U : ℝ → ℝ) (z : ℝ × ℝ) :
    (transportDerivative a b L U z).det = U z.2 - L z.2 := by
  simp [transportDerivative, LinearMap.det_toContinuousLinearMap,
    LinearMap.det_toLin, Matrix.det_fin_two_of]

theorem contDiffOn_transport {a b : ℝ} {L U : ℝ → ℝ}
    (hL : ContDiffOn ℝ 2 L (Icc a b)) (hU : ContDiffOn ℝ 2 U (Icc a b)) :
    ContDiffOn ℝ 2 (transport L U) (Icc (0 : ℝ) 1 ×ˢ Icc a b) := by
  have hm : MapsTo (fun z : ℝ × ℝ => z.2) (Icc (0 : ℝ) 1 ×ˢ Icc a b) (Icc a b) :=
    fun _ hz => hz.2
  have hLd := hL.comp contDiffOn_snd hm
  have hUd := hU.comp contDiffOn_snd hm
  exact (hLd.add (contDiffOn_fst.mul (hUd.sub hLd))).prodMk contDiffOn_snd

theorem contDiffOn_slope {a b : ℝ} (hab : a < b) {L U : ℝ → ℝ}
    (hL : ContDiffOn ℝ 2 L (Icc a b)) (hU : ContDiffOn ℝ 2 U (Icc a b)) :
    ContDiffOn ℝ 1 (slope a b L U) (Icc (0 : ℝ) 1 ×ˢ Icc a b) := by
  have hm : MapsTo (fun z : ℝ × ℝ => z.2) (Icc (0 : ℝ) 1 ×ˢ Icc a b) (Icc a b) :=
    fun _ hz => hz.2
  have hLd := (hL.derivWithin (uniqueDiffOn_Icc hab) (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).comp
    contDiffOn_snd hm
  have hUd := (hU.derivWithin (uniqueDiffOn_Icc hab) (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).comp
    contDiffOn_snd hm
  exact hLd.add (contDiffOn_fst.mul (hUd.sub hLd))

end
end SeifertSurfaces.GraphGreenTransport
