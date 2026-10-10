import Mathlib

/-!
# Section 5: numerical consequences of the exchange estimates

Source: `references/seifert-surfaces.txt`, Theorem 5.1, Proposition 5.2,
Lemma 5.6, §5.2 and Appendix B. These are arithmetic subclaims only.
No theorem here asserts existence of a geometric exchange surface.
-/

namespace SeifertSurfaces.Section5

/-- Genus followed by area, with Mathlib's genuine lexicographic order. -/
def complexityValue (g : ℕ) (a : ℝ) : ℕ ×ₗ ℝ := toLex (g, a)

/-- Proposition 5.2's local-descent argument, with the same two output choices. -/
theorem local_descent_of_exchange_inequalities
    (gx gu gw gup gdown : ℕ) (ax au aw aup adown : ℝ)
    (hu : complexityValue gu au ≤ complexityValue gx ax)
    (hw : complexityValue gw aw ≤ complexityValue gx ax)
    (hgenus : gup + gdown ≤ gu + gw)
    (harea : gup + gdown = gu + gw → aup + adown < au + aw) :
    (complexityValue gup aup < complexityValue gx ax ∧ gup ≤ gx) ∨
      (complexityValue gdown adown < complexityValue gx ax ∧ gdown ≤ gx) := by
  have hu' := (Prod.Lex.toLex_le_toLex'.mp hu)
  have hw' := (Prod.Lex.toLex_le_toLex'.mp hw)
  by_cases hup : gup < gx
  · exact Or.inl ⟨Prod.Lex.toLex_lt_toLex.mpr (Or.inl hup), hup.le⟩
  by_cases hdown : gdown < gx
  · exact Or.inr ⟨Prod.Lex.toLex_lt_toLex.mpr (Or.inl hdown), hdown.le⟩
  have hgu : gu = gx := by omega
  have hgw : gw = gx := by omega
  have hgup : gup = gx := by omega
  have hgdown : gdown = gx := by omega
  have hsum : gup + gdown = gu + gw := by omega
  have hau : au ≤ ax := hu'.2 hgu
  have haw : aw ≤ ax := hw'.2 hgw
  have hstrict := harea hsum
  by_cases h : aup < ax
  · exact Or.inl ⟨Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hgup, h⟩), hgup.le⟩
  · have h' : adown < ax := by linarith
    exact Or.inr ⟨Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hgdown, h'⟩), hgdown.le⟩

/-- The genus truncation in Proposition 5.2(3), retaining the descended witness. -/
theorem genus_le_of_complexity_lt_max
    (gx gu gw : ℕ) (ax au aw : ℝ)
    (h : complexityValue gx ax < max (complexityValue gu au) (complexityValue gw aw)) :
    gx ≤ max gu gw := by
  rcases lt_max_iff.mp h with hu | hw
  · exact ((Prod.Lex.toLex_lt_toLex'.mp hu).1).trans (le_max_left _ _)
  · exact ((Prod.Lex.toLex_lt_toLex'.mp hw).1).trans (le_max_right _ _)

/-- The equality case in Proposition 5.2's local-descent argument. -/
theorem balanced_genus_sums_force_equality
    (gx gu gw gup gdown : ℕ)
    (hu : gu ≤ gx) (hw : gw ≤ gx)
    (hup : gx ≤ gup) (hdown : gx ≤ gdown)
    (hsum : gup + gdown ≤ gu + gw) :
    gu = gx ∧ gw = gx ∧ gup = gx ∧ gdown = gx ∧ gup + gdown = gu + gw := by
  omega

/-- Lemma 5.6, Step 3: the two possibly different curves need separate disc areas. -/
theorem disc_exchange_gain_sum_le_error
    (areaAa areaBa areaAb areaBb gainA gainB error : ℝ)
    (hA : areaBa + gainA ≤ areaAa)
    (hB : areaAb + gainB ≤ areaBb + error)
    (hminA : areaAa ≤ areaAb)
    (hminB : areaBb ≤ areaBa) :
    gainA + gainB ≤ error := by
  linarith

/-- The two curves in Lemma 5.6 need not be distinct. No distinctness is assumed. -/
theorem no_small_error_gain_pair
    {Curve : Type*} (gain : Curve → ℝ) (epsilon error : ℝ)
    (hlower : ∀ curve, epsilon ≤ gain curve)
    (herror : error < 2 * epsilon) :
    ¬ ∃ a b, gain a + gain b ≤ error := by
  rintro ⟨a, b, hab⟩
  have ha := hlower a
  have hb := hlower b
  linarith

/-- The transverse case of Lemma 5.6, where the perturbation error is zero. -/
theorem no_positive_gain_pair_at_zero_error
    {Curve : Type*} (gain : Curve → ℝ) (hpositive : ∀ curve, 0 < gain curve) :
    ¬ ∃ a b, gain a + gain b ≤ 0 := by
  rintro ⟨a, b, hab⟩
  have ha := hpositive a
  have hb := hpositive b
  linarith

/-- The fixed width and gain of Appendix B, equation (42). -/
theorem fixed_uniform_gain_positive
    (etaGeo kappa rho gainDensity goodLength : ℝ)
    (heta : 0 < etaGeo) (hkappa : 0 < kappa) (hrho : 0 < rho)
    (hgain : 0 < gainDensity) (hlength : 0 < goodLength) :
    0 < min etaGeo (kappa * rho / 4) ∧
      0 < gainDensity * min etaGeo (kappa * rho / 4) * goodLength := by
  have hwidth : 0 < min etaGeo (kappa * rho / 4) :=
    lt_min heta (div_pos (mul_pos hkappa hrho) (by norm_num))
  exact ⟨hwidth, mul_pos (mul_pos hgain hwidth) hlength⟩

/-- Appendix B, (44), before smoothing: the chosen width is the same on the good set. -/
theorem transition_width_equals_fixed_width
    (etaOne etaTwo kappa rho : ℝ)
    (hetaTwo : 0 ≤ etaTwo) (hkappa : 0 ≤ kappa) (hrho : 0 ≤ rho)
    (hfit : etaOne ≤ kappa * rho / 4) :
    min etaOne (etaTwo + kappa * rho / 2) = etaOne := by
  have hprod : 0 ≤ kappa * rho := mul_nonneg hkappa hrho
  apply min_eq_left
  linarith

/-- The length estimate in Corollary B.4(1), after the geometric quotient estimate. -/
theorem length_lower_bound_after_collapsing
    (rhoZero rhoTwo outsideLength : ℝ) (numberOfBalls : ℕ)
    (hdiameter : rhoZero / 2 ≤ outsideLength + 4 * (numberOfBalls : ℝ) * rhoTwo)
    (hsmall : 4 * (numberOfBalls : ℝ) * rhoTwo < rhoZero / 8) :
    3 * rhoZero / 8 < outsideLength := by
  linarith

/-- The strict area budget in §5.2; the two rounding gains are both retained. -/
theorem transverse_strict_area_budget
    (inputUp inputDown outputUp outputDown epsilon cost : ℝ)
    (hepsilon : 0 < epsilon)
    (houtput : outputUp + outputDown ≤ inputUp + inputDown - 2 * epsilon + cost)
    (hcost : cost < epsilon) :
    outputUp + outputDown < inputUp + inputDown - epsilon := by
  linarith

/-- The strict area budget in (43) and the final paragraph of configuration (T2). -/
theorem perturbed_strict_area_budget
    (baseArea perturbedArea otherArea outputUp outputDown epsilon cost : ℝ)
    (hperturbation : perturbedArea < baseArea + epsilon / 2)
    (houtput : outputUp + outputDown ≤ perturbedArea + otherArea - epsilon + cost)
    (hcost : cost < epsilon / 4) :
    outputUp + outputDown < baseArea + otherArea - epsilon / 4 := by
  linarith

end SeifertSurfaces.Section5
