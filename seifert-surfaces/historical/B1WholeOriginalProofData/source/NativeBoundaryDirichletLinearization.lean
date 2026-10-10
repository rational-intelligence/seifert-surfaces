import NativeBoundaryQuotientPackage
import NativeBoundaryFluxReflection

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

def subtractDatumCoefficients (C : LinearizedCoefficients) (w : E2 → ℝ)
    (Gw : E2 → E2) : LinearizedCoefficients where
  a := C.a
  c := C.c
  d x := C.a x (Gw x) + w x • C.c x + C.d x
  b := C.b
  q := C.q
  f x := C.b x (Gw x) + C.q x * w x + C.f x

theorem subtractDatum_flux (C : LinearizedCoefficients) (v w : E2 → ℝ)
    (G Gw : E2 → E2) (x : E2) :
    linearizedFlux (subtractDatumCoefficients C w Gw) (v - w) (G - Gw) x =
      linearizedFlux C v G x := by
  simp only [linearizedFlux, subtractDatumCoefficients, Pi.sub_apply, map_sub, sub_smul]
  module

theorem subtractDatum_source (C : LinearizedCoefficients) (v w : E2 → ℝ)
    (G Gw : E2 → E2) (x : E2) :
    linearizedSource (subtractDatumCoefficients C w Gw) (v - w) (G - Gw) x =
      linearizedSource C v G x := by
  simp only [linearizedSource, subtractDatumCoefficients, Pi.sub_apply, map_sub]
  ring

theorem linearized_weak_equation_subtract_datum
    (B : Set E2) (C : LinearizedCoefficients) (v w : E2 → ℝ) (G Gw : E2 → E2)
    (hw : LinearWeakEquation B C v G) :
    LinearWeakEquation B (subtractDatumCoefficients C w Gw) (v - w) (G - Gw) := by
  intro φ hφ hc ht
  simpa only [subtractDatum_flux, subtractDatum_source] using hw φ hφ hc ht

/-- Subtracting a smooth boundary datum only changes the actual two forcing
fields. Ellipticity and all constants remain independent of the quotient step. -/
theorem subtractDatum_coefficient_bounds
    (B : Set E2) (C : LinearizedCoefficients) (κ M D : ℝ)
    (hc : CoefficientBounds B C κ M) (hD : 0 ≤ D)
    (w : E2 → ℝ) (Gw : E2 → E2)
    (hb : ∀ x ∈ B, |w x| ≤ D ∧ ‖Gw x‖ ≤ D) :
    CoefficientBounds B (subtractDatumCoefficients C w Gw) κ (M * (2 * D + 1)) := by
  have hM : 0 ≤ M := by linarith [hc.2.1]
  have hMM : M ≤ M * (2 * D + 1) := by nlinarith [mul_nonneg hM hD]
  refine ⟨hc.1, hc.2.1.trans hMM, hc.2.2.1, ?_⟩
  intro x hx
  obtain ⟨ha, hc', hd, hb', hq, hf⟩ := hc.2.2.2 x hx
  obtain ⟨hw, hG⟩ := hb x hx
  refine ⟨ha.trans hMM, hc'.trans hMM, ?_, hb'.trans hMM, hq.trans hMM, ?_⟩
  · change ‖C.a x (Gw x) + w x • C.c x + C.d x‖ ≤ _
    calc
      _ ≤ ‖C.a x (Gw x)‖ + ‖w x • C.c x‖ + ‖C.d x‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ M * D + D * M + M := by
        rw [norm_smul, Real.norm_eq_abs]
        exact add_le_add (add_le_add
          ((C.a x).le_opNorm (Gw x) |>.trans (mul_le_mul ha hG (norm_nonneg _) hM))
          (mul_le_mul hw hc' (norm_nonneg _) hD)) hd
      _ = _ := by ring
  · change |C.b x (Gw x) + C.q x * w x + C.f x| ≤ _
    calc
      _ ≤ |C.b x (Gw x)| + |C.q x * w x| + |C.f x| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ M * D + M * D + M := by
        rw [abs_mul]
        apply add_le_add (add_le_add ?_ (mul_le_mul hq hw (abs_nonneg _) hM)) hf
        exact (show |C.b x (Gw x)| ≤ ‖C.b x‖ * ‖Gw x‖ by
          simpa only [Real.norm_eq_abs] using (C.b x).le_opNorm (Gw x)).trans
            (mul_le_mul hb' hG (norm_nonneg _) hM)
      _ = _ := by ring

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
