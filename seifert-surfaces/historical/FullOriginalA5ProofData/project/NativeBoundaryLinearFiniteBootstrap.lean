import NativeBoundaryFiniteLinearNormalGain
import NativeBoundaryFiniteHolderAssembly
import NativeBoundaryLinearSecondOrderGain

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- The same zero-trace linear solution gains one full finite Holder order.
All differentiated forcing fields are constructed from the actual equation. -/
theorem native_linear_finite_holder_gain (n : ℕ)
    (R κ M : ℝ) (hR : 0 < R) (hκ : 0 < κ) (hM : 0 < M)
    (C : LinearizedCoefficients) (v : E2 → ℝ) (α : ℝ≥0)
    (hα : 0 < α) (hα1 : α < 1)
    (hv : NativeCapHolder (closedHalfDisc R) α (n + 1) v)
    (ha : NativeCapHolder (closedHalfDisc R) α (n + 1) C.a)
    (hd : NativeCapHolder (closedHalfDisc R) α (n + 1) C.d)
    (hvi : ContDiffOn ℝ ∞ v (openHalfDisc R))
    (hz : ∀ x ∈ flatBoundary R, v x = 0)
    (hc : C.c = 0) (hb : C.b = 0) (hq : C.q = 0) (hf : C.f = 0)
    (hprincipal : ∀ x ∈ closedHalfDisc R,
      (∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤ inner ℝ (C.a x ξ) ξ) ∧ ‖C.a x‖ ≤ M)
    (hw : LinearWeakEquation (openHalfDisc R) C v (planarGradient v)) :
    ∃ s : ℝ, 0 < s ∧ s < R ∧ NativeCapHolder (closedHalfDisc s) α (n + 2) v := by
  induction n generalizing R κ M C v with
  | zero =>
    have hv1 := (nativeCapHolder_one_iff _ α v).mp hv
    have ha1 := (nativeCapHolder_one_iff _ α C.a).mp ha
    have hd1 := (nativeCapHolder_one_iff _ α C.d).mp hd
    let r := R / 4
    have hr : 0 < r := by dsimp [r]; positivity
    have he : 4 * r = R := by dsimp [r]; ring
    have hg := native_linear_C2_holder_gain r κ M hr hκ hM C v α hα hα1
      (he.symm ▸ hv1.1) (he.symm ▸ ha1.1) (he.symm ▸ hd1.1)
      (he.symm ▸ ha1.2) (he.symm ▸ hd1.2) (he.symm ▸ hv1.2)
      (he.symm ▸ hvi.of_le (by simp)) (he.symm ▸ hz) hc hb hq hf
      (he.symm ▸ hprincipal) (he.symm ▸ hw)
    let s := r / 64
    have hs : 0 < s := by dsimp [s]; positivity
    have hsR : s < R := by dsimp [s, r]; linarith
    refine ⟨s, hs, hsR, ?_⟩
    apply native_capHolder_of_partials 0 (by simp) s hs (closedHalfDisc R)
      (closedHalfDisc_mono hsR.le) v (hv1.1.differentiableOn (by norm_num)) α hα 1
    intro i
    have hh := (nativeCapHolder_one_iff _ α _).mpr (hg.2 i)
    simpa only [he, s, nativeClosedBoundaryCap, closedHalfDisc] using hh
  | succ n ih =>
    let K := closedHalfDisc R
    let U := openHalfDisc R
    let t := fun x => fderivWithin ℝ v K x (coordinateVector 2 1)
    let D := nativeClosedDifferentiatedLinearCoefficients K C v
    have hKD := closedHalfDisc_uniqueDiffOn hR
    have hUK : U ⊆ K := openHalfDisc_subset_closedHalfDisc R
    have hvC : ContDiffOn ℝ 1 v K := hv.1.of_le (by simp)
    have haC : ContDiffOn ℝ 1 C.a K := ha.1.of_le (by simp)
    have hdC : ContDiffOn ℝ 1 C.d K := hd.1.of_le (by simp)
    have ht : NativeCapHolder K α (n + 1) t := hv.2 1
    have hDa : NativeCapHolder K α (n + 1) D.a := ha.lower 0 R hR hα1.le
    have hDd : NativeCapHolder K α (n + 1) D.d :=
      ((ha.2 1).clm_apply 0 R hR (by simp) hα hα1.le (hv.gradient_field hKD)).add hKD (hd.2 1)
    have htSmooth : ContDiffOn ℝ ∞ t U := by
      apply ((hvi.fderiv_of_isOpen (openHalfDisc_isOpen R) (by simp)).clm_apply
        contDiffOn_const).congr
      intro x hx
      change fderivWithin ℝ v K x (coordinateVector 2 1) = _
      rw [fderivWithin_of_mem_nhds (mem_of_superset ((openHalfDisc_isOpen R).mem_nhds hx) hUK)]
    have htz : ∀ x ∈ flatBoundary R, t x = 0 := by
      intro x hx
      exact native_tangential_cap_derivative_zero_trace 0 R v hvC hz x hx.1 hx.2
    have hdt := native_closed_tangential_derivative_linear_weak U K (openHalfDisc_isOpen R)
      (fun x hx => mem_of_superset ((openHalfDisc_isOpen R).mem_nhds hx) hUK) C v
      (haC.mono hUK) (hdC.mono hUK) (hvi.of_le (by simp)) hc hb hq hf hw
    obtain ⟨s, hs, hsR, htgain⟩ := ih R κ M hR hκ hM D t ht hDa hDd htSmooth
      htz rfl rfl rfl rfl hprincipal hdt.2
    have hngain := native_linear_higher_normal_derivative R s κ hs hsR hκ C v α hα hα1.le
      (n + 1) hv ha hd (hvi.of_le (by simp)) hc hb hq hf
      (fun x hx => (hprincipal x hx).1) hw htgain
    have hs2 : 0 < s / 2 := by positivity
    have hs2R : s / 2 < R := by linarith
    refine ⟨s / 2, hs2, hs2R, ?_⟩
    apply native_capHolder_of_partials 0 (by simp) (s / 2) hs2 K
      (closedHalfDisc_mono hs2R.le) v (hvC.differentiableOn (by norm_num)) α hα (n + 2)
    intro i
    fin_cases i
    · simpa [Nat.add_assoc, K, nativeClosedBoundaryCap, closedHalfDisc, coordinateVector] using hngain
    · exact htgain.restrict (closedHalfDisc_mono (by linarith)) (closedHalfDisc_uniqueDiffOn hs2)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
