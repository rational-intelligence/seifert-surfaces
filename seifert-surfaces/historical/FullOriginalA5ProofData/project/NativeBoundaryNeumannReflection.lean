import NativeBoundaryParityWeakGradient
import NativeBoundaryCurlIdentity

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

def nativeEvenGradient (G : E2 → E2) (x : E2) : E2 :=
  if 0 < x 0 then G x else normalReflection (G (normalReflection x))

def nativeNeumannCoefficients (ρ κ : ℝ) (C : LinearizedCoefficients) : LinearizedCoefficients where
  a := (reflectLinearizedCoefficients C κ).a
  c := 0
  d := nativeEvenReflectedFlux ρ C.d
  b := 0
  q := 0
  f := 0

theorem nativeQuarterTurn_odd_reflection (v : E2) :
    nativeQuarterTurn (-normalReflection v) = normalReflection (nativeQuarterTurn v) := by
  ext i
  fin_cases i
  · change nativeQuarterTurn (-normalReflection v) 0 = normalReflection (nativeQuarterTurn v) 0
    simp only [nativeQuarterTurn_zero, PiLp.neg_apply, normalReflection_one, normalReflection_zero, neg_neg]
  · change nativeQuarterTurn (-normalReflection v) 1 = normalReflection (nativeQuarterTurn v) 1
    simp only [nativeQuarterTurn_one, PiLp.neg_apply, normalReflection_zero, normalReflection_one, neg_neg]

theorem native_neumann_flux_off_flat
    (ρ κ : ℝ) (C : LinearizedCoefficients) (v : E2 → ℝ) (G : E2 → E2)
    (x : E2) (hx : x ∈ Metric.ball 0 ρ) (hn : x 0 ≠ 0) :
    linearizedFlux (nativeNeumannCoefficients ρ κ C) (nativeEvenExtension v)
      (nativeEvenGradient G) x = nativeEvenReflectedFlux ρ (fun y => C.a y (G y) + C.d y) x := by
  have hRx := normalReflection_maps_ball ρ hx
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hxU : x ∉ openHalfDisc ρ := fun hh => (not_lt_of_ge hneg.le) hh.2
    have hRU : normalReflection x ∈ openHalfDisc ρ :=
      ⟨hRx, by change 0 < normalReflection x 0; rw [normalReflection_zero]; linarith⟩
    simp only [linearizedFlux, nativeNeumannCoefficients, reflectLinearizedCoefficients,
      if_neg (not_lt.mpr hneg.le), if_pos hneg, nativeEvenGradient,
      nativeEvenReflectedFlux, indicator_of_notMem hxU, indicator_of_mem hRU, smul_zero,
      Pi.zero_apply, add_zero, zero_add]
    change normalReflection (C.a (normalReflection x) (normalReflection (normalReflection (G (normalReflection x))))) +
      normalReflection (C.d (normalReflection x)) = _
    rw [normalReflection_involutive, map_add]
  · have hxU : x ∈ openHalfDisc ρ := ⟨hx, hpos⟩
    have hRU : normalReflection x ∉ openHalfDisc ρ := by
      intro hh
      have hp : 0 < normalReflection x 0 := hh.2
      rw [normalReflection_zero] at hp
      linarith
    simp only [linearizedFlux, nativeNeumannCoefficients, reflectLinearizedCoefficients,
      if_pos hpos, nativeEvenGradient, nativeEvenReflectedFlux, indicator_of_mem hxU,
      indicator_of_notMem hRU, map_zero, add_zero, Pi.zero_apply, smul_zero]

/-- Actual reflected Neumann identity from the odd H1 conjugate. The input
is a paid one-sided relation between the same gradients, rather than a
Neumann identity supplied as an oracle. -/
theorem native_neumann_reflected_equation_of_conjugacy
    (ρ κ : ℝ) (C : LinearizedCoefficients) (f w : E2 → ℝ)
    (hf : ContDiffOn ℝ 1 f (openHalfDisc ρ))
    (hw : ContDiffOn ℝ 1 w (openHalfDisc ρ))
    (hEven : DeGiorgi.MemW1p 2 (nativeEvenExtension f) (Metric.ball 0 ρ))
    (hOdd : DeGiorgi.MemW1p 2 (nativeOddExtension w) (Metric.ball 0 ρ))
    (hrel : ∀ x ∈ openHalfDisc ρ, C.a x (planarGradient f x) + C.d x =
      nativeQuarterTurn (planarGradient w x)) :
    ∀ hF : DeGiorgi.MemW1pWitness 2 (nativeEvenExtension f) (Metric.ball 0 ρ),
      LinearWeakEquation (Metric.ball 0 ρ) (nativeNeumannCoefficients ρ κ C)
        (nativeEvenExtension f) hF.weakGrad := by
  intro hF
  let hW := hOdd.someWitness
  have he := native_parity_weak_gradient_agrees ρ 1 f (nativeEvenExtension f) hf hF
    (fun x hx => by simp [nativeEvenExtension, le_of_lt (show 0 < x 0 from hx.2)])
    (fun x hx => by simp [nativeEvenExtension, not_le.mpr (show x 0 < 0 from hx.2)])
  have ho := native_parity_weak_gradient_agrees ρ (-1) w (nativeOddExtension w) hw hW
    (fun x hx => by simp [nativeOddExtension, le_of_lt (show 0 < x 0 from hx.2)])
    (fun x hx => by simp [nativeOddExtension, not_le.mpr (show x 0 < 0 from hx.2)])
  have hflat : ∀ᵐ x : E2 ∂volume, x 0 ≠ 0 := by
    simpa only [ae_iff, not_not] using native_flat_plane_null
  have hEq : (fun x => linearizedFlux (nativeNeumannCoefficients ρ κ C)
      (nativeEvenExtension f) hF.weakGrad x) =ᵐ[volume.restrict (Metric.ball 0 ρ)]
      (fun x => nativeQuarterTurn (hW.weakGrad x)) := by
    filter_upwards [he, ho, ae_restrict_mem Metric.isOpen_ball.measurableSet,
      ae_restrict_of_ae hflat] with x hxe hxo hx hn
    have hfluxcongr : linearizedFlux (nativeNeumannCoefficients ρ κ C)
        (nativeEvenExtension f) hF.weakGrad x =
        linearizedFlux (nativeNeumannCoefficients ρ κ C)
          (nativeEvenExtension f) (nativeEvenGradient (planarGradient f)) x := by
      unfold linearizedFlux
      rw [hxe]
      simp only [one_smul, nativeEvenGradient]
    rw [hfluxcongr, native_neumann_flux_off_flat ρ κ C f (planarGradient f) x hx hn, hxo]
    have hRx := normalReflection_maps_ball ρ hx
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · have hxU : x ∉ openHalfDisc ρ := fun hh => (not_lt_of_ge hneg.le) hh.2
      have hRU : normalReflection x ∈ openHalfDisc ρ :=
        ⟨hRx, by change 0 < normalReflection x 0; rw [normalReflection_zero]; linarith⟩
      simp only [nativeEvenReflectedFlux, indicator_of_notMem hxU, indicator_of_mem hRU,
        zero_add, if_neg (not_lt.mpr hneg.le), neg_one_smul]
      rw [hrel _ hRU, nativeQuarterTurn_odd_reflection]
    · have hxU : x ∈ openHalfDisc ρ := ⟨hx, hpos⟩
      have hRU : normalReflection x ∉ openHalfDisc ρ := by
        intro hh
        have hp : 0 < normalReflection x 0 := hh.2
        rw [normalReflection_zero] at hp
        linarith
      simp only [nativeEvenReflectedFlux, indicator_of_mem hxU, indicator_of_notMem hRU,
        map_zero, add_zero, if_pos hpos]
      exact hrel _ hxU
  intro ψ hs hc ht
  obtain ⟨hi, hzero⟩ := native_rotated_weak_gradient_divergence_zero _ _ hW ψ hs hc ht
  have hfluxI : IntegrableOn (fun x => inner ℝ (linearizedFlux (nativeNeumannCoefficients ρ κ C)
      (nativeEvenExtension f) hF.weakGrad x) (planarGradient ψ x)) (Metric.ball 0 ρ) := by
    apply hi.congr
    filter_upwards [hEq] with x hx
    rw [hx]
  refine ⟨hfluxI, by simp [linearizedSource, nativeNeumannCoefficients], ?_⟩
  have hEqInt : (fun x => inner ℝ (linearizedFlux (nativeNeumannCoefficients ρ κ C)
      (nativeEvenExtension f) hF.weakGrad x) (planarGradient ψ x) -
      linearizedSource (nativeNeumannCoefficients ρ κ C) (nativeEvenExtension f) hF.weakGrad x * ψ x) =ᵐ[
        volume.restrict (Metric.ball 0 ρ)] (fun x => inner ℝ (nativeQuarterTurn (hW.weakGrad x)) (planarGradient ψ x)) := by
    filter_upwards [hEq] with x hx
    rw [hx]
    simp only [linearizedSource, nativeNeumannCoefficients, ContinuousLinearMap.zero_apply,
      Pi.zero_apply, zero_mul, add_zero, sub_zero]
  exact (integral_congr_ae hEqInt).trans hzero

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
