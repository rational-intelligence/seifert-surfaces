import NativeBoundarySecondOrderGain

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak

theorem native_swap_coordinateVector (i : Fin 2) :
    coordinateSwap (coordinateVector 2 i) = coordinateVector 2 (Equiv.swap (0 : Fin 2) 1 i) := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [coordinateSwap, coordinateVector]

theorem native_scalar_representative_holder_transfer
    (r s : ℝ) (hs : 0 < s) (hsr : s < r) (v w : E2 → ℝ)
    (hv : ContinuousOn v (closedHalfDisc r))
    (hw : ContDiffOn ℝ 1 w (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r))
    (hae : w =ᵐ[volume.restrict (halfDisc r)] (fun y => v (coordinateSwap y)))
    (α : ℝ≥0)
    (hH : ∀ j, ∃ C : ℝ≥0, HolderOnWith C α
      (fun y => fderivWithin ℝ w (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r) y
        (coordinateVector 2 j)) (SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r)) :
    ContDiffOn ℝ 1 v (closedHalfDisc s) ∧
      ∀ i, ∃ C : ℝ≥0, HolderOnWith C α
        (fun x => fderivWithin ℝ v (closedHalfDisc s) x (coordinateVector 2 i)) (closedHalfDisc s) := by
  let W := SeifertSurfaces.OriginalEndpoints.B1Tangency.closedHalfDisc r
  let K := closedHalfDisc s
  let wc := fun x => w (coordinateSwap x)
  have hmapR : MapsTo coordinateSwap (closedHalfDisc r) W := by
    intro x hx
    exact (Set.ext_iff.mp (native_swap_preimage_B1_closedHalfDisc r) x).mpr hx
  have hmap : MapsTo coordinateSwap K W := fun x hx => hmapR (closedHalfDisc_mono hsr.le hx)
  have hwc : ContDiffOn ℝ 1 wc (closedHalfDisc r) :=
    hw.comp coordinateSwap.contDiff.contDiffOn hmapR
  have hmp := coordinateSwap.measurePreserving.restrict_preimage
    (show MeasurableSet (halfDisc r) from Metric.isOpen_ball.measurableSet.inter
      ((isOpen_lt continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous).measurableSet))
  rw [native_swap_preimage_B1_halfDisc] at hmp
  have he : wc =ᵐ[volume.restrict (openHalfDisc r)] v := by
    filter_upwards [hmp.quasiMeasurePreserving.ae hae] with x hx
    simpa only [wc, coordinateSwap_involutive] using hx
  have heq : EqOn wc v K := native_same_continuous_representative_on_smaller_cap r s hsr v wc hv
    hwc.continuousOn he
  refine ⟨(hwc.mono (closedHalfDisc_mono hsr.le)).congr heq.symm, ?_⟩
  intro i
  obtain ⟨C, hC⟩ := hH (Equiv.swap (0 : Fin 2) 1 i)
  have hformula : ∀ x ∈ K,
      fderivWithin ℝ v K x (coordinateVector 2 i) =
        fderivWithin ℝ w W (coordinateSwap x) (coordinateVector 2 (Equiv.swap (0 : Fin 2) 1 i)) := by
    intro x hx
    rw [← fderivWithin_congr' heq hx]
    have hp : DifferentiableWithinAt ℝ coordinateSwap K x :=
      coordinateSwap.toContinuousLinearEquiv.hasFDerivAt.differentiableAt.differentiableWithinAt
    have hdf := fderivWithin_comp x (hw.differentiableOn (by norm_num) _ (hmap hx)) hp hmap
      (closedHalfDisc_uniqueDiffOn hs x hx)
    have hPder : fderivWithin ℝ coordinateSwap K x = coordinateSwap.toContinuousLinearEquiv.toContinuousLinearMap :=
      coordinateSwap.toContinuousLinearEquiv.hasFDerivAt.hasFDerivWithinAt.fderivWithin
        (closedHalfDisc_uniqueDiffOn hs x hx)
    change fderivWithin ℝ (w ∘ coordinateSwap) K x (coordinateVector 2 i) = _
    rw [hdf, hPder, ContinuousLinearMap.comp_apply]
    change fderivWithin ℝ w W (coordinateSwap x) (coordinateSwap (coordinateVector 2 i)) = _
    rw [native_swap_coordinateVector]
  refine ⟨C, ?_⟩
  intro x hx y hy
  have hh := hC (coordinateSwap x) (hmap hx) (coordinateSwap y) (hmap hy)
  have hdist : edist (coordinateSwap x) (coordinateSwap y) = edist x y :=
    coordinateSwap.isometry.edist_eq _ _
  change edist ((fderivWithin ℝ v K x) (coordinateVector 2 i))
      ((fderivWithin ℝ v K y) (coordinateVector 2 i)) ≤ _
  rw [hformula x hx, hformula y hy]
  simpa only [Function.comp_def, hdist] using hh

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
