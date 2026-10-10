import NativeBoundaryFirstOrderCoefficientHolder

set_option autoImplicit false
set_option maxHeartbeats 50000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem native_holder_derivative_apply_const
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set E2) (f : E2 → F) (α : ℝ≥0)
    (hH : ∃ C, HolderOnWith C α (fderivWithin ℝ f K) K) (ξ : E2) :
    ∃ C, HolderOnWith C α (fun x => fderivWithin ℝ f K x ξ) K := by
  obtain ⟨C, hC⟩ := hH
  let L : (E2 →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F ξ
  exact ⟨‖L‖₊ * C, native_holder_comp_linear K _ C α hC L⟩

theorem native_cap_C1_holder_comp_linear
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (K : Set E2) (hKD : UniqueDiffOn ℝ K) (f : E2 → F) (α : ℝ≥0)
    (hf : ContDiffOn ℝ 1 f K) (hH : ∃ C, HolderOnWith C α (fderivWithin ℝ f K) K)
    (L : F →L[ℝ] G) :
    ContDiffOn ℝ 1 (fun x => L (f x)) K ∧
      ∃ C, HolderOnWith C α (fderivWithin ℝ (fun x => L (f x)) K) K := by
  refine ⟨L.contDiff.comp_contDiffOn hf, ?_⟩
  apply native_clm_holder_of_coordinate_evaluations
  intro i
  obtain ⟨C, hC⟩ := native_holder_derivative_apply_const K f α hH (coordinateVector 2 i)
  have hCL := native_holder_comp_linear K _ C α hC L
  refine ⟨‖L‖₊ * C, ?_⟩
  have hEq (x : E2) (hx : x ∈ K) :
      fderivWithin ℝ (fun y => L (f y)) K x (coordinateVector 2 i) =
        L (fderivWithin ℝ f K x (coordinateVector 2 i)) := by
    have hd := L.hasFDerivAt.comp_hasFDerivWithinAt x
      ((hf.differentiableOn (by norm_num) x hx).hasFDerivWithinAt)
    exact congrArg (fun A : E2 →L[ℝ] G => A (coordinateVector 2 i)) (hd.fderivWithin (hKD x hx))
  intro x hx y hy
  change edist (fderivWithin ℝ (fun y => L (f y)) K x (coordinateVector 2 i))
    (fderivWithin ℝ (fun y => L (f y)) K y (coordinateVector 2 i)) ≤ _
  rw [hEq x hx, hEq y hy]
  exact hCL x hx y hy

theorem native_cap_C1_holder_add
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set E2) (hKD : UniqueDiffOn ℝ K) (f g : E2 → F) (α : ℝ≥0)
    (hf : ContDiffOn ℝ 1 f K) (hg : ContDiffOn ℝ 1 g K)
    (hF : ∃ C, HolderOnWith C α (fderivWithin ℝ f K) K)
    (hG : ∃ C, HolderOnWith C α (fderivWithin ℝ g K) K) :
    ContDiffOn ℝ 1 (fun x => f x + g x) K ∧
      ∃ C, HolderOnWith C α (fderivWithin ℝ (fun x => f x + g x) K) K := by
  obtain ⟨A, hA⟩ := hF
  obtain ⟨B, hB⟩ := hG
  refine ⟨hf.add hg, A + B, ?_⟩
  have hsum := native_holder_add K _ _ A B α hA hB
  have hEq (x : E2) (hx : x ∈ K) :=
    fderivWithin_fun_add (hKD x hx) (hf.differentiableOn (by norm_num) x hx)
      (hg.differentiableOn (by norm_num) x hx)
  intro x hx y hy
  change edist (fderivWithin ℝ (fun y => f y + g y) K x)
    (fderivWithin ℝ (fun y => f y + g y) K y) ≤ _
  rw [hEq x hx, hEq y hy]
  exact hsum x hx y hy

theorem native_cap_C1_holder_clm_apply
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c : E2) (hcf : c 0 = 0) (r : ℝ) (hr : 0 < r)
    (a : E2 → F →L[ℝ] G) (v : E2 → F) (α : ℝ≥0) (hα : 0 < α) (hα1 : α ≤ 1)
    (ha : ContDiffOn ℝ 1 a (nativeClosedBoundaryCap c r))
    (hv : ContDiffOn ℝ 1 v (nativeClosedBoundaryCap c r))
    (hDa : ∃ C, HolderOnWith C α (fderivWithin ℝ a (nativeClosedBoundaryCap c r))
      (nativeClosedBoundaryCap c r))
    (hDv : ∃ C, HolderOnWith C α (fderivWithin ℝ v (nativeClosedBoundaryCap c r))
      (nativeClosedBoundaryCap c r)) :
    ContDiffOn ℝ 1 (fun x => a x (v x)) (nativeClosedBoundaryCap c r) ∧
      ∃ C, HolderOnWith C α (fderivWithin ℝ (fun x => a x (v x)) (nativeClosedBoundaryCap c r))
        (nativeClosedBoundaryCap c r) := by
  let K := nativeClosedBoundaryCap c r
  have hKD := nativeClosedBoundaryCap_uniqueDiffOn c r hr hcf
  have hK : IsCompact K := (isCompact_closedBall c r).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  obtain ⟨A, hA⟩ := native_contDiffOn_cap_holder c r hr a α hα1 ha
  obtain ⟨B, hB⟩ := native_contDiffOn_cap_holder c r hr v α hα1 hv
  refine ⟨ha.clm_apply hv, ?_⟩
  apply native_clm_holder_of_coordinate_evaluations
  intro i
  obtain ⟨Ca, hCa⟩ := native_holder_derivative_apply_const K a α hDa (coordinateVector 2 i)
  obtain ⟨Cv, hCv⟩ := native_holder_derivative_apply_const K v α hDv (coordinateVector 2 i)
  obtain ⟨P, hP⟩ := native_compact_holder_clm_apply_exists K hK a
    (fun x => fderivWithin ℝ v K x (coordinateVector 2 i)) α hα ⟨A, hA⟩ ⟨Cv, hCv⟩
  obtain ⟨R, hR⟩ := native_compact_holder_clm_apply_exists K hK
    (fun x => fderivWithin ℝ a K x (coordinateVector 2 i)) v α hα ⟨Ca, hCa⟩ ⟨B, hB⟩
  have hsum := native_holder_add K _ _ P R α hP hR
  refine ⟨P + R, ?_⟩
  have hEq (x : E2) (hx : x ∈ K) :
      fderivWithin ℝ (fun y => a y (v y)) K x (coordinateVector 2 i) =
        a x (fderivWithin ℝ v K x (coordinateVector 2 i)) +
          fderivWithin ℝ a K x (coordinateVector 2 i) (v x) := by
    rw [fderivWithin_clm_apply (hKD x hx) (ha.differentiableOn (by norm_num) x hx)
      (hv.differentiableOn (by norm_num) x hx)]
    rfl
  intro x hx y hy
  change edist (fderivWithin ℝ (fun y => a y (v y)) K x (coordinateVector 2 i))
    (fderivWithin ℝ (fun y => a y (v y)) K y (coordinateVector 2 i)) ≤ _
  rw [hEq x hx, hEq y hy]
  exact hsum x hx y hy

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
