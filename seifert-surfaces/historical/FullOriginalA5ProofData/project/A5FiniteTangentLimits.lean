import A5BoundaryPuncturedTopology
import A5FiniteVertexLimits
import A5GraphGluing
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations

/-- An invertible transverse projection canonically normalizes a rank-two
parametrization differential into a section with the same tangent range. -/
theorem transverse_differential_normalization
    (D : Euc 2 →L[ℝ] Euc 3) (P : Euc 3 →L[ℝ] Euc 2)
    (hP : Function.Bijective (P.comp D)) :
    P.comp (D.comp (P.comp D).inverse) = ContinuousLinearMap.id ℝ (Euc 2) ∧
      (D.comp (P.comp D).inverse).toLinearMap.range = D.toLinearMap.range := by
  let L := ContinuousLinearEquiv.ofBijective (P.comp D)
    (LinearMap.ker_eq_bot.mpr hP.1) (LinearMap.range_eq_top.mpr hP.2)
  have hi : (P.comp D).IsInvertible := ⟨L,rfl⟩
  refine ⟨?_,?_⟩
  · apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun A : Euc 2 →L[ℝ] Euc 2 => A v) hi.self_comp_inverse
  · apply le_antisymm
    · rintro v ⟨w,rfl⟩
      exact ⟨(P.comp D).inverse w,rfl⟩
    · rintro v ⟨w,rfl⟩
      refine ⟨(P.comp D) w,?_⟩
      change D ((P.comp D).inverse ((P.comp D) w)) = D w
      rw [hi.inverse_apply_self]

/-- Transverse normalized differentials are continuous wherever the original
actual differential is continuous. -/
theorem continuousWithinAt_normalized_differential
    {X : Type*} [TopologicalSpace X]
    (D : X → Euc 2 →L[ℝ] Euc 3) (P : Euc 3 →L[ℝ] Euc 2)
    (A : Set X) (x : X) (hD : ContinuousWithinAt D A x)
    (hP : Function.Bijective (P.comp (D x))) :
    ContinuousWithinAt (fun y => (D y).comp (P.comp (D y)).inverse) A x := by
  let L := ContinuousLinearEquiv.ofBijective (P.comp (D x))
    (LinearMap.ker_eq_bot.mpr hP.1) (LinearMap.range_eq_top.mpr hP.2)
  have hi : (P.comp (D x)).IsInvertible := ⟨L,rfl⟩
  have hPcont : ContinuousWithinAt (fun y => P.comp (D y)) A x :=
    continuousWithinAt_const.clm_comp hD
  have hInv : ContinuousAt (fun A : Euc 2 →L[ℝ] Euc 2 => A.inverse) (P.comp (D x)) :=
    (hi.contDiffAt_map_inverse (n := ∞)).continuousAt
  have hInvComp : ContinuousWithinAt (fun y => (P.comp (D y)).inverse) A x :=
    hInv.comp_continuousWithinAt (f := fun y => P.comp (D y)) hPcont
  exact hD.clm_comp hInvComp

/-- Equality of tangent ranges off a single point forces equality at that
point for finitely many incident closed pieces of a native surface. This
also applies at its boundary, before any graph homeomorphism is constructed. -/
theorem finite_native_incident_tangent_limits_agree
    {ι : Type*} [Finite ι]
    (S : CompactOrientedSurface) (x : S)
    (regions : ι → Set S) (hclosed : ∀ i, IsClosed (regions i))
    (hcover : (⋃ i, regions i) ∈ 𝓝 x)
    (hincident : ∀ i, x ∈ regions i)
    (hacc : ∀ i, x ∈ closure (regions i \ {x}))
    (D : ι → S → Euc 2 →L[ℝ] Euc 3)
    (hD : ∀ i, ContinuousWithinAt (D i) (regions i) x)
    (P : Euc 3 →L[ℝ] Euc 2)
    (hP : ∀ i y, y ∈ regions i → Function.Bijective (P.comp (D i y)))
    (hmatch : ∀ i j y, y ∈ regions i → y ∈ regions j → y ≠ x →
      (D i y).toLinearMap.range = (D j y).toLinearMap.range) :
    ∀ i j, (D i x).toLinearMap.range = (D j x).toLinearMap.range := by
  let B := fun i y => (D i y).comp (P.comp (D i y)).inverse
  have hBc (i : ι) : ContinuousWithinAt (B i) (regions i) x :=
    continuousWithinAt_normalized_differential (D i) P (regions i) x (hD i)
      (hP i x (hincident i))
  have hBm (i j : ι) (y : S) (hi : y ∈ regions i) (hj : y ∈ regions j) (hne : y ≠ x) :
      B i y = B j y := by
    have hiN := transverse_differential_normalization (D i y) P (hP i y hi)
    have hjN := transverse_differential_normalization (D j y) P (hP j y hj)
    exact section_derivatives_eq_of_range_eq P (B i y) (B j y) hiN.1 hjN.1
      (hiN.2.trans ((hmatch i j y hi hj hne).trans hjN.2.symm))
  have hBeq := finite_incident_limits_agree x regions hclosed hcover hacc B hBc hBm
    (native_surface_punctured_neighborhoods S x)
  intro i j
  have hiN := (transverse_differential_normalization (D i x) P (hP i x (hincident i))).2
  have hjN := (transverse_differential_normalization (D j x) P (hP j x (hincident j))).2
  exact hiN.symm.trans ((congrArg (fun L : Euc 2 →L[ℝ] Euc 3 => L.toLinearMap.range)
    (hBeq i j)).trans hjN)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
