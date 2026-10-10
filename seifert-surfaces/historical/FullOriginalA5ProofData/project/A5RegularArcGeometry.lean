import A5RegularCurveSignedGeometry

set_option autoImplicit false
open scoped ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC CurvedDivergence

theorem nonzero_planar_vector_transverse_frame (v : E2) (hv : v ≠ 0) :
    ∃ w : E2, Function.Bijective
      ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).smulRight v +
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).smulRight w) := by
  let w := v 1 • coordinateVector 2 0 - v 0 • coordinateVector 2 1
  let D := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).smulRight v +
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).smulRight w
  have hpos : 0 < (v 0) ^ 2 + (v 1) ^ 2 := by
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        ext k
        fin_cases k <;> simp [h0, h1]
      nlinarith [sq_pos_of_ne_zero h1]
    · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (v 1)]
  have hinj : Function.Injective D := by
    apply (injective_iff_map_eq_zero D).mpr
    intro z hz
    have h0 := congrArg (fun y : E2 => y 0) hz
    have h1 := congrArg (fun y : E2 => y 1) hz
    simp [D, w, coordinateVector, EuclideanSpace.single] at h0 h1
    have he0 : z 0 * ((v 0) ^ 2 + (v 1) ^ 2) = 0 := by
      linear_combination v 1 * h0 - v 0 * h1
    have he1 : z 1 * ((v 0) ^ 2 + (v 1) ^ 2) = 0 := by
      linear_combination v 0 * h0 + v 1 * h1
    have hz0 : z 0 = 0 := (mul_eq_zero.mp he0).resolve_right (ne_of_gt hpos)
    have hz1 : z 1 = 0 := (mul_eq_zero.mp he1).resolve_right (ne_of_gt hpos)
    ext k
    fin_cases k <;> simp [hz0, hz1]
  exact ⟨w, hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- A regular smooth projected seam curve alone constructs the whole
signed-arc geometry needed by the curved Green theorem. -/
theorem local_signed_geometry_of_regular_curve
    (γ : ℝ → E2) (I : Set ℝ) (hI : IsOpen I) (hzero : (0 : ℝ) ∈ I)
    (hγ : ContDiffOn ℝ ∞ γ I) (hregular : deriv γ 0 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ left right : ℝ, left < 0 ∧ 0 < right ∧
      ∃ s : E2 → ℝ, SignedArcGeometry (Metric.ball (γ 0) r) s γ left right := by
  obtain ⟨w, hw⟩ := nonzero_planar_vector_transverse_frame (deriv γ 0) hregular
  exact signed_arc_geometry_near_regular_curve γ I hI hzero hγ (deriv γ 0) w
    ((hγ.contDiffAt (hI.mem_nhds hzero)).differentiableAt (by simp)).hasDerivAt hw

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
