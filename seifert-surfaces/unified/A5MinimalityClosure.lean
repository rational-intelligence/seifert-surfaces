import A5NativeVertexRemoval
import HopfAdapters.Coefficients

set_option autoImplicit false
open scoped Manifold ContDiff BigOperators
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates HopfAdapters

/-- The actual coordinate mean-curvature trace varies continuously on a
smooth regular patch, with the actual positive metric and its inverse. -/
theorem traced_acceleration_continuous_on
    (V : Set E3) (hV : IsOpen V) (g : CoordinateMetric V)
    (U : Set E2) (hU : IsOpen U) (Φ : E2 → E3)
    (hΦ : ContDiffOn ℝ ∞ Φ U) (himage : MapsTo Φ U V)
    (hrank : ∀ x ∈ U, Function.Injective (fderiv ℝ Φ x)) :
    ContinuousOn (tracedAcceleration g.tensor Φ) U := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ Φ) U := hΦ.fderiv_of_isOpen hU (by simp)
  have hT (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => graphTangent Φ x i) U :=
    hD.clm_apply contDiffOn_const
  have hTcomp (i : Fin 2) (a : Fin 3) :
      ContinuousOn (fun x => graphTangent Φ x i a) U :=
    (EuclideanSpace.proj a : E3 →L[ℝ] ℝ).continuous.comp_continuousOn (hT i).continuousOn
  have hinv : ContinuousOn (fun x => (inducedMetric g.tensor Φ x)⁻¹) U :=
    (inverse_gram_continuous_posDef V g U Φ (fderiv ℝ Φ) hΦ.continuousOn
      hD.continuousOn himage hrank).1
  have hΓ (a b k : Fin 3) : ContinuousOn (fun x => christoffel g.tensor (Φ x) a b k) U :=
    (christoffel_continuous V hV g a b k).comp hΦ.continuousOn himage
  have hacc (i j : Fin 2) : ContinuousOn (fun x => covariantAcceleration g.tensor Φ x i j) U := by
    apply ContinuousOn.add
    · exact ((hT j).continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
    · apply continuousOn_finsetSum
      intro k hk
      have hscalar : ContinuousOn (fun x => ∑ a : Fin 3, ∑ b : Fin 3,
          christoffel g.tensor (Φ x) a b k * graphTangent Φ x i a * graphTangent Φ x j b) U := by
        apply continuousOn_finsetSum
        intro a ha
        apply continuousOn_finsetSum
        intro b hb
        exact ((hΓ a b k).mul (hTcomp i a)).mul (hTcomp j b)
      exact hscalar.smul continuousOn_const
  unfold tracedAcceleration
  apply continuousOn_finsetSum
  intro i hi
  apply continuousOn_finsetSum
  intro j hj
  exact (continuousOn_pi.mp (continuousOn_pi.mp hinv i) j).smul (hacc i j)

/-- For a projected immersion, genuine minimality extends from a dense
subset by continuity of the actual trace and the exact tangent projection. -/
theorem coordinate_minimality_of_dense_projected_patch
    (V : Set E3) (hV : IsOpen V) (g : CoordinateMetric V)
    (U W : Set E2) (hU : IsOpen U) (hWU : W ⊆ U) (hdense : U ⊆ closure W)
    (Φ : E2 → E3) (hΦ : ContDiffOn ℝ ∞ Φ U) (himage : MapsTo Φ U V)
    (P : E3 →L[ℝ] E2)
    (hP : ∀ x ∈ U, P.comp (fderiv ℝ Φ x) = ContinuousLinearMap.id ℝ E2)
    (hminimal : IsMinimalParametrizationOn g.tensor Φ W) :
    IsMinimalParametrizationOn g.tensor Φ U := by
  have hrank (x : E2) (hx : x ∈ U) : Function.Injective (fderiv ℝ Φ x) := by
    have hi : Function.Injective (P.comp (fderiv ℝ Φ x)) := by
      rw [hP x hx]
      exact Function.injective_id
    exact Function.Injective.of_comp hi
  have ht := traced_acceleration_continuous_on V hV g U hU Φ hΦ himage hrank
  let R : E2 → E3 := fun x => (fderiv ℝ Φ x) (P (tracedAcceleration g.tensor Φ x)) -
    tracedAcceleration g.tensor Φ x
  have hR : ContinuousOn R U :=
    ((hΦ.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply
      (P.continuous.comp_continuousOn ht)).sub ht
  have hz (x : E2) (hx : x ∈ W) : R x = 0 := by
    obtain ⟨v, hv⟩ := hminimal.2 x hx
    change (fderiv ℝ Φ x) v = tracedAcceleration g.tensor Φ x at hv
    have hp : P ((fderiv ℝ Φ x) v) = v :=
      congrArg (fun D : E2 →L[ℝ] E2 => D v) (hP x (hWU hx))
    dsimp [R]
    rw [← hv, hp, sub_self]
  refine ⟨hΦ, ?_⟩
  intro x hx
  have he : R x = 0 :=
    (hR.continuousAt (hU.mem_nhds hx)).continuousWithinAt.eq_const_of_mem_closure (hdense hx) hz
  exact ⟨P (tracedAcceleration g.tensor Φ x), sub_eq_zero.mp he⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
