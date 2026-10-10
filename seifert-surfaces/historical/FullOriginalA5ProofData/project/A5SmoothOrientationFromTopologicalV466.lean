import A5SignedFiniteRefinementV466
import A5BoundarySignExtensionV466

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
open SeifertSurfaces.Foundations
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
universe u

/-- Any smooth halfspace atlas on the same oriented topological surface admits an actual smooth volume form. -/
theorem a5_smooth_orientation_from_oriented_topology
    (R : CompactOrientedSurface.{0}) (S : A5CompactSmoothCarrier.{u}) (h : R ≃ₜ S) :
    Nonempty (SmoothVolumeOrientation (𝓡∂ 2) S) := by
  classical
  choose U hUopen hUp hUsub hUconn hUnon using
    fun p : S => a5_connected_interior_chart_neighborhood S p
  choose a ha using hUnon
  have haplane : ∀ p, a p ∈ (a5NativeComplexChart S p).source := by
    intro p
    exact (a5_native_complex_chart_source S p (a p)).mpr ⟨hUsub p (ha p).1,(ha p).2⟩
  let σ : S → ℝ := fun p => a5TransportedChartSign R S h p ⟨a p,haplane p⟩
  have hσunit : ∀ p, σ p = 1 ∨ σ p = -1 :=
    fun p => a5TransportedChartSign_unit R S h p ⟨a p,haplane p⟩
  have hconstant : ∀ p x (hx : x ∈ U p) (hi : (𝓡∂ 2).IsInteriorPoint x),
      a5TransportedChartSign R S h p
        ⟨x,(a5_native_complex_chart_source S p x).mpr ⟨hUsub p hx,hi⟩⟩ = σ p := by
    intro p x hx hi
    let W := U p ∩ (𝓡∂ 2).interior S
    letI : PreconnectedSpace W := Subtype.preconnectedSpace (hUconn p)
    let g : W → (a5NativeComplexChart S p).source := fun z =>
      ⟨z.val,(a5_native_complex_chart_source S p z.val).mpr ⟨hUsub p z.property.1,z.property.2⟩⟩
    have hg : Continuous g := continuous_subtype_val.subtype_mk _
    have hlc := (a5TransportedChartSign_locally_constant R S h p).comp_continuous hg
    exact hlc.apply_eq_of_preconnectedSpace (⟨x,hx,hi⟩ : W) (⟨a p,ha p⟩ : W)
  have hpositiveInterior : ∀ p q x, x ∈ U p → x ∈ U q → (𝓡∂ 2).IsInteriorPoint x →
      0 < σ q * σ p * (a5TransitionJacobian S p q x).det := by
    intro p q x hp hq hi
    have hpx := (a5_native_complex_chart_source S p x).mpr ⟨hUsub p hp,hi⟩
    have hqx := (a5_native_complex_chart_source S q x).mpr ⟨hUsub q hq,hi⟩
    have ht := a5TransportedChartSign_positive_transition R S h p q x hpx hqx
    rw [hconstant p x hp hi,hconstant q x hq hi] at ht
    exact ht
  have hpositive : ∀ p q x, x ∈ U p → x ∈ U q →
      0 < σ q * σ p * (a5TransitionJacobian S p q x).det := by
    intro p q
    exact a5_positive_transition_boundary_extension S p q (U p) (U q)
      (hUopen p) (hUopen q) (hUsub p) (hUsub q) (σ p) (σ q)
      (hσunit p) (hσunit q) (hpositiveInterior p q)
  obtain ⟨C⟩ := a5_signed_finite_refinement S U hUopen hUp hUsub σ hσunit hpositive
  obtain ⟨O,_⟩ := a5_signed_chart_orientation_exists S C
  exact ⟨O⟩

#print axioms a5_smooth_orientation_from_oriented_topology
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
