import ActualAnnulusHalfSupportedClosedStripV848
import ActualNativeOriginalAnnulusOutsideCollarsV835
import ActualAnnulusHalfPolarModelV768

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped Manifold ContDiff
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualPlanarPolarCoordinatesV761
open CompressionActualAnnulusHalfPolarModelV768
noncomputable section
namespace CompressionActualAnnulusEmbeddingOpenMiddleV853

/-- The open middle of every embedded annulus is open in the native
    surface. Invariance of domain is applied to actual polar coordinates. -/
theorem annulus_embedding_open_middle (S : CompactOrientedSurface.{0})
    (c : C(Circle × Time,S)) (hc : IsEmbedding c) :
    IsOpen (c '' {p : Circle × Time | 0 < p.2.val ∧ p.2.val < 1}) := by
  let U : Set Plane := {x | 1 < ‖x‖ ∧ ‖x‖ < 2}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  let a : U → Circle × Time := fun x => (angle x.val,⟨‖x.val‖-1,by
    constructor <;> linarith [x.property.1,x.property.2]⟩)
  have hac : Continuous a := by
    apply Continuous.prodMk
    · apply angle_continuousOn.comp_continuous continuous_subtype_val
      intro x
      change x.val ≠ 0
      intro he
      have hn := x.property.1
      rw [he,norm_zero] at hn
      norm_num at hn
    · exact (continuous_subtype_val.norm.sub continuous_const).subtype_mk _
  have haid (x : U) : polar (a x) = x.val := by
    change (1+(‖x.val‖-1)) • circleVector (angle x.val) = x.val
    rw [show 1+(‖x.val‖-1) = ‖x.val‖ by ring]
    exact polar_reconstruction x.val (norm_ne_zero_iff.mp (by linarith [x.property.1]))
  have hai : Function.Injective a := by
    intro x y he
    exact Subtype.ext ((haid x).symm.trans ((congrArg polar he).trans (haid y)))
  let f : U → S := c ∘ a
  have hfo : IsOpen (range f) :=
    DifferentialGeometry.Topology.isOpen_range_of_isOpen_of_continuous_injective_real
      (𝓡∂ 2) hU f (c.continuous.comp hac) (hc.injective.comp hai)
  have heq : range f = c '' {p : Circle × Time | 0 < p.2.val ∧ p.2.val < 1} := by
    apply Subset.antisymm
    · rintro y ⟨x,rfl⟩
      exact ⟨a x,⟨by change 0 < ‖x.val‖-1; linarith [x.property.1],
        by change ‖x.val‖-1 < 1; linarith [x.property.2]⟩,rfl⟩
    · rintro y ⟨p,hp,rfl⟩
      let x : U := ⟨polar p,by
        change 1 < ‖polar p‖ ∧ ‖polar p‖ < 2
        rw [polar_norm]
        constructor <;> linarith [hp.1,hp.2]⟩
      have hax : a x = p := by
        apply Prod.ext
        · exact polar_angle p
        · apply Subtype.ext
          change ‖polar p‖-1 = p.2.val
          rw [polar_norm]
          ring
      exact ⟨x,congrArg c hax⟩
  exact heq ▸ hfo

#print axioms annulus_embedding_open_middle
end CompressionActualAnnulusEmbeddingOpenMiddleV853
