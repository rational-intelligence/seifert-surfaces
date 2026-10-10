import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualShrunkAxisRectangleExtension
namespace CurveComplex
open Set Topology Schoenflies

/-- An actual supported change of coordinates straightens a narrowed embedded
rectangle, fixes its entire center axis, and chooses the required side sign. -/
theorem source_axis_rectangle_transplant
    (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
    (hc : ∀ t : Icc (-1 : ℝ) 1,
      B ⟨Plane.mk t 0, by
        simpa [Plane.closedSquare, Plane.supDist, Plane.supNorm] using abs_le.mpr t.property⟩ =
        Plane.mk t 0)
    (hmeet : Set.range B ∩ {z : Plane | z 1 = 0} =
      (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ ∧ δ ≤ 1,
    ∃ σ : ℝ, ∃ G : Plane ≃ₜ Plane,
      (σ = -1 ∨ σ = 1) ∧
      (∀ z, z ∉ Plane.openSquare 0 2 → G z = z) ∧
      (∀ t : ℝ, G (Plane.mk t 0) = Plane.mk t 0) ∧
      ∀ z : ↥(Plane.closedSquare 0 1),
        G (B ⟨Plane.mk (z.val 0) (δ * z.val 1), by
          have hz : max |z.val 0| |z.val 1| ≤ 1 := by
            simpa [Plane.closedSquare, Plane.supDist, Plane.supNorm] using z.property
          have hx := (le_max_left _ _).trans hz
          have hy := (le_max_right _ _).trans hz
          simpa [Plane.closedSquare, Plane.supDist, Plane.supNorm, abs_mul,
            abs_of_pos hδ.1] using
            max_le hx ((mul_le_mul_of_nonneg_left hy hδ.1.le).trans
              (by simpa using hδ.2))⟩) = Plane.mk (z.val 0) (σ * z.val 1) := by
  obtain ⟨δ, hδ, flip, H, hfix, haxis, hformula⟩ :=
    source_shrunk_axis_rectangle_supported_extension B hB hc hmeet
  refine ⟨δ, hδ, (if flip then -1 else 1), H.symm, ?_, ?_, ?_, ?_⟩
  · cases flip <;> simp
  · intro z hz
    apply H.injective
    rw [H.apply_symm_apply, hfix z hz]
  · intro t
    apply H.injective
    rw [H.apply_symm_apply, haxis t]
  · intro z
    have hh := congrArg H.symm (hformula z)
    rw [H.symm_apply_apply] at hh
    rw [← hh]
    cases flip <;> simp
end CurveComplex
#print axioms CurveComplex.source_axis_rectangle_transplant
