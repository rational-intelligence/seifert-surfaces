import SectorPieces
import Mathlib.Analysis.SpecialFunctions.PolarCoord

open scoped Manifold ContDiff Pointwise
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.MetricFoundations
open Foundations
set_option maxSynthPendingDepth 3
set_option allowUnsafeReducibility true in
attribute [local reducible] sectorUnit

theorem planarSector_uniqueDiffWithinAt_zero {θ : ℝ}
    (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi) :
    UniqueDiffWithinAt ℝ (planarSector θ) 0 := by
  let α := θ / 2
  have hα : 0 < α := by dsimp [α]; linarith
  have hαπ : α < Real.pi := by dsimp [α]; linarith
  have hαθ : α ≤ θ := by dsimp [α]; linarith
  have hsin : Real.sin α ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hα hαπ)
  have hunit (t : ℝ) (ht : t ∈ Icc 0 θ) :
      sectorUnit t ∈ tangentConeAt ℝ (planarSector θ) 0 := by
    have hseg : segment ℝ (0 : Euc 2) (sectorUnit t) ⊆ planarSector θ := by
      rw [segment_eq_image_lineMap]
      rintro z ⟨r, hr, rfl⟩
      exact ⟨r, hr.1, t, ht, by simp [AffineMap.lineMap_apply_module']⟩
    simpa using mem_tangentConeAt_of_segment_subset hseg
  have hspan : Submodule.span ℝ (tangentConeAt ℝ (planarSector θ) (0 : Euc 2)) = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro v
    have hu0 : sectorUnit 0 ∈
        Submodule.span ℝ (tangentConeAt ℝ (planarSector θ) (0 : Euc 2)) :=
      Submodule.subset_span (hunit 0 ⟨le_rfl, hθ.le⟩)
    have huα : sectorUnit α ∈
        Submodule.span ℝ (tangentConeAt ℝ (planarSector θ) (0 : Euc 2)) :=
      Submodule.subset_span (hunit α ⟨hα.le, hαθ⟩)
    have hv := (Submodule.span ℝ (tangentConeAt ℝ (planarSector θ) (0 : Euc 2))).add_mem
      ((Submodule.span ℝ _).smul_mem (v 0 - v 1 * Real.cos α / Real.sin α) hu0)
      ((Submodule.span ℝ _).smul_mem (v 1 / Real.sin α) huα)
    convert hv using 1
    ext k
    fin_cases k <;> simp [sectorUnit]
    · field_simp
      <;> ring
    · exact (div_mul_cancel₀ (v 1) hsin).symm
  refine ⟨?_, subset_closure ?_⟩
  · rw [hspan]
    simp
  · exact ⟨0, le_rfl, 0, ⟨le_rfl, hθ.le⟩, by simp⟩

theorem planarSector_uniqueDiffOn {θ : ℝ}
    (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi) :
    UniqueDiffOn ℝ (planarSector θ) := by
  intro x hx
  rcases hx with ⟨r, hr, t, ht, rfl⟩
  rcases eq_or_lt_of_le hr with hr | hr
  · subst r
    simpa using planarSector_uniqueDiffWithinAt_zero hθ hθπ
  · let L : (ℝ × ℝ) ≃L[ℝ] Euc 2 :=
      (LinearEquiv.finTwoArrow ℝ ℝ).symm.toContinuousLinearEquiv.trans
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm
    let f : ℝ × ℝ → Euc 2 := L ∘ polarCoord.symm
    let s : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Icc (0 : ℝ) θ
    have hq : (r, t) ∈ s := ⟨hr, ht⟩
    have hu : UniqueDiffWithinAt ℝ s (r, t) :=
      (uniqueDiffOn_Ioi (0 : ℝ) r hr).prod (uniqueDiffOn_Icc hθ t ht)
    have hp := hasFDerivAt_polarCoord_symm (r, t)
    have hf := L.hasFDerivAt.comp (r, t) hp
    have hdet : (fderivPolarCoordSymm (r, t)).det ≠ 0 := by
      rw [det_fderivPolarCoordSymm]
      exact hr.ne'
    have hd : Function.Surjective
        (L.toContinuousLinearMap.comp (fderivPolarCoordSymm (r, t))) := by
      exact L.surjective.comp
        ((fderivPolarCoordSymm (r, t)).toContinuousLinearEquivOfDetNeZero hdet).surjective
    have himage : f '' s ⊆ planarSector θ := by
      rintro y ⟨⟨a, b⟩, hab, rfl⟩
      refine ⟨a, hab.1.le, b, hab.2, ?_⟩
      ext k
      fin_cases k <;> simp [f, L, polarCoord, sectorUnit, LinearEquiv.finTwoArrow]
    have hpoint : f (r, t) = r • sectorUnit t := by
      ext k
      fin_cases k <;> simp [f, L, polarCoord, sectorUnit, LinearEquiv.finTwoArrow]
    rw [← hpoint]
    exact (hf.hasFDerivWithinAt.uniqueDiffWithinAt hu hd.denseRange).mono himage

theorem SectorModel.uniqueDiffOn_domain (A : SectorModel) :
    UniqueDiffOn ℝ A.domain := by
  intro y hy
  unfold SectorModel.domain at hy ⊢
  split_ifs at hy ⊢ with h
  · simp only [inter_univ] at hy ⊢
    exact Metric.isOpen_ball.uniqueDiffWithinAt hy
  · rw [inter_comm]
    exact (planarSector_uniqueDiffOn A.angle_positive A.angle_lt_two_pi y hy.2).inter
      (Metric.isOpen_ball.mem_nhds hy.1)

end SeifertSurfaces.MetricFoundations
