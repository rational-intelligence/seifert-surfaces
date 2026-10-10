import A5NativeBoundaryProjectedClock

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u

/-- The original longitude gives a smooth regular boundary clock covering
the entire native boundary in an actual open source neighborhood. This is
the exact trace coverage required by the boundary straightener. -/
theorem native_longitude_boundary_clock_with_coverage
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (J : LongitudeFoliation.{u} E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (hF : J.BoundaryIn F.map)
    (x : S) (hx : x ∈ S.boundary) :
    ∃ b : ℝ → S, b 0 = x ∧ ContinuousOn b (Ioo (-1 : ℝ) 1) ∧
      (∀ t, b t ∈ S.boundary) ∧
      IsEmbedding (fun t : Ioo (-1 : ℝ) 1 => b t) ∧
      ContMDiffOn 𝓘(ℝ) (𝓡 3) ∞ (E.toSphere ∘ F.map ∘ b) (Ioo (-1 : ℝ) 1) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 1,
        mfderiv 𝓘(ℝ) (𝓡 3) (E.toSphere ∘ F.map ∘ b) t 1 ≠ 0) ∧
      ∃ U : Set S, IsOpen U ∧ x ∈ U ∧
        range (fun t : Ioo (-1 : ℝ) 1 => b t) = U ∩ S.boundary := by
  obtain ⟨a,B,hBi,hBr,_,hBs,hBd⟩ := native_longitude_boundary_circle E J F hF
  obtain ⟨s,hs⟩ := (show x ∈ range B by rwa [hBr])
  obtain ⟨q,hq0,hqi,hqo,hqs,hqd⟩ := native_smooth_circle_centered_clock s
  let b := B ∘ q
  have hb0 : b 0 = x := by change B (q 0) = x; rw [hq0,hs]
  obtain ⟨U,hU,hUr⟩ := hBi.isInducing.image_eq_isOpen_inter_range hqo
  have hcover : range (fun t : Ioo (-1 : ℝ) 1 => b t) = U ∩ S.boundary := by
    rw [← hBr,← hUr]
    exact (range_comp B (fun t : Ioo (-1 : ℝ) 1 => q t))
  refine ⟨b,hb0,B.continuous.comp_continuousOn hqs.continuousOn,?_,hBi.comp hqi,
    hBs.comp_contMDiffOn hqs,?_,U,hU,?_,hcover⟩
  · intro t
    rw [← hBr]
    exact mem_range_self (q t)
  · intro t ht
    change mfderiv 𝓘(ℝ) (𝓡 3) ((E.toSphere ∘ F.map ∘ B) ∘ q) t 1 ≠ 0
    rw [mfderiv_comp _ (hBs.mdifferentiable (by simp) _)
      ((hqs.contMDiffAt (isOpen_Ioo.mem_nhds ht)).mdifferentiableAt (by simp))]
    intro he
    apply hqd t ht
    exact (hBd (q t)) (he.trans (map_zero _).symm)
  · have hh : x ∈ range (fun t : Ioo (-1 : ℝ) 1 => b t) :=
      ⟨⟨0,neg_one_lt_zero,zero_lt_one⟩,hb0⟩
    rw [hcover] at hh
    exact hh.1

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
