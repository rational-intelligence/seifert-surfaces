import B1ActualInteriorSlice_v475
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe u
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The actual slice shrinking also retains that an interior source point
lies over the interior of the planar model half-space. -/
theorem native_actual_slice_of_complement_with_base_v475
    {S : CompactOrientedSurface.{u}} {f : S → ThreeSphere} {x : S}
    (h : Manifold.IsImmersionAtOfComplement ℝ (𝓡∂ 2) (𝓡 3) ∞ f x)
    (hf : IsInducing f) (hxi : (𝓡∂ 2).IsInteriorPoint x) :
    ∃ Φ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ), f x ∈ Φ.source ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Φ Φ.source ∧
      ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target ∧
      Φ '' (Φ.source ∩ range f)=Φ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) ∧
      (Φ (f x)).1 ∈ interior (range (𝓡∂ 2)) := by
  -- The ambient chart of the immersion, read in the splitting `E2 × ℝ` of the ambient model space.
  let Ψ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ) :=
    h.codChart.transHomeomorph ((𝓡 3).toHomeomorph.trans h.equiv.toHomeomorph.symm)
  have hΨ_apply : ∀ p : ThreeSphere, Ψ p = h.equiv.symm ((h.codChart.extend (𝓡 3)) p) := fun _ => rfl
  have hextend : ∀ y : S, (h.domChart.extend (𝓡∂ 2)) y = (𝓡∂ 2) (h.domChart y) := fun _ => rfl
  have hΨsmooth : ContMDiffOn (𝓡 3) 𝓘(ℝ, E2 × ℝ) ∞ Ψ Ψ.source := by
    change ContMDiffOn (𝓡 3) 𝓘(ℝ, E2 × ℝ) ∞
      (h.equiv.symm ∘ h.codChart.extend (𝓡 3)) h.codChart.source
    exact h.contMDiffOn_equiv_symm_extend_codChart
  have hΨsmooth_inv : ContMDiffOn 𝓘(ℝ, E2 × ℝ) (𝓡 3) ∞ Ψ.symm Ψ.target := by
    change ContMDiffOn 𝓘(ℝ, E2 × ℝ) (𝓡 3) ∞
      ((h.codChart.extend (𝓡 3)).symm ∘ h.equiv) Ψ.target
    refine (contMDiffOn_extend_symm h.codChart_mem_maximalAtlas).comp
      h.equiv.contDiff.contMDiff.contMDiffOn ?_
    intro q hq
    change (𝓡 3).symm (h.equiv q) ∈ h.codChart.target at hq
    exact ⟨(𝓡 3).symm (h.equiv q), hq, (𝓡 3).right_inv (by rw [(𝓡 3).range_eq_univ]; trivial)⟩
  -- In this chart the immersion normal form says that `f` is the standard inclusion.
  have key : ∀ y ∈ h.domChart.source, Ψ (f y) = ((h.domChart.extend (𝓡∂ 2)) y, 0) := by
    intro y hy
    rw [hΨ_apply]
    exact h.equiv_symm_extend_codChart_apply hy
  -- An open ambient set cuts the domain chart out of the image.
  obtain ⟨W, hW, hWf⟩ := hf.isOpen_iff.1 h.domChart.open_source
  have hmemW : ∀ y : S, f y ∈ W ↔ y ∈ h.domChart.source := fun y => by
    rw [← hWf]
    exact Iff.rfl
  -- The part of the ambient model space lying over the target of the domain chart.
  have hU : IsOpen ((𝓡∂ 2).symm ⁻¹' h.domChart.target) :=
    h.domChart.open_target.preimage (𝓡∂ 2).continuous_symm
  let V : Set ThreeSphere :=
    (Ψ.source ∩ Ψ ⁻¹' (((𝓡∂ 2).symm ⁻¹' h.domChart.target) ×ˢ (univ : Set ℝ))) ∩ W
  have hVopen : IsOpen V := (Ψ.isOpen_inter_preimage (hU.prod isOpen_univ)).inter hW
  -- The point `f x` survives both restrictions.
  have hx : x ∈ h.domChart.source := h.mem_domChart_source
  have hfx : f x ∈ Ψ.source := h.mem_codChart_source
  have hfxV : f x ∈ V := by
    refine ⟨⟨hfx, ?_⟩, (hmemW x).2 hx⟩
    rw [mem_preimage, key x hx]
    exact ⟨by rw [mem_preimage, hextend, (𝓡∂ 2).left_inv]; exact h.domChart.map_source hx,
      mem_univ _⟩
  let Φ := Ψ.restrOpen V hVopen
  have hiff : ∀ p ∈ Φ.source, p ∈ range f ↔ Φ p ∈ range (𝓡∂ 2) ×ˢ ({0} : Set ℝ) := by
    intro p hp
    change p ∈ Ψ.source ∩ V at hp
    change p ∈ range f ↔ Ψ p ∈ range (𝓡∂ 2) ×ˢ ({0} : Set ℝ)
    constructor
    · rintro ⟨y, rfl⟩
      have hy : y ∈ h.domChart.source := (hmemW y).1 hp.2.2
      rw [key y hy, hextend]
      exact ⟨mem_range_self _, rfl⟩
    · intro hps
      have hmem : (Ψ p).1 ∈ (h.domChart.extend (𝓡∂ 2)).target := by
        rw [h.domChart.extend_target]
        exact ⟨hp.2.1.2.1, hps.1⟩
      have hys : (h.domChart.extend (𝓡∂ 2)).symm (Ψ p).1 ∈ h.domChart.source := by
        rw [← h.domChart.extend_source (I := 𝓡∂ 2)]
        exact (h.domChart.extend (𝓡∂ 2)).map_target hmem
      have hfy : Ψ (f ((h.domChart.extend (𝓡∂ 2)).symm (Ψ p).1)) = Ψ p := by
        rw [key _ hys, (h.domChart.extend (𝓡∂ 2)).right_inv hmem, ← (hps.2 : (Ψ p).2 = 0)]
      exact ⟨_, Ψ.injOn (h.source_subset_preimage_source hys) hp.1 hfy⟩
  have hbase : (Φ (f x)).1 ∈ interior (range (𝓡∂ 2)) := by
    change (Ψ (f x)).1 ∈ _
    rw [key x hx]
    have hh := (ModelWithCorners.isInteriorPoint_iff_of_mem_maximalAtlas
      (I := 𝓡∂ 2) (by simp : (∞ : ℕ∞ω) ≠ 0) h.domChart_mem_maximalAtlas hx).mp hxi
    exact h.domChart.interior_extend_target_subset_interior_range hh
  refine ⟨Φ, ⟨hfx, hfxV⟩, hΨsmooth.mono inter_subset_left,
    hΨsmooth_inv.mono inter_subset_left, ?_,hbase⟩
  ext q
  constructor
  · rintro ⟨p, ⟨hps, hpr⟩, rfl⟩
    exact ⟨Φ.map_source hps, (hiff p hps).mp hpr⟩
  · rintro ⟨hqt, hqS⟩
    refine ⟨Φ.symm q, ⟨Φ.map_target hqt, ?_⟩, Φ.right_inv hqt⟩
    apply (hiff _ (Φ.map_target hqt)).mpr
    rwa [Φ.right_inv hqt]


#print axioms native_actual_slice_of_complement_with_base_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
