import MovingHalfspaceInverse
import DifferentialGeometry.Topology.Manifold.IntervalExtension

open scoped ContDiff Manifold Topology
open Set Filter

namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
open DifferentialGeometry.Analysis

-- The local corner extension is exposed here so it can be applied to actual
-- moving immersion charts, rather than assuming a jointly smooth retraction.
theorem exists_contDiff_extension_strip_local_of_lt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b c : ℝ} {f : ℝ × (ℝ × E) → F} {U : Set (ℝ × (ℝ × E))}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f ((Icc a b ×ˢ (Ici c ×ˢ univ)) ∩ U))
    {x : ℝ × (ℝ × E)} (hx : x ∈ U) (hxb : x.1 < b) :
    ∃ G : ℝ × (ℝ × E) → F, ContDiff ℝ ∞ G ∧
      G =ᶠ[𝓝[Icc a b ×ˢ (Ici c ×ˢ univ)] x] f := by
  let W : Set (ℝ × (ℝ × E)) := U ∩ {q | q.1 < b}
  have hW : IsOpen W := hU.inter (isOpen_lt continuous_fst continuous_const)
  have hread : ContDiffOn ℝ ∞ f ((Ici a ×ˢ (Ici c ×ˢ univ)) ∩ W) :=
    hf.mono (fun _ hq => ⟨⟨⟨hq.1.1, hq.2.2.le⟩, hq.1.2⟩, hq.2.1⟩)
  obtain ⟨g, hg, -, hgeq⟩ := exists_contDiffOn_cutoff_extension hW hread
    (show x ∈ W from ⟨hx, hxb⟩)
  obtain ⟨G, hG, hGg⟩ := hg.exists_contDiff_extension_quadrant
  refine ⟨G, hG, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hgeq.filter_mono nhdsWithin_le_nhds] with q hq heq
  exact (hGg ⟨hq.1.1, hq.2⟩).trans heq

theorem exists_contDiff_extension_strip_local
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b c : ℝ} (hab : a < b) {f : ℝ × (ℝ × E) → F} {U : Set (ℝ × (ℝ × E))}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f ((Icc a b ×ˢ (Ici c ×ˢ univ)) ∩ U))
    {x : ℝ × (ℝ × E)} (hx : x ∈ U) :
    ∃ G : ℝ × (ℝ × E) → F, ContDiff ℝ ∞ G ∧
      G =ᶠ[𝓝[Icc a b ×ˢ (Ici c ×ˢ univ)] x] f := by
  by_cases hxb : x.1 < b
  · exact exists_contDiff_extension_strip_local_of_lt hU hf hx hxb
  · let σ : ℝ × (ℝ × E) → ℝ × (ℝ × E) := fun q => (-q.1, q.2)
    have hσ : ContDiff ℝ ∞ σ := contDiff_fst.neg.prodMk contDiff_snd
    have hread : ContDiffOn ℝ ∞ (f ∘ σ)
        ((Icc (-b) (-a) ×ˢ (Ici c ×ˢ univ)) ∩ (σ ⁻¹' U)) := by
      apply hf.comp hσ.contDiffOn
      intro q hq
      exact ⟨⟨⟨by dsimp [σ]; linarith [hq.1.1.2],
        by dsimp [σ]; linarith [hq.1.1.1]⟩, hq.1.2⟩, hq.2⟩
    obtain ⟨G, hG, hGeq⟩ := exists_contDiff_extension_strip_local_of_lt
      (hU.preimage hσ.continuous) hread
      (show σ x ∈ σ ⁻¹' U by simpa only [σ, mem_preimage, neg_neg] using hx)
      (show (σ x).1 < -a by dsimp [σ]; linarith)
    refine ⟨G ∘ σ, hG.comp hσ, ?_⟩
    have ht : Tendsto σ (𝓝[Icc a b ×ˢ (Ici c ×ˢ univ)] x)
        (𝓝[Icc (-b) (-a) ×ˢ (Ici c ×ˢ univ)] σ x) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hσ.continuous.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact ⟨⟨by dsimp [σ]; linarith [hq.1.2],
        by dsimp [σ]; linarith [hq.1.1]⟩, hq.2⟩
    filter_upwards [hGeq.comp_tendsto ht] with q hq
    simpa only [Function.comp_apply, σ, neg_neg] using hq

theorem exists_contDiff_extension_Icc_halfspace_local
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b : ℝ} (hab : a < b)
    {f : ℝ × EuclideanSpace ℝ (Fin (d + 1)) → F}
    {U : Set (ℝ × EuclideanSpace ℝ (Fin (d + 1)))} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f ((Icc a b ×ˢ range (𝓡∂ (d + 1))) ∩ U))
    {x : ℝ × EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ U) :
    ∃ G : ℝ × EuclideanSpace ℝ (Fin (d + 1)) → F, ContDiff ℝ ∞ G ∧
      G =ᶠ[𝓝[Icc a b ×ˢ range (𝓡∂ (d + 1))] x] f := by
  let κ : (ℝ × (Fin d → ℝ)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
    (Fin.consEquivL ℝ (fun _ : Fin (d + 1) => ℝ)).trans
      (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm
  have hκzero (z : ℝ × (Fin d → ℝ)) : κ z 0 = z.1 := by simp [κ]
  let k : ℝ × (ℝ × (Fin d → ℝ)) → ℝ × EuclideanSpace ℝ (Fin (d + 1)) :=
    fun q => (q.1, κ q.2)
  let j : ℝ × EuclideanSpace ℝ (Fin (d + 1)) → ℝ × (ℝ × (Fin d → ℝ)) :=
    fun q => (q.1, κ.symm q.2)
  have hk : ContDiff ℝ ∞ k := contDiff_fst.prodMk (κ.contDiff.comp contDiff_snd)
  have hj : ContDiff ℝ ∞ j := contDiff_fst.prodMk (κ.symm.contDiff.comp contDiff_snd)
  have hkj (q : ℝ × EuclideanSpace ℝ (Fin (d + 1))) : k (j q) = q := by
    change (q.1, κ (κ.symm q.2)) = q
    rw [κ.apply_symm_apply]
  have hread : ContDiffOn ℝ ∞ (f ∘ k)
      ((Icc a b ×ˢ (Ici 0 ×ˢ univ)) ∩ (k ⁻¹' U)) := by
    apply hf.comp hk.contDiffOn
    intro q hq
    refine ⟨⟨hq.1.1, ?_⟩, hq.2⟩
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ κ q.2 0
    rw [hκzero]
    exact mem_Ici.mp hq.1.2.1
  obtain ⟨G, hG, hGeq⟩ := exists_contDiff_extension_strip_local hab
    (hU.preimage hk.continuous) hread (show j x ∈ k ⁻¹' U by rwa [mem_preimage, hkj])
  refine ⟨G ∘ j, hG.comp hj, ?_⟩
  have ht : Tendsto j (𝓝[Icc a b ×ˢ range (𝓡∂ (d + 1))] x)
      (𝓝[Icc a b ×ˢ (Ici (0 : ℝ) ×ˢ univ)] j x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hj.continuous.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with q hq
    refine ⟨hq.1, mem_Ici.mpr ?_, mem_univ _⟩
    change 0 ≤ (κ.symm q.2).1
    rw [← hκzero _, κ.apply_symm_apply]
    simpa only [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hq.2
  filter_upwards [hGeq.comp_tendsto ht] with q hq
  simpa only [Function.comp_apply, hkj] using hq


end
end SeifertSurfaces.Foundations.AmbientNeatTransport
