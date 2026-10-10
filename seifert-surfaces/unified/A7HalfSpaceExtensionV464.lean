import DifferentialGeometry.Analysis.Calculus.SmoothExtension.HalfSpace
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
noncomputable section
open scoped ContDiff Manifold Topology
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open Set Filter

theorem exists_contDiff_extension_prod_halfspace_local
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : P × EuclideanSpace ℝ (Fin (d + 1)) → F}
    {U : Set (P × EuclideanSpace ℝ (Fin (d + 1)))}
    (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f (U ∩ (univ ×ˢ range (𝓡∂ (d + 1)))))
    {x : P × EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ U) :
    ∃ G : P × EuclideanSpace ℝ (Fin (d + 1)) → F, ContDiff ℝ ∞ G ∧
      G =ᶠ[𝓝[univ ×ˢ range (𝓡∂ (d + 1))] x] f := by
  let κ : (ℝ × (Fin d → ℝ)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
    (Fin.consEquivL ℝ (fun _ : Fin (d + 1) => ℝ)).trans
      (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm
  have hκzero (z : ℝ × (Fin d → ℝ)) : κ z 0 = z.1 := by
    simp [κ]
  let k : ℝ × (P × (Fin d → ℝ)) → P × EuclideanSpace ℝ (Fin (d + 1)) :=
    fun q => (q.2.1, κ (q.1, q.2.2))
  let j : P × EuclideanSpace ℝ (Fin (d + 1)) → ℝ × (P × (Fin d → ℝ)) :=
    fun q => ((κ.symm q.2).1, (q.1, (κ.symm q.2).2))
  have hk : ContDiff ℝ ∞ k :=
    contDiff_snd.fst.prodMk (κ.contDiff.comp (contDiff_fst.prodMk contDiff_snd.snd))
  have hj : ContDiff ℝ ∞ j :=
    (κ.symm.contDiff.comp contDiff_snd).fst.prodMk
      (contDiff_fst.prodMk (κ.symm.contDiff.comp contDiff_snd).snd)
  have hkj (z : P × EuclideanSpace ℝ (Fin (d + 1))) : k (j z) = z := by
    change (z.1, κ (κ.symm z.2)) = z
    rw [κ.apply_symm_apply]
  have hread : ContDiffOn ℝ ∞ (f ∘ k) ((Ici 0 ×ˢ univ) ∩ (k ⁻¹' U)) := by
    apply hf.comp hk.contDiffOn
    intro z hz
    refine ⟨hz.2, mem_univ _, ?_⟩
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ κ (z.1, z.2.2) 0
    rw [hκzero]
    exact mem_Ici.mp hz.1.1
  obtain ⟨G, hG, hGf⟩ := hread.exists_contDiff_extension_Ici_prod_nhdsWithin
    (hU.preimage hk.continuous) (show j x ∈ k ⁻¹' U by
      change k (j x) ∈ U
      rw [hkj]
      exact hx)
  refine ⟨G ∘ j, hG.comp hj, ?_⟩
  have hjH (z : P × EuclideanSpace ℝ (Fin (d + 1)))
      (hz : z ∈ univ ×ˢ range (𝓡∂ (d + 1))) :
      j z ∈ Ici (0 : ℝ) ×ˢ (univ : Set (P × (Fin d → ℝ))) := by
    refine ⟨mem_Ici.mpr ?_, mem_univ _⟩
    change 0 ≤ (κ.symm z.2).1
    rw [← hκzero _, κ.apply_symm_apply]
    simpa only [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hz.2
  have ht : Tendsto j (𝓝[univ ×ˢ range (𝓡∂ (d + 1))] x)
      (𝓝[Ici (0 : ℝ) ×ˢ (univ : Set (P × (Fin d → ℝ)))] j x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hj.continuous.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hjH z hz
  filter_upwards [hGf.comp_tendsto ht] with z hz
  change G (j z) = f z
  simpa only [Function.comp_apply, hkj] using hz

theorem exists_contDiff_extension_halfspace_local
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : EuclideanSpace ℝ (Fin (n + 1)) → F} {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f (U ∩ range (𝓡∂ (n + 1))))
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ U) :
    ∃ G : EuclideanSpace ℝ (Fin (n + 1)) → F, ContDiff ℝ ∞ G ∧
      G =ᶠ[𝓝[range (𝓡∂ (n + 1))] x] f := by
  let φ : PUnit.{1} × EuclideanSpace ℝ (Fin (n + 1)) → F := fun q => f q.2
  have hφ : ContDiffOn ℝ ∞ φ ((univ ×ˢ U) ∩ (univ ×ˢ range (𝓡∂ (n + 1)))) :=
    hf.comp contDiff_snd.contDiffOn (fun _ hq => ⟨hq.1.2, hq.2.2⟩)
  obtain ⟨G, hG, hGeq⟩ := exists_contDiff_extension_prod_halfspace_local
    (isOpen_univ.prod hU) hφ
      (show (PUnit.unit, x) ∈ univ ×ˢ U from ⟨mem_univ _, hx⟩)
  refine ⟨fun z => G (PUnit.unit, z), hG.comp (contDiff_const.prodMk contDiff_id), ?_⟩
  have ht : Tendsto (fun z : EuclideanSpace ℝ (Fin (n + 1)) => ((PUnit.unit : PUnit.{1}), z))
      (𝓝[range (𝓡∂ (n + 1))] x)
      (𝓝[univ ×ˢ range (𝓡∂ (n + 1))] (PUnit.unit, x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuousAt_const.prodMk continuousAt_id).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact ⟨mem_univ _, hz⟩
  exact hGeq.comp_tendsto ht


end SeifertSurfaces.OriginalEndpoints.A7Support
