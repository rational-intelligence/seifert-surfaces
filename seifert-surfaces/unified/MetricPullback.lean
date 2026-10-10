import Mathlib

noncomputable section
open Bundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace SeifertSurfaces.AppendixC

def pullbackBilinear
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [T2Space W]
    [FiniteDimensional ℝ W]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (D : W →L[ℝ] V) : W →L[ℝ] W →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (B (D v)).comp D
      map_add' := by intro v w; ext x; simp
      map_smul' := by intro c v; ext x; simp }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES]
    [FiniteDimensional ℝ ES]
    {HS : Type*} [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS}
    {S : Type*} [TopologicalSpace S] [ChartedSpace HS S] [IsManifold IS ∞ S]

lemma contMDiff_pullback_bilinear
    (j : S → M) (hj : ContMDiff IS I ∞ j)
    (g : ∀ p : M, TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ)
    (hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) p (g p))) :
    ContMDiff IS (IS.prod 𝓘(ℝ, ES →L[ℝ] ES →L[ℝ] ℝ)) ∞
      (fun p => TotalSpace.mk' (ES →L[ℝ] ES →L[ℝ] ℝ) p
        (pullbackBilinear (g (j p)) (mfderiv IS I j p))) := by
  intro p
  rw [contMDiffAt_section]
  let A := inTangentCoordinates IS I id j (mfderiv IS I j) p
  let B := fun q => (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
    (fun p : M => TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) (j p)
      ⟨j q, g (j q)⟩).2
  have hA : ContMDiffAt IS 𝓘(ℝ, ES →L[ℝ] E) ∞ A p :=
    (hj p).mfderiv_const (by simp)
  have hB : ContMDiffAt IS 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ B p :=
    ((contMDiffAt_section (j p)).mp (hg (j p))).comp p (hj p)
  have h : ContMDiffAt IS 𝓘(ℝ, ES →L[ℝ] ES →L[ℝ] ℝ) ∞
      (fun q => (B q).bilinearComp (A q) (A q)) p := by
    exact ((hA.clm_precomp (F₃ := ℝ)).clm_comp (hB.clm_comp hA))
  apply h.congr_of_eventuallyEq
  have hS : ∀ᶠ q in 𝓝 p,
      q ∈ (trivializationAt ES (fun q : S => TangentSpace IS q) p).baseSet :=
    (trivializationAt ES (fun q : S => TangentSpace IS q) p).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt ES (fun q : S => TangentSpace IS q) p)
  have hM : ∀ᶠ q in 𝓝 p,
      j q ∈ (trivializationAt E (fun q : M => TangentSpace I q) (j p)).baseSet :=
    (hj p).continuousAt
      ((trivializationAt E (fun q : M => TangentSpace I q) (j p)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (fun q : M => TangentSpace I q) (j p)))
  filter_upwards [hS, hM] with q hqS hqM
  ext v w
  simp only [B, hom_trivializationAt_apply]
  simp only [ContinuousLinearMap.bilinearComp_apply]
  rw [inCoordinates_apply_eq₂ hqS hqS (by simp),
    inCoordinates_apply_eq₂ hqM hqM (by simp)]
  simp [A, inTangentCoordinates, ContinuousLinearMap.inCoordinates_eq hqS hqM,
    pullbackBilinear, Trivialization.symm_apply_apply_mk _ hqM]

end SeifertSurfaces.AppendixC
