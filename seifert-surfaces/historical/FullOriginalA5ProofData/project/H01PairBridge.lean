import ApprovedDataClosure

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder

set_option maxHeartbeats 3000000

lemma witness_grad_ae_eq {Ω : Set V} (hΩ : IsOpen Ω) {v : V → ℝ}
    (hv hw : H1Witness v Ω) : hv.weakGrad =ᵐ[volume.restrict Ω] hw.weakGrad := by
  have hcomp : ∀ i : Fin 3, (fun x => hv.weakGrad x i) =ᵐ[volume.restrict Ω]
      (fun x => hw.weakGrad x i) := fun i =>
    DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ (hv.isWeakGrad i) (hw.isWeakGrad i)
      ((hv.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
      ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
  filter_upwards [ae_all_iff.2 hcomp] with x hx
  ext i
  exact hx i

lemma witnessPair_add {Ω : Set V} {v w : V → ℝ}
    (hv : H1Witness v Ω) (hw : H1Witness w Ω) :
    witnessPair (hv.add hw) = witnessPair hv + witnessPair hw := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · exact MemLp.toLp_add hv.memLp hw.memLp
  · exact MemLp.toLp_add (weak_gradient_memLp Ω v hv) (weak_gradient_memLp Ω w hw)

lemma witnessPair_smul {Ω : Set V} {v : V → ℝ} (hv : H1Witness v Ω) (c : ℝ) :
    witnessPair (hv.smul c) = c • witnessPair hv := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · exact MemLp.toLp_const_smul c hv.memLp
  · exact MemLp.toLp_const_smul c (weak_gradient_memLp Ω v hv)

def smoothWitness (Ω : Set V) (hΩ : IsOpen Ω) {v : V → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hc : HasCompactSupport v) : H1Witness v Ω :=
  (DeGiorgi.MemW1pWitness.ofContDiffHasCompactSupport hv hc).restrict hΩ (subset_univ Ω)

lemma witnessPair_smooth_grad {Ω : Set V} (hΩ : IsOpen Ω) {v : V → ℝ}
    (hv : H1Witness v Ω) (hs : ContDiff ℝ (⊤ : ℕ∞) v) (hc : HasCompactSupport v) :
    hv.weakGrad =ᵐ[volume.restrict Ω] classicalGradient v :=
  witness_grad_ae_eq hΩ hv (smoothWitness Ω hΩ hs hc)

def smoothPairSubmodule (Ω : Set V) (hΩ : IsOpen Ω) : Submodule ℝ (SobolevPair Ω) where
  carrier := smoothPairs Ω
  zero_mem' := by
    let hv := smoothWitness Ω hΩ (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (0 : V → ℝ))
      HasCompactSupport.zero
    refine ⟨(0 : V → ℝ), hv, contDiff_const, ?_, ?_, ?_⟩
    · exact HasCompactSupport.zero
    · simp
    · have hgrad : hv.weakGrad = 0 := by
        ext x i
        simp [hv, smoothWitness, DeGiorgi.MemW1pWitness.restrict,
          DeGiorgi.MemW1pWitness.ofContDiffHasCompactSupport]
      simp only [witnessPair, hgrad, MemLp.toLp_zero]
      rfl
  add_mem' := by
    rintro p q ⟨v, hv, hs, hc, ht, rfl⟩ ⟨w, hw, hs', hc', ht', rfl⟩
    refine ⟨fun x => v x + w x, hv.add hw, hs.add hs', hc.add hc', ?_, ?_⟩
    · exact (tsupport_add v w).trans (union_subset ht ht')
    · exact (witnessPair_add hv hw).symm
  smul_mem' := by
    rintro c p ⟨v, hv, hs, hc, ht, rfl⟩
    refine ⟨fun x => c * v x, hv.smul c, contDiff_const.mul hs, hc.mul_left, ?_, ?_⟩
    · exact (tsupport_smul_subset_right (fun _ => c) v).trans ht
    · exact (witnessPair_smul hv c).symm

lemma H01Space_eq_closure_smoothPairs (Ω : Set V) (hΩ : IsOpen Ω) :
    (H01Space Ω : Set (SobolevPair Ω)) = closure (smoothPairs Ω) := by
  rw [H01Space, Submodule.topologicalClosure_coe]
  change closure (Submodule.span ℝ (smoothPairSubmodule Ω hΩ : Set (SobolevPair Ω)) :
    Set (SobolevPair Ω)) = _
  rw [Submodule.span_eq]
  rfl

lemma norm_le_sum_abs_coordinates (ξ : V) : ‖ξ‖ ≤ ∑ i : Fin 3, |ξ i| := by
  have heq : ξ = ∑ i : Fin 3, ξ i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Pi.single_apply, hij, Ne.symm hij]
    · simp
  conv_lhs => rw [heq]
  exact (norm_sum_le _ _).trans_eq (by simp [norm_smul, PiLp.norm_single])

lemma vector_eLpNorm_le_sum_coordinates {μ : Measure V} (G : V → V)
    (hG : MemLp G 2 μ) :
    eLpNorm G 2 μ ≤ ∑ i : Fin 3, eLpNorm (fun x => G x i) 2 μ := by
  calc
    _ ≤ eLpNorm (fun x => ∑ i : Fin 3, |G x i|) 2 μ :=
      eLpNorm_mono_real hG.aestronglyMeasurable (fun x => norm_le_sum_abs_coordinates _)
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x => |G x i|) 2 μ := by
      convert
        (eLpNorm_sum_le (p := 2) (s := Finset.univ)
          (f := fun i : Fin 3 => fun x => |G x i|) (μ := μ) (by norm_num)) using 1
      congr 1
    _ = _ := by
      congr 1
      funext i
      simpa only [Real.norm_eq_abs] using
        eLpNorm_norm (fun x => G x i) (hG.eval_piLp i).aestronglyMeasurable

lemma vector_eLpNorm_tendsto_zero {μ : Measure V} (G : ℕ → V → V)
    (hG : ∀ n, MemLp (G n) 2 μ)
    (hcoord : ∀ i : Fin 3, Tendsto (fun n => eLpNorm (fun x => G n x i) 2 μ)
      atTop (𝓝 0)) : Tendsto (fun n => eLpNorm (G n) 2 μ) atTop (𝓝 0) := by
  have hsum : Tendsto (fun n => ∑ i : Fin 3, eLpNorm (fun x => G n x i) 2 μ)
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hcoord i)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun n => bot_le) (fun n => vector_eLpNorm_le_sum_coordinates (G n) (hG n))

end SeifertSurfaces.WeakSchauder
