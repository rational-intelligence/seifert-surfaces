import H01Realize

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder

set_option maxHeartbeats 3000000

lemma memH01_congr_ae {Ω : Set V} {v w : V → ℝ}
    (hvw : v =ᵐ[volume.restrict Ω] w) (hw : DeGiorgi.MemH01 w Ω) :
    DeGiorgi.MemH01 v Ω := by
  rcases hw with ⟨_, hw, φ, hs, hc, ht, hfun, hgrad⟩
  let hv : H1Witness v Ω :=
    { memLp := hw.memLp.ae_eq hvw.symm
      weakGrad := hw.weakGrad
      weakGrad_component_memLp := hw.weakGrad_component_memLp
      isWeakGrad := by
        intro i ψ hψ hcψ htψ
        calc
          (∫ x in Ω, v x * (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) =
              ∫ x in Ω, w x * (fderiv ℝ ψ x) (EuclideanSpace.single i 1) := by
            apply integral_congr_ae
            filter_upwards [hvw] with x hx
            rw [hx]
          _ = _ := hw.isWeakGrad i ψ hψ hcψ htψ }
  refine ⟨hv.memW1p, hv, φ, hs, hc, ht, ?_, hgrad⟩
  apply (tendsto_congr (fun n => ?_)).mp hfun
  apply eLpNorm_congr_ae
  filter_upwards [hvw] with x hx
  rw [hx]

theorem H01Space_mem_iff (Ω : Set V) (hΩ : IsOpen Ω)
    (v : V → ℝ) (hv : H1Witness v Ω) :
    witnessPair hv ∈ H01Space Ω ↔ DeGiorgi.MemH01 v Ω := by
  classical
  constructor
  · intro hmem
    obtain ⟨w, hw, hw0, hpair⟩ := H01Space_realize Ω hΩ ⟨witnessPair hv, hmem⟩
    have hfun : w =ᵐ[volume.restrict Ω] v := by
      apply (MemLp.toLp_eq_toLp_iff hw.memLp hv.memLp).mp
      exact congrArg (fun q : SobolevPair Ω => q.ofLp.1) hpair
    exact memH01_congr_ae hfun.symm hw0
  · rintro ⟨_, hw, φ, hs, hc, ht, hfun, hgrad⟩
    let ψ (n : ℕ) := smoothWitness Ω hΩ (hs n) (hc n)
    have hveq := witness_grad_ae_eq hΩ hw hv
    have hcoord (i : Fin 3) : Tendsto
        (fun n => eLpNorm (fun x => (ψ n).weakGrad x i - hv.weakGrad x i) 2 (volume.restrict Ω))
        atTop (𝓝 0) := by
      apply (tendsto_congr (fun n => ?_)).mp (hgrad i)
      apply eLpNorm_congr_ae
      filter_upwards [hveq] with x hx
      rw [hx]
      rfl
    have hvec := vector_eLpNorm_tendsto_zero (fun n => fun x => (ψ n).weakGrad x - hv.weakGrad x)
      (fun n => (weak_gradient_memLp Ω _ (ψ n)).sub (weak_gradient_memLp Ω v hv)) hcoord
    have hflim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' φ (fun n => (ψ n).memLp) v hv.memLp).mpr hfun
    have hglim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => (ψ n).weakGrad)
      (fun n => weak_gradient_memLp Ω _ (ψ n)) hv.weakGrad (weak_gradient_memLp Ω v hv)).mpr hvec
    have hpairlim : Tendsto (fun n => witnessPair (ψ n)) atTop (𝓝 (witnessPair hv)) :=
      (WithLp.prod_continuous_toLp 2 (Lp ℝ 2 (volume.restrict Ω))
        (Lp V 2 (volume.restrict Ω))).tendsto _ |>.comp (hflim.prodMk_nhds hglim)
    have hmem : witnessPair hv ∈ closure (smoothPairs Ω) :=
      mem_closure_iff_seq_limit.mpr ⟨fun n => witnessPair (ψ n),
        fun n => ⟨φ n, ψ n, hs n, hc n, ht n, rfl⟩, hpairlim⟩
    rw [← H01Space_eq_closure_smoothPairs Ω hΩ] at hmem
    exact hmem

end SeifertSurfaces.WeakSchauder
