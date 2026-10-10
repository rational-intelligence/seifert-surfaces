import MovingCornerExtension

open scoped Manifold ContDiff
open Set Filter Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v
variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
  {f g : NeatEmbedding S M}

/-- Actual chart coordinates of the moving family admit a local smooth
Euclidean extension, including at time/source corners. -/
theorem normal_exists_local_chart_extension (F : SmoothNormalIsotopy S M f g)
    (c : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
    (hc : c ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ S)
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    (t : Time) (x : S) (hx : x ∈ c.source)
    (hfx : (F.stage t).toFun x ∈ d.source) :
    ∃ U : Set (ℝ × Euc 2), IsOpen U ∧ ((t : ℝ), (c.extend (𝓡∂ 2)) x) ∈ U ∧
      ∃ G : ℝ × Euc 2 → Euc 3, ContDiff ℝ ∞ G ∧
        ∀ q ∈ U, q.1 ∈ Icc 0 1 → q.2 ∈ range (𝓡∂ 2) →
          (q.2 ∈ (c.extend (𝓡∂ 2)).target ∧
           (F.stage (projIcc 0 1 (by norm_num) q.1)).toFun
             ((c.extend (𝓡∂ 2)).symm q.2) ∈ d.source ∧
           G q = (d.extend (𝓡∂ 3))
             ((F.stage (projIcc 0 1 (by norm_num) q.1)).toFun
               ((c.extend (𝓡∂ 2)).symm q.2))) := by
  let P : ℝ → Time := projIcc 0 1 (by norm_num)
  let ψ : ℝ × Euc 2 → Time × S := fun q => (P q.1, (c.extend (𝓡∂ 2)).symm q.2)
  let k : ℝ × Euc 2 → M := fun q => (F.stage (ψ q).1).toFun (ψ q).2
  let q₀ : ℝ × Euc 2 := ((t : ℝ), (c.extend (𝓡∂ 2)) x)
  let C : Set (ℝ × Euc 2) := Icc 0 1 ×ˢ range (𝓡∂ 2)
  let A : Set (Euc 2) := (𝓡∂ 2).symm ⁻¹' c.target
  have hA : IsOpen A := c.open_target.preimage (𝓡∂ 2).continuous_symm
  have hqx : (c.extend (𝓡∂ 2)) x ∈ A := by
    change (𝓡∂ 2).symm ((𝓡∂ 2) (c x)) ∈ c.target
    rw [(𝓡∂ 2).left_inv]
    exact c.map_source hx
  have hP : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ P (Icc 0 1) := contMDiffOn_projIcc
  have hci : ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 2) ∞ (c.extend (𝓡∂ 2)).symm
      (c.extend (𝓡∂ 2)).target := by
    simpa only [OpenPartialHomeomorph.extend_target' ] using contMDiffOn_extend_symm hc
  let B : Set (ℝ × Euc 2) := Icc 0 1 ×ˢ (c.extend (𝓡∂ 2)).target
  have hψ : ContMDiffOn 𝓘(ℝ, ℝ × Euc 2) ((𝓡∂ 1).prod (𝓡∂ 2)) ∞ ψ B :=
    (hP.comp contDiff_fst.contMDiff.contMDiffOn (fun _ hq => hq.1)).prodMk
      (hci.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hq => hq.2))
  have hk : ContMDiffOn 𝓘(ℝ, ℝ × Euc 2) (𝓡∂ 3) ∞ k B :=
    F.smooth_family.comp_contMDiffOn hψ
  have hqB : q₀ ∈ B := ⟨t.property,(c.extend (𝓡∂ 2)).map_source (by simpa using hx)⟩
  have hψq : ψ q₀ = (t,x) := by
    apply Prod.ext
    · exact Subtype.ext (by simp [ψ,P,q₀,projIcc_of_mem (show (0:ℝ) ≤ 1 by norm_num) t.property])
    · exact (c.extend (𝓡∂ 2)).left_inv (by simpa using hx)
  have hkq : k q₀ = (F.stage t).toFun x := by change (F.stage (ψ q₀).1).toFun (ψ q₀).2 = _; rw [hψq]
  have hn : k ⁻¹' d.source ∈ 𝓝[B] q₀ :=
    hk.continuousOn q₀ hqB ((d.open_source.mem_nhds (hkq ▸ hfx)))
  obtain ⟨W,hWo,hqW,hWB⟩ := mem_nhdsWithin.mp hn
  let U₀ : Set (ℝ × Euc 2) := W ∩ (univ ×ˢ A)
  have hU₀ : IsOpen U₀ := hWo.inter (isOpen_univ.prod hA)
  have hqU₀ : q₀ ∈ U₀ := ⟨hqW,mem_univ _,hqx⟩
  have hCB : C ∩ U₀ ⊆ B := by
    intro q hq
    refine ⟨hq.1.1,?_⟩
    change q.2 ∈ (c.extend (𝓡∂ 2)).target
    rw [OpenPartialHomeomorph.extend_target]
    exact ⟨hq.2.2.2,hq.1.2⟩
  have hkd : ∀ q ∈ C ∩ U₀, k q ∈ d.source := fun q hq => hWB ⟨hq.2.1,hCB hq⟩
  have hdext : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, Euc 3) ∞ (d.extend (𝓡∂ 3)) d.source :=
    (ModelWithCorners.contMDiff (𝓡∂ 3)).comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas hd)
  have hread : ContDiffOn ℝ ∞ (fun q => (d.extend (𝓡∂ 3)) (k q)) (C ∩ U₀) :=
    (hdext.comp (hk.mono hCB) hkd).contDiffOn
  obtain ⟨G,hG,hGeq⟩ := exists_contDiff_extension_Icc_halfspace_local
    (show (0:ℝ)<1 by norm_num) hU₀ hread hqU₀
  obtain ⟨V,hVo,hqV,hVC⟩ := mem_nhdsWithin.mp hGeq
  refine ⟨U₀ ∩ V,hU₀.inter hVo,⟨hqU₀,hqV⟩,G,hG,?_⟩
  intro q hq ht hh
  have hqC : q ∈ C := ⟨ht,hh⟩
  exact ⟨(hCB ⟨hqC,hq.1⟩).2,hkd q ⟨hqC,hq.1⟩,hVC ⟨hq.2,hqC⟩⟩

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
