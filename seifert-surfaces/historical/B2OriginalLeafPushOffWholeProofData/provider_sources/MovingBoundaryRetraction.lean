import MovingBoundaryInverse

open scoped Manifold ContDiff
open Set Filter Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v
variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] {f g : NeatEmbedding S M}

/-- The actual moving compact trace admits jointly smooth local retractions
near its boundary, compatible with the ambient boundary at every time. -/
theorem normal_exists_moving_boundary_retraction (F : SmoothNormalIsotopy S M f g)
    (p : Time × S) (hp : p.2 ∈ S.boundary) :
    ∃ U : Set (Time × M), IsOpen U ∧ normalTrace F p ∈ U ∧
      ∃ r : Time × M → S,
        ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 2) ∞ r U ∧
        (∀ q, normalTrace F q ∈ U → r (normalTrace F q) = q.2) ∧
        ∀ q ∈ U, q.2 ∈ (𝓡∂ 3).boundary M → r q ∈ S.boundary := by
  obtain ⟨c,d,R,a,V,G,e,hc,hd,hpc,hfpd,ha,hRn,hV,hpV,hG,hGeq,hpe,heV,he,hei,hemap,heparam,hesign⟩ :=
    normal_exists_moving_boundary_inverse F p.1 p.2 hp
  let ψ : Time × M → ℝ × (ℝ × (Fin 1 → ℝ)) :=
    fun q => ((q.1 : ℝ), splitSurface.symm (R ((d.extend (𝓡∂ 3)) q.2)))
  let C : Set (Time × M) := univ ×ˢ d.source
  have hC : IsOpen C := isOpen_univ.prod d.open_source
  have hψ : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3))
      𝓘(ℝ, ℝ × (ℝ × (Fin 1 → ℝ))) ∞ ψ C := by
    have hdext : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, Euc 3) ∞ (d.extend (𝓡∂ 3)) d.source :=
      (𝓡∂ 3).contMDiff.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas hd)
    exact ((contMDiff_subtypeVal_Icc (x := 0) (y := 1)).comp contMDiff_fst).contMDiffOn.prodMk_space
      ((splitSurface.symm.contDiff.contMDiff.comp R.contDiff.contMDiff).comp_contMDiffOn
        (hdext.comp contMDiffOn_snd (fun _ hq => hq.2)))
  let D : Set (Time × M) := C ∩ ψ ⁻¹' e.target
  have hD : IsOpen D := hψ.continuousOn.isOpen_inter_preimage hC e.open_target
  have hbase : ψ (normalTrace F p) = e ((p.1 : ℝ),splitSurface.symm ((c.extend (𝓡∂ 2)) p.2)) := by
    have hh := hGeq ((p.1 : ℝ),(c.extend (𝓡∂ 2)) p.2) hpV p.1.property (mem_range_self (c p.2))
    have ht : projIcc 0 1 (by norm_num) (p.1 : ℝ) = p.1 :=
      Subtype.ext (by simp [projIcc_of_mem (show (0:ℝ) ≤ 1 by norm_num) p.1.property])
    rw [hemap]
    rw [ContinuousLinearEquiv.apply_symm_apply,hh.2.2,ht,
      (c.extend (𝓡∂ 2)).left_inv (by simpa using hpc)]
    rfl
  have hpD : normalTrace F p ∈ D := ⟨⟨mem_univ _,hfpd⟩,by
    change ψ (normalTrace F p) ∈ e.target
    rw [hbase]
    exact e.map_source hpe⟩
  let θ : Time × M → EuclideanHalfSpace 2 :=
    fun q => (𝓡∂ 2).symm (splitSurface (e.symm (ψ q)).2)
  have hθread (q : Time × M) (hq : q ∈ D) :
      (𝓡∂ 2) (θ q) = splitSurface (e.symm (ψ q)).2 := by
    apply (𝓡∂ 2).right_inv
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ splitSurface (e.symm (ψ q)).2 0
    rw [splitSurface_zero]
    apply (hesign (ψ q) hq.2 q.1.property).1.mpr
    change 0 ≤ (splitSurface.symm (R ((d.extend (𝓡∂ 3)) q.2))).1
    rw [splitSurface_symm_zero,hRn]
    exact div_nonneg (d q.2).property ha.le
  have hθ : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 2) ∞ θ D := by
    have heψ := hei.contMDiffOn.comp (hψ.mono inter_subset_left) inter_subset_right
    have hκ := splitSurface.contDiff.contMDiff.comp_contMDiffOn
      (contDiff_snd.contMDiff.comp_contMDiffOn heψ)
    apply (𝓡∂ 2).contMDiffOn_symm.comp hκ
    intro q hq
    change splitSurface (e.symm (ψ q)).2 ∈ range (𝓡∂ 2)
    rw [← hθread q hq]
    exact mem_range_self (θ q)
  let U₀ : Set (Time × M) := D ∩ θ ⁻¹' c.target
  have hU₀ : IsOpen U₀ := hθ.continuousOn.isOpen_inter_preimage hD c.open_target
  have hθbase : θ (normalTrace F p) = c p.2 := by
    dsimp [θ]
    rw [hbase,e.left_inv hpe,ContinuousLinearEquiv.apply_symm_apply]
    exact (𝓡∂ 2).left_inv (c p.2)
  have hpU₀ : normalTrace F p ∈ U₀ := ⟨hpD,by
    change θ (normalTrace F p) ∈ c.target
    rw [hθbase]
    exact c.map_source hpc⟩
  let r : Time × M → S := fun q => c.symm (θ q)
  have hr : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 2) ∞ r U₀ :=
    (contMDiffOn_symm_of_mem_maximalAtlas hc).comp (hθ.mono inter_subset_left) inter_subset_right
  let η : Time × S → ℝ × (ℝ × (Fin 1 → ℝ)) :=
    fun q => ((q.1 : ℝ), splitSurface.symm ((c.extend (𝓡∂ 2)) q.2))
  let B : Set (Time × S) := univ ×ˢ c.source
  have hB : IsOpen B := isOpen_univ.prod c.open_source
  have hη : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 2))
      𝓘(ℝ, ℝ × (ℝ × (Fin 1 → ℝ))) ∞ η B := by
    have hcext : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ, Euc 2) ∞ (c.extend (𝓡∂ 2)) c.source :=
      (𝓡∂ 2).contMDiff.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas hc)
    exact ((contMDiff_subtypeVal_Icc (x := 0) (y := 1)).comp contMDiff_fst).contMDiffOn.prodMk_space
      (splitSurface.symm.contDiff.contMDiff.comp_contMDiffOn
        (hcext.comp contMDiffOn_snd (fun _ hq => hq.2)))
  let O : Set (Time × S) := B ∩ η ⁻¹' e.source
  have hO : IsOpen O := hη.continuousOn.isOpen_inter_preimage hB e.open_source
  have hpO : p ∈ O := ⟨⟨mem_univ _,hpc⟩,hpe⟩
  obtain ⟨W,hW,hWeq⟩ := (normalTrace_isClosedEmbedding F).isEmbedding.isInducing.isOpen_iff.mp hO
  let U : Set (Time × M) := U₀ ∩ W
  refine ⟨U,hU₀.inter hW,⟨hpU₀,?_⟩,r,hr.mono inter_subset_left,?_,?_⟩
  · change p ∈ normalTrace F ⁻¹' W
    rw [hWeq]
    exact hpO
  · intro q hq
    have hqO : q ∈ O := by rw [← hWeq]; exact hq.2
    have hqη : η q ∈ e.source := hqO.2
    have hqV : ((q.1 : ℝ),(c.extend (𝓡∂ 2)) q.2) ∈ V := by
      have hv := heV hqη
      simpa only [η,mem_preimage,ContinuousLinearEquiv.apply_symm_apply] using hv
    have hh := hGeq ((q.1 : ℝ),(c.extend (𝓡∂ 2)) q.2) hqV q.1.property (mem_range_self (c q.2))
    have ht : projIcc 0 1 (by norm_num) (q.1 : ℝ) = q.1 :=
      Subtype.ext (by simp [projIcc_of_mem (show (0:ℝ) ≤ 1 by norm_num) q.1.property])
    have hmatch : ψ (normalTrace F q) = e (η q) := by
      rw [hemap]
      change ψ (normalTrace F q) = ((q.1 : ℝ),splitSurface.symm (R (G ((q.1 : ℝ),splitSurface (splitSurface.symm ((c.extend (𝓡∂ 2)) q.2))))))
      rw [ContinuousLinearEquiv.apply_symm_apply,hh.2.2,ht,
        (c.extend (𝓡∂ 2)).left_inv (by simpa using hqO.1.2)]
      rfl
    change c.symm ((𝓡∂ 2).symm (splitSurface (e.symm (ψ (normalTrace F q))).2)) = q.2
    rw [hmatch,e.left_inv hqη]
    dsimp [η]
    rw [ContinuousLinearEquiv.apply_symm_apply]
    change c.symm ((𝓡∂ 2).symm ((𝓡∂ 2) (c q.2))) = q.2
    rw [(𝓡∂ 2).left_inv,c.left_inv hqO.1.2]
  · intro q hq hqb
    have hcy : r q ∈ c.source := c.map_target hq.1.2
    apply (chart_boundary_normal_iff c hc hcy).mpr
    change (𝓡∂ 2) (c (c.symm (θ q))) 0 = 0
    rw [c.right_inv hq.1.2,hθread q hq.1.1,splitSurface_zero]
    apply (hesign (ψ q) hq.1.1.2 q.1.property).2.mpr
    change (splitSurface.symm (R ((d.extend (𝓡∂ 3)) q.2))).1 = 0
    rw [splitSurface_symm_zero,hRn]
    have hb := (chart_boundary_normal_iff d hd hq.1.1.1.2).mp hqb
    change (𝓡∂ 3) (d q.2) 0 / a = 0
    rw [hb,zero_div]

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
