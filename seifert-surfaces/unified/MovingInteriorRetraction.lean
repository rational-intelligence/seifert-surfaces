import MovingInteriorInverse

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
theorem normal_exists_moving_interior_retraction (F : SmoothNormalIsotopy S M f g)
    (p : Time × S) (hp : p.2 ∉ S.boundary) :
    ∃ U : Set (Time × M), IsOpen U ∧ normalTrace F p ∈ U ∧
      ∃ r : Time × M → S,
        ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 2) ∞ r U ∧
        (∀ q, normalTrace F q ∈ U → r (normalTrace F q) = q.2) ∧
        ∀ q ∈ U, q.2 ∈ (𝓡∂ 3).boundary M → r q ∈ S.boundary := by
  obtain ⟨c,d,R,V,G,e,hc,hd,hpc,hfpd,hV,hpV,hG,hGeq,hpe,heV,he,hei,hemap,heparam⟩ :=
    normal_exists_moving_inverse F p.1 p.2
  let ψ : Time × M → ℝ × Euc 2 :=
    fun q => ((q.1 : ℝ), R ((d.extend (𝓡∂ 3)) q.2))
  let C : Set (Time × M) := univ ×ˢ d.source
  have hC : IsOpen C := isOpen_univ.prod d.open_source
  have hψ : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3))
      𝓘(ℝ, ℝ × Euc 2) ∞ ψ C := by
    have hdext : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, Euc 3) ∞ (d.extend (𝓡∂ 3)) d.source :=
      (𝓡∂ 3).contMDiff.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas hd)
    exact ((contMDiff_subtypeVal_Icc (x := 0) (y := 1)).comp contMDiff_fst).contMDiffOn.prodMk_space
      (R.contDiff.contMDiff.comp_contMDiffOn
        (hdext.comp contMDiffOn_snd (fun _ hq => hq.2)))
  let D₀ : Set (Time × M) := C ∩ ψ ⁻¹' e.target
  have hD₀ : IsOpen D₀ := hψ.continuousOn.isOpen_inter_preimage hC e.open_target
  let ξ : Time × M → Euc 2 := fun q => (e.symm (ψ q)).2
  have hξ : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) 𝓘(ℝ, Euc 2) ∞ ξ D₀ :=
    contDiff_snd.contMDiff.comp_contMDiffOn
      (hei.contMDiffOn.comp (hψ.mono inter_subset_left) inter_subset_right)
  let D : Set (Time × M) := D₀ ∩ ξ ⁻¹' interior (range (𝓡∂ 2))
  have hD : IsOpen D := hξ.continuousOn.isOpen_inter_preimage hD₀ isOpen_interior
  have hbase : ψ (normalTrace F p) = e ((p.1 : ℝ),(c.extend (𝓡∂ 2)) p.2) := by
    have hh := hGeq ((p.1 : ℝ),(c.extend (𝓡∂ 2)) p.2) hpV p.1.property (mem_range_self (c p.2))
    have ht : projIcc 0 1 (by norm_num) (p.1 : ℝ) = p.1 :=
      Subtype.ext (by simp [projIcc_of_mem (show (0:ℝ) ≤ 1 by norm_num) p.1.property])
    rw [hemap]
    rw [hh.2.2,ht,
      (c.extend (𝓡∂ 2)).left_inv (by simpa using hpc)]
    rfl
  have hu : (c.extend (𝓡∂ 2)) p.2 ∈ interior (range (𝓡∂ 2)) := by
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    have hne : (𝓡∂ 2) (c p.2) 0 ≠ 0 := fun hz => hp ((chart_boundary_normal_iff c hc hpc).mpr hz)
    exact lt_of_le_of_ne (c p.2).property hne.symm
  have hpD : normalTrace F p ∈ D := by
    refine ⟨⟨⟨mem_univ _,hfpd⟩,?_⟩,?_⟩
    · change ψ (normalTrace F p) ∈ e.target
      rw [hbase]
      exact e.map_source hpe
    · change (e.symm (ψ (normalTrace F p))).2 ∈ interior (range (𝓡∂ 2))
      rw [hbase,e.left_inv hpe]
      exact hu
  let θ : Time × M → EuclideanHalfSpace 2 := fun q => (𝓡∂ 2).symm (ξ q)
  have hθread (q : Time × M) (hq : q ∈ D) : (𝓡∂ 2) (θ q) = ξ q :=
    (𝓡∂ 2).right_inv (interior_subset hq.2)
  have hθ : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 2) ∞ θ D :=
    (𝓡∂ 2).contMDiffOn_symm.comp (hξ.mono inter_subset_left)
      (fun q hq => (show ξ q ∈ range (𝓡∂ 2) from interior_subset hq.2))
  let U₀ : Set (Time × M) := D ∩ θ ⁻¹' c.target
  have hU₀ : IsOpen U₀ := hθ.continuousOn.isOpen_inter_preimage hD c.open_target
  have hθbase : θ (normalTrace F p) = c p.2 := by
    dsimp [θ,ξ]
    rw [hbase,e.left_inv hpe]
    exact (𝓡∂ 2).left_inv (c p.2)
  have hpU₀ : normalTrace F p ∈ U₀ := ⟨hpD,by
    change θ (normalTrace F p) ∈ c.target
    rw [hθbase]
    exact c.map_source hpc⟩
  let r : Time × M → S := fun q => c.symm (θ q)
  have hr : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 2) ∞ r U₀ :=
    (contMDiffOn_symm_of_mem_maximalAtlas hc).comp (hθ.mono inter_subset_left) inter_subset_right
  let η : Time × S → ℝ × Euc 2 :=
    fun q => ((q.1 : ℝ), (c.extend (𝓡∂ 2)) q.2)
  let B : Set (Time × S) := univ ×ˢ c.source
  have hB : IsOpen B := isOpen_univ.prod c.open_source
  have hη : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 2))
      𝓘(ℝ, ℝ × Euc 2) ∞ η B := by
    have hcext : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ, Euc 2) ∞ (c.extend (𝓡∂ 2)) c.source :=
      (𝓡∂ 2).contMDiff.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas hc)
    exact ((contMDiff_subtypeVal_Icc (x := 0) (y := 1)).comp contMDiff_fst).contMDiffOn.prodMk_space
      (hcext.comp contMDiffOn_snd (fun _ hq => hq.2))
  let O : Set (Time × S) := B ∩ η ⁻¹' e.source
  have hO : IsOpen O := hη.continuousOn.isOpen_inter_preimage hB e.open_source
  have hpO : p ∈ O := ⟨⟨mem_univ _,hpc⟩,hpe⟩
  obtain ⟨W,hW,hWeq⟩ := (normalTrace_isClosedEmbedding F).isEmbedding.isInducing.isOpen_iff.mp hO
  let I : Set (Time × M) := univ ×ˢ ((𝓡∂ 3).boundary M)ᶜ
  have hI : IsOpen I := isOpen_univ.prod
    ((ModelWithCorners.isClosed_boundary (I := 𝓡∂ 3) (n := ∞) (by simp)).isOpen_compl)
  have hpI : normalTrace F p ∈ I := by
    refine ⟨mem_univ _,?_⟩
    change p.2 ∉ (F.stage p.1).toFun ⁻¹' (𝓡∂ 3).boundary M
    rwa [(F.stage p.1).boundary_preimage]
  let U : Set (Time × M) := (U₀ ∩ W) ∩ I
  refine ⟨U,(hU₀.inter hW).inter hI,⟨⟨hpU₀,?_⟩,hpI⟩,r,
    hr.mono (inter_subset_left.trans inter_subset_left),?_,?_⟩
  · change p ∈ normalTrace F ⁻¹' W
    rw [hWeq]
    exact hpO
  · intro q hq
    have hqO : q ∈ O := by rw [← hWeq]; exact hq.1.2
    have hqη : η q ∈ e.source := hqO.2
    have hqV : ((q.1 : ℝ),(c.extend (𝓡∂ 2)) q.2) ∈ V := heV hqη
    have hh := hGeq ((q.1 : ℝ),(c.extend (𝓡∂ 2)) q.2) hqV q.1.property (mem_range_self (c q.2))
    have ht : projIcc 0 1 (by norm_num) (q.1 : ℝ) = q.1 :=
      Subtype.ext (by simp [projIcc_of_mem (show (0:ℝ) ≤ 1 by norm_num) q.1.property])
    have hmatch : ψ (normalTrace F q) = e (η q) := by
      rw [hemap]
      change ψ (normalTrace F q) = ((q.1 : ℝ),R (G ((q.1 : ℝ),(c.extend (𝓡∂ 2)) q.2)))
      rw [hh.2.2,ht,(c.extend (𝓡∂ 2)).left_inv (by simpa using hqO.1.2)]
      rfl
    change c.symm ((𝓡∂ 2).symm (e.symm (ψ (normalTrace F q))).2) = q.2
    rw [hmatch,e.left_inv hqη]
    change c.symm ((𝓡∂ 2).symm ((𝓡∂ 2) (c q.2))) = q.2
    rw [(𝓡∂ 2).left_inv,c.left_inv hqO.1.2]
  · intro q hq hqb
    exact False.elim (hq.2.2 hqb)

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
