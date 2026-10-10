import ActualRelativeRadialSqueezeV765
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Topology Metric Filter
open SeifertSurfaces.Foundations
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualRelativeRadialSqueezeV765
noncomputable section
namespace CompressionActualDiskFixedConfinedIsotopyV767

abbrev Disk2 := Metric.closedBall (0 : Plane) 2

/-- A joint family fixing the unit disk has one positive collar which stays
    inside the radius-two disk uniformly over its whole parameter interval. -/
theorem compact_fixed_disk_uniform_collar
    (K : Time → Plane ≃ₜ Plane)
    (hK : Continuous (fun p : Time × Plane => K p.1 p.2))
    (hfix : ∀ t x,‖x‖ ≤ 1 → K t x = x) :
    ∃ η : ℝ,0 < η ∧ η ≤ 1 ∧ ∀ t x,‖x‖ ≤ 1+η → ‖K t x‖ < 2 := by
  let O : Set (Time × Plane) := {p | ‖K p.1 p.2‖ < 2}
  have hO : IsOpen O := isOpen_lt hK.norm continuous_const
  have hcontain : (Set.univ : Set Time) ×ˢ Metric.closedBall (0 : Plane) 1 ⊆ O := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    have hn : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    change ‖K t x‖ < 2
    rw [hfix t x hn]
    linarith
  obtain ⟨D,V,hD,hV,hall,hKV,hDV⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (Set.univ : Set Time)) (isCompact_closedBall (0 : Plane) 1)
    hO hcontain
  obtain ⟨δ,hδ,hδV⟩ := (isCompact_closedBall (0 : Plane) 1).exists_cthickening_subset_open hV hKV
  let η : ℝ := min (δ/2) (1/2)
  have hη : 0 < η := lt_min (half_pos hδ) (by norm_num)
  have hηδ : η ≤ δ := (min_le_left _ _).trans (by linarith)
  refine ⟨η,hη,(min_le_right _ _).trans (by norm_num),?_⟩
  intro t x hx
  have hxthick : x ∈ cthickening δ (Metric.closedBall (0 : Plane) 1) := by
    rw [cthickening_closedBall hδ.le (by norm_num),mem_closedBall_zero_iff]
    linarith
  have hmem : (t,x) ∈ D ×ˢ V := ⟨hall (mem_univ t),hδV hxthick⟩
  have hval : (t,x) ∈ O := hDV hmem
  exact hval

/-- A supplied whole disk embedding which fixes the entire inner disk can be
    joined to the identity through embeddings confined to the same outer disk.
    The construction shrinks the source before using the relative global family. -/
theorem disk_fixed_confined_embedding_isotopy (H : Plane ≃ₜ Plane)
    (hfix : ∀ x,‖x‖ ≤ 1 → H x = x)
    (houter : ∀ x,‖x‖ ≤ 2 → ‖H x‖ ≤ 2) :
    ∃ G : C(Time × Disk2,Plane),
      (∀ t,IsEmbedding (fun x : Disk2 => G (t,x))) ∧
      (∀ x,G (0,x) = H x) ∧ (∀ x,G (1,x) = x.val) ∧
      (∀ t x,‖x.val‖ ≤ 1 → G (t,x) = x.val) ∧
      ∀ t x,‖G (t,x)‖ ≤ 2 := by
  classical
  obtain ⟨K,hK,hK0,hK1,hKfix⟩ :=
    CompressionActualDiskFixedPlanarIsotopyV757.disk_fixed_homeomorph_isotopy H hfix
  obtain ⟨η,hη,hη1,hnear⟩ := compact_fixed_disk_uniform_collar K hK hKfix
  let a : Time → ℝ := fun t => max η (1-3*(t:ℝ)*(1-η))
  let b : Time → ℝ := fun t => max η (min 1 (η+(3*(t:ℝ)-2)*(1-η)))
  let s : Time → Time := fun t => Set.projIcc 0 1 zero_le_one (2-3*(t:ℝ))
  have hac : Continuous a := continuous_const.max
    (continuous_const.sub ((continuous_const.mul continuous_subtype_val).mul continuous_const))
  have hbc : Continuous b := by dsimp [b]; fun_prop
  have hsc : Continuous s := continuous_projIcc.comp
    (continuous_const.sub (continuous_const.mul continuous_subtype_val))
  have hap (t : Time) : 0 < a t := hη.trans_le (le_max_left _ _)
  have hbp (t : Time) : 0 < b t := hη.trans_le (le_max_left _ _)
  have ha1 (t : Time) : a t ≤ 1 := max_le hη1 (by
    nlinarith [t.property.1])
  have hb1 (t : Time) : b t ≤ 1 := max_le hη1 (min_le_left _ _)
  have ha0 : a 0 = 1 := by dsimp [a]; simp [max_eq_right hη1]
  have ha13 : a ⟨1/3,by norm_num⟩ = η := by
    dsimp [a]
    have he : (1:ℝ)-3*(1/3)*(1-η)=η := by ring
    rw [he,max_self]
  have hb23 : b ⟨2/3,by norm_num⟩ = η := by
    dsimp [b]
    have he : η+(3*(2/3)-2)*(1-η)=η := by ring
    rw [he,min_eq_right hη1,max_self]
  have hbend : b 1 = 1 := by
    dsimp [b]
    have he : η+(3*1-2)*(1-η)=(1:ℝ) := by ring
    rw [he,min_self,max_eq_right hη1]
  have hs13 : s ⟨1/3,by norm_num⟩ = 1 := by
    apply Subtype.ext
    dsimp [s]
    norm_num
  have hs23 : s ⟨2/3,by norm_num⟩ = 0 := by
    apply Subtype.ext
    dsimp [s]
    norm_num
  let p₀ : Time × Disk2 → Plane := fun p => H (squeeze (a p.1) p.2.val)
  let p₁ : Time × Disk2 → Plane := fun p => K (s p.1) (squeeze η p.2.val)
  let p₂ : Time × Disk2 → Plane := fun p => squeeze (b p.1) p.2.val
  have hp₀ : Continuous p₀ := H.continuous.comp (squeeze_joint_continuous.comp
    ((hac.comp continuous_fst).prodMk continuous_snd.subtype_val))
  have hp₁ : Continuous p₁ := hK.comp ((hsc.comp continuous_fst).prodMk
    (squeeze_joint_continuous.comp (continuous_const.prodMk continuous_snd.subtype_val)))
  have hp₂ : Continuous p₂ := squeeze_joint_continuous.comp
    ((hbc.comp continuous_fst).prodMk continuous_snd.subtype_val)
  let p₁₂ : Time × Disk2 → Plane := fun p => if (p.1:ℝ) ≤ 2/3 then p₁ p else p₂ p
  have hp₁₂ : Continuous p₁₂ := by
    apply continuous_if_le continuous_fst.subtype_val continuous_const hp₁.continuousOn hp₂.continuousOn
    intro p hp
    have ht : p.1 = ⟨2/3,by norm_num⟩ := Subtype.ext hp
    dsimp only [p₁,p₂]
    rw [ht,hs23,hK0,hb23]
  let G : Time × Disk2 → Plane := fun p => if (p.1:ℝ) ≤ 1/3 then p₀ p else p₁₂ p
  have hGc : Continuous G := by
    apply continuous_if_le continuous_fst.subtype_val continuous_const hp₀.continuousOn hp₁₂.continuousOn
    intro p hp
    have ht : p.1 = ⟨1/3,by norm_num⟩ := Subtype.ext hp
    dsimp only [p₁₂]
    rw [ite_eq_left (by rw [hp]; norm_num)]
    dsimp only [p₀,p₁]
    rw [ht,ha13,hs13,hK1]
  have hGinj (t : Time) : Function.Injective (fun x : Disk2 => G (t,x)) := by
    intro x y he
    dsimp only [G,p₁₂] at he
    split_ifs at he with ht ht
    · exact Subtype.ext (squeeze_injective (a t) (hap t) (H.injective he))
    · exact Subtype.ext (squeeze_injective η hη ((K (s t)).injective he))
    · exact Subtype.ext (squeeze_injective (b t) (hbp t) he)
  have hGcont (t : Time) : Continuous (fun x : Disk2 => G (t,x)) :=
    hGc.comp (continuous_const.prodMk continuous_id)
  refine ⟨⟨G,hGc⟩,fun t => ((hGcont t).isClosedEmbedding (hGinj t)).isEmbedding,?_,?_,?_,?_⟩
  · intro x
    change G (0,x) = H x.val
    dsimp only [G]
    rw [ite_eq_left (by norm_num)]
    dsimp only [p₀]
    rw [ha0,squeeze_one]
  · intro x
    change G (1,x) = x.val
    dsimp only [G,p₁₂]
    rw [ite_eq_right (by norm_num),ite_eq_right (by norm_num)]
    dsimp only [p₂]
    rw [hbend,squeeze_one]
  · intro t x hx
    change G (t,x) = x.val
    dsimp only [G,p₁₂]
    split_ifs
    · exact (congrArg H (squeeze_fixed _ _ hx)).trans (hfix _ hx)
    · exact (congrArg (K (s t)) (squeeze_fixed _ _ hx)).trans (hKfix _ _ hx)
    · exact squeeze_fixed _ _ hx
  · intro t x
    change ‖G (t,x)‖ ≤ 2
    have hx : ‖x.val‖ ≤ 2 := mem_closedBall_zero_iff.mp x.property
    dsimp only [G,p₁₂]
    split_ifs
    · exact houter _ ((squeeze_norm_le _ (hap t) (ha1 t) x.val).trans hx)
    · apply (hnear (s t) _ _).le
      by_cases hx1 : ‖x.val‖ ≤ 1
      · rw [squeeze_fixed η x.val hx1]
        linarith
      · rw [squeeze_norm_outer η hη x.val (le_of_not_ge hx1)]
        nlinarith
    · exact (squeeze_norm_le _ (hbp t) (hb1 t) x.val).trans hx

end CompressionActualDiskFixedConfinedIsotopyV767
