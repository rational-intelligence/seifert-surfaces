import ActualRelativeRadialSqueezeHomeomorphV891
import ActualDiskFixedPlanarInverseIsotopyV890
import ActualDiskFixedConfinedIsotopyV767
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Topology Metric Filter
open SeifertSurfaces.Foundations
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualRelativeRadialSqueezeV765
noncomputable section
namespace CompressionActualGlobalConfinedAnnulusFamilyV892

abbrev Disk2 := Metric.closedBall (0 : Plane) 2

/-- A supplied whole disk embedding which fixes the entire inner disk can be
    joined to the identity through embeddings confined to the same outer disk.
    The construction shrinks the source before using the relative global family. -/
theorem disk_fixed_global_confined_isotopy (H : Plane ≃ₜ Plane)
    (hfix : ∀ x,‖x‖ ≤ 1 → H x = x)
    (houter : ∀ x,‖x‖ ≤ 2 → ‖H x‖ ≤ 2) :
    ∃ G : Time → Plane ≃ₜ Plane,
      Continuous (fun p : Time × Plane => G p.1 p.2) ∧
      Continuous (fun p : Time × Plane => (G p.1).symm p.2) ∧
      (∀ x,G 0 x = H x) ∧ (∀ x,G 1 x = x) ∧
      (∀ t x,‖x‖ ≤ 1 → G t x = x) ∧
      ∀ t x,‖x‖ ≤ 2 → ‖G t x‖ ≤ 2 := by
  classical
  obtain ⟨K,hK,hKi,hK0,hK1,hKfix⟩ :=
    CompressionActualDiskFixedPlanarInverseIsotopyV890.disk_fixed_homeomorph_inverse_isotopy H hfix
  obtain ⟨η,hη,hη1,hnear⟩ := CompressionActualDiskFixedConfinedIsotopyV767.compact_fixed_disk_uniform_collar K hK hKfix
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
  let p₀ : Time × Plane → Plane := fun p => H (squeeze (a p.1) p.2)
  let p₁ : Time × Plane → Plane := fun p => K (s p.1) (squeeze η p.2)
  let p₂ : Time × Plane → Plane := fun p => squeeze (b p.1) p.2
  have hp₀ : Continuous p₀ := H.continuous.comp (squeeze_joint_continuous.comp
    ((hac.comp continuous_fst).prodMk continuous_snd))
  have hp₁ : Continuous p₁ := hK.comp ((hsc.comp continuous_fst).prodMk
    (squeeze_joint_continuous.comp (continuous_const.prodMk continuous_snd)))
  have hp₂ : Continuous p₂ := squeeze_joint_continuous.comp
    ((hbc.comp continuous_fst).prodMk continuous_snd)
  let p₁₂ : Time × Plane → Plane := fun p => if (p.1:ℝ) ≤ 2/3 then p₁ p else p₂ p
  have hp₁₂ : Continuous p₁₂ := by
    apply continuous_if_le continuous_fst.subtype_val continuous_const hp₁.continuousOn hp₂.continuousOn
    intro p hp
    have ht : p.1 = ⟨2/3,by norm_num⟩ := Subtype.ext hp
    dsimp only [p₁,p₂]
    rw [ht,hs23,hK0,hb23]
  let gf : Time × Plane → Plane := fun p => if (p.1:ℝ) ≤ 1/3 then p₀ p else p₁₂ p
  have hGc : Continuous gf := by
    apply continuous_if_le continuous_fst.subtype_val continuous_const hp₀.continuousOn hp₁₂.continuousOn
    intro p hp
    have ht : p.1 = ⟨1/3,by norm_num⟩ := Subtype.ext hp
    dsimp only [p₁₂]
    rw [ite_eq_left (by rw [hp]; norm_num)]
    dsimp only [p₀,p₁]
    rw [ht,ha13,hs13,hK1]
  let G (t : Time) : Plane ≃ₜ Plane :=
    if t.val ≤ 1/3 then (CompressionActualRelativeRadialSqueezeHomeomorphV891.squeezeHomeomorph (a t) (hap t)).trans H
    else if t.val ≤ 2/3 then (CompressionActualRelativeRadialSqueezeHomeomorphV891.squeezeHomeomorph η hη).trans (K (s t))
    else CompressionActualRelativeRadialSqueezeHomeomorphV891.squeezeHomeomorph (b t) (hbp t)
  have hGv (t : Time) (x : Plane) : G t x = (if t.val ≤ 1/3 then p₀ (t,x) else p₁₂ (t,x)) := by
    dsimp only [G,p₁₂,p₀,p₁,p₂]
    split_ifs <;> rfl
  have hGcont : Continuous (fun p : Time × Plane => G p.1 p.2) :=
    hGc.congr (fun p => (hGv p.1 p.2).symm)
  have haic : Continuous (fun t : Time => (1:ℝ)/(a t)) :=
    continuous_const.div hac (fun t => (hap t).ne')
  have hbic : Continuous (fun t : Time => (1:ℝ)/(b t)) :=
    continuous_const.div hbc (fun t => (hbp t).ne')
  let i₀ : Time × Plane → Plane := fun p => squeeze (1/a p.1) (H.symm p.2)
  let i₁ : Time × Plane → Plane := fun p => squeeze (1/η) ((K (s p.1)).symm p.2)
  let i₂ : Time × Plane → Plane := fun p => squeeze (1/b p.1) p.2
  have hi₀ : Continuous i₀ := squeeze_joint_continuous.comp
    ((haic.comp continuous_fst).prodMk (H.symm.continuous.comp continuous_snd))
  have hi₁ : Continuous i₁ := squeeze_joint_continuous.comp
    (continuous_const.prodMk (hKi.comp ((hsc.comp continuous_fst).prodMk continuous_snd)))
  have hi₂ : Continuous i₂ := squeeze_joint_continuous.comp
    ((hbic.comp continuous_fst).prodMk continuous_snd)
  let i₁₂ : Time × Plane → Plane := fun p => if p.1.val ≤ 2/3 then i₁ p else i₂ p
  have hi₁₂ : Continuous i₁₂ := by
    apply continuous_if_le continuous_fst.subtype_val continuous_const hi₁.continuousOn hi₂.continuousOn
    intro p hp
    have ht : p.1 = ⟨2/3,by norm_num⟩ := Subtype.ext hp
    dsimp only [i₁,i₂]
    rw [ht,hs23,hb23]
    have he : (K 0).symm p.2 = p.2 := (K 0).injective (by rw [(K 0).apply_symm_apply,hK0])
    rw [he]
  let gi : Time × Plane → Plane := fun p => if p.1.val ≤ 1/3 then i₀ p else i₁₂ p
  have hgi : Continuous gi := by
    apply continuous_if_le continuous_fst.subtype_val continuous_const hi₀.continuousOn hi₁₂.continuousOn
    intro p hp
    have ht : p.1 = ⟨1/3,by norm_num⟩ := Subtype.ext hp
    dsimp only [i₁₂]
    rw [ite_eq_left (by rw [hp]; norm_num)]
    dsimp only [i₀,i₁]
    rw [ht,ha13,hs13]
    have he : (K 1).symm p.2 = H.symm p.2 := (K 1).injective
      (by rw [(K 1).apply_symm_apply,hK1,H.apply_symm_apply])
    rw [he]
  have hgiv (t : Time) (x : Plane) : (G t).symm x = gi (t,x) := by
    dsimp only [G,gi,i₁₂,i₀,i₁,i₂]
    split_ifs <;> rfl
  refine ⟨G,hGcont,hgi.congr (fun p => (hgiv p.1 p.2).symm),?_,?_,?_,?_⟩
  · intro x
    rw [hGv]
    dsimp only [p₀]
    rw [ite_eq_left (by norm_num),ha0,squeeze_one]
  · intro x
    rw [hGv]
    dsimp only [p₁₂,p₂]
    rw [ite_eq_right (by norm_num),ite_eq_right (by norm_num),hbend,squeeze_one]
  · intro t x hx
    rw [hGv]
    dsimp only [p₁₂,p₀,p₁,p₂]
    split_ifs
    · exact (congrArg H (squeeze_fixed _ _ hx)).trans (hfix _ hx)
    · exact (congrArg (K (s t)) (squeeze_fixed _ _ hx)).trans (hKfix _ _ hx)
    · exact squeeze_fixed _ _ hx
  · intro t x hx
    rw [hGv]
    dsimp only [p₁₂,p₀,p₁,p₂]
    split_ifs
    · exact houter _ ((squeeze_norm_le _ (hap t) (ha1 t) x).trans hx)
    · apply (hnear (s t) _ _).le
      by_cases hx1 : ‖x‖ ≤ 1
      · rw [squeeze_fixed η x hx1]
        linarith
      · rw [squeeze_norm_outer η hη x (le_of_not_ge hx1)]
        nlinarith
    · exact (squeeze_norm_le _ (hbp t) (hb1 t) x).trans hx

#print axioms disk_fixed_global_confined_isotopy
end CompressionActualGlobalConfinedAnnulusFamilyV892
