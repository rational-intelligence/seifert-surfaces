import ActualAnnulusHalfPolarModelV768
import ActualDiskFixedConfinedIsotopyV767

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualPlanarPolarCoordinatesV761
open CompressionActualAnnulusHalfPolarModelV768
noncomputable section
namespace CompressionActualAnnulusHalfRelativeFamilyV769

/-- Deform the whole supplied annulus-half embedding to the identity within
    that annulus half, fixing the core circle pointwise throughout. -/
theorem annulus_half_relative_embedding_family
    (β : C(Circle × Time,Circle × Time)) (hβ : IsEmbedding β)
    (hcore : ∀ z,β (z,0) = (z,0))
    (hpositive : ∀ z t,t ≠ 0 → 0 < (β (z,t)).2.val) :
    ∃ Γ : C(Time × (Circle × Time),Circle × Time),
      (∀ s,IsEmbedding (fun p => Γ (s,p))) ∧
      (∀ p,Γ (0,p) = β p) ∧ (∀ p,Γ (1,p) = p) ∧
      (∀ s z,Γ (s,(z,0)) = (z,0)) ∧
      ∀ s z t,t ≠ 0 → 0 < (Γ (s,(z,t))).2.val := by
  classical
  let q : C(Circle × Time,Plane) := ⟨polar ∘ β,polar_continuous.comp β.continuous⟩
  have hq : IsEmbedding q := polar_embedding.comp hβ
  have hq0 (z : Circle) : q (z,0) = circleVector z := by
    change polar (β (z,0)) = _
    rw [hcore]
    simp [polar]
  have hqout (z : Circle) (t : Time) (ht : t ≠ 0) : 1 < ‖q (z,t)‖ := by
    change 1 < ‖polar (β (z,t))‖
    rw [polar_norm]
    linarith [hpositive z t ht]
  obtain ⟨H,hHfix,hHq⟩ :=
    CompressionActualAnnulusHalfWholeExtensionV762.annulus_half_whole_extension q hq hq0 hqout
  have hHouter (x : Plane) (hx : ‖x‖ ≤ 2) : ‖H x‖ ≤ 2 := by
    by_cases hx1 : ‖x‖ ≤ 1
    · rw [hHfix x hx1]
      linarith
    · let p := coord x (le_of_not_ge hx1) hx
      have hp : polar p = x := polar_coord x (le_of_not_ge hx1) hx
      have he : H x = q p := by
        rw [← hp]
        exact hHq p.1 p.2
      rw [he]
      change ‖polar (β p)‖ ≤ 2
      rw [polar_norm]
      linarith [(β p).2.property.2]
  obtain ⟨G,hG,hG0,hG1,hGfix,hGbound⟩ :=
    CompressionActualDiskFixedConfinedIsotopyV767.disk_fixed_confined_embedding_isotopy H hHfix hHouter
  let ip : Circle × Time → CompressionActualDiskFixedConfinedIsotopyV767.Disk2 := fun p =>
    ⟨polar p,mem_closedBall_zero_iff.mpr (by rw [polar_norm]; linarith [p.2.property.2])⟩
  have hip : Continuous ip := polar_continuous.subtype_mk _
  let w : Time × (Circle × Time) → Plane := fun p => G (p.1,ip p.2)
  have hw : Continuous w := G.continuous.comp (continuous_fst.prodMk (hip.comp continuous_snd))
  have hwbound (s : Time) (p : Circle × Time) : ‖w (s,p)‖ ≤ 2 := hGbound s (ip p)
  have hwlower (s : Time) (p : Circle × Time) : 1 ≤ ‖w (s,p)‖ := by
    apply not_lt.mp
    intro hn
    let y : CompressionActualDiskFixedConfinedIsotopyV767.Disk2 :=
      ⟨w (s,p),mem_closedBall_zero_iff.mpr (by linarith)⟩
    have hy : G (s,y) = w (s,p) := hGfix s y hn.le
    have he : ip p = y := (hG s).injective hy.symm
    have hn' : ‖polar p‖ = ‖w (s,p)‖ := congrArg (fun x => ‖x.val‖) he
    rw [polar_norm] at hn'
    linarith [p.2.property.1]
  have hwne (p : Time × (Circle × Time)) : w p ≠ 0 := by
    intro he
    have hh := hwlower p.1 p.2
    rw [he,norm_zero] at hh
    norm_num at hh
  let Γ : Time × (Circle × Time) → Circle × Time :=
    fun p => coord (w p) (hwlower p.1 p.2) (hwbound p.1 p.2)
  have hΓc : Continuous Γ := by
    apply Continuous.prodMk
    · exact angle_continuousOn.comp_continuous hw (fun p => hwne p)
    · exact (hw.norm.sub continuous_const).subtype_mk _
  have hΓpolar (s : Time) (p : Circle × Time) : polar (Γ (s,p)) = w (s,p) :=
    polar_coord _ _ _
  have hΓinj (s : Time) : Function.Injective (fun p => Γ (s,p)) := by
    intro p r he
    have hh : G (s,ip p) = G (s,ip r) := by
      change w (s,p) = w (s,r)
      exact (hΓpolar s p).symm.trans ((congrArg polar he).trans (hΓpolar s r))
    have hi : ip p = ip r := (hG s).injective hh
    exact polar_injective (congrArg Subtype.val hi)
  have hΓ0 (p : Circle × Time) : Γ (0,p) = β p := by
    apply polar_injective
    rw [hΓpolar]
    change G (0,ip p) = polar (β p)
    rw [hG0]
    exact hHq p.1 p.2
  have hΓ1 (p : Circle × Time) : Γ (1,p) = p := by
    apply polar_injective
    rw [hΓpolar]
    exact hG1 (ip p)
  have hΓcore (s : Time) (z : Circle) : Γ (s,(z,0)) = (z,0) := by
    apply polar_injective
    rw [hΓpolar]
    exact hGfix s (ip (z,0)) (by change ‖polar (z,0)‖ ≤ 1; rw [polar_norm]; norm_num)
  refine ⟨⟨Γ,hΓc⟩,?_,hΓ0,hΓ1,hΓcore,?_⟩
  · intro s
    exact ((hΓc.comp (continuous_const.prodMk continuous_id)).isClosedEmbedding
      (hΓinj s)).isEmbedding
  · intro s z t ht
    change 0 < (Γ (s,(z,t))).2.val
    have hn : (Γ (s,(z,t))).2 ≠ 0 := by
      intro he
      have hp : Γ (s,(z,t)) = ((Γ (s,(z,t))).1,0) := Prod.ext rfl he
      have hh : (z,t) = ((Γ (s,(z,t))).1,0) := (hΓinj s) (hp.trans (hΓcore s _).symm)
      exact ht (congrArg Prod.snd hh)
    have hv : (Γ (s,(z,t))).2.val ≠ 0 := by
      intro he
      exact hn (Subtype.ext he)
    exact lt_of_le_of_ne (Γ (s,(z,t))).2.property.1 hv.symm

end CompressionActualAnnulusHalfRelativeFamilyV769
