import Section5CoorientedVolumeV481
import Section5CoorientedLinearAlgebraV481

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations

variable {S : Type} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]

/-- A genuine rank-three collar in the oriented unit sphere induces an actual
smooth orientation on every source slice, including its boundary. -/
theorem sphere_collar_slice_orientation
    (ψ : S × ℝ → ThreeSphere) {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hψ : ContMDiffOn ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡 3) ∞ ψ (univ ×ˢ Ioo a b))
    (hrank : ∀ x : S, Injective (mfderiv ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡 3) ψ (x,t))) :
    Nonempty (SmoothVolumeOrientation (𝓡∂ 2) S) := by
  letI : Fact (Module.finrank ℝ (Euc 4) = 3 + 1) := ⟨by simp [Euc]⟩
  let G : S × ℝ → Euc 4 := fun q => (ψ q).val
  have hG : ContMDiffOn ((𝓡∂ 2).prod 𝓘(ℝ)) 𝓘(ℝ, Euc 4) ∞ G
      (univ ×ˢ Ioo a b) := (contMDiff_coe_sphere (E := Euc 4) (n := 3) (m := ∞)).comp_contMDiffOn hψ
  have hp (x : S) : ContMDiffAt ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡 3) ∞ ψ (x,t) :=
    hψ.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ x, ht⟩)
  have hg (x : S) : ContMDiffAt ((𝓡∂ 2).prod 𝓘(ℝ)) 𝓘(ℝ, Euc 4) ∞ G (x,t) :=
    hG.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ x, ht⟩)
  let f : S → Euc 4 := fun x => G (x,t)
  let n : S → Euc 4 := fun x => mfderiv 𝓘(ℝ) 𝓘(ℝ, Euc 4) (fun s => G (x,s)) t 1
  have hf : ContMDiff (𝓡∂ 2) 𝓘(ℝ, Euc 4) ∞ f := by
    intro x
    have hh := (hg x).comp (f := fun x : S => (x,t)) x
      (contMDiffAt_id.prodMk contMDiffAt_const)
    convert hh using 1 <;> rfl
  have hn : ContMDiff (𝓡∂ 2) 𝓘(ℝ, Euc 4) ∞ n := by
    intro x
    have hh := ContMDiffAt.mfderiv_apply (m := ∞) (n := ∞)
      (fun x : S => fun s : ℝ => G (x,s)) (fun _ : S => t) id (fun _ : S => (1 : ℝ))
      (hg x) contMDiffAt_const contMDiffAt_id contMDiffAt_const (by simp)
    simp only [inTangentCoordinates_model_space] at hh
    convert hh using 1 <;> rfl
  have hder (x : S) :
      mfderiv ((𝓡∂ 2).prod 𝓘(ℝ)) 𝓘(ℝ, Euc 4) G (x,t) =
        (mfderiv (𝓡 3) 𝓘(ℝ, Euc 4) (Subtype.val : ThreeSphere → Euc 4) (ψ (x,t))).comp
          (mfderiv ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡 3) ψ (x,t)) := by
    exact mfderiv_comp (x,t) ((contMDiff_coe_sphere (E := Euc 4) (n := 3) (m := ∞)).mdifferentiableAt (by simp))
      ((hp x).mdifferentiableAt (by simp))
  have hinj (x : S) : Injective (mfderiv ((𝓡∂ 2).prod 𝓘(ℝ)) 𝓘(ℝ, Euc 4) G (x,t)) := by
    rw [hder x]
    exact (mfderiv_coe_sphere_injective (n := 3) (ψ (x,t))).comp (hrank x)
  have horth (x : S) (v : TangentSpace ((𝓡∂ 2).prod 𝓘(ℝ)) (x,t)) :
      inner ℝ (f x) (mfderiv ((𝓡∂ 2).prod 𝓘(ℝ)) 𝓘(ℝ, Euc 4) G (x,t) v) = 0 := by
    have hmem : mfderiv ((𝓡∂ 2).prod 𝓘(ℝ)) 𝓘(ℝ, Euc 4) G (x,t) v ∈
        (ℝ ∙ (ψ (x,t)).val)ᗮ := by
      rw [← range_mfderiv_coe_sphere (n := 3) (ψ (x,t)), hder x]
      exact ⟨mfderiv ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡 3) ψ (x,t) v, rfl⟩
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem)
  have hleft (x : S) (v : TangentSpace (𝓡∂ 2) x) :
      mfderiv (𝓡∂ 2) 𝓘(ℝ, Euc 4) f x v =
        mfderiv ((𝓡∂ 2).prod 𝓘(ℝ)) 𝓘(ℝ, Euc 4) G (x,t) (v,0) := by
    have hh := mfderiv_comp x ((hg x).mdifferentiableAt (by simp))
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    simp only [id_eq] at hh
    rw [mfderiv_prod_left] at hh
    exact congrArg (fun L : Euc 2 →L[ℝ] Euc 4 => L v) hh
  have hright (x : S) : n x =
      mfderiv ((𝓡∂ 2).prod 𝓘(ℝ)) 𝓘(ℝ, Euc 4) G (x,t) (0,1) := by
    have hh := mfderiv_comp t ((hg x).mdifferentiableAt (by simp))
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    rw [mfderiv_prod_right] at hh
    exact congrArg (fun L : ℝ →L[ℝ] Euc 4 => L 1) hh
  apply cooriented_sphere_volume_orientation f n hf hn
  intro x
  apply contracted_sphere_determinant_ne_zero
  · have hnorm : ‖f x‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using (ψ (x,t)).property
    intro hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  · rw [hright x]
    exact horth x (0,1)
  · intro v
    exact (congrArg (fun z : Euc 4 => inner ℝ (f x) z) (hleft x v)).trans (horth x (v,0))
  · have heq (v : Euc 2 × ℝ) :
        (show Euc 4 from mfderiv (𝓡∂ 2) 𝓘(ℝ, Euc 4) f x v.1) + v.2 • n x =
        mfderiv ((𝓡∂ 2).prod 𝓘(ℝ)) 𝓘(ℝ, Euc 4) G (x,t) v := by
      rw [hleft x v.1, hright x]
      let d : Euc 2 × ℝ →L[ℝ] Euc 4 := mfderiv ((𝓡∂ 2).prod 𝓘(ℝ)) 𝓘(ℝ, Euc 4) G (x,t)
      change d (v.1,0) + v.2 • d (0,1) = d v
      calc
        d (v.1,0) + v.2 • d (0,1) = d (v.1,0) + d (v.2 • (0,1)) :=
          congrArg (fun w => d (v.1,0) + w) (d.map_smul v.2 (0,1)).symm
        _ = d ((v.1,0) + v.2 • (0,1)) := (d.map_add _ _).symm
        _ = d v := congrArg d (by ext <;> simp)
    intro v w hvw
    apply hinj x
    exact (heq v).symm.trans (hvw.trans (heq w))

#print axioms sphere_collar_slice_orientation

variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- The actual one-sided collar in the knot exterior constructs the source
orientation required by the original push-off lemma. No orientation of the
source is assumed. -/
theorem general_one_sided_collar_orientation
    (F : GeneralNeatImage E.Carrier) {U : Set E.Carrier}
    (C : GeneralOneSidedCollar F U) :
    Nonempty (SmoothVolumeOrientation (𝓡∂ 2) F.surface) := by
  let t : ℝ := C.epsilon / 2
  have ht : t ∈ Ioo (0 : ℝ) C.epsilon := ⟨half_pos C.positive, half_lt_self C.positive⟩
  let ψ : F.surface × ℝ → ThreeSphere := E.toSphere ∘ C.map
  have hsub : (univ ×ˢ Ioo (0 : ℝ) C.epsilon : Set (F.surface × ℝ)) ⊆
      univ ×ˢ Ico 0 C.epsilon := by
    rintro q ⟨h1,h2,h3⟩
    exact ⟨h1,h2.le,h3⟩
  have hs : ContMDiffOn ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3) ∞ C.map
      (univ ×ˢ Ioo (0 : ℝ) C.epsilon) := C.smooth.mono hsub
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  apply sphere_collar_slice_orientation ψ ht (hinc.isImmersion.contMDiff.comp_contMDiffOn hs)
  intro x
  have hnh : (univ ×ˢ Ico (0 : ℝ) C.epsilon : Set (F.surface × ℝ)) ∈ 𝓝 (x,t) :=
    Filter.mem_of_superset ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ x,ht⟩) hsub
  have hC : ContMDiffAt ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3) ∞ C.map (x,t) :=
    C.smooth.contMDiffAt hnh
  have hchain := mfderiv_comp (x,t) (hinc.isImmersion.contMDiff.mdifferentiableAt (by simp))
    (hC.mdifferentiableAt (by simp))
  change Injective (mfderiv ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡 3) (E.toSphere ∘ C.map) (x,t))
  rw [hchain]
  apply (hinc.isImmersion.mfderiv_injective (by simp) (C.map (x,t))).comp
  have hr := C.immersion (x,t) ⟨mem_univ x,ht.1.le,ht.2⟩
  rwa [mfderivWithin_of_mem_nhds hnh] at hr

#print axioms general_one_sided_collar_orientation
end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
