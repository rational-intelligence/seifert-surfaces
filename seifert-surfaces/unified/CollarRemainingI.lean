import CollarRemainingE
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse

set_option maxSynthPendingDepth 3
set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.LongitudeProducers.CollarCutHelpers.Remaining
open Foundations
universe u v w
noncomputable section

section Rank
variable {n : ℕ} [NeZero n] {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {N : Type w} [TopologicalSpace N] [ChartedSpace V N] [IsManifold 𝓘(ℝ,V) ∞ N]

structure HalfspaceCoordinateExtension (f : M → N) (x : M) where
  source : OpenPartialHomeomorph M (EuclideanHalfSpace n)
  target : OpenPartialHomeomorph N V
  source_mem : x ∈ source.source
  target_mem : f x ∈ target.source
  source_atlas : source ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M
  target_atlas : target ∈ IsManifold.maximalAtlas 𝓘(ℝ,V) ∞ N
  source_subset : source.source ⊆ f ⁻¹' target.source
  domain : Set (Euc n)
  domain_open : IsOpen domain
  point_mem : source.extend (𝓡∂ n) x ∈ domain
  extended_target_subset : (source.extend (𝓡∂ n)).target ⊆ domain
  extended : Euc n → V
  smooth : ContDiffOn ℝ ∞ extended domain
  agrees : EqOn extended (target ∘ f ∘ (source.extend (𝓡∂ n)).symm)
    (source.extend (𝓡∂ n)).target
  derivative : fderiv ℝ extended (source.extend (𝓡∂ n) x) =
    fderivWithin ℝ (target ∘ f ∘ (source.extend (𝓡∂ n)).symm)
      (source.extend (𝓡∂ n)).target (source.extend (𝓡∂ n) x)
  rank : Function.Injective (fderiv ℝ extended (source.extend (𝓡∂ n) x))
  first_factor : Euc n ≃L[ℝ] (ℝ × Euc (n-1))
  normal_first : ∀ u, (first_factor u).1 = u 0

theorem I1_halfspace_coordinate_extension (f : M → N)
    (hf : ContMDiff (𝓡∂ n) 𝓘(ℝ,V) ∞ f)
    (hrank : ∀ x, Function.Injective (mfderiv (𝓡∂ n) 𝓘(ℝ,V) f x)) (x : M) :
    Nonempty (HalfspaceCoordinateExtension (n := n) (V := V) f x) := by
  classical
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  let I := 𝓡∂ (k+1)
  let c := chartAt (EuclideanHalfSpace (k+1)) x
  let d := chartAt V (f x)
  let cf := c.restr (f ⁻¹' d.source)
  have hfxopen : IsOpen (f ⁻¹' d.source) := d.open_source.preimage hf.continuous
  have hcfatlas : cf ∈ IsManifold.maximalAtlas I ∞ M :=
    restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas x) hfxopen
  have hxcf : x ∈ cf.source := by simp [cf, hfxopen.interior_eq, c, d]
  let U : Set (Euc (k+1)) := I.symm ⁻¹' cf.target
  have hU : IsOpen U := cf.open_target.preimage I.continuous_symm
  let q := cf.extend I x
  have hq : q ∈ (cf.extend I).target := (cf.extend I).map_source
    (by simpa only [OpenPartialHomeomorph.extend_source] using hxcf)
  have hqU : q ∈ U := (cf.extend_target (I := I) ▸ hq).1
  have hqrange : q ∈ range I := (cf.extend_target (I := I) ▸ hq).2
  let g : Euc (k+1) → V := d ∘ f ∘ (cf.extend I).symm
  have hg : ContDiffOn ℝ ∞ g (U ∩ range I) := by
    have hcfs := contMDiffOn_extend_symm hcfatlas
    rw [← cf.extend_target' (I := I)] at hcfs
    have hfcomp := hf.comp_contMDiffOn hcfs
    have hd := contMDiffOn_of_mem_maximalAtlas (I := 𝓘(ℝ,V)) (n := ∞)
      (IsManifold.chart_mem_maximalAtlas (f x))
    have hm : MapsTo (f ∘ (cf.extend I).symm) (cf.extend I).target d.source := by
      intro u hu
      have hy := (cf.extend I).map_target hu
      rw [OpenPartialHomeomorph.extend_source, c.restr_source' _ hfxopen] at hy
      exact hy.2
    have hs := (hd.comp hfcomp hm).contDiffOn
    simpa only [cf.extend_target (I := I)] using hs
  let e : Euc (k+1) ≃L[ℝ] (ℝ × Euc k) :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (k+1) => ℝ)).trans
      (Fin.consLinearEquiv ℝ (fun _ : Fin (k+1) => ℝ)).symm.toContinuousLinearEquiv).trans
      (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)).symm)
  have he (u : Euc (k+1)) : (e u).1 = u 0 := rfl
  have hrange (u : Euc (k+1)) : u ∈ range I ↔ 0 ≤ (e u).1 := by
    simp only [I, range_modelWithCornersEuclideanHalfSpace, mem_setOf_eq, he]
  have hlocal : ∃ D : Set (Euc (k+1)), IsOpen D ∧ q ∈ D ∧
      ∃ H : Euc (k+1) → V, ContDiffOn ℝ ∞ H D ∧ EqOn H g (D ∩ range I) := by
    have hnonneg : 0 ≤ (e q).1 := (hrange q).mp hqrange
    by_cases hzero : (e q).1 = 0
    · let Ue := e.symm ⁻¹' U
      have hUe : IsOpen Ue := hU.preimage e.symm.continuous
      have hqe : (0,(e q).2) ∈ Ue := by
        have hp : (0,(e q).2) = e q := by ext <;> simp [hzero]
        rw [hp]
        exact e.symm_apply_apply q ▸ hqU
      let ge := g ∘ e.symm
      have hge : ContDiffOn ℝ ∞ ge (Ue ∩ (Ici 0 ×ˢ univ)) :=
        hg.comp e.symm.contDiff.contDiffOn (by
          intro p hp
          exact ⟨hp.1, (hrange _).mpr (by simpa using hp.2.1)⟩)
      obtain ⟨R⟩ := E1_positive_rectangle Ue hUe (e q).2 hqe
      obtain ⟨Y⟩ := E2_interval_extension Ue hUe (e q).2 hqe ge hge R
      let De := Ioo (-Y.r) Y.r ×ˢ Y.W
      have hDe : IsOpen De := isOpen_Ioo.prod Y.W_open
      refine ⟨e ⁻¹' De, hDe.preimage e.continuous, ?_, Y.extended ∘ e,
        Y.smooth.comp e.contDiff.contDiffOn (fun _ h => h), ?_⟩
      · exact ⟨⟨by simpa [hzero] using neg_lt_zero.mpr Y.r_pos,
          by simpa [hzero] using Y.r_pos⟩, Y.z_mem⟩
      · intro u hu
        exact (Y.agrees ⟨hu.1, (hrange u).mp hu.2, mem_univ _⟩).trans
          (congrArg g (e.symm_apply_apply u))
    · let D := U ∩ {u | 0 < (e u).1}
      have hD : IsOpen D := hU.inter (isOpen_lt continuous_const
        (continuous_fst.comp e.continuous))
      exact ⟨D,hD,⟨hqU,lt_of_le_of_ne hnonneg (Ne.symm hzero)⟩,g,
        hg.mono (fun u hu => ⟨hu.1,(hrange u).mpr hu.2.le⟩), fun _ _ => rfl⟩
  obtain ⟨D,hD,hqD,H,hH,hHg⟩ := hlocal
  let O : Set M := cf.source ∩ (cf.extend I) ⁻¹' D
  have hO : IsOpen O := cf.isOpen_inter_preimage (hD.preimage I.continuous)
  let source := cf.restr O
  have hsrc : source.source = O := by
    simp only [source, OpenPartialHomeomorph.restr_source, hO.interior_eq]
    exact inter_eq_right.mpr inter_subset_left
  have hx : x ∈ source.source := by rw [hsrc]; exact ⟨hxcf,hqD⟩
  have hsat : source ∈ IsManifold.maximalAtlas I ∞ M := restr_mem_maximalAtlas _ hcfatlas hO
  have htargetD : (source.extend I).target ⊆ D := by
    intro u hu
    have hy : (source.extend I).symm u ∈ source.source := by
      simpa only [OpenPartialHomeomorph.extend_source] using (source.extend I).map_target hu
    have hh := (hsrc ▸ hy).2
    change (source.extend I) ((source.extend I).symm u) ∈ D at hh
    rwa [(source.extend I).right_inv hu] at hh
  have hqsource : source.extend I x = q := rfl
  have htargetrange : (source.extend I).target ⊆ range I := source.extend_target_subset_range (I := I)
  have hagree : EqOn H (d ∘ f ∘ (source.extend I).symm) (source.extend I).target :=
    fun u hu => hHg ⟨htargetD hu,htargetrange hu⟩
  have hpoint : q ∈ (source.extend I).target := (source.extend I).map_source
    (by simpa only [OpenPartialHomeomorph.extend_source] using hx)
  have huniq : UniqueDiffWithinAt ℝ (source.extend I).target q := by
    have hu := (I.uniqueDiffOn q hqrange).inter'
      (source.extend_target_mem_nhdsWithin (I := I) hx)
    simpa only [inter_eq_right.mpr htargetrange] using hu
  have hderiv : fderiv ℝ H q = fderivWithin ℝ g (source.extend I).target q := by
    exact ((hH.contDiffAt (hD.mem_nhds hqD)).differentiableAt (by simp)).hasFDerivAt
      |>.hasFDerivWithinAt.congr (fun u hu => (hagree hu).symm) (hagree hpoint).symm
      |>.fderivWithin huniq |>.symm
  have hr : Function.Injective (fderivWithin ℝ g (source.extend I).target q) := by
    have hm := (hf.mdifferentiableAt (by simp) (x := x)).hasMFDerivAt
    have hfd := (hm.2.mono htargetrange).fderivWithin huniq
    change fderivWithin ℝ g (source.extend I).target q = _ at hfd
    rw [hfd]
    exact (tangentSpaceCastModel 𝓘(ℝ,V) (f x)).injective.comp
      ((hrank x).comp (tangentSpaceCastModel I x).symm.injective)
  refine ⟨{ source := source
            target := d
            source_mem := hx
            target_mem := by simp [d]
            source_atlas := hsat
            target_atlas := IsManifold.chart_mem_maximalAtlas (f x)
            source_subset := ?_
            domain := D
            domain_open := hD
            point_mem := hqD
            extended_target_subset := htargetD
            extended := H
            smooth := hH
            agrees := hagree
            derivative := hderiv
            rank := by change Function.Injective (fderiv ℝ H q); rw [hderiv]; exact hr
            first_factor := e
            normal_first := he }⟩
  intro y hy
  have hycf := (hsrc ▸ hy).1
  rw [c.restr_source' _ hfxopen] at hycf
  exact hycf.2

structure HalfspaceAugmentation {f : M → N} {x : M}
    (X : HalfspaceCoordinateExtension (n := n) (V := V) f x) where
  complement : Submodule ℝ V
  isCompl : IsCompl (fderiv ℝ X.extended (X.source.extend (𝓡∂ n) x)).range complement
  linear : (Euc n × complement) ≃L[ℝ] V
  column : ∀ u, linear (u,0) = fderiv ℝ X.extended (X.source.extend (𝓡∂ n) x) u
  inverse : OpenPartialHomeomorph (Euc n × complement) V
  point_source : (X.source.extend (𝓡∂ n) x,0) ∈ inverse.source
  domain_subset : inverse.source ⊆ Prod.fst ⁻¹' X.domain
  equation : EqOn inverse (fun p => X.extended p.1 + linear (0,p.2)) inverse.source
  derivative : HasFDerivAt (fun p => X.extended p.1 + linear (0,p.2))
    linear.toContinuousLinearMap (X.source.extend (𝓡∂ n) x,0)
  smooth : ContDiffOn ℝ ∞ inverse inverse.source
  inverse_smooth : ContDiffOn ℝ ∞ inverse.symm inverse.target

theorem I2_complement_augmented_inverse {f : M → N} {x : M}
    (X : HalfspaceCoordinateExtension (n := n) (V := V) f x)
    (hrank : Function.Injective (fderiv ℝ X.extended (X.source.extend (𝓡∂ n) x))) :
    Nonempty (HalfspaceAugmentation X) := by
  classical
  let L := fderiv ℝ X.extended (X.source.extend (𝓡∂ n) x)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl L.range
  let A : (Euc n × C) ≃L[ℝ] V :=
    ((LinearEquiv.prodCongr (LinearEquiv.ofInjective L.toLinearMap hrank)
      (LinearEquiv.refl ℝ C)).trans (L.range.prodEquivOfIsCompl C hC)).toContinuousLinearEquiv
  have hA (u : Euc n) : A (u,0) = L u := by
    change L u + (0 : V) = L u
    exact add_zero _
  let G : Euc n × C → V := fun p => X.extended p.1 + A (0,p.2)
  have hG : ContDiffOn ℝ ∞ G (Prod.fst ⁻¹' X.domain) :=
    (X.smooth.comp contDiff_fst.contDiffOn (fun _ h => h)).add
      (A.contDiff.comp (contDiff_const.prodMk contDiff_snd)).contDiffOn
  have hdf : HasFDerivAt X.extended L (X.source.extend (𝓡∂ n) x) :=
    (X.smooth.contDiffAt (X.domain_open.mem_nhds X.point_mem)).differentiableAt (by simp) |>.hasFDerivAt
  have hdG : HasFDerivAt G A.toContinuousLinearMap (X.source.extend (𝓡∂ n) x,0) := by
    let B : Euc n × C →L[ℝ] V := A.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inr ℝ (Euc n) C).comp (ContinuousLinearMap.snd ℝ (Euc n) C))
    have h : HasFDerivAt G (L.comp (ContinuousLinearMap.fst ℝ (Euc n) C) + B)
        (X.source.extend (𝓡∂ n) x,0) :=
      (hdf.comp (X.source.extend (𝓡∂ n) x,(0:C)) hasFDerivAt_fst).add B.hasFDerivAt
    have hL : L.comp (ContinuousLinearMap.fst ℝ (Euc n) C) + B = A := by
      apply ContinuousLinearMap.ext
      intro p
      change L p.1 + A (0,p.2) = A p
      rw [← hA, ← map_add]
      congr 1
      ext <;> simp
    rwa [hL] at h
  obtain ⟨e, hxe, heU, he, heinv, heq⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv
      hG (X.domain_open.preimage continuous_fst) X.point_mem hdG
  exact ⟨{ complement := C
           isCompl := hC
           linear := A
           column := hA
           inverse := e
           point_source := hxe
           domain_subset := heU
           equation := fun p _ => heq p
           derivative := hdG
           smooth := he
           inverse_smooth := heinv }⟩

theorem I3_actual_halfspace_normal_form {f : M → N} {x : M}
    (X : HalfspaceCoordinateExtension (n := n) (V := V) f x) (A : HalfspaceAugmentation X) :
    ∃ source : OpenPartialHomeomorph M (EuclideanHalfSpace n),
      ∃ target : OpenPartialHomeomorph N V,
        x ∈ source.source ∧ f x ∈ target.source ∧
        source ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M ∧
        target ∈ IsManifold.maximalAtlas 𝓘(ℝ,V) ∞ N ∧
        source.source ⊆ X.source.source ∧ EqOn source X.source source.source ∧
        source.source ⊆ f ⁻¹' target.source ∧
        (∀ u ∈ (source.extend (𝓡∂ n)).target, (u,(0:A.complement)) ∈ A.inverse.source) ∧
        EqOn target (fun y => A.linear (A.inverse.symm (X.target y))) target.source ∧
        EqOn (target ∘ f ∘ (source.extend (𝓡∂ n)).symm)
          (fun u => A.linear (u,0)) (source.extend (𝓡∂ n)).target ∧
        Manifold.IsImmersionAtOfComplement A.complement (𝓡∂ n) 𝓘(ℝ,V) ∞ f x := by
  let Z : Set (EuclideanHalfSpace n) :=
    (fun u => ((𝓡∂ n) u,(0:A.complement))) ⁻¹' A.inverse.source
  have hZ : IsOpen Z := A.inverse.open_source.preimage
    ((𝓡∂ n).continuous.prodMk continuous_const)
  let O : Set M := X.source.source ∩ X.source ⁻¹' Z
  have hO : IsOpen O := X.source.isOpen_inter_preimage hZ
  let source := X.source.restr O
  let β := A.inverse.symm.trans A.linear.toHomeomorph.toOpenPartialHomeomorph
  let target := X.target.trans β
  have hsrc : source.source = O := by
    simp only [source, OpenPartialHomeomorph.restr_source, hO.interior_eq]
    exact inter_eq_right.mpr inter_subset_left
  have hx : x ∈ source.source := by
    rw [hsrc]
    exact ⟨X.source_mem, A.point_source⟩
  have hsourceatlas : source ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M :=
    restr_mem_maximalAtlas _ X.source_atlas hO
  have hβatlas : β ∈ IsManifold.maximalAtlas 𝓘(ℝ,V) ∞ V := by
    apply β.mem_maximalAtlas_of_contMDiffOn
    · exact (A.linear.contDiff.comp_contDiffOn
        (A.inverse_smooth.mono inter_subset_left)).contMDiffOn
    · exact (A.smooth.comp A.linear.symm.contDiff.contDiffOn (fun _ h => h.2)).contMDiffOn
  have htargetatlas : target ∈ IsManifold.maximalAtlas 𝓘(ℝ,V) ∞ N := by
    apply target.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas hβatlas).comp
        ((contMDiffOn_of_mem_maximalAtlas X.target_atlas).mono inter_subset_left)
        (fun _ h => h.2)
    · exact (contMDiffOn_symm_of_mem_maximalAtlas X.target_atlas).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas hβatlas).mono inter_subset_left)
        (fun _ h => h.2)
  have hzero (y : M) (hy : y ∈ source.source) :
      A.inverse (X.source.extend (𝓡∂ n) y,0) = X.target (f y) := by
    have hOmem := hsrc ▸ hy
    have heq := A.equation hOmem.2
    change A.inverse (X.source.extend (𝓡∂ n) y,0) =
      X.extended (X.source.extend (𝓡∂ n) y) + A.linear (0,0) at heq
    rw [heq]
    simp only [← Prod.zero_eq_mk, map_zero, add_zero]
    rw [X.agrees ((X.source.extend (𝓡∂ n)).map_source
      (by simpa only [OpenPartialHomeomorph.extend_source] using hOmem.1))]
    simp only [Function.comp_apply, X.source.extend_left_inv hOmem.1]
  have hmap (y : M) (hy : y ∈ source.source) : f y ∈ target.source := by
    have hOmem := hsrc ▸ hy
    refine ⟨X.source_subset hOmem.1, ?_⟩
    exact ⟨hzero y hy ▸ A.inverse.map_source hOmem.2, mem_univ _⟩
  have hzsrc : ∀ u ∈ (source.extend (𝓡∂ n)).target,
      (u,(0:A.complement)) ∈ A.inverse.source := by
    intro u hu
    have hy := (source.extend (𝓡∂ n)).map_target hu
    have hyO : (source.extend (𝓡∂ n)).symm u ∈ O :=
      hsrc ▸ (by simpa only [OpenPartialHomeomorph.extend_source] using hy)
    have hh := hyO.2
    change ((X.source.extend (𝓡∂ n)) ((source.extend (𝓡∂ n)).symm u),0) ∈ A.inverse.source at hh
    change ((source.extend (𝓡∂ n)) ((source.extend (𝓡∂ n)).symm u),0) ∈ A.inverse.source at hh
    rwa [(source.extend (𝓡∂ n)).right_inv hu] at hh
  have hnormal : EqOn (target ∘ f ∘ (source.extend (𝓡∂ n)).symm)
      (fun u => A.linear (u,0)) (source.extend (𝓡∂ n)).target := by
    intro u hu
    have hy : (source.extend (𝓡∂ n)).symm u ∈ source.source := by
      simpa only [OpenPartialHomeomorph.extend_source] using (source.extend (𝓡∂ n)).map_target hu
    change A.linear (A.inverse.symm (X.target (f ((source.extend (𝓡∂ n)).symm u)))) = A.linear (u,0)
    rw [← hzero _ hy]
    change A.linear (A.inverse.symm (A.inverse
      ((source.extend (𝓡∂ n)) ((source.extend (𝓡∂ n)).symm u),0))) = A.linear (u,0)
    rw [(source.extend (𝓡∂ n)).right_inv hu, A.inverse.left_inv (hzsrc u hu)]
  refine ⟨source, target, hx, hmap x hx, hsourceatlas, htargetatlas,
    ?_, ?_, hmap, hzsrc, ?_, hnormal, ?_⟩
  · intro y hy
    exact (hsrc ▸ hy).1
  · intro y hy
    rfl
  · intro y hy
    rfl
  · exact Manifold.IsImmersionAtOfComplement.mk_of_charts A.linear source target
      hx (hmap x hx) hsourceatlas htargetatlas hmap hnormal

theorem I4_fixed_finite_complement (f : M → N)
    (hf : ContMDiff (𝓡∂ n) 𝓘(ℝ,V) ∞ f)
    (hrank : ∀ x, Function.Injective (mfderiv (𝓡∂ n) 𝓘(ℝ,V) f x)) :
    ((IsEmpty M → Manifold.IsImmersionOfComplement (Euc (Module.finrank ℝ V-n))
      (𝓡∂ n) 𝓘(ℝ,V) ∞ f) ∧
    (∀ x (X : HalfspaceCoordinateExtension (n := n) (V := V) f x) (A : HalfspaceAugmentation X),
      Module.finrank ℝ A.complement = Module.finrank ℝ V-n ∧
        Nonempty (A.complement ≃L[ℝ] Euc (Module.finrank ℝ V-n))) ∧
    Manifold.IsImmersionOfComplement (Euc (Module.finrank ℝ V-n)) (𝓡∂ n) 𝓘(ℝ,V) ∞ f ∧
    Manifold.IsImmersion (𝓡∂ n) 𝓘(ℝ,V) ∞ f ∧
    (IsEmbedding f → Manifold.IsSmoothEmbedding (𝓡∂ n) 𝓘(ℝ,V) ∞ f)) := by
  classical
  have hdim (x : M) (X : HalfspaceCoordinateExtension (n := n) (V := V) f x)
      (A : HalfspaceAugmentation X) :
      Module.finrank ℝ A.complement = Module.finrank ℝ V-n := by
    have hsum := A.linear.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at hsum
    simp only [Foundations.Euc, finrank_euclideanSpace_fin] at hsum
    omega
  have hequiv (x : M) (X : HalfspaceCoordinateExtension (n := n) (V := V) f x)
      (A : HalfspaceAugmentation X) :
      Nonempty (A.complement ≃L[ℝ] Euc (Module.finrank ℝ V-n)) := by
    exact ⟨ContinuousLinearEquiv.ofFinrankEq (by
      rw [hdim x X A]
      simp [Foundations.Euc])⟩
  have himm : Manifold.IsImmersionOfComplement (Euc (Module.finrank ℝ V-n))
      (𝓡∂ n) 𝓘(ℝ,V) ∞ f := by
    intro x
    obtain ⟨X⟩ := I1_halfspace_coordinate_extension f hf hrank x
    obtain ⟨A⟩ := I2_complement_augmented_inverse X X.rank
    obtain ⟨source,target,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ :=
      I3_actual_halfspace_normal_form X A
    obtain ⟨e⟩ := hequiv x X A
    exact h11.trans_F e
  exact ⟨fun _ => himm, fun x X A => ⟨hdim x X A,hequiv x X A⟩,
    himm,himm.isImmersion,fun he => ⟨himm.isImmersion,he⟩⟩
end Rank

theorem I5_sphere_composition (S : CompactOrientedSurface.{u})
    (M : CompactOrientedSurface.{v}) (a : S → M) (b : M → ThreeSphere)
    (ha : Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 2) ∞ a)
    (hb : Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ b) :
    ContMDiff (𝓡∂ 2) (𝓡 3) ∞ (b ∘ a) ∧
    (∀ x, mfderiv (𝓡∂ 2) (𝓡 3) (b ∘ a) x =
      (mfderiv (𝓡∂ 2) (𝓡 3) b (a x)).comp (mfderiv (𝓡∂ 2) (𝓡∂ 2) a x)) ∧
    (∀ x, Function.Injective (mfderiv (𝓡∂ 2) (𝓡 3) (b ∘ a) x)) ∧
    IsEmbedding (b ∘ a) ∧ Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ (b ∘ a) := by
  have hs : ContMDiff (𝓡∂ 2) (𝓡 3) ∞ (b ∘ a) := hb.contMDiff.comp ha.contMDiff
  have hd (x : S) : mfderiv (𝓡∂ 2) (𝓡 3) (b ∘ a) x =
      (mfderiv (𝓡∂ 2) (𝓡 3) b (a x)).comp (mfderiv (𝓡∂ 2) (𝓡∂ 2) a x) :=
    mfderiv_comp x (hb.contMDiff.mdifferentiableAt (by simp))
      (ha.contMDiff.mdifferentiableAt (by simp))
  have hr (x : S) : Function.Injective (mfderiv (𝓡∂ 2) (𝓡 3) (b ∘ a) x) := by
    rw [hd]
    exact (hb.isImmersion.mfderiv_injective (by simp) (a x)).comp
      (ha.isImmersion.mfderiv_injective (by simp) x)
  have he : IsEmbedding (b ∘ a) := hb.isEmbedding.comp ha.isEmbedding
  have hi := (I4_fixed_finite_complement (V := Euc 3) (b ∘ a) hs hr).2.2.2.2 he
  exact ⟨hs,hd,hr,he,hi⟩

end
end SeifertSurfaces.LongitudeProducers.CollarCutHelpers.Remaining
