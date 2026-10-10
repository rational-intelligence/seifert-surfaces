import MovingStageCoordinates

open scoped Manifold ContDiff
open Set Filter Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v

def splitSurface : (ℝ × (Fin 1 → ℝ)) ≃L[ℝ] Euc 2 :=
  (Fin.consEquivL ℝ (fun _ : Fin 2 => ℝ)).trans (EuclideanSpace.equiv (Fin 2) ℝ).symm

@[simp] theorem splitSurface_zero (w : ℝ × (Fin 1 → ℝ)) : splitSurface w 0 = w.1 := by
  simp [splitSurface]

@[simp] theorem splitSurface_symm_zero (w : Euc 2) : (splitSurface.symm w).1 = w 0 := by
  rw [← splitSurface_zero, ContinuousLinearEquiv.apply_symm_apply]

variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] {f g : NeatEmbedding S M}

/-- The actual moving family, in the supplied stage charts, has a smooth
parameter inverse which preserves source and ambient boundary coordinates.
The inverse is constructed from the family, not assumed as a tubular datum. -/
theorem normal_exists_moving_boundary_inverse (F : SmoothNormalIsotopy S M f g)
    (t : Time) (x : S) (hx : x ∈ S.boundary) :
    ∃ (c : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
      (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
      (R : Euc 3 →L[ℝ] Euc 2) (a : ℝ)
      (U : Set (ℝ × Euc 2)) (G : ℝ × Euc 2 → Euc 3)
      (e : OpenPartialHomeomorph (ℝ × (ℝ × (Fin 1 → ℝ)))
        (ℝ × (ℝ × (Fin 1 → ℝ)))),
      c ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ S ∧
      d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M ∧
      x ∈ c.source ∧ (F.stage t).toFun x ∈ d.source ∧ 0 < a ∧
      (∀ w, R w 0 = w 0 / a) ∧ IsOpen U ∧
      ((t : ℝ), (c.extend (𝓡∂ 2)) x) ∈ U ∧ ContDiff ℝ ∞ G ∧
      (∀ q ∈ U, q.1 ∈ Icc 0 1 → q.2 ∈ range (𝓡∂ 2) →
        q.2 ∈ (c.extend (𝓡∂ 2)).target ∧
        (F.stage (projIcc 0 1 (by norm_num) q.1)).toFun
          ((c.extend (𝓡∂ 2)).symm q.2) ∈ d.source ∧
        G q = (d.extend (𝓡∂ 3))
          ((F.stage (projIcc 0 1 (by norm_num) q.1)).toFun
            ((c.extend (𝓡∂ 2)).symm q.2))) ∧
      ((t : ℝ), splitSurface.symm ((c.extend (𝓡∂ 2)) x)) ∈ e.source ∧
      e.source ⊆ (fun q => (q.1, splitSurface q.2)) ⁻¹' U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ q, e q = (q.1, splitSurface.symm (R (G (q.1,splitSurface q.2))))) ∧
      (∀ q ∈ e.target, (e.symm q).1 = q.1) ∧
      ∀ q ∈ e.target, q.1 ∈ Icc 0 1 →
        ((0 ≤ (e.symm q).2.1 ↔ 0 ≤ q.2.1) ∧
          ((e.symm q).2.1 = 0 ↔ q.2.1 = 0)) := by
  obtain ⟨c,d,A,R,a,hc,hd,hxc,hfxd,ha,hRA,hAn,hRn,hread⟩ :=
    neat_exists_boundary_coordinates (F.stage t) x hx
  obtain ⟨U,hU,hqU,G,hG,hGeq⟩ := normal_exists_local_chart_extension F c hc d hd t x hxc hfxd
  let u : Euc 2 := (c.extend (𝓡∂ 2)) x
  let w : ℝ × (Fin 1 → ℝ) := splitSurface.symm u
  have hu0 : u 0 = 0 := (chart_boundary_normal_iff c hc hxc).mp hx
  have hw0 : w.1 = 0 := by simp [w,hu0]
  let h : ℝ × (ℝ × (Fin 1 → ℝ)) → ℝ × (Fin 1 → ℝ) :=
    fun q => splitSurface.symm (R (G (q.1,splitSurface q.2)))
  have hh : ContDiff ℝ ∞ h := splitSurface.symm.contDiff.comp
    (R.contDiff.comp (hG.comp (contDiff_fst.prodMk (splitSurface.contDiff.comp contDiff_snd))))
  let V : Set (ℝ × (ℝ × (Fin 1 → ℝ))) := (fun q => (q.1,splitSurface q.2)) ⁻¹' U
  have hV : IsOpen V := hU.preimage
    (continuous_fst.prodMk (splitSurface.continuous.comp continuous_snd))
  have hqV : ((t : ℝ),w) ∈ V := by simpa only [V,mem_preimage,w,ContinuousLinearEquiv.apply_symm_apply] using hqU
  have htime : projIcc 0 1 (by norm_num) (t : ℝ) = t :=
    Subtype.ext (by simp [projIcc_of_mem (show (0:ℝ) ≤ 1 by norm_num) t.property])
  have hslice : (fun b => h ((t : ℝ),splitSurface.symm b)) =ᶠ[𝓝[range (𝓡∂ 2)] u]
      splitSurface.symm := by
    have hnear : ∀ᶠ b in 𝓝[range (𝓡∂ 2)] u, ((t : ℝ),b) ∈ U :=
      mem_nhdsWithin_of_mem_nhds ((continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
        (hU.mem_nhds hqU))
    filter_upwards [hnear,self_mem_nhdsWithin] with b hbU hb
    have he := hGeq ((t : ℝ),b) hbU t.property hb
    have hcb : (c.extend (𝓡∂ 2)).symm b ∈ c.source := by
      have hy := (c.extend (𝓡∂ 2)).map_target he.1
      simpa only [OpenPartialHomeomorph.extend_source] using hy
    have hr := (hread _ hcb).2
    dsimp [h]
    rw [ContinuousLinearEquiv.apply_symm_apply,he.2.2,htime,hr,
      (c.extend (𝓡∂ 2)).right_inv he.1,hRA]
  have hsmooth : ContDiff ℝ ∞ (fun b => h ((t : ℝ),splitSurface.symm b)) :=
    hh.comp (contDiff_const.prodMk splitSurface.symm.contDiff)
  have hderSlice : fderiv ℝ (fun b => h ((t : ℝ),splitSurface.symm b)) u =
      splitSurface.symm.toContinuousLinearMap := by
    have hu : u ∈ range (𝓡∂ 2) := mem_range_self (c x)
    have hud := (𝓡∂ 2).uniqueDiffOn u hu
    rw [← fderivWithin_eq_fderiv hud (hsmooth.differentiable (by simp)).differentiableAt,
      hslice.fderivWithin_eq (hslice.eq_of_nhdsWithin hu)]
    exact splitSurface.symm.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt.fderivWithin hud
  have hvertical : ∀ b, fderiv ℝ h ((t : ℝ),w) (0,b) = b := by
    have hl : HasFDerivAt (fun b : Euc 2 => ((t : ℝ),splitSurface.symm b))
        ((ContinuousLinearMap.inr ℝ ℝ (ℝ × (Fin 1 → ℝ))).comp
          splitSurface.symm.toContinuousLinearMap) u := by
      exact (hasFDerivAt_const (t : ℝ) u).prodMk splitSurface.symm.hasFDerivAt
    have hd := ((hh.differentiable (by simp)).differentiableAt.hasFDerivAt).comp u hl
    have heq := hd.fderiv
    change fderiv ℝ (fun b => h ((t : ℝ),splitSurface.symm b)) u = _ at heq
    rw [hderSlice] at heq
    intro b
    have hb := congrArg (fun L : Euc 2 →L[ℝ] (ℝ × (Fin 1 → ℝ)) => L (splitSurface b)) heq
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply,w] using hb.symm
  have hzero : ∀ q ∈ V, q.1 ∈ Icc 0 1 → q.2.1 = 0 → (h q).1 = 0 := by
    intro q hq ht hq0
    have hH : splitSurface q.2 ∈ range (𝓡∂ 2) := by
      rw [range_modelWithCornersEuclideanHalfSpace]
      change 0 ≤ splitSurface q.2 0
      simp [hq0]
    have he := hGeq (q.1,splitSurface q.2) hq ht hH
    let y : S := (c.extend (𝓡∂ 2)).symm (splitSurface q.2)
    have hy : y ∈ c.source := by
      have hy := (c.extend (𝓡∂ 2)).map_target he.1
      simpa only [OpenPartialHomeomorph.extend_source] using hy
    have hyb : y ∈ S.boundary := (chart_boundary_normal_iff c hc hy).mpr (by
      change (c.extend (𝓡∂ 2)) y 0 = 0
      rw [(c.extend (𝓡∂ 2)).right_inv he.1,splitSurface_zero,hq0])
    have hfy : (F.stage (projIcc 0 1 (by norm_num) q.1)).toFun y ∈ (𝓡∂ 3).boundary M := by
      change y ∈ (F.stage (projIcc 0 1 (by norm_num) q.1)).toFun ⁻¹' (𝓡∂ 3).boundary M
      rw [(F.stage _).boundary_preimage]
      exact hyb
    have hnormal := (chart_boundary_normal_iff d hd he.2.1).mp hfy
    dsimp [h]
    rw [splitSurface_symm_zero,hRn,he.2.2]
    change (𝓡∂ 3) (d ((F.stage (projIcc 0 1 (by norm_num) q.1)).toFun y)) 0 / a = 0
    rw [hnormal,zero_div]
  obtain ⟨e,hqe,heV,he,hei,hemap,heinv,hesign⟩ :=
    exists_local_inverse_preserving_halfspace_parameter hh hV
      (show ((t : ℝ),(0,w.2)) ∈ V by simpa only [← hw0,Prod.mk.eta] using hqV)
      (ContinuousLinearEquiv.refl ℝ (ℝ × (Fin 1 → ℝ)))
      (by simpa only [← hw0,Prod.mk.eta,ContinuousLinearEquiv.refl_apply] using hvertical) (fun _ => rfl) hzero
  refine ⟨c,d,R,a,U,G,e,hc,hd,hxc,hfxd,ha,hRn,hU,hqU,hG,hGeq,?_,heV,he,hei,hemap,?_,hesign⟩
  · simpa only [w,← hw0,Prod.mk.eta] using hqe
  · intro q hq
    exact (heinv q hq).1

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
