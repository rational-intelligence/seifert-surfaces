import Foundations
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M]

def chartPatch (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (D : EuclideanHalfSpace 3 → EuclideanHalfSpace 3) (x : M) : M := by
  classical
  exact if x ∈ e.source then e.symm (D (e x)) else x

theorem chartPatch_of_mem (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (D : EuclideanHalfSpace 3 → EuclideanHalfSpace 3) {x : M} (hx : x ∈ e.source) :
    chartPatch e D x = e.symm (D (e x)) := ite_eq_left hx

theorem chartPatch_of_notMem (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (D : EuclideanHalfSpace 3 → EuclideanHalfSpace 3) {x : M} (hx : x ∉ e.source) :
    chartPatch e D x = x := ite_eq_right hx

theorem chartPatch_eq_of_notMem_image
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (D : EuclideanHalfSpace 3 → EuclideanHalfSpace 3) {K : Set (EuclideanHalfSpace 3)}
    (hfix : ∀ z, z ∉ K → D z = z) {x : M} (hx : x ∉ e.symm '' K) :
    chartPatch e D x = x := by
  by_cases hxs : x ∈ e.source
  · rw [chartPatch_of_mem e D hxs]
    have hek : e x ∉ K := fun h => hx ⟨e x, h, e.left_inv hxs⟩
    rw [hfix _ hek, e.left_inv hxs]
  · exact chartPatch_of_notMem e D hxs

theorem diffeomorph_mapsTo_of_fixed_outside
    (D : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (EuclideanHalfSpace 3) (EuclideanHalfSpace 3) ∞)
    {K U : Set (EuclideanHalfSpace 3)} (hKU : K ⊆ U)
    (hfix : ∀ z, z ∉ K → D z = z) : MapsTo D U U := by
  intro z hz
  by_contra hDz
  have hk : D z ∉ K := fun hk => hDz (hKU hk)
  have hh : D (D z) = D z := hfix _ hk
  have he : D z = z := D.injective hh
  exact hDz (he.symm ▸ hz)

theorem chartPatch_leftInverse
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (D : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (EuclideanHalfSpace 3) (EuclideanHalfSpace 3) ∞)
    (hmap : MapsTo D e.target e.target) :
    Function.LeftInverse (chartPatch e D.symm) (chartPatch e D) := by
  intro x
  by_cases hx : x ∈ e.source
  · have hDx := hmap (e.map_source hx)
    rw [chartPatch_of_mem e D hx, chartPatch_of_mem e D.symm (e.map_target hDx),
      e.right_inv hDx, D.symm_apply_apply, e.left_inv hx]
  · rw [chartPatch_of_notMem e D hx, chartPatch_of_notMem e D.symm hx]

theorem chartPatch_contMDiff
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    (D : Time → Diffeomorph (𝓡∂ 3) (𝓡∂ 3)
      (EuclideanHalfSpace 3) (EuclideanHalfSpace 3) ∞)
    (hD : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun p : Time × EuclideanHalfSpace 3 => D p.1 p.2))
    {K : Set (EuclideanHalfSpace 3)} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hfix : ∀ t z, z ∉ K → D t z = z) :
    ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun p : Time × M => chartPatch e (D p.1) p.2) := by
  have hei := contMDiffOn_symm_of_mem_maximalAtlas he
  have hKi : IsCompact (e.symm '' K) :=
    hK.image_of_continuousOn (hei.continuousOn.mono hKt)
  intro q
  by_cases hq : q.2 ∈ e.source
  · have hmap := diffeomorph_mapsTo_of_fixed_outside (D q.1) hKt (hfix q.1)
    have hc : ContMDiffAt ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
        (fun r : Time × M => e r.2) q :=
      ((contMDiffOn_of_mem_maximalAtlas he).contMDiffAt
        (e.open_source.mem_nhds hq)).comp q contMDiffAt_snd
    have hfun := hD.contMDiffAt.comp q (contMDiffAt_fst.prodMk hc)
    have hi := (hei.contMDiffAt
      (e.open_target.mem_nhds (hmap (e.map_source hq)))).comp q hfun
    apply hi.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hq)] with r hr
    exact chartPatch_of_mem e _ hr
  · have hqK : q.2 ∉ e.symm '' K := by
      rintro ⟨z, hz, heq⟩
      exact hq (heq ▸ e.map_target (hKt hz))
    apply contMDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (hKi.isClosed.isOpen_compl.mem_nhds hqK)] with r hr
    exact chartPatch_eq_of_notMem_image e _ (hfix r.1) hr

/-- A compactly supported half-space diffeomorphism family gives a genuine
ambient isotopy on any charted ambient manifold. The chart target may be proper. -/
def chartAmbientIsotopy
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    (D : Time → Diffeomorph (𝓡∂ 3) (𝓡∂ 3)
      (EuclideanHalfSpace 3) (EuclideanHalfSpace 3) ∞)
    (hD : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun p : Time × EuclideanHalfSpace 3 => D p.1 p.2))
    (hDi : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun p : Time × EuclideanHalfSpace 3 => (D p.1).symm p.2))
    {K : Set (EuclideanHalfSpace 3)} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hfix : ∀ t z, z ∉ K → D t z = z ∧ (D t).symm z = z)
    (hzero : D 0 = Diffeomorph.refl (𝓡∂ 3) (EuclideanHalfSpace 3) ∞) :
    SmoothAmbientIsotopy M := by
  have hF := chartPatch_contMDiff e he D hD hK hKt (fun t z hz => (hfix t z hz).1)
  have hG := chartPatch_contMDiff e he (fun t => (D t).symm) hDi hK hKt
    (fun t z hz => (hfix t z hz).2)
  let J (t : Time) : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞ :=
    { toEquiv :=
        { toFun := chartPatch e (D t)
          invFun := chartPatch e (D t).symm
          left_inv := chartPatch_leftInverse e (D t)
            (diffeomorph_mapsTo_of_fixed_outside (D t) hKt (fun z hz => (hfix t z hz).1))
          right_inv := chartPatch_leftInverse e (D t).symm
            (diffeomorph_mapsTo_of_fixed_outside (D t).symm hKt (fun z hz => (hfix t z hz).2)) }
      contMDiff_toFun := hF.comp (contMDiff_const.prodMk contMDiff_id)
      contMDiff_invFun := hG.comp (contMDiff_const.prodMk contMDiff_id) }
  refine
    { stage := J
      smooth_family := hF
      initial := ?_
      boundary_setwise := fun t => Diffeomorph.image_boundary (by simp) (J t) }
  intro x
  change chartPatch e (D 0) x = x
  rw [hzero]
  by_cases hx : x ∈ e.source
  · rw [chartPatch_of_mem e _ hx]
    exact e.left_inv hx
  · exact chartPatch_of_notMem e _ hx

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
