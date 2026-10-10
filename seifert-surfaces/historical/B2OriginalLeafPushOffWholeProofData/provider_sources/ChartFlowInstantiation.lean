import ChartPatch
import HalfspaceFlow

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M]

def halfspaceSpatialSupport (V : ℝ × Euc 3 → Euc 3) : Set (EuclideanHalfSpace 3) :=
  (𝓡∂ 3) ⁻¹' (Prod.snd '' tsupport V)

theorem halfspaceSpatialSupport_isCompact {V : ℝ × Euc 3 → Euc 3}
    (hs : HasCompactSupport V) : IsCompact (halfspaceSpatialSupport V) := by
  apply Subtype.isCompact_iff.mpr
  change IsCompact ((Subtype.val : EuclideanHalfSpace 3 → Euc 3) ''
    ((Subtype.val : EuclideanHalfSpace 3 → Euc 3) ⁻¹' (Prod.snd '' tsupport V)))
  rw [image_preimage_eq_inter_range]
  apply (hs.image continuous_snd).inter_right
  rw [show range (Subtype.val : EuclideanHalfSpace 3 → Euc 3) =
    {z : Euc 3 | 0 ≤ z 0} from Subtype.range_coe]
  exact isClosed_le continuous_const
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).continuous

def chartFlow_family
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V)
    (hs : HasCompactSupport V) (hb : ∀ t x, x 0 = 0 → V (t, x) 0 = 0)
    {K : Set (EuclideanHalfSpace 3)} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hfix : ∀ t z, z ∉ K →
      Diffeomorph.timeDependentFlow V hV hs 0 t ((𝓡∂ 3) z) = (𝓡∂ 3) z ∧
      (Diffeomorph.timeDependentFlow V hV hs 0 t).symm ((𝓡∂ 3) z) = (𝓡∂ 3) z) :
    SmoothAmbientIsotopy M := by
  let D : Time → Diffeomorph (𝓡∂ 3) (𝓡∂ 3)
      (EuclideanHalfSpace 3) (EuclideanHalfSpace 3) ∞ :=
    fun t => halfspaceFlow hV hs hb 0 t.1
  have hD : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun p : Time × EuclideanHalfSpace 3 => D p.1 p.2) := by
    have hfull := halfspaceFlow_contMDiff hV hs hb
    exact hfull.comp
      ((contMDiff_const.prodMk (contMDiff_subtypeVal_Icc.comp contMDiff_fst)).prodMk
        contMDiff_snd)
  have hDi : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun p : Time × EuclideanHalfSpace 3 => (D p.1).symm p.2) := by
    have hfull := halfspaceFlow_contMDiff hV hs hb
    simpa only [D, halfspaceFlow_symm, Function.comp_def] using hfull.comp
      (((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk contMDiff_const).prodMk
        contMDiff_snd)
  apply chartAmbientIsotopy e he D hD hDi hK hKt
  · intro t z hz
    constructor
    · apply (𝓡∂ 3).injective
      rw [halfspaceFlow_apply]
      exact (hfix t.1 z hz).1
    · apply (𝓡∂ 3).injective
      rw [show (D t).symm = halfspaceFlow hV hs hb t.1 0 from
        halfspaceFlow_symm hV hs hb 0 t.1, halfspaceFlow_apply,
        ← Diffeomorph.timeDependentFlow_symm]
      exact (hfix t.1 z hz).2
  · exact halfspaceFlow_refl hV hs hb 0

/-- Chartwise ambient flows require only compact support inside the chart;
their support and both outside-identity equations are derived from the field. -/
def chartCompactFlow
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V)
    (hs : HasCompactSupport V) (hb : ∀ t x, x 0 = 0 → V (t, x) 0 = 0)
    (hlocal : halfspaceSpatialSupport V ⊆ e.target) :
    SmoothAmbientIsotopy M := by
  apply chartFlow_family e he hV hs hb (halfspaceSpatialSupport_isCompact hs) hlocal
  intro t z hz
  have h := Diffeomorph.timeDependentFlow_eqOn_compl_image_tsupport V hV hs 0 t
  exact ⟨h.1 hz, h.2 hz⟩

theorem chartCompactFlow_tracks
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V)
    (hs : HasCompactSupport V) (hb : ∀ t x, x 0 = 0 → V (t, x) 0 = 0)
    (hlocal : halfspaceSpatialSupport V ⊆ e.target)
    {γ : ℝ → Euc 3} (hγ : ContinuousOn γ (Icc 0 1))
    (hγ' : ∀ t ∈ Ico 0 1, HasDerivWithinAt γ (V (t, γ t)) (Ici t) t)
    (hγhalf : ∀ t ∈ Icc 0 1, γ t ∈ range (𝓡∂ 3))
    (hγchart : (𝓡∂ 3).symm (γ 0) ∈ e.target) (t : Time) :
    (chartCompactFlow e he hV hs hb hlocal).stage t
      (e.symm ((𝓡∂ 3).symm (γ 0))) = e.symm ((𝓡∂ 3).symm (γ t)) := by
  have hx : e.symm ((𝓡∂ 3).symm (γ 0)) ∈ e.source := e.map_target hγchart
  change chartPatch e (halfspaceFlow hV hs hb 0 t.1)
    (e.symm ((𝓡∂ 3).symm (γ 0))) = _
  rw [chartPatch_of_mem e _ hx, e.right_inv hγchart]
  apply congrArg e.symm
  apply (𝓡∂ 3).injective
  rw [halfspaceFlow_apply, (𝓡∂ 3).right_inv (hγhalf 0 (by constructor <;> norm_num)),
    (𝓡∂ 3).right_inv (hγhalf t t.property)]
  exact Diffeomorph.timeDependentFlow_eqOn_Icc V hV hs hγ hγ' t.property

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
