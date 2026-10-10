import A5StraightenedHalfdiscSection
import A5NativeHalfdiscDirichletDatum

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
universe u

/-- The actual longitude straightener is lifted to an ambient smooth
coordinate change. The resulting metric graph uses that changed ambient
chart, preserves the exact original image, and has a constructed smooth
Dirichlet datum. No transformed operator or boundary datum is postulated. -/
theorem native_metric_graph_of_straightened_C1_halfdisc
    {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ,E3) ∞ N]
    (h : AmbientMetric N) (c : SmoothAmbientChart N)
    (ρ : ℝ) (f : E2 → E3) (hf : ContDiffOn ℝ 1 f (closedHalfDisc ρ))
    (hchart : MapsTo f (closedHalfDisc ρ) c.chart.target)
    (L : E3 ≃L[ℝ] E2 × ℝ)
    (d : OpenPartialHomeomorph E2 E2)
    (hd : ContDiffOn ℝ ∞ d d.source) (hdi : ContDiffOn ℝ ∞ d.symm d.target)
    (e : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanHalfSpace 2))
    (he0 : (0 : EuclideanHalfSpace 2) ∈ e.source) (hez : e 0 = 0)
    (hemap : ∀ z ∈ e.source, (𝓡∂ 2) z ∈ closedHalfDisc ρ ∧
      (L (f ((𝓡∂ 2) z))).1 ∈ d.source ∧
      (𝓡∂ 2) (e z) = d (L (f ((𝓡∂ 2) z))).1)
    (heb : ∀ z ∈ e.source, ((𝓡∂ 2) (e z)) 0 = 0 ↔ ((𝓡∂ 2) z) 0 = 0)
    (hei : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) 1 e.symm e.target)
    (γ : ℝ → E3) (I : Set ℝ) (hI : IsOpen I) (hI0 : (0 : ℝ) ∈ I)
    (hγ : ContDiffOn ℝ ∞ γ I)
    (hetrace : ∀ z ∈ e.source, ((𝓡∂ 2) z) 0 = 0 →
      f ((𝓡∂ 2) z) = γ (((𝓡∂ 2) (e z)) 1)) :
    ∃ G : NativeMetricGraph h, ∃ r : ℝ, ∃ g : SmoothDirichletDatum r,
      0 < r ∧ r < G.radius ∧
      (L G.origin).1 = 0 ∧ (∀ v, (L (G.plane v)).1 = v) ∧
      (L G.normal).1 = 0 ∧
      (∀ z ∈ closedHalfDisc r,
        (𝓡∂ 2).symm z ∈ e.target ∧
        (𝓡∂ 2) (e.symm ((𝓡∂ 2).symm z)) ∈ closedHalfDisc ρ ∧
        c.chart.symm (f ((𝓡∂ 2) (e.symm ((𝓡∂ 2).symm z)))) ∈ G.coordinates.chart.source ∧
        graphMap G.origin G.plane G.normal G.height z =
          G.coordinates.chart (c.chart.symm (f ((𝓡∂ 2) (e.symm ((𝓡∂ 2).symm z)))))) ∧
      (∀ z ∈ flatBoundary r, G.height z = g.value (z 1)) := by
  obtain ⟨c',hcf,hcs,_⟩ := ambient_chart_of_projected_coordinate_change c L d hd hdi
  let q : E2 → E3 := fun z => L.symm (z,
    (L (f ((𝓡∂ 2) (e.symm ((𝓡∂ 2).symm z))))).2)
  obtain ⟨r₀,hr₀,hmap,hq,hsection,hqeq,htrace⟩ :=
    C1_straightened_halfspace_section ρ f hf L d e he0 hez hemap heb hei γ hetrace
  have hpoint (z : E2) (hz : z ∈ closedHalfDisc r₀) :
      c.chart.symm (f ((𝓡∂ 2) (e.symm ((𝓡∂ 2).symm z)))) ∈ c'.chart.source := by
    rw [hcs]
    have hfz := hchart (hqeq z hz).1
    exact ⟨c.chart.map_target hfz,by rw [c.chart.right_inv hfz]; exact (hqeq z hz).2.1⟩
  have hqchart (z : E2) (hz : z ∈ closedHalfDisc r₀) :
      q z = c'.chart (c.chart.symm (f ((𝓡∂ 2) (e.symm ((𝓡∂ 2).symm z))))) := by
    rw [hcf,c.chart.right_inv (hchart (hqeq z hz).1)]
    exact (hqeq z hz).2.2
  let γ' : ℝ → E3 := fun t => L.symm (t • coordinateVector 2 1,(L (γ t)).2)
  have hγ' : ContDiffOn ℝ ∞ γ' I :=
    L.symm.contDiff.comp_contDiffOn
      ((contDiffOn_id.smul contDiffOn_const).prodMk ((L.contDiff.comp_contDiffOn hγ).snd))
  have htrace' (z : E2) (hz : z ∈ closedHalfDisc r₀) (hz0 : z 0 = 0) : q z = γ' (z 1) := by
    have hh := htrace z hz hz0
    have hzline : z = z 1 • coordinateVector 2 1 := by
      ext i
      fin_cases i <;> simp [coordinateVector,EuclideanSpace.single,hz0]
    exact hh.trans (congrArg L.symm (Prod.ext hzline rfl))
  let P := (ContinuousLinearMap.fst ℝ E2 ℝ).comp L.toContinuousLinearMap
  let height := (ContinuousLinearMap.snd ℝ E2 ℝ).comp L.toContinuousLinearMap
  have hsep : Function.Injective (fun z => (P z,height z)) := by
    intro x y hxy
    exact L.injective hxy
  obtain ⟨G,r,g,hr,hrG,hrr₀,hGc,hGo,hPo,hGp,hPn,_,_,hGq,hb⟩ :=
    native_halfdisc_metric_graph_with_smooth_dirichlet_datum h c' r₀ hr₀ q hq
      (fun z hz => (hqchart z hz).symm ▸ c'.chart.map_source (hpoint z hz))
      P height hsep (fun z _ => hsection z) γ' I hI hI0 hγ' htrace'
  refine ⟨G,r,g,hr,hrG,hPo,fun v => (hGp v).1,hPn,?_,hb⟩
  intro z hz
  have hz₀ := closedHalfDisc_mono hrr₀.le hz
  refine ⟨hmap hz₀,(hqeq z hz₀).1,?_,?_⟩
  · rw [hGc]
    exact hpoint z hz₀
  · rw [hGq z hz,hGc]
    exact hqchart z hz₀

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
