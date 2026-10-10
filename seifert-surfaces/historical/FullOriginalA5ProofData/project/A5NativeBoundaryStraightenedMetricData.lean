import A5NativeCenteredClockCompatibility
import A5NativeLongitudeCoordinateClock
import A5C1BoundaryClockDerivative
import A5NormalizedTangentProjection
import A5StraightenedNativeMetricGraph

set_option autoImplicit false
set_option maxHeartbeats 2500000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
universe u

/-- The native boundary C1 image chart and the original smooth longitude
construct an actual straightened metric graph with smooth Dirichlet data.
Every projection, coordinate change, scalar datum and graph is constructed.
No graph, source derivative or transformed equation is an input. -/
theorem native_boundary_C1_image_straightened_metric_data
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (J : LongitudeFoliation.{u} E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (hF : J.BoundaryIn F.map)
    (C : BoundaryC1ImageChart S E.Carrier F.map)
    (x : S) (hx : x ∈ C.chart.source) (hxb : x ∈ S.boundary)
    (h : AmbientMetric ThreeSphere) :
    ∃ e : OpenPartialHomeomorph S (EuclideanHalfSpace 2),
      x ∈ e.source ∧ e x = 0 ∧
      e '' (S.boundary ∩ e.source) =
        ((𝓡∂ 2).boundary (EuclideanHalfSpace 2)) ∩ e.target ∧
      ∃ G : NativeMetricGraph h, ∃ P : E3 →L[ℝ] E2,
        ∃ r : ℝ, ∃ g : SmoothDirichletDatum r,
          0 < r ∧ r < G.radius ∧ P G.origin = 0 ∧
          (∀ v, P (G.plane v) = v) ∧ P G.normal = 0 ∧
          (∀ z ∈ closedHalfDisc r,
            (𝓡∂ 2).symm z ∈ e.target ∧
            E.toSphere (F.map (e.symm ((𝓡∂ 2).symm z))) ∈ G.coordinates.chart.source ∧
            graphMap G.origin G.plane G.normal G.height z =
              G.coordinates.chart (E.toSphere (F.map (e.symm ((𝓡∂ 2).symm z))))) ∧
          (∀ z ∈ flatBoundary r, G.height z = g.value (z 1)) := by
  let c : SmoothAmbientChart ThreeSphere := {
    chart := chartAt E3 (E.toSphere (F.map x))
    smooth := contMDiffOn_chart
    inverse_smooth := contMDiffOn_chart_symm }
  have hc : E.toSphere (F.map x) ∈ c.chart.source := mem_chart_source _ _
  obtain ⟨d₀,hd₀s,hd₀t,hd₀x,hdi₀x,hd₀f,_,_,ρ,hρ,hρmap,hf,hfi⟩ :=
    native_boundary_C1_chart_centered_halfdisc E F C x hx hxb c hc
  let f := c.chart ∘ E.toSphere ∘ F.map ∘ C.chart.symm ∘ d₀.symm ∘ (𝓡∂ 2).symm
  obtain ⟨b,hb0,hbc,hbb,hbi,⟨U,hU,hxU,hcover⟩,I,hI,hI0,hγ,hγn⟩ :=
    native_longitude_coordinate_clock_with_coverage E J F hF x hxb c hc
  let γ := c.chart ∘ E.toSphere ∘ F.map ∘ b
  let q := (𝓡∂ 2) ∘ d₀ ∘ C.chart ∘ b
  obtain ⟨hq0,hqc,hqmap,hqflat,hfγ,hsmall⟩ :=
    native_centered_boundary_clock_compatibility E F C x hx hxb c d₀ hd₀s hd₀t
      hd₀x hdi₀x hd₀f ρ hρ (fun z hz => (hρmap z hz).1)
      b hb0 (hbc.continuousAt (isOpen_Ioo.mem_nhds (by constructor <;> norm_num)))
      hbb hbi U hU hxU hcover
  have hdγ : HasDerivAt γ (deriv γ 0) 0 :=
    ((hγ.contDiffAt (hI.mem_nhds hI0)).differentiableAt (by simp)).hasDerivAt
  obtain ⟨a,ha,_,hDa⟩ := C1_halfdisc_boundary_clock_derivative ρ hρ f hf hfi
    q hq0 hqc hqmap hqflat γ (deriv γ 0) hdγ hγn hfγ
  obtain ⟨P,height,hsep,hP⟩ := rank_two_normalized_projection_with_height
    (fderivWithin ℝ f (closedHalfDisc ρ) 0) hfi
  have hγ0 : γ 0 = f 0 := by
    have hh : f (q 0) = γ 0 := hfγ.self_of_nhds
    have hh0 : q 0 = 0 := hq0
    rw [hh0] at hh
    exact hh.symm
  obtain ⟨d,hds,hdz,_,hd,hdi,e₁,he₁0,he₁z,he₁map,he₁b,_,he₁i,he₁trace⟩ :=
    C1_halfdisc_straightened_boundary_coordinates ρ hρ f hf P hP γ I hI hI0 hγ hγ0
      a ha (hDa.symm ▸ hdγ) hsmall
  let A : E3 →L[ℝ] E2 × ℝ := P.prod height
  have hA : Function.Bijective A := by
    refine ⟨hsep,?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := A.toLinearMap) (by simp [E2,E3,Module.finrank_prod])).mp hsep
  let L : E3 ≃L[ℝ] E2 × ℝ := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hA.1) (LinearMap.range_eq_top.mpr hA.2)
  have hfc : MapsTo f (closedHalfDisc ρ) c.chart.target :=
    fun z hz => c.chart.map_source (hρmap z hz).2
  obtain ⟨G,r,g,hr,hrG,hPo,hPp,hPn,hG,hb⟩ :=
    native_metric_graph_of_straightened_C1_halfdisc h c ρ f hf hfc L d hd hdi
      e₁ he₁0 he₁z he₁map he₁b he₁i γ I hI hI0 hγ
      (fun z hz hz0 => (he₁trace z hz hz0).2)
  let c₀ : OpenPartialHomeomorph S (EuclideanHalfSpace 2) :=
    ⟨C.chart,C.source_open,C.target_open⟩
  let e := (c₀.trans d₀).trans e₁
  have hx₀ : x ∈ (c₀.trans d₀).source := ⟨hx,hd₀s.symm ▸ mem_univ _⟩
  have hxe : x ∈ e.source := ⟨hx₀,by change d₀ (C.chart x) ∈ e₁.source; rwa [hd₀x]⟩
  have hex : e x = 0 := by change e₁ (d₀ (C.chart x)) = 0; rw [hd₀x,he₁z]
  have hxflat : ((𝓡∂ 2) (C.chart x)) 0 = 0 := by
    have hh : C.chart x ∈ C.chart '' (S.boundary ∩ C.chart.source) := ⟨x,⟨hxb,hx⟩,rfl⟩
    rw [C.boundary_image] at hh
    exact (model_halfspace_boundary_iff _).mp hh.1
  have hd₀b (z : EuclideanHalfSpace 2) (_hz : z ∈ d₀.source) :
      ((𝓡∂ 2) (d₀ z)) 0 = 0 ↔ ((𝓡∂ 2) z) 0 = 0 := by
    rw [hd₀f]
    simp only [PiLp.sub_apply,hxflat,sub_zero]
  have heb := boundary_image_of_halfspace_chart_comp S.boundary (c₀.trans d₀)
    (boundary_image_of_halfspace_chart_comp S.boundary c₀ C.boundary_image d₀ hd₀b) e₁ he₁b
  refine ⟨e,hxe,hex,heb,G,P,r,g,hr,hrG,hPo,hPp,hPn,?_,hb⟩
  intro z hz
  have hzG := hG z hz
  have hzρ := (he₁map (e₁.symm ((𝓡∂ 2).symm z)) (e₁.map_target hzG.1)).1
  have hez : (𝓡∂ 2).symm z ∈ e.target := by
    refine ⟨hzG.1,⟨hd₀t.symm ▸ mem_univ _,?_⟩⟩
    have hh := (hρmap _ hzρ).1
    rwa [ModelWithCorners.left_inv] at hh
  have hnative : c.chart.symm (f ((𝓡∂ 2) (e₁.symm ((𝓡∂ 2).symm z)))) =
      E.toSphere (F.map (e.symm ((𝓡∂ 2).symm z))) := by
    have hh := (hρmap _ hzρ).2
    simp only [f, Function.comp_apply]
    rw [c.chart.left_inv hh]
    have hm : (𝓡∂ 2).symm ((𝓡∂ 2) (e₁.symm ((𝓡∂ 2).symm z))) =
        e₁.symm ((𝓡∂ 2).symm z) := (𝓡∂ 2).left_inv _
    rw [hm]
    rfl
  exact ⟨hez,hnative ▸ hzG.2.2.1,hnative ▸ hzG.2.2.2⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
