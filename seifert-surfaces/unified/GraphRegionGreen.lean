import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.ContDiff.Basic
import GraphGreenRectangle

set_option autoImplicit false
open Set MeasureTheory
open scoped ContDiff

namespace SeifertSurfaces.GraphRegionGreen
noncomputable section

/-- The actual closed strip between the two graphs, in `(x,y)` coordinates. -/
def closedGraphStrip (a b : ℝ) (L U : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {z | z.2 ∈ Icc a b ∧ z.1 ∈ Icc (L z.2) (U z.2)}

/-- The actual open region between the two graphs. -/
def openGraphRegion (a b : ℝ) (L U : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {z | z.2 ∈ Ioo a b ∧ z.1 ∈ Ioo (L z.2) (U z.2)}

/-- The native real Fréchet partial derivatives of `(f,g)` summed as divergence. -/
def graphDivergence (f g : (ℝ × ℝ) → ℝ) (z : ℝ × ℝ) : ℝ :=
  (fderiv ℝ f z) (1, 0) + (fderiv ℝ g z) (0, 1)

/-- Graph flux with the sign appropriate to the upper boundary. The lower
graph contributes the negative of this same expression. -/
def graphFlux (H : ℝ → ℝ) (f g : (ℝ × ℝ) → ℝ) (y : ℝ) : ℝ :=
  f (H y, y) - deriv H y * g (H y, y)

/-- Generic Green identity on a region between two C² graphs meeting at the
endpoints. Smoothness of the field is required only on an open neighborhood of
the actual closed strip. All integrability conclusions use native volume. -/
theorem graph_region_Green
    (a b : ℝ) (hab : a < b) (L U : ℝ → ℝ)
    (hL : ContDiffOn ℝ 2 L (Icc a b)) (hU : ContDiffOn ℝ 2 U (Icc a b))
    (ha : L a = U a) (hb : L b = U b)
    (hLU : ∀ y ∈ Ioo a b, L y < U y)
    (f g : (ℝ × ℝ) → ℝ) (Ω : Set (ℝ × ℝ)) (hΩ : IsOpen Ω)
    (hstrip : closedGraphStrip a b L U ⊆ Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω) :
    let V := openGraphRegion a b L U
    let D := graphDivergence f g
    let upper := graphFlux U f g
    let lower := graphFlux L f g
    IntegrableOn D V volume ∧
      IntegrableOn upper (Icc a b) volume ∧
      IntegrableOn lower (Icc a b) volume ∧
      (∫ z in V, D z ∂volume) =
        ∫ y in Icc a b,
          f (U y, y) - f (L y, y) - deriv U y * g (U y, y) +
            deriv L y * g (L y, y) ∂volume := by
  change IntegrableOn (graphDivergence f g) (openGraphRegion a b L U) volume ∧ _
  have hm : MapsTo (GraphGreenTransport.transport L U)
      (Icc (0 : ℝ) 1 ×ˢ Icc a b) Ω := by
    intro z hz
    exact hstrip (GraphGreenTransport.transport_closed ha hb hLU hz)
  obtain ⟨hi, hu, hl, heq⟩ := GraphGreenTransport.rectangle_green hab hL hU ha hb hΩ hm hf hg
  let S := Ioo (0 : ℝ) 1 ×ˢ Ioo a b
  have hS : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hTd : ∀ z ∈ S, HasFDerivWithinAt (GraphGreenTransport.transport L U)
      (GraphGreenTransport.transportDerivative a b L U z) S z := by
    intro z hz
    exact (GraphGreenTransport.hasFDerivAt_transport hL hU hz.2).hasFDerivWithinAt
  have hinj := GraphGreenTransport.transport_inj hLU
  have himage : GraphGreenTransport.transport L U '' S = openGraphRegion a b L U :=
    GraphGreenTransport.transport_image hLU
  have hJ (z : ℝ × ℝ) (hz : z ∈ S) :
      |(GraphGreenTransport.transportDerivative a b L U z).det| •
        graphDivergence f g (GraphGreenTransport.transport L U z) =
        GraphGreenTransport.weightedDivergence L U f g z := by
    rw [GraphGreenTransport.det_transportDerivative, abs_of_pos (sub_pos.mpr (hLU z.2 hz.2))]
    rfl
  have hiOpen : IntegrableOn (GraphGreenTransport.weightedDivergence L U f g) S volume :=
    hi.mono_set (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hiJac := hiOpen.congr_fun (fun z hz => (hJ z hz).symm) hS
  have hInt := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    volume hS hTd hinj (graphDivergence f g)).mpr hiJac
  rw [himage] at hInt
  have hInterior : ∀ᵐ y ∂volume.restrict (Icc a b), y ∈ Ioo a b := by
    have hh := ae_restrict_mem (μ := (volume : Measure ℝ))
      (measurableSet_Ioo : MeasurableSet (Ioo a b))
    rwa [Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))] at hh
  have hUae : GraphGreenTransport.withinFlux a b U f g =ᵐ[volume.restrict (Icc a b)]
      graphFlux U f g := by
    filter_upwards [hInterior] with y hy
    simp only [GraphGreenTransport.withinFlux, graphFlux,
      derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
  have hLae : GraphGreenTransport.withinFlux a b L f g =ᵐ[volume.restrict (Icc a b)]
      graphFlux L f g := by
    filter_upwards [hInterior] with y hy
    simp only [GraphGreenTransport.withinFlux, graphFlux,
      derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
  refine ⟨hInt, hu.congr_fun_ae hUae, hl.congr_fun_ae hLae, ?_⟩
  calc
    (∫ z in openGraphRegion a b L U, graphDivergence f g z) =
        ∫ z in S, |(GraphGreenTransport.transportDerivative a b L U z).det| •
          graphDivergence f g (GraphGreenTransport.transport L U z) := by
      rw [← himage]
      exact integral_image_eq_integral_abs_det_fderiv_smul volume hS hTd hinj _
    _ = ∫ z in S, GraphGreenTransport.weightedDivergence L U f g z :=
      setIntegral_congr_fun hS hJ
    _ = ∫ z in Icc (0 : ℝ) 1 ×ˢ Icc a b,
        GraphGreenTransport.weightedDivergence L U f g z :=
      setIntegral_congr_set (GraphGreenTransport.rectangle_ae a b)
    _ = ∫ y in Icc a b,
        GraphGreenTransport.withinFlux a b U f g y -
          GraphGreenTransport.withinFlux a b L f g y := heq
    _ = ∫ y in Icc a b,
        f (U y, y) - f (L y, y) - deriv U y * g (U y, y) +
          deriv L y * g (L y, y) := by
      apply integral_congr_ae
      filter_upwards [hUae, hLae] with y hUy hLy
      rw [hUy, hLy]
      unfold graphFlux
      ring

end
end SeifertSurfaces.GraphRegionGreen
