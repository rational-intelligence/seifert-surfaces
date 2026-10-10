import CapCoordinateField
import CapBoundaryGreenPackage
import GraphRegionGreen
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem cap_native_Green (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (B b : ℝ→E2) (hB : Continuous B) (hBp : Periodic B (2*Real.pi))
    (hb : ContDiff ℝ ∞ b)
    (hagree : ∀t∈Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)), B t=b t)
    (psi : E2→ℝ) (hpsi : ContDiff ℝ ∞ psi) (i j : Fin 2) :
    IntegrableOn (fun z => capBaseMap s b z i * fderiv ℝ psi z (coordinateVector 2 j) + capBaseJet s b i z j * psi z)
      (planarCap (unitCircleParameter s) q) ∧
    IntegrableOn (fun t => b (capArtificialAngle s q t) i * psi (unitCircleParameter s+q • unitCircleParameter t) * unitCircleParameter t j)
      (Icc (s+Real.pi/2+Real.arcsin (q/2)) (s+3*Real.pi/2-Real.arcsin (q/2))) ∧
    IntegrableOn (fun t => B t i * psi (unitCircleParameter t) * unitCircleParameter t j)
      (circlePatch (unitCircleParameter s) q) ∧
    (∫ z in planarCap (unitCircleParameter s) q,
      capBaseMap s b z i * fderiv ℝ psi z (coordinateVector 2 j) + capBaseJet s b i z j * psi z) =
      q*(∫ t in Icc (s+Real.pi/2+Real.arcsin (q/2)) (s+3*Real.pi/2-Real.arcsin (q/2)),
        b (capArtificialAngle s q t) i * psi (unitCircleParameter s+q • unitCircleParameter t) * unitCircleParameter t j) +
      (∫ t in circlePatch (unitCircleParameter s) q, B t i * psi (unitCircleParameter t) * unitCircleParameter t j) := by
  let V := capLensReach q
  let Ω : Set (ℝ×ℝ) := {p | |p.2|<1}
  let A := planarCap (unitCircleParameter s) q
  let F := fun z => capBaseMap s b z i * fderiv ℝ psi z (coordinateVector 2 j) + capBaseJet s b i z j * psi z
  have hV := cap_lens_reach q hq hq1
  have hab : -V<V := by dsimp [V];linarith [hV.1]
  have hΩ : IsOpen Ω := isOpen_lt continuous_snd.abs continuous_const
  have hstrip : SeifertSurfaces.GraphRegionGreen.closedGraphStrip (-V) V (capLensLower q) capLensUpper ⊆ Ω := by
    intro p hp
    exact (cap_transverse_interval_bounds q p.2 hq hq1 hp.1).1
  have hends := cap_lens_boundary_endpoints q hq hq1
  have hfields := cap_coordinate_flux_smooth s b hb psi hpsi i j
  have hg := SeifertSurfaces.GraphRegionGreen.graph_region_Green (-V) V hab (capLensLower q) capLensUpper
    ((cap_lens_lower_smooth q hq hq1).of_le (by simp))
    ((cap_lens_upper_smooth q hq hq1).of_le (by simp)) hends.1 hends.2
    (fun y hy => cap_lens_width_pos q y hq hq1 (abs_lt.mpr hy))
    (capCoordinateFluxX s b psi i j) (capCoordinateFluxY s b psi i j) Ω hΩ hstrip hfields.1 hfields.2
  dsimp only at hg
  have hregion : SeifertSurfaces.GraphRegionGreen.openGraphRegion (-V) V (capLensLower q) capLensUpper =
      (capCoordinateEquiv s) ⁻¹' A := by
    ext p
    exact (cap_coordinate_graph_iff s q hq hq1 p).symm
  have hmeas : MeasurableSet ((capCoordinateEquiv s) ⁻¹' A) := (cap_measurableSet s q).preimage (capCoordinateEquiv s).measurable
  have hD : EqOn (SeifertSurfaces.GraphRegionGreen.graphDivergence (capCoordinateFluxX s b psi i j) (capCoordinateFluxY s b psi i j))
      (F ∘ capCoordinateEquiv s) ((capCoordinateEquiv s) ⁻¹' A) := by
    intro p hp
    have h1 : |p.2|<1 := by
      have hh := (cap_coordinate_graph_iff s q hq hq1 p).mp hp
      exact (cap_transverse_interval_bounds q p.2 hq hq1 ⟨hh.1.1.le,hh.1.2.le⟩).1
    exact cap_coordinate_divergence s b hb psi hpsi i j p h1
  rw [hregion] at hg
  have hFi : IntegrableOn F A :=
    ((capCoordinateEquiv_measurePreserving s).integrableOn_comp_preimage (capCoordinateEquiv s).measurableEmbedding).mp
      (hg.1.congr_fun hD hmeas)
  have hboundary := cap_native_boundary_Green_package s q hq hq1 B b hB hBp hb hagree psi hpsi i j
  refine ⟨hFi,hboundary.2.2.1,hboundary.2.2.2.1,?_⟩
  have hchange := (capCoordinateEquiv_measurePreserving s).setIntegral_preimage_emb
    (capCoordinateEquiv s).measurableEmbedding F A
  calc
    _ = ∫ p in (capCoordinateEquiv s) ⁻¹' A, F (capCoordinateEquiv s p) := hchange.symm
    _ = ∫ p in (capCoordinateEquiv s) ⁻¹' A,
        SeifertSurfaces.GraphRegionGreen.graphDivergence (capCoordinateFluxX s b psi i j) (capCoordinateFluxY s b psi i j) p :=
      (setIntegral_congr_fun hmeas hD).symm
    _ = ∫ y in Icc (-V) V, capUpperFlux s b psi i j y-capLowerFlux s q b psi i j y := hg.2.2.2.trans (by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      dsimp [capCoordinateFluxX,capCoordinateFluxY,capCoordinateProduct,capScalarProfile,capUpperFlux,capLowerFlux]
      ring)
    _ = _ := hboundary.2.2.2.2

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
