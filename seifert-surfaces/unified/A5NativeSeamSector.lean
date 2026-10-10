import A5SeamTangents
import A5RegularSectorBoundary
import A5SectorC1Extension

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- Actual native seam image data forces a straight sector if its coordinate
lift passes through the polar origin. The lift's continuity and derivative
are proved from native rank and exact image equality. -/
theorem native_regular_seam_through_sector_origin
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (U : Set ℝ) (hU : IsOpen U) (h0 : 0 ∈ U)
    (γ : ℝ → ThreeSphere) (q : ℝ → Euc 2)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 3) 1 γ U)
    (hreg : mfderiv 𝓘(ℝ) (𝓡 3) γ 0 1 ≠ 0)
    (hq : MapsTo q U (((F.domain i).chart j).map.target ∩ frontier ((F.domain i).chart j).map.target))
    (heq : ∀ t ∈ U, E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q t)) = γ t)
    (hq0 : q 0 = 0) (c : SmoothAmbientChart ThreeSphere)
    (hc : γ 0 ∈ c.chart.source) :
    ((F.domain i).chart j).model.interiorChart = false ∧
      ((F.domain i).chart j).model.angle = Real.pi := by
  have hmaps : MapsTo q U ((F.domain i).chart j).map.target := fun _ ht => (hq ht).1
  obtain ⟨w, hw, hew⟩ := native_curve_coordinates_hasDerivAt E F i j U hU γ q hγ hmaps heq 0 h0 c hc
  have hca := (c.smooth _ hc).contMDiffAt (c.chart.open_source.mem_nhds hc)
  have hga := (hγ 0 h0).contMDiffAt (hU.mem_nhds h0)
  have hcdiff : c.chart.MDifferentiable (𝓡 3) 𝓘(ℝ, Euc 3) :=
    ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
  have hd : mfderiv 𝓘(ℝ) 𝓘(ℝ, Euc 3) (c.chart ∘ γ) 0 1 ≠ 0 := by
    rw [mfderiv_comp_apply 0 (hca.mdifferentiableAt (by simp))
      (hga.mdifferentiableAt (by norm_num))]
    intro he
    apply hreg
    apply hcdiff.mfderiv_injective hc
    simpa only [map_zero] using he
  have hcoord : deriv (c.chart ∘ γ) 0 ≠ 0 := by
    intro he
    apply hd
    rw [mfderiv_eq_fderiv]
    simp only [ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv, he, smul_zero, map_zero]
  have hwne : w ≠ 0 := by
    intro he
    apply hcoord
    rw [he, map_zero] at hew
    exact hew.symm
  apply regular_curve_in_sector_frontier_forces_pi ((F.domain i).chart j).model q w hq0 hw hwne
  filter_upwards [hU.mem_nhds h0] with t ht
  simpa only [((F.domain i).chart j).target_eq] using hq ht

/-- At a regular native seam point the actual ambient-coordinate piece map
has a local C1 extension, with exactly its original within derivative. This
uses neither a smooth closed-side sheet nor regularity of its supplied lift. -/
theorem native_regular_seam_C1_extension
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (U : Set ℝ) (hU : IsOpen U) (h0 : 0 ∈ U)
    (γ : ℝ → ThreeSphere) (q : ℝ → Euc 2)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 3) 1 γ U)
    (hreg : mfderiv 𝓘(ℝ) (𝓡 3) γ 0 1 ≠ 0)
    (hq : MapsTo q U (((F.domain i).chart j).map.target ∩ frontier ((F.domain i).chart j).map.target))
    (heq : ∀ t ∈ U, E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q t)) = γ t)
    (c : SmoothAmbientChart ThreeSphere) (hc : γ 0 ∈ c.chart.source) :
    let H := c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j
    ∃ g : Euc 2 → Euc 3, ContDiffAt ℝ 1 g (q 0) ∧
      g =ᶠ[𝓝[((F.domain i).chart j).map.target] (q 0)] H ∧
      fderiv ℝ g (q 0) = fderivWithin ℝ H ((F.domain i).chart j).map.target (q 0) := by
  dsimp only
  have hregular : q 0 ≠ 0 ∨ ((F.domain i).chart j).model.angle = Real.pi := by
    by_cases hn : q 0 = 0
    · exact Or.inr (native_regular_seam_through_sector_origin E F i j U hU h0 γ q
        hγ hreg hq heq hn c hc).2
    · exact Or.inl hn
  obtain ⟨hG, _⟩ := native_piece_chart_C1_rank_at E F i j (q 0) (hq h0).1 c
    (by rw [heq 0 h0]; exact hc)
  rw [((F.domain i).chart j).target_eq] at hG ⊢
  exact C1_sector_model_extension ((F.domain i).chart j).model _ (q 0)
    (by simpa only [← ((F.domain i).chart j).target_eq] using (hq h0).1) hregular hG

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
