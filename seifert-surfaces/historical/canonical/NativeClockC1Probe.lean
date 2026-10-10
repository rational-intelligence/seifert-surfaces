import NativeBoundaryLiftProbe
import A5RelativeC1Inverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- The exact native sector lift is C1 on the original open clock whenever
that clock remains in one actual ambient chart. Its differentiability is
derived from native immersion rank and the exact image equality. -/
theorem native_piece_curve_coordinates_c1
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (U : Set ℝ) (hU : IsOpen U) (γ : ℝ → ThreeSphere) (q : ℝ → Euc 2)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 3) 1 γ U)
    (hq : MapsTo q U ((F.domain i).chart j).map.target)
    (heq : ∀ t ∈ U, E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q t)) = γ t)
    (c : SeifertSurfaces.OriginalEndpoints.SmoothAmbientChart ThreeSphere)
    (hc : MapsTo γ U c.chart.source) : ContDiffOn ℝ 1 q U := by
  let A := ((F.domain i).chart j).map.target
  let f := E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j
  let B := A ∩ f ⁻¹' c.chart.source
  let H := c.chart ∘ f
  have hA : UniqueDiffOn ℝ A := by
    rw [show A = ((F.domain i).chart j).model.domain from ((F.domain i).chart j).target_eq]
    exact ((F.domain i).chart j).model.uniqueDiffOn_domain
  obtain ⟨hf, _⟩ := native_piece_sphere_C1_rank E F i j
  have hBnhds (y : Euc 2) (hy : y ∈ B) : B ∈ 𝓝[A] y :=
    inter_mem self_mem_nhdsWithin ((hf.continuousOn y hy.1).preimage_mem_nhdsWithin
      (c.chart.open_source.mem_nhds hy.2))
  have hB : UniqueDiffOn ℝ B := fun y hy =>
    (hA y hy.1).inter' ((hf.continuousOn y hy.1).preimage_mem_nhdsWithin
      (c.chart.open_source.mem_nhds hy.2))
  have hH : ContDiffOn ℝ 1 H B := by
    intro y hy
    exact (native_piece_chart_C1_rank_at E F i j y hy.1 c hy.2).1.mono inter_subset_left
  have hrank (y : Euc 2) (hy : y ∈ B) :
      Function.Injective (fderivWithin ℝ H B y) := by
    rw [fderivWithin_subset inter_subset_left (hB y hy)
      ((native_piece_chart_C1_rank_at E F i j y hy.1 c hy.2).1.differentiableWithinAt (by norm_num))]
    exact (native_piece_chart_C1_rank_at E F i j y hy.1 c hy.2).2
  have hg : ContDiffOn ℝ 1 (c.chart ∘ γ) U := by
    intro t ht
    have hca := (c.smooth _ (hc ht)).contMDiffAt (c.chart.open_source.mem_nhds (hc ht))
    exact ((hca.of_le (by simp)).comp_contMDiffWithinAt t (hγ t ht)).contDiffWithinAt
  have hqcont := native_piece_curve_coordinates_continuous E F i j U γ q
    hγ.continuousOn hq heq
  have hqm : MapsTo q U B := fun t ht => ⟨hq ht, by
    change f (q t) ∈ c.chart.source
    rw [show f (q t) = γ t from heq t ht]
    exact hc ht⟩
  exact (C1_lift_through_relative_immersion B U hB hU.uniqueDiffOn H (c.chart ∘ γ) q
    hH hg hrank hqcont hqm (fun t ht => congrArg c.chart (heq t ht))).1

/-- Native rank and the actual smooth edge make its exact coordinate lift
C1 on the entire original open clock. No fixed ambient chart is required. -/
theorem native_piece_curve_coordinates_c1_all
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (U : Set ℝ) (hU : IsOpen U) (γ : ℝ → ThreeSphere) (q : ℝ → Euc 2)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 3) 1 γ U)
    (hq : MapsTo q U ((F.domain i).chart j).map.target)
    (heq : ∀ t ∈ U, E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q t)) = γ t) :
    ContDiffOn ℝ 1 q U := by
  intro t ht
  let c : SeifertSurfaces.OriginalEndpoints.SmoothAmbientChart ThreeSphere := {
    chart := chartAt (Euc 3) (γ t)
    smooth := contMDiffOn_chart
    inverse_smooth := contMDiffOn_chart_symm }
  let V := U ∩ γ ⁻¹' c.chart.source
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU c.chart.open_source
  have htV : t ∈ V := ⟨ht, by change γ t ∈ (chartAt (Euc 3) (γ t)).source; exact mem_chart_source _ _⟩
  have hqV := native_piece_curve_coordinates_c1 E F i j V hV γ q
    (hγ.mono inter_subset_left) (fun _ ht => hq ht.1)
    (fun t ht => heq t ht.1) c (fun _ ht => ht.2)
  exact ((hqV t htV).contDiffAt (hV.mem_nhds htV)).contDiffWithinAt

/-- Nonzero actual ambient edge velocity forces the derivative of the exact
native coordinate lift to be nonzero at every point of the open clock. -/
theorem native_piece_curve_coordinates_regular
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (U : Set ℝ) (hU : IsOpen U) (γ : ℝ → ThreeSphere) (q : ℝ → Euc 2)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 3) 1 γ U)
    (hq : MapsTo q U ((F.domain i).chart j).map.target)
    (heq : ∀ t ∈ U, E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q t)) = γ t)
    (hreg : ∀ t ∈ U, mfderiv 𝓘(ℝ) (𝓡 3) γ t 1 ≠ 0) :
    ∀ t ∈ U, deriv q t ≠ 0 := by
  intro t ht
  let c : SeifertSurfaces.OriginalEndpoints.SmoothAmbientChart ThreeSphere := {
    chart := chartAt (Euc 3) (γ t)
    smooth := contMDiffOn_chart
    inverse_smooth := contMDiffOn_chart_symm }
  have hc : γ t ∈ c.chart.source := mem_chart_source _ _
  obtain ⟨w, hw, hD⟩ := native_curve_coordinates_hasDerivAt E F i j U hU γ q
    hγ hq heq t ht c hc
  have hca := (c.smooth _ hc).contMDiffAt (c.chart.open_source.mem_nhds hc)
  have hga := (hγ t ht).contMDiffAt (hU.mem_nhds ht)
  have hcdiff : c.chart.MDifferentiable (𝓡 3) 𝓘(ℝ, Euc 3) :=
    ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
  have hd : mfderiv 𝓘(ℝ) 𝓘(ℝ, Euc 3) (c.chart ∘ γ) t 1 ≠ 0 := by
    rw [mfderiv_comp_apply t (hca.mdifferentiableAt (by simp))
      (hga.mdifferentiableAt (by norm_num))]
    intro he
    exact hreg t ht (hcdiff.mfderiv_injective hc (by simpa only [map_zero] using he))
  have hv : deriv (c.chart ∘ γ) t ≠ 0 := by
    intro he
    apply hd
    rw [mfderiv_eq_fderiv]
    simp only [ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv, he, smul_zero, map_zero]
  intro hzero
  have hwzero : w = 0 := hw.deriv.symm.trans hzero
  rw [hwzero, map_zero] at hD
  exact hv hD.symm

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
