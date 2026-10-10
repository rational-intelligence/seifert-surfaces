import A7AmbientChartStraighteningV464
import A7HalfDiscV464
import A7MinimalTranslationV464
import A7MinimalLocalityV464
import OriginalA4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u v
variable {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]
  {N : Type v} [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ,E3) ∞ N]

theorem halfspace_minimal_graph_data {F : S → N}
    (hF : ContMDiff (𝓡∂ 2) 𝓘(ℝ,E3) ∞ F) (x : S)
    (hx : x ∈ (𝓡∂ 2).boundary S)
    (hinj : Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) F x))
    (h : AmbientMetric N) (M : Set N) (C : WarpedBoundaryCollar h M)
    (hp : F x ∈ C.coordinates.chart.source)
    (himage : ∀ y, F y ∈ M)
    (hboundary : ∀ y, F y ∈ frontier M ↔ y ∈ (𝓡∂ 2).boundary S)
    (hminimal : IsMinimalPatch h (F ∘ (extChartAt (𝓡∂ 2) x).symm)
      ((extChartAt (𝓡∂ 2) x).target ∩ {y : E2 | 0 < y 0})) :
    ∃ D : A4OriginalData h M C,
      D.p = F x ∧ D.plane = LinearMap.range (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) F x).toLinearMap := by
  let e := extChartAt (𝓡∂ 2) x
  let a := e x
  have ha : a 0 = 0 := by
    have hb : a ∈ frontier (range (𝓡∂ 2)) := hx
    rw [frontier_range_modelWithCornersEuclideanHalfSpace] at hb
    exact hb.symm
  obtain ⟨n,hn,hort,c,hpc,hstraight⟩ := ambient_chart_straightening hF x hinj h
  let P := LinearMap.range (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) F x).toLinearMap
  let frame : E2 ≃L[ℝ] P := rangeFrame x hinj
  let L := (chartDifferential c (F x)).comp (P.subtypeL.comp frame.toContinuousLinearMap)
  let Φ : E2 → N := fun z => F (e.symm (a+z))
  have hshift : Tendsto (fun z : E2 => a+z) (𝓝[range (𝓡∂ 2)] 0)
      (𝓝[range (𝓡∂ 2)] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · have hc : Continuous (fun z : E2 => a+z) := continuous_const.add continuous_id
      have ht : Tendsto (fun z : E2 => a+z) (𝓝 0) (𝓝 a) := by
        convert hc.continuousAt (x := 0) |>.tendsto using 1 <;> first | rfl | simp
      exact ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      rw [range_modelWithCornersEuclideanHalfSpace] at hz ⊢
      change 0 ≤ (a+z) 0
      simpa [ha] using hz
  have hst : ∀ᶠ z : E2 in 𝓝[range (𝓡∂ 2)] 0,
      Φ z ∈ c.chart.source ∧ c.chart (Φ z) = c.chart (F x) + L z := by
    filter_upwards [hshift.eventually hstraight] with z hz
    refine ⟨hz.1,?_⟩
    have hL (w : E2) : L w = (chartDifferential c (F x))
        (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) F x ((tangentSpaceCastModel (𝓡∂ 2) x).symm w)) := rfl
    have hz' := hz.2
    change c.chart (Φ z) = c.chart (F x) + (chartDifferential c (F x))
      (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) F x ((tangentSpaceCastModel (𝓡∂ 2) x).symm (a+z-a))) at hz'
    rw [add_sub_cancel_left,←hL] at hz'
    exact hz' 
  have het : ∀ᶠ z : E2 in 𝓝[range (𝓡∂ 2)] 0, a+z ∈ e.target :=
    hshift.eventually (extChartAt_target_mem_nhdsWithin x)
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhdsWithin_iff.mp (Filter.inter_mem hst het)
  let U := closedHalfDisc r
  let V := U ∩ Metric.ball 0 r
  have hlocal (z : E2) (hz : z ∈ V) :
      Φ z ∈ c.chart.source ∧ c.chart (Φ z) = c.chart (F x) + L z ∧ a+z ∈ e.target := by
    have hzR : z ∈ range (𝓡∂ 2) := by
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact hz.1.2
    have hh := hrsub ⟨hz.2,hzR⟩
    exact ⟨hh.1.1,hh.1.2,hh.2⟩
  have hgraph (z : E2) (hz : z ∈ V) :
      c.chart.symm (graphMap (c.chart (F x)) L (chartDifferential c (F x) n) 0 z) = Φ z := by
    change c.chart.symm (c.chart (F x) + L z + 0 • chartDifferential c (F x) n) = Φ z
    simp only [zero_smul,add_zero]
    rw [←(hlocal z hz).2.1,c.chart.left_inv (hlocal z hz).1]
  have hminimalDomain : IsOpen (e.target ∩ {y : E2 | 0 < y 0}) := by
    have hpos : IsOpen {y : E2 | 0 < y 0} := isOpen_lt continuous_const
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)
    have heq : e.target ∩ {y : E2 | 0 < y 0} =
        ((𝓡∂ 2).symm ⁻¹' (chartAt (EuclideanHalfSpace 2) x).target) ∩ {y : E2 | 0 < y 0} := by
      change (extChartAt (𝓡∂ 2) x).target ∩ _ = _
      rw [extChartAt_target]
      ext y
      constructor
      · exact fun hy => ⟨hy.1.1,hy.2⟩
      · intro hy
        refine ⟨⟨hy.1,?_⟩,hy.2⟩
        rw [range_modelWithCornersEuclideanHalfSpace]
        exact (show 0 < y 0 from hy.2).le
    rw [heq]
    exact ((chartAt (EuclideanHalfSpace 2) x).open_target.preimage (𝓡∂ 2).continuous_symm).inter hpos
  have hminΦ : IsMinimalPatch h Φ (interior U ∩ Metric.ball 0 r) := by
    apply IsMinimalPatch.mono (IsMinimalPatch.translate hminimal hminimalDomain a)
    intro z hz
    refine ⟨(hlocal z ⟨interior_subset hz.1,hz.2⟩).2.2,?_⟩
    change 0 < (a+z) 0
    simpa [ha] using halfDisc_interior_positive hz.1
  have hminG : IsMinimalPatch h
      (c.chart.symm ∘ graphMap (c.chart (F x)) L (chartDifferential c (F x) n) 0)
      (interior U ∩ Metric.ball 0 r) := by
    apply IsMinimalPatch.congr_open hminΦ (isOpen_interior.inter Metric.isOpen_ball)
    exact fun z hz => hgraph z ⟨interior_subset hz.1,hz.2⟩
  let D : A4OriginalData h M C := {
    p := F x
    p_boundary := (hboundary x).2 hx
    p_collar := hp
    plane := P
    planeFrame := frame
    normal := n
    normal_nonzero := hn
    normal_orthogonal := hort
    graphCoordinates := c
    p_chart := hpc
    region := U
    region_closed := halfDisc_isClosed r
    zero_boundary := halfDisc_zero_boundary hr
    sphere_condition := halfDisc_has_interiorSphere r hr
    delta := r
    delta_pos := hr
    height := 0
    height_C1 := contDiff_const.contDiffOn
    height_zero := rfl
    height_flat := hasFDerivWithinAt_const (0 : ℝ) (0 : E2) _
    graph_in_chart := by
      intro z hz
      change c.chart (F x) + L z + 0 • chartDifferential c (F x) n ∈ c.chart.target
      simp only [zero_smul,add_zero]
      rw [←(hlocal z hz).2.1]
      exact c.chart.map_source (hlocal z hz).1
    graph_in_manifold := by
      intro z hz
      change c.chart.symm (graphMap (c.chart (F x)) L (chartDifferential c (F x) n) 0 z) ∈ M
      rw [hgraph z hz]
      exact himage _
    minimal_interior := hminG
    boundary_only := by
      intro z hz hb
      change c.chart.symm (graphMap (c.chart (F x)) L (chartDifferential c (F x) n) 0 z) ∈ frontier M at hb
      rw [hgraph z hz] at hb
      have hbs : e.symm (a+z) ∈ (𝓡∂ 2).boundary S := (hboundary _).1 hb
      have hbt := (𝓡∂ 2).isBoundaryPoint_iff_of_mem_atlas (n := ∞) (by simp)
        (chart_mem_atlas (EuclideanHalfSpace 2) x)
        (show e.symm (a+z) ∈ (chartAt (EuclideanHalfSpace 2) x).source by
          have hh := e.map_target (hlocal z hz).2.2
          change e.symm (a+z) ∈ (extChartAt (𝓡∂ 2) x).source at hh
          rw [extChartAt_source] at hh
          exact hh)
      have hf := hbt.1 hbs
      change e (e.symm (a+z)) ∈ frontier e.target at hf
      rw [e.right_inv (hlocal z hz).2.2] at hf
      -- Use the exact zero coordinate of a boundary point in this source chart.
      have hz0 : (a+z) 0 = 0 := by
        have htar := (hlocal z hz).2.2
        have hB : IsOpen ((𝓡∂ 2).symm ⁻¹' (chartAt (EuclideanHalfSpace 2) x).target) :=
          (chartAt (EuclideanHalfSpace 2) x).open_target.preimage (𝓡∂ 2).continuous_symm
        have htr : a+z ∈ range (𝓡∂ 2) := extChartAt_target_subset_range x htar
        by_contra hne
        have hnonneg : 0 ≤ (a+z) 0 := by
          simpa only [range_modelWithCornersEuclideanHalfSpace,Set.mem_setOf_eq] using htr
        have hpositive : 0 < (a+z) 0 := lt_of_le_of_ne hnonneg (Ne.symm hne)
        have hi : a+z ∈ interior e.target := by
          change a+z ∈ interior (extChartAt (𝓡∂ 2) x).target
          rw [extChartAt_target,interior_inter,hB.interior_eq,interior_range_modelWithCornersEuclideanHalfSpace]
          exact ⟨(by have ht := htar; rw [extChartAt_target] at ht; exact ht.1),hpositive⟩
        exact disjoint_interior_frontier.le_bot ⟨hi,hf⟩
      apply halfDisc_boundary_of_zero hz.1
      simpa [ha] using hz0 }
  exact ⟨D,rfl,rfl⟩

end SeifertSurfaces.OriginalEndpoints.A7Support
