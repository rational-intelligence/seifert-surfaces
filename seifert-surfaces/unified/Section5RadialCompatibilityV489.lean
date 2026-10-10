import Section5RadialComparisonV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
noncomputable section
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ,E3) ∞ N]

theorem radial_line_dist_bound (y z : E3) (hz : z 0 = 0) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) (y 0)) : dist (radialLine y t) z ≤ 2 * dist y z := by
  have hcoord : |y 0| ≤ ‖y-z‖ := by
    simpa only [PiLp.sub_apply,hz,sub_zero,Real.norm_eq_abs] using
      PiLp.norm_apply_le (y-z) 0
  have he : ‖coordinateVector 3 0‖ = 1 := by
    simp [coordinateVector,EuclideanSpace.single]
  rw [dist_eq_norm,dist_eq_norm]
  have heq : radialLine y t-z = (y-z)+(t-y 0) • coordinateVector 3 0 := by
    unfold radialLine
    abel
  rw [heq]
  calc
    ‖y-z+(t-y 0) • coordinateVector 3 0‖ ≤ ‖y-z‖ + ‖(t-y 0) • coordinateVector 3 0‖ := norm_add_le _ _
    _ = ‖y-z‖+(y 0-t) := by
      rw [norm_smul,he,mul_one,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr ht.2)]
      ring
    _ ≤ 2 * ‖y-z‖ := by
      have hy : 0 ≤ y 0 := ht.1.trans ht.2
      rw [abs_of_nonneg hy] at hcoord
      linarith [ht.1]

theorem warped_radial_segments_near_boundary {h : AmbientMetric N} {M : Set N}
    (C D : WarpedBoundaryCollar h M) (p : N)
    (hpC : p ∈ C.coordinates.chart.source) (hpD : p ∈ D.coordinates.chart.source)
    (hp : p ∈ frontier M) :
    ∃ U : Set N, IsOpen U ∧ p ∈ U ∧ U ⊆ C.coordinates.chart.source ∧
      ∀ q ∈ U, ∀ t ∈ Icc (0 : ℝ) (C.radial q),
        radialLine (C.coordinates.chart q) t ∈ C.coordinates.chart.target ∧
        C.coordinates.chart.symm (radialLine (C.coordinates.chart q) t) ∈ D.coordinates.chart.source := by
  let V := C.coordinates.chart.target ∩ C.coordinates.chart.symm ⁻¹' D.coordinates.chart.source
  have hV : IsOpen V := C.coordinates.chart.continuousOn_symm.isOpen_inter_preimage
    C.coordinates.chart.open_target D.coordinates.chart.open_source
  have hpV : C.coordinates.chart p ∈ V :=
    ⟨C.coordinates.chart.map_source hpC,by simpa only [mem_preimage,C.coordinates.chart.left_inv hpC] using hpD⟩
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hV _ hpV
  let U := C.coordinates.chart.source ∩ C.coordinates.chart ⁻¹' Metric.ball (C.coordinates.chart p) (ε/3)
  have hU : IsOpen U := C.coordinates.chart.continuousOn.isOpen_inter_preimage
    C.coordinates.chart.open_source Metric.isOpen_ball
  have hpU : p ∈ U := ⟨hpC,by simpa only [mem_preimage,Metric.mem_ball,dist_self] using (by linarith : 0 < ε/3)⟩
  refine ⟨U,hU,hpU,inter_subset_left,?_⟩
  intro q hq t ht
  have hz : C.coordinates.chart p 0 = 0 :=
    (C.radial_coordinate p hpC).symm.trans ((C.boundary_identification p hpC).mp hp)
  have ht' : t ∈ Icc (0 : ℝ) (C.coordinates.chart q 0) := by
    rwa [← C.radial_coordinate q hq.1]
  apply hball
  rw [Metric.mem_ball]
  have hqdist : dist (C.coordinates.chart q) (C.coordinates.chart p) < ε/3 := hq.2
  exact (radial_line_dist_bound _ _ hz t ht').trans_lt (by linarith)

theorem warped_radial_agreement_near_boundary {h : AmbientMetric N} {M : Set N}
    (C D : WarpedBoundaryCollar h M) (p : N)
    (hpC : p ∈ C.coordinates.chart.source) (hpD : p ∈ D.coordinates.chart.source)
    (hp : p ∈ frontier M) :
    ∃ U : Set N, IsOpen U ∧ p ∈ U ∧
      U ⊆ C.coordinates.chart.source ∩ D.coordinates.chart.source ∧
      ∀ q ∈ U ∩ M, C.radial q = D.radial q := by
  obtain ⟨UC,hUC,hpUC,hC,hsegC⟩ := warped_radial_segments_near_boundary C D p hpC hpD hp
  obtain ⟨UD,hUD,hpUD,hD,hsegD⟩ := warped_radial_segments_near_boundary D C p hpD hpC hp
  refine ⟨UC ∩ UD,hUC.inter hUD,⟨hpUC,hpUD⟩,
    fun q hq => ⟨hC hq.1,hD hq.2⟩,?_⟩
  intro q hq
  apply le_antisymm
  · exact warped_radial_comparison D C q (hD hq.1.2)
      ((D.region_identification q (hD hq.1.2)).mp hq.2) (hsegD q hq.1.2)
  · exact warped_radial_comparison C D q (hC hq.1.1)
      ((C.region_identification q (hC hq.1.1)).mp hq.2) (hsegC q hq.1.1)

#print axioms warped_radial_agreement_near_boundary
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
