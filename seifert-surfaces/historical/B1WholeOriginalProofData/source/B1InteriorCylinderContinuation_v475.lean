import B1InteriorCoefficientMeanValue_v475
import B1InteriorCoefficientEllipticity_v475
import B1InteriorGermRestriction_v475
import B1InteriorCommonCylinder_v475
noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- In one actual convex height cylinder, the difference between the zero
minimal graph and the other minimal graph has a coefficient-only elliptic
continuation equation; all coefficients and uniform bounds are constructed. -/
theorem native_interior_cylinder_zero_continuation_v475
    (O : Set E2) (hO : IsOpen O) (p : E2) (hp : p ∈ O)
    (u : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u O)
    (V : Set E3) (hV : IsOpen V) (η : ℝ) (hη : 0 < η)
    (hVc : V=native_interior_graph_splitting_v475 '' (O ×ˢ Ioo (-η) η))
    (H : CoordinateMetric V)
    (hpoints : ∀ z ∈ O, jetPoint (z,0,0) ∈ V ∧ jetPoint (z,u z,0) ∈ V)
    (heq0 : ∀ z ∈ O, native_interior_graph_residual_v475 H (fun _ => 0) z=0)
    (hequ : ∀ z ∈ O, native_interior_graph_residual_v475 H u z=0)
    (hacc : p ∈ closure {z | z ∈ O ∧ native_planar_zero_germ_v475 O u z}) :
    native_planar_zero_germ_v475 O u p := by
  classical
  obtain ⟨r,hr,hclosed⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hp)
  let C := Metric.closedBall p r
  have hsegments (z : E2) (hz : z ∈ O) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      jetPoint (z,t*u z,t • planarGradient u z) ∈ V := by
    have hb : -η < u z ∧ u z < η := by
      obtain ⟨w,hw,he⟩ := hVc ▸ (hpoints z hz).2
      have he' : w=(z,u z) := native_interior_graph_splitting_v475.injective he
      rw [he'] at hw
      exact hw.2
    have htlo : -η < t*u z := by
      by_cases hzu : 0 ≤ u z
      · have hh := mul_nonneg ht.1 hzu
        linarith
      · have hh := mul_nonneg (sub_nonneg.mpr ht.2) (neg_nonneg.mpr (le_of_not_ge hzu))
        nlinarith
    have hthi : t*u z < η := by
      by_cases hzu : 0 ≤ u z
      · have hh := mul_nonneg (sub_nonneg.mpr ht.2) hzu
        nlinarith
      · have hh := mul_nonpos_of_nonneg_of_nonpos ht.1 (le_of_not_ge hzu)
        linarith
    rw [hVc]
    exact ⟨(z,t*u z),⟨hz,htlo,hthi⟩,rfl⟩
  let W : NativeInteriorGraphWindow_v475 :=
    { U := O
      U_open := hO
      V := V
      V_open := hV
      metric := H
      height := u
      height_smooth := hu
      compactBase := C
      compactBase_compact := isCompact_closedBall p r
      U_contains := hclosed
      jets_inside := fun z hz t ht => hsegments z (hclosed hz) t ht }
  obtain ⟨N,hN,hCN,hNO,hseg,hheight,hgrad,ha,hq,hlg,hlh,hb,hc⟩ :=
    native_interior_coefficient_open_tube_v475 W
  obtain ⟨hformula,hsym,ell,A,hell,hA,hbounds⟩ :=
    native_interior_slope_hessian_uniform_bounds_v475 W
  obtain ⟨_,_,_,_,_,_,hidentity⟩ :=
    native_interior_coefficient_mean_value_v475 W N hN hNO hseg hq
  let B := Metric.ball p r
  have hB : IsOpen B := Metric.isOpen_ball
  have hpB : p ∈ B := Metric.mem_ball_self hr
  have hBC : B ⊆ C := Metric.ball_subset_closedBall
  have hBN : B ⊆ N := hBC.trans hCN
  have hBO : B ⊆ O := hBC.trans hclosed
  have hEll : SmoothEllipticOn W.a W.b W.c B :=
    ⟨fun i j => (ha i j).mono hBN,hb.mono hBN,hc.mono hBN,
      fun z hz => hsym z (hBC hz),ell,A,hell,hA,fun z hz => hbounds z (hBC hz)⟩
  have hPDE : ∀ z ∈ B, classicalL W.a W.b W.c u z=0 := by
    intro z hz
    have hh := hidentity z (hBN hz)
    change native_interior_graph_residual_v475 H u z-
      native_interior_graph_residual_v475 H (fun _ => 0) z=classicalL W.a W.b W.c u z at hh
    rw [hequ z (hBO hz),heq0 z (hBO hz),sub_self] at hh
    exact hh.symm
  have haccB := native_planar_zero_germ_accumulation_restrict_v475 O B hB hBO u p hpB hacc
  obtain ⟨Z,hZ,hpZ,hZB,hZu⟩ := native_interior_local_zero_continuation_v475 B hB p hpB
    W.a W.b W.c u hEll (hu.mono hBO) hPDE haccB
  exact ⟨Z,hZ,hpZ,hZB.trans hBO,hZu⟩

#print axioms native_interior_cylinder_zero_continuation_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
