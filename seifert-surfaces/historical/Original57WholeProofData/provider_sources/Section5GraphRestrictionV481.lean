import Section5EllipticAssemblyV480

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff BigOperators

namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open AppendixBOriginalV479

variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

private theorem graph_plane_point (x : E2) (z : ℝ) :
    graphPlaneCoordinates (graphPoint x z) = x := by
  ext i
  fin_cases i <;> simp [graphPlaneCoordinates, graphPoint]

private theorem graph_point_height (x : E2) (z : ℝ) : graphPoint x z 2 = z := by
  simp [graphPoint]

/-- The literal same two heights persist when their actual ambient graph chart
is restricted to a smaller planar cylinder. -/
theorem interior_graph_restrict {A B : IncompressibleSpanningSurface.{0} E}
    {p : E.Carrier} (c : InteriorGraph A B p) (r : ℝ) (hr : 0 < r) (hrc : r ≤ c.R) :
    ∃ d : InteriorGraph A B p, d.R = r ∧ d.lower = c.lower ∧ d.upper = c.upper := by
  let V : Set E3 := {y | ‖graphPlaneCoordinates y‖ < r}
  have hplane : Continuous graphPlaneCoordinates := by
    unfold graphPlaneCoordinates
    fun_prop
  have hV : IsOpen V := isOpen_lt hplane.norm continuous_const
  let coord : OpenPartialHomeomorph E.Carrier E3 :=
    (c.coordinates.symm.restrOpen V hV).symm
  have hsource : coord.source = c.coordinates.source ∩ c.coordinates ⁻¹' V := rfl
  have htarget : coord.target = c.coordinates.target ∩ V := rfl
  have hfun : (coord : E.Carrier → E3) = c.coordinates := rfl
  have hinv : (coord.symm : E3 → E.Carrier) = c.coordinates.symm := rfl
  have hsub : Metric.ball (0 : E2) r ⊆ Metric.ball 0 c.R := Metric.ball_subset_ball hrc
  have graph_restrict (F : Set E.Carrier) (u : E2 → ℝ)
      (hu : ∀ x ∈ Metric.ball (0 : E2) c.R, |u x| < c.eta)
      (hg : F ∩ c.coordinates.source =
        (fun x : E2 => c.coordinates.symm (graphPoint x (u x))) '' Metric.ball 0 c.R) :
      F ∩ coord.source =
        (fun x : E2 => coord.symm (graphPoint x (u x))) '' Metric.ball 0 r := by
    ext z
    constructor
    · rintro ⟨hz, hzs⟩
      have hzold : z ∈ F ∩ c.coordinates.source := ⟨hz, hzs.1⟩
      rw [hg] at hzold
      obtain ⟨x, hx, rfl⟩ := hzold
      have ht : graphPoint x (u x) ∈ c.coordinates.target := c.cylinder_inside
        ⟨by simpa only [graph_plane_point, Metric.mem_ball, dist_zero_right] using hx,
         by simpa only [graph_point_height] using hu x hx⟩
      refine ⟨x, ?_, rfl⟩
      have hzV := hzs.2
      change ‖graphPlaneCoordinates (c.coordinates (c.coordinates.symm (graphPoint x (u x))))‖ < r at hzV
      simpa only [c.coordinates.right_inv ht, graph_plane_point, Metric.mem_ball,
        dist_zero_right] using hzV
    · rintro ⟨x, hx, rfl⟩
      have hxold := hsub hx
      have ht : graphPoint x (u x) ∈ c.coordinates.target := c.cylinder_inside
        ⟨by simpa only [graph_plane_point, Metric.mem_ball, dist_zero_right] using hxold,
         by simpa only [graph_point_height] using hu x hxold⟩
      have hzold : c.coordinates.symm (graphPoint x (u x)) ∈ F ∩ c.coordinates.source := by
        rw [hg]
        exact ⟨x, hxold, rfl⟩
      refine ⟨hzold.1, hzold.2, ?_⟩
      change ‖graphPlaneCoordinates (c.coordinates (c.coordinates.symm (graphPoint x (u x))))‖ < r
      simpa only [c.coordinates.right_inv ht, graph_plane_point, Metric.mem_ball,
        dist_zero_right] using hx
  refine ⟨{
    coordinates := coord
    source_interior := fun x hx => c.source_interior hx.1
    smooth := c.smooth.mono (fun _ hx => hx.1)
    inverse_smooth := c.inverse_smooth.mono (fun _ hx => hx.1)
    base_mem := ?_
    base_zero := c.base_zero
    R := r
    R_pos := hr
    eta := c.eta
    eta_pos := c.eta_pos
    cylinder_inside := ?_
    lower := c.lower
    upper := c.upper
    lower_smooth := c.lower_smooth.mono hsub
    upper_smooth := c.upper_smooth.mono hsub
    lower_zero := c.lower_zero
    upper_zero := c.upper_zero
    lower_tangent := c.lower_tangent
    upper_tangent := c.upper_tangent
    lower_inside := fun x hx => c.lower_inside x (hsub hx)
    upper_inside := fun x hx => c.upper_inside x (hsub hx)
    graph_A := graph_restrict A.1.image c.upper c.upper_inside c.graph_A
    graph_B := graph_restrict B.1.image c.lower c.lower_inside c.graph_B
  }, rfl, rfl, rfl⟩
  · refine ⟨c.base_mem, ?_⟩
    change ‖graphPlaneCoordinates (c.coordinates p)‖ < r
    rw [c.base_zero]
    have hz : graphPlaneCoordinates (0 : E3) = 0 := by
      ext i
      fin_cases i <;> simp [graphPlaneCoordinates]
    simpa only [hz, norm_zero] using hr
  · intro y hy
    exact ⟨c.cylinder_inside ⟨lt_of_lt_of_le hy.1 hrc, hy.2⟩, hy.1⟩

end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480

namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open AppendixBOriginalV479

variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- Local coefficient production suffices: both heights, their difference,
the integer order estimate and the two signs survive the same radius restriction. -/
theorem interior_tangency_of_local_equations
    {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : OriginalPair g J) (hB3 : InteriorTangencyConclusion D)
    (hlocal : ∀ p : E.Carrier, ∀ c : InteriorGraph D.A D.B p,
      ∃ r : ℝ, 0 < r ∧ r ≤ c.R ∧
        Nonempty (LinearGraphEquation (graphDifference c) (Metric.ball 0 r))) :
    InteriorTangencyResult E D.A D.B := by
  intro p hp
  obtain ⟨hiso, c, m, hm, c1, c2, R, hc1, hc2, hR, hRc, hgrad, hzero, hsign⟩ := hB3 p hp
  obtain ⟨r, hr, hrc, L⟩ := hlocal p c
  obtain ⟨d, hdr, hdl, hdu⟩ := interior_graph_restrict c r hr hrc
  have hdiff : graphDifference d = graphDifference c := by
    change (fun x => d.upper x - d.lower x) = (fun x => c.upper x - c.lower x)
    rw [hdl, hdu]
  refine ⟨hiso, d, ?_, m, hm, c1, c2, min R r, hc1, hc2, lt_min hR hr, ?_, ?_, ?_, ?_⟩
  · simpa only [hdiff, hdr] using L
  · rw [hdr]
    exact min_le_right _ _
  · intro x hx0 hx
    simpa only [hdiff] using hgrad x hx0 (lt_of_lt_of_le hx (min_le_left _ _))
  · intro x hx
    rw [hdiff]
    exact hzero x (Metric.ball_subset_ball (min_le_left R r) hx)
  · intro V hV
    have hsmall : Metric.ball (0 : E2) (min R r) ∈ 𝓝 (0 : E2) :=
      Metric.ball_mem_nhds _ (lt_min hR hr)
    obtain ⟨⟨x, hx, hxp⟩, ⟨y, hy, hyn⟩⟩ := hsign
      (V ∩ Metric.ball 0 (min R r)) (Filter.inter_mem hV hsmall)
    exact ⟨⟨x, ⟨hx.1.1, hx.1.2⟩, by simpa only [hdiff] using hxp⟩,
      ⟨y, ⟨hy.1.1, hy.1.2⟩, by simpa only [hdiff] using hyn⟩⟩

end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
