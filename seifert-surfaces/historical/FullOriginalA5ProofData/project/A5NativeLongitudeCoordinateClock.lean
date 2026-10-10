import A5NativeBoundaryClockCoverage

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u

/-- The original longitude is a smooth regular ambient-coordinate curve,
and its native source clock covers the complete boundary near the point. -/
theorem native_longitude_coordinate_clock_with_coverage
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (J : LongitudeFoliation.{u} E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (hF : J.BoundaryIn F.map)
    (x : S) (hx : x ∈ S.boundary)
    (c : SmoothAmbientChart ThreeSphere) (hc : E.toSphere (F.map x) ∈ c.chart.source) :
    ∃ b : ℝ → S, b 0 = x ∧ ContinuousOn b (Ioo (-1 : ℝ) 1) ∧
      (∀ t, b t ∈ S.boundary) ∧
      IsEmbedding (fun t : Ioo (-1 : ℝ) 1 => b t) ∧
      (∃ U : Set S, IsOpen U ∧ x ∈ U ∧
        range (fun t : Ioo (-1 : ℝ) 1 => b t) = U ∩ S.boundary) ∧
      ∃ I : Set ℝ, IsOpen I ∧ (0 : ℝ) ∈ I ∧
        ContDiffOn ℝ ∞ (c.chart ∘ E.toSphere ∘ F.map ∘ b) I ∧
        deriv (c.chart ∘ E.toSphere ∘ F.map ∘ b) 0 ≠ 0 := by
  obtain ⟨b,hb0,hbc,hbb,hbi,hbs,hbr,U,hU,hxU,hcover⟩ :=
    native_longitude_boundary_clock_with_coverage E J F hF x hx
  let γ := E.toSphere ∘ F.map ∘ b
  let I := Ioo (-1 : ℝ) 1 ∩ γ ⁻¹' c.chart.source
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨neg_one_lt_zero,zero_lt_one⟩
  have hc0 : γ 0 ∈ c.chart.source := by
    change E.toSphere (F.map (b 0)) ∈ c.chart.source
    rwa [hb0]
  have hI : IsOpen I := hbs.continuousOn.isOpen_inter_preimage isOpen_Ioo c.chart.open_source
  have h0I : (0 : ℝ) ∈ I := ⟨h0,hc0⟩
  have hs : ContDiffOn ℝ ∞ (c.chart ∘ γ) I :=
    (c.smooth.comp (hbs.mono inter_subset_left) (fun t ht => ht.2)).contDiffOn
  obtain ⟨A,hA⟩ := ambient_chart_tangent_equivalence c (γ 0) hc0
  have hd : deriv (c.chart ∘ γ) 0 = A (mfderiv 𝓘(ℝ) (𝓡 3) γ 0 1) := by
    rw [hA]
    exact ambient_chart_curve_derivative_transport γ 0
      ((hbs.contMDiffAt (isOpen_Ioo.mem_nhds h0)).mdifferentiableAt (by simp)) c hc0
  refine ⟨b,hb0,hbc,hbb,hbi,⟨U,hU,hxU,hcover⟩,I,hI,h0I,hs,?_⟩
  rw [hd]
  intro hh
  exact hbr 0 h0 (A.injective (hh.trans (map_zero _).symm))

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
