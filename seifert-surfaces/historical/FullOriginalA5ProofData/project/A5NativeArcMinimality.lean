import A5GraphMinimalityClosure

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter MeasureTheory
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC CurvedDivergence
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N] {h : AmbientMetric N}

theorem signed_arc_sides_dense
    (U : Set E2) (s : E2 → ℝ) (γ : ℝ → E2) (left right : ℝ)
    (G : SignedArcGeometry U s γ left right) :
    U ⊆ closure (signedDomain U s false ∪ signedDomain U s true) := by
  have hsource : (μH[2] : Measure ℝ) = 0 := Real.hausdorffMeasure_of_finrank_lt (by simp)
  have himage : μH[2] (γ '' Ioo left right) = 0 :=
    (G.arc_smooth.differentiableOn (by simp)).hausdorffMeasure_image_eq_zero
      (by norm_num) (by rw [hsource]; simp)
  have harc : volume (γ '' Ioo left right) = 0 := by
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2,
      Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
    simp only [Nat.cast_ofNat, himage, smul_zero]
  have hnull : volume {x ∈ U | s x = 0} = 0 := by
    rw [G.zero_set_exact]
    exact measure_mono_null inter_subset_left harc
  have hd : Dense {x | x ∉ {y ∈ U | s y = 0}} :=
    volume.dense_of_ae (measure_eq_zero_iff_ae_notMem.mp hnull)
  have hs : U ∩ {x | x ∉ {y ∈ U | s y = 0}} ⊆
      signedDomain U s false ∪ signedDomain U s true := by
    intro x hx
    have hn : s x ≠ 0 := fun hz => hx.2 ⟨hx.1, hz⟩
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · exact Or.inl ⟨hx.1, hneg⟩
    · exact Or.inr ⟨hx.1, hpos⟩
  exact (hd.open_subset_closure_inter G.disc_open).trans (closure_mono hs)

/-- Both smoothness and actual metric minimality extend through a curved
seam. All metric operators, weak equations and density facts are proved. -/
theorem native_metric_graph_smooth_minimal_across_arc
    (G : NativeMetricGraph h) (s : E2 → ℝ) (γ : ℝ → E2) (left right : ℝ)
    (hgeom : SignedArcGeometry G.disc s γ left right)
    (hsmooth : ∀ p : Bool, ContDiffOn ℝ ∞ G.height (signedDomain G.disc s p))
    (hminimal : ∀ p : Bool, IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) (signedDomain G.disc s p)) :
    ContDiffOn ℝ ∞ G.height G.disc ∧
    IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) G.disc := by
  have hs := native_metric_graph_smooth_across_arc G s γ left right hgeom hsmooth hminimal
  refine ⟨hs, ?_⟩
  apply native_metric_graph_minimal_of_dense G
    (signedDomain G.disc s false ∪ signedDomain G.disc s true)
    (by rintro x (hx | hx) <;> exact hx.1)
    (signed_arc_sides_dense G.disc s γ left right hgeom) hs
  refine ⟨?_, ?_⟩
  · exact ((contDiffOn_const.add G.plane.contDiff.contDiffOn).add
      (hs.smul_const G.normal)).mono (by rintro x (hx | hx) <;> exact hx.1)
  · intro x hx
    rcases hx with hx | hx
    · exact (hminimal false).2 x hx
    · exact (hminimal true).2 x hx

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
