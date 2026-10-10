import Section5CommonLeafEmbeddingV488
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter MeasureTheory Bundle
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem longitude_speed_smooth (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    ContDiff ℝ ∞ (longitudeSpeed g J a) := by
  have ht := (longitude_clock_smooth J a).contMDiff_tangentMap (m := ∞) (by simp)
  have hinput : ContMDiff 𝓘(ℝ) (𝓘(ℝ).tangent) ∞ (fun t : ℝ =>
      (⟨t,(1 : TangentSpace 𝓘(ℝ) t)⟩ : TangentBundle 𝓘(ℝ) ℝ)) := by
    convert! (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ))).comp
      ((contDiff_id.prodMk (contDiff_const (c := (1 : ℝ)))).contMDiff) using 1
  have hv := ht.comp hinput
  letI : RiemannianBundle (fun p : E.Carrier => TangentSpace (𝓡∂ 3) p) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle (𝓡∂ 3) ∞ (Euc 3)
      (fun p : E.Carrier => TangentSpace (𝓡∂ 3) p) :=
    ⟨⟨g.inner,g.contMDiff,fun _ _ _ => rfl⟩⟩
  have hg : ContDiff ℝ ∞ (fun t : ℝ => g.inner (longitudeClock J a t)
      (mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeClock J a) t 1)
      (mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeClock J a) t 1)) :=
    (hv.inner_bundle hv).contDiff
  exact hg.sqrt (fun t => (g.pos _ _ (longitude_clock_velocity_ne_zero J a t)).ne')

theorem longitude_arclength_smooth (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    ContDiff ℝ ∞ (longitudeArclength g J a) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (longitude_arclength_hasDerivAt g J a t).differentiableAt, ?_⟩
  have hd : deriv (longitudeArclength g J a) = longitudeSpeed g J a :=
    funext (fun t => (longitude_arclength_hasDerivAt g J a t).deriv)
  rw [hd]
  exact longitude_speed_smooth g J a

theorem longitude_arclength_inverse_smooth (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    ContDiff ℝ ∞ (longitudeArclengthIso g J a).symm := by
  exact (longitudeArclengthIso g J a).toHomeomorph.contDiff_symm_deriv
    (fun t => (longitude_speed_positive g J a t).ne')
    (longitude_arclength_hasDerivAt g J a) (longitude_arclength_smooth g J a)

theorem longitude_unit_clock_smooth (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    ContMDiff 𝓘(ℝ) (𝓡∂ 3) ∞ (longitudeUnitClock g J a) :=
  (longitude_clock_smooth J a).comp (longitude_arclength_inverse_smooth g J a).contMDiff

#print axioms longitude_unit_clock_smooth
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
