import Section5GeometricDefinitions
import AreaHelpers
import EmbeddedTransitionV487
import MeasurableRefinementV487

set_option autoImplicit false
noncomputable section
open Set Topology Function MeasureTheory Metric Filter Bundle
open scoped Manifold ContDiff ENNReal NNReal BigOperators Pointwise

namespace SeifertSurfaces.OriginalEndpoints.Section5.NativeAreaV487
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates

variable {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M]

private def density {F : Set M} (g : SmoothMetric M) (A : ImageAreaAtlas F)
    (i : ℕ) (x : E2) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (Matrix.det (A.gram g i x)))

private theorem atlas_injOn {F : Set M} (A : ImageAreaAtlas F) (i : ℕ) :
    InjOn (A.map i) (A.chartDomain i) := by
  intro x hx y hy heq
  exact congrArg Subtype.val ((A.chart_embedding i).injective (a₁ := ⟨x, hx⟩)
    (a₂ := ⟨y, hy⟩) heq)

private theorem atlas_embedding_subset {F : Set M} (A : ImageAreaAtlas F) (i : ℕ)
    {s : Set E2} (hs : s ⊆ A.chartDomain i) :
    IsEmbedding (s.domRestrict (A.map i)) := by
  exact (A.chart_embedding i).comp (.inclusion hs)

private theorem atlas_continuousOn {F : Set M} (A : ImageAreaAtlas F) (i : ℕ)
    {s : Set E2} (hs : s ⊆ A.chartDomain i) : ContinuousOn (A.map i) s :=
  (A.c2 i).continuousOn.mono hs

private theorem atlas_hasMFDeriv {F : Set M} (A : ImageAreaAtlas F) (i : ℕ)
    {s : Set E2} (hs : s ⊆ A.chartDomain i) (x : E2) (hx : x ∈ s) :
    HasMFDerivWithinAt 𝓘(ℝ, E2) (𝓡∂ 3) (A.map i) s x
      (mfderivWithin 𝓘(ℝ, E2) (𝓡∂ 3) (A.map i) (A.chartDomain i) x) :=
  (((A.c2 i).mdifferentiableOn (by norm_num) x (hs hx)).hasMFDerivWithinAt).mono hs

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
/-- The native Gram density transforms with the absolute determinant on the
actual inverse transition between any two measurable embedded image pieces. -/
theorem paired_piece_integral {F : Set M} (g : SmoothMetric M) (A B : ImageAreaAtlas F)
    (i j : ℕ) {s t : Set E2} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsA : s ⊆ A.chartDomain i) (htB : t ⊆ B.chartDomain j)
    (heq : (A.map i) '' s = (B.map j) '' t) :
    (∫⁻ x in s, density g A i x) = ∫⁻ y in t, density g B j y := by
  let τ := (invFunOn (B.map j) t) ∘ (A.map i)
  obtain ⟨hτt, hτeq, hτc, hτinj, hτimage⟩ := embedded_transition
    (atlas_continuousOn A i hsA) (atlas_embedding_subset B j htB)
    ((atlas_injOn A i).mono hsA) heq
  have hτd : ∀ x ∈ s, DifferentiableWithinAt ℝ τ s x := by
    intro x hx
    exact differentiableWithinAt_transition (𝓡∂ 3) hx (hτc x hx) hτt hτeq
      (atlas_hasMFDeriv A i hsA x hx) (atlas_hasMFDeriv B j htB (τ x) (hτt hx))
      (B.immersion j (τ x) (htB (hτt hx)))
  let Df : E2 → E2 →L[ℝ] E3 := fun x =>
    mfderivWithin 𝓘(ℝ, E2) (𝓡∂ 3) (A.map i) (A.chartDomain i) x
  let Dg : E2 → E2 →L[ℝ] E3 := fun y =>
    mfderivWithin 𝓘(ℝ, E2) (𝓡∂ 3) (B.map j) (B.chartDomain j) y
  have hchain : ∀ᵐ x ∂volume.restrict s,
      Df x = (Dg (τ x)).comp (fderivWithin ℝ τ s x) :=
    ae_derivative_comp_transition (𝓡∂ 3) volume hs hτc hτt hτeq Df Dg
      (atlas_hasMFDeriv A i hsA) (atlas_hasMFDeriv B j htB)
      (fun y hy => B.immersion j y (htB hy))
  have hdensity : ∀ᵐ x ∂volume.restrict s,
      density g A i x = ENNReal.ofReal |(fderivWithin ℝ τ s x).det| * density g B j (τ x) := by
    filter_upwards [hchain, ae_restrict_mem hs] with x hchain hx
    have hp : B.map j (τ x) = A.map i x := hτeq hx
    letI : RiemannianBundle (fun p : M => TangentSpace (𝓡∂ 3) p) :=
      ⟨g.toRiemannianMetric⟩
    have hgram : A.gram g i x = Matrix.gram ℝ (fun k : Fin 2 =>
        (mfderivWithin 𝓘(ℝ, E2) (𝓡∂ 3) (B.map j) (B.chartDomain j) (τ x))
          ((fderivWithin ℝ τ s x) (coordinateVector 2 k))) := by
      ext k l
      change g.inner (A.map i x) ((Df x) (coordinateVector 2 k))
        ((Df x) (coordinateVector 2 l)) = _
      rw [hchain]
      simp only [ContinuousLinearMap.comp_apply]
      rw [← hp]
      rfl
    unfold density
    rw [hgram]
    have hreal := linearMapGramDensity_comp
      (mfderivWithin 𝓘(ℝ, E2) (𝓡∂ 3) (B.map j) (B.chartDomain j) (τ x)).toLinearMap
      (fderivWithin ℝ τ s x).toLinearMap
    change ENNReal.ofReal _ = _
    rw [show Real.sqrt (Matrix.det (Matrix.gram ℝ (fun k : Fin 2 =>
        (mfderivWithin 𝓘(ℝ, E2) (𝓡∂ 3) (B.map j) (B.chartDomain j) (τ x))
        ((fderivWithin ℝ τ s x) (coordinateVector 2 k))))) =
        |(fderivWithin ℝ τ s x).det| * Real.sqrt (Matrix.det (B.gram g j (τ x))) by
      exact hreal]
    exact ENNReal.ofReal_mul (abs_nonneg _)
  calc
    ∫⁻ x in s, density g A i x =
        ∫⁻ x in s, ENNReal.ofReal |(fderivWithin ℝ τ s x).det| * density g B j (τ x) :=
      lintegral_congr_ae hdensity
    _ = ∫⁻ y in t, density g B j y := by
      rw [← hτimage]
      exact (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
        (fun x hx => (hτd x hx).hasFDerivWithinAt) hτinj (density g B j)).symm

/-- Countable measurable native image atlases have equal extended area. -/
theorem image_area_chart_independence {F : Set M} (g : SmoothMetric M)
    (A B : ImageAreaAtlas F) (hA : A.Valid g) (hB : B.Valid g) :
    A.area g = B.area g := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  apply tsum_lintegral_common_refinement volume
    A.map B.map A.piece B.piece A.piece_measurable B.piece_measurable
    (fun i => atlas_continuousOn A i (A.subordinate i))
    (fun j => atlas_continuousOn B j (B.subordinate j))
    (fun i => (atlas_injOn A i).mono (A.subordinate i))
    (fun j => (atlas_injOn B j).mono (B.subordinate j))
    A.partition B.partition (A.covers.trans B.covers.symm)
    (density g A) (density g B)
  intro i j
  apply paired_piece_integral g A B i j
  · exact measurableSet_piece_preimage (A.piece_measurable i)
      ((B.piece_measurable j).image_of_continuousOn_injOn
        (atlas_continuousOn B j (B.subordinate j))
        ((atlas_injOn B j).mono (B.subordinate j)))
      (atlas_continuousOn A i (A.subordinate i))
  · exact measurableSet_piece_preimage (B.piece_measurable j)
      ((A.piece_measurable i).image_of_continuousOn_injOn
        (atlas_continuousOn A i (A.subordinate i))
        ((atlas_injOn A i).mono (A.subordinate i)))
      (atlas_continuousOn B j (B.subordinate j))
  · exact inter_subset_left.trans (A.subordinate i)
  · exact inter_subset_left.trans (B.subordinate j)
  · exact image_common_piece (A.map i) (B.map j) (A.piece i) (B.piece j)

end SeifertSurfaces.OriginalEndpoints.Section5.NativeAreaV487
