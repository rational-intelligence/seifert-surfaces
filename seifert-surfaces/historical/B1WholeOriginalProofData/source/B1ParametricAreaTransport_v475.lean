import B1ActualAreaLocalization_v475
import B1MetricGramTransport_v475

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.MetricFoundations.AreaAnalysis
open Bundle
open scoped Bundle
universe u v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Literal Gram density of a smooth Euclidean parametrization into the
original metric manifold. -/
def native_parametric_density_v475 (g : SmoothMetric M) (Γ : Euc 2 → M) (x : Euc 2) : ℝ :=
  Real.sqrt (Matrix.det (fun i j : Fin 2 =>
    g.inner (Γ x)
      (mfderiv 𝓘(ℝ,Euc 2) (𝓡∂ 3) Γ x
        ((NormedSpace.fromTangentSpace x).symm (EuclideanSpace.single i 1)))
      (mfderiv 𝓘(ℝ,Euc 2) (𝓡∂ 3) Γ x
        ((NormedSpace.fromTangentSpace x).symm (EuclideanSpace.single j 1)))))

/-- The area density changes by the absolute Jacobian under a supplied smooth
Euclidean source parameter, in the actual metric and actual surface chart. -/
theorem native_parameter_coordinate_density_v475
    (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (F : S → M) (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F)
    (p : S) (c : Euc 2 → Euc 2) (O : Set (Euc 2)) (hO : IsOpen O)
    (hc : ContDiffOn ℝ ∞ c O) (hct : MapsTo c O (interior (surfaceChart p).target))
    (x : Euc 2) (hx : x ∈ O) :
    native_parametric_density_v475 g ((F ∘ (surfaceChart p).symm) ∘ c) x =
      |(fderiv ℝ c x).det| * coordinateAreaDensity g F p (c x) := by
  letI : Bundle.RiemannianBundle (fun z : M => TangentSpace (𝓡∂ 3) z) := ⟨g.toRiemannianMetric⟩
  have hc' : MDifferentiableAt 𝓘(ℝ,Euc 2) 𝓘(ℝ,Euc 2) c x :=
    ((hc.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)).mdifferentiableAt
  have ht : (surfaceChart p).target ∈ 𝓝 (c x) := mem_interior_iff_mem_nhds.mp (hct hx)
  have hf : MDifferentiableAt 𝓘(ℝ,Euc 2) (𝓡∂ 3) (F ∘ (surfaceChart p).symm) (c x) :=
    ((hF.comp_contMDiffOn (contMDiffOn_extChartAt_symm p)).contMDiffAt ht).mdifferentiableAt (by simp)
  have hd := mfderiv_comp x hf hc'
  have hwithin := mfderivWithin_of_mem_nhds (I := 𝓘(ℝ,Euc 2)) (I' := 𝓡∂ 3)
    (f := F ∘ (surfaceChart p).symm) ht
  rw [mfderiv_eq_fderiv] at hd
  have heval (w : Euc 2) :
      mfderiv 𝓘(ℝ,Euc 2) (𝓡∂ 3) ((F ∘ (surfaceChart p).symm) ∘ c) x
        ((NormedSpace.fromTangentSpace x).symm w) =
      coordinateDifferential F p (c x) (fderiv ℝ c x w) := by
    rw [hd]
    change mfderiv 𝓘(ℝ,Euc 2) (𝓡∂ 3) (F ∘ (surfaceChart p).symm) (c x)
      ((NormedSpace.fromTangentSpace (c x)).symm (fderiv ℝ c x w)) = _
    unfold coordinateDifferential
    rw [hwithin]
    rfl
  unfold native_parametric_density_v475
  simp only [heval]
  have hgramcomp := metric_gram_density_comp_v475
    (B := fun v w => g.inner (((F ∘ (surfaceChart p).symm) ∘ c) x) v w)
    (d := coordinateDifferential F p (c x))
    (A := (fderiv ℝ c x).toLinearMap)
    (by intro a b z; simp only [map_add, ContinuousLinearMap.add_apply])
    (by intro a b z; simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul])
    (by intro a b z; simp only [map_add])
    (by intro a b z; simp only [map_smul, smul_eq_mul])
  have hcoord : coordinateAreaDensity g F p (c x) = Real.sqrt (Matrix.det
      (fun i j : Fin 2 => g.inner (F ((surfaceChart p).symm (c x)))
        (coordinateDifferential F p (c x) (EuclideanSpace.single i 1))
        (coordinateDifferential F p (c x) (EuclideanSpace.single j 1)))) := rfl
  rw [hcoord]
  simpa only [AppendixACoordinates.coordinateVector, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, Function.comp_apply] using hgramcomp

/-- Actual surface-chart integration expressed in an arbitrary smooth
injective Euclidean source parameter. No orientation choice is introduced. -/
theorem native_parameter_coordinate_integral_v475
    (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (F : S → M) (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F)
    (p : S) (c : Euc 2 → Euc 2) (O A : Set (Euc 2))
    (hO : IsOpen O) (hA : MeasurableSet A) (hAO : A ⊆ O)
    (hc : ContDiffOn ℝ ∞ c O) (hct : MapsTo c O (interior (surfaceChart p).target))
    (hinj : InjOn c A) :
    (∫ y in c '' A, coordinateAreaDensity g F p y) =
      ∫ x in A, native_parametric_density_v475 g ((F ∘ (surfaceChart p).symm) ∘ c) x := by
  have hderiv : ∀ x ∈ A, HasFDerivWithinAt c (fderiv ℝ c x) A x := by
    intro x hx
    exact ((hc.contDiffAt (hO.mem_nhds (hAO hx))).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hA hderiv hinj]
  apply setIntegral_congr_fun hA
  intro x hx
  exact (native_parameter_coordinate_density_v475 g F hF p c O hO hc hct x (hAO hx)).symm

#print axioms native_parameter_coordinate_density_v475
#print axioms native_parameter_coordinate_integral_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
