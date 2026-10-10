import Section5CommonLeafGeometryV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter MeasureTheory Bundle
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

theorem circle_clock_differential_injective (t : ℝ) :
    Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t) := by
  let V : ℂ := Complex.exp (t * Complex.I) * Complex.I
  have hV : V ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero
  have hd : HasDerivAt (fun r : ℝ => (Circle.exp r : ℂ)) V t := by
    simpa only [Circle.coe_exp, Complex.ofReal_one, one_mul, V, id_eq] using
      (((hasDerivAt_id t).ofReal_comp).mul_const Complex.I).cexp
  have hdf : Injective (fderiv ℝ (fun r : ℝ => (Circle.exp r : ℂ)) t) := by
    intro a b hab
    rw [hd.hasFDerivAt.fderiv] at hab
    simp only [ContinuousLinearMap.toSpanSingleton_apply] at hab
    have h : (a - b) • V = 0 := by rw [sub_smul, hab, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hV)
  have hmf : Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      (fun r : ℝ => (Circle.exp r : ℂ)) t) := by
    rw [mfderiv_eq_fderiv]
    exact (NormedSpace.fromTangentSpace (Circle.exp t : ℂ)).symm.injective.comp
      (hdf.comp (NormedSpace.fromTangentSpace t).injective)
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  have hCoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ)) :=
    contMDiff_coe_sphere
  change Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
    ((fun z : Circle => (z : ℂ)) ∘ Circle.exp) t) at hmf
  rw [mfderiv_comp t (hCoe.mdifferentiableAt (by simp))
    ((contMDiff_circleExp (m := ∞)).mdifferentiableAt (by simp))] at hmf
  exact Injective.of_comp hmf


def longitudeClock (J : LongitudeFoliation.{0} E) (a : Circle) (t : ℝ) : E.Carrier :=
  J.torus (a,Circle.exp t)

theorem longitude_clock_smooth (J : LongitudeFoliation.{0} E) (a : Circle) :
    ContMDiff 𝓘(ℝ) (𝓡∂ 3) ∞ (longitudeClock J a) :=
  (longitude_leaf_regular J a).1.comp contMDiff_circleExp

theorem longitude_clock_velocity_ne_zero (J : LongitudeFoliation.{0} E)
    (a : Circle) (t : ℝ) :
    mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeClock J a) t 1 ≠ 0 := by
  have he := longitude_leaf_regular J a
  have hi : Injective (mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeClock J a) t) := by
    change Injective (mfderiv 𝓘(ℝ) (𝓡∂ 3)
      ((fun z => J.torus (a,z)) ∘ Circle.exp) t)
    rw [mfderiv_comp t (he.1.mdifferentiableAt (by simp))
      ((contMDiff_circleExp (m := ∞)).mdifferentiableAt (by simp))]
    exact (he.2.2 _).comp
      (circle_clock_differential_injective t)
  intro hz
  have h10 := hi (hz.trans (map_zero _).symm)
  change (1 : ℝ) = 0 at h10
  exact one_ne_zero h10

def longitudeSpeed (g : SmoothMetric E.Carrier) (J : LongitudeFoliation.{0} E)
    (a : Circle) (t : ℝ) : ℝ :=
  Real.sqrt (g.inner (longitudeClock J a t)
    (mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeClock J a) t 1)
    (mfderiv 𝓘(ℝ) (𝓡∂ 3) (longitudeClock J a) t 1))

theorem longitude_speed_positive (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) (t : ℝ) :
    0 < longitudeSpeed g J a t :=
  Real.sqrt_pos.mpr (g.pos _ _ (longitude_clock_velocity_ne_zero J a t))

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem longitude_speed_continuous (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    Continuous (longitudeSpeed g J a) := by
  have ht := (longitude_clock_smooth J a).continuous_tangentMap (by simp)
  have hinput : Continuous (fun t : ℝ =>
      (⟨t,(1 : TangentSpace 𝓘(ℝ) t)⟩ : TangentBundle 𝓘(ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hv := ht.comp hinput
  letI : RiemannianBundle (fun p : E.Carrier => TangentSpace (𝓡∂ 3) p) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (Euc 3) (fun p : E.Carrier => TangentSpace (𝓡∂ 3) p) :=
    ⟨⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩⟩
  exact (hv.inner_bundle hv).sqrt

def longitudeLength (g : SmoothMetric E.Carrier) (J : LongitudeFoliation.{0} E)
    (a : Circle) : ℝ := ∫ t in (0 : ℝ)..(2*Real.pi), longitudeSpeed g J a t

theorem longitude_length_positive (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) : 0 < longitudeLength g J a := by
  unfold longitudeLength
  apply intervalIntegral.integral_pos (by positivity)
    (longitude_speed_continuous g J a).continuousOn
  · intro t ht
    exact (longitude_speed_positive g J a t).le
  · exact ⟨0,⟨le_rfl,by positivity⟩,longitude_speed_positive g J a 0⟩

#print axioms longitude_length_positive
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
