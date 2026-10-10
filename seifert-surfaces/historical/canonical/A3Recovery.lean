import A3MetricPDE
import AppendixAInteriorRegularity
import A3RecoveryGeometryBridges

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u v
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N]
variable {h : AmbientMetric N} {M : Set N} {D : A3OriginalData.{u,v} h M}

/-- The canonical interior regularity theorem applied to the fixed actual
metric operator. Its inputs must be proved by the preceding construction. -/
theorem A3_same_graph_smooth (G : A3SharedGraph D) :
    ContDiffOn ℝ ∞ G.height G.disc := by
  obtain ⟨C⟩ := A3_actual_metric_operator_control G
  have hC1 : ContDiffOn ℝ 1 G.height G.disc := G.height_C1.mono (by
    intro x hx
    have hx' : dist x 0 < G.radius := hx
    change dist x 0 ≤ 2 * G.radius
    linarith [G.radius_pos])
  exact smooth_of_C1_weak_uniformlyElliptic G.disc Metric.isOpen_ball
    C.jetDomain C.jetDomain_open (G.operator C) C.elliptic G.height hC1
    C.attained (A3_actual_metric_weak_equation G)

/-- The weak equation for a now-smooth graph is the pointwise equation,
including the former interface. -/
theorem A3_same_graph_classical (G : A3SharedGraph D) :
    ∀ x ∈ G.disc, G.classicalResidual x = 0 := by
  classical
  obtain ⟨C⟩ := A3_actual_metric_operator_control G
  let Ω := G.disc
  have hΩ : IsOpen Ω := Metric.isOpen_ball
  let J := C.jetDomain
  have hJ : IsOpen J := C.jetDomain_open
  let Q := G.operator C
  let u := G.height
  have hC2 : ContDiffOn ℝ 2 u Ω := (A3_same_graph_smooth G).of_le (by simp)
  have hjets : ∀ x ∈ Ω, SeifertSurfaces.QuasilinearLocalization.firstJet u x ∈ J := C.attained
  have hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u :=
    A3_actual_metric_weak_equation G
  let A : E2 → E2 := fun x => Q.flux (SeifertSurfaces.QuasilinearLocalization.firstJet u x)
  let b : E2 → ℝ := fun x => Q.lowerOrder (SeifertSurfaces.QuasilinearLocalization.firstJet u x)
  have hdu : ContDiffOn ℝ 1 (fderiv ℝ u) Ω := hC2.fderiv_of_isOpen hΩ (by norm_num)
  have hgrad : ContDiffOn ℝ 1 (planarGradient u) Ω := by
    unfold planarGradient
    exact ContDiffOn.sum (fun i _ => (hdu.clm_apply contDiffOn_const).smul_const _)
  have hjet : ContDiffOn ℝ 1 (SeifertSurfaces.QuasilinearLocalization.firstJet u) Ω :=
    contDiffOn_id.prodMk ((hC2.of_le (by norm_num)).prodMk hgrad)
  have hA : ContDiffOn ℝ 1 A Ω :=
    (Q.flux_smooth.of_le (by simp)).comp hjet hjets
  have hb : ContinuousOn b Ω := Q.lowerOrder_smooth.continuousOn.comp hjet.continuousOn hjets
  have hAi (i : Fin 2) : ContDiffOn ℝ 1 (fun x => A x i) Ω := by
    simpa only [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using
      (EuclideanSpace.proj i).contDiff.contDiffOn.comp hA (mapsTo_univ _ _)
  let d (i : Fin 2) (x : E2) : ℝ := fderiv ℝ (fun y => A y i) x (coordinateVector 2 i)
  let div (x : E2) : ℝ := ∑ i : Fin 2, d i x
  have hd (i : Fin 2) : ContinuousOn (d i) Ω :=
    ((hAi i).continuousOn_fderiv_of_isOpen hΩ (by norm_num)).clm_apply continuousOn_const
  have hdiv : ContinuousOn div Ω := continuousOn_finsetSum _ (fun i _ => hd i)
  have heq : ∀ x ∈ Ω, div x + b x = 0 := by
    have hae : (fun x => div x + b x) =ᵐ[volume.restrict Ω] 0 := by
      change ∀ᵐ x ∂(volume.restrict Ω), div x + b x = 0
      rw [ae_restrict_iff' hΩ.measurableSet]
      apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        ((hdiv.add hb).locallyIntegrableOn hΩ.measurableSet)
      intro φ hφ hsupp hsub
      have hdint (i : Fin 2) : IntegrableOn (fun x => d i x * φ x) Ω :=
        (SeifertSurfaces.QuasilinearLocalization.Helpers.continuousOn_supported_integrable Ω (tsupport φ) _ hsupp hsub
          ((hd i).mul hφ.continuous.continuousOn) (SeifertSurfaces.QuasilinearLocalization.Helpers.mul_test_support_subset _ φ)).integrableOn
      have hφgrad (i : Fin 2) : Continuous (fun x => planarGradient φ x i) := by
        simpa only [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using
          (EuclideanSpace.proj i).continuous.comp (SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_continuous φ hφ)
      have hfluxint (i : Fin 2) : IntegrableOn
          (fun x => A x i * planarGradient φ x i) Ω := by
        apply Integrable.integrableOn
        apply SeifertSurfaces.QuasilinearLocalization.Helpers.continuousOn_supported_integrable Ω (tsupport φ) _ hsupp hsub
          ((hAi i).continuousOn.mul
            (hφgrad i).continuousOn)
        intro x hx
        apply (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i))
        apply subset_tsupport
        simpa only [Function.mem_support, SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_apply] using (mul_ne_zero_iff.mp hx).2
      have hbint : IntegrableOn (fun x => b x * φ x) Ω :=
        (SeifertSurfaces.QuasilinearLocalization.Helpers.continuousOn_supported_integrable Ω (tsupport φ) _ hsupp hsub
          (hb.mul hφ.continuous.continuousOn) (SeifertSurfaces.QuasilinearLocalization.Helpers.mul_test_support_subset _ φ)).integrableOn
      have hip (i : Fin 2) : (∫ x in Ω, A x i * planarGradient φ x i) =
          -(∫ x in Ω, d i x * φ x) := by
        simpa only [SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_apply, coordinateVector, d] using
          (SeifertSurfaces.QuasilinearProviderBridge.Helpers.C1_hasWeakGrad Ω hΩ
            (fun x => A x i) (hAi i) i φ hφ hsupp hsub)
      have hweakφ := hweak φ hφ hsupp hsub
      change (∫ x in Ω, inner ℝ (A x) (planarGradient φ x) - b x * φ x) = 0 at hweakφ
      have hinner : (fun x => inner ℝ (A x) (planarGradient φ x)) =
          (fun x => ∑ i : Fin 2, A x i * planarGradient φ x i) := by
        funext x
        simp [PiLp.inner_apply, mul_comm]
      have hinnerPt (x : E2) := congrFun hinner x
      simp_rw [hinnerPt] at hweakφ
      rw [integral_sub (integrable_finsetSum _ (fun i _ => hfluxint i)) hbint,
        integral_finsetSum _ (fun i _ => hfluxint i)] at hweakφ
      simp_rw [hip] at hweakφ
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω) (fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h))])]
      simp only [smul_eq_mul]
      have hfun : (fun x => φ x * (div x + b x)) =
          (fun x => (∑ i : Fin 2, d i x * φ x) + b x * φ x) := by
        funext x
        simp only [div, Fin.sum_univ_two]
        ring
      change (∫ x in Ω, φ x * (div x + b x)) = 0
      rw [hfun, integral_add (integrable_finsetSum _ (fun i _ => hdint i)) hbint,
        integral_finsetSum _ (fun i _ => hdint i)]
      simp only [Fin.sum_univ_two] at hweakφ ⊢
      linarith
    exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae hΩ (hdiv.add hb) continuousOn_const
  exact heq

/-- Euler--Lagrange to vanishing normal mean curvature in the actual chart. -/
theorem A3_same_graph_coordinate_minimal (G : A3SharedGraph D) :
    IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap (G.coordinates.chart (D.edge D.pointParameter))
        G.plane G.normal G.height) G.disc := by
  obtain ⟨C⟩ := A3_actual_metric_operator_control G
  refine ⟨?_, ?_⟩
  · exact (contDiffOn_const.add G.plane.contDiff.contDiffOn).add
      ((A3_same_graph_smooth G).smul_const G.normal)
  · exact A3RecoveryGeometryBridges.actual_area_residual_implies_covariant_trace_tangent
      G C (A3_same_graph_smooth G) (A3_same_graph_classical G)

/-- Smoothness and differential injectivity of the original shared chart
parametrization: constant/singular maps cannot discharge this obligation. -/
theorem A3_same_graph_smooth_immersion (G : A3SharedGraph D) :
    ContMDiffOn 𝓘(ℝ, E2) 𝓘(ℝ, E3) ∞ G.parameter G.disc ∧
    (∀ x ∈ G.disc, Function.Injective
      (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) G.parameter x)) := by
  let f := graphMap (G.coordinates.chart (D.edge D.pointParameter))
    G.plane G.normal G.height
  have hf : ContDiffOn ℝ ∞ f G.disc :=
    (contDiffOn_const.add G.plane.contDiff.contDiffOn).add
      ((A3_same_graph_smooth G).smul_const G.normal)
  have hsub : G.disc ⊆ Metric.closedBall 0 (2 * G.radius) := by
    intro x hx
    have hx' : dist x 0 < G.radius := hx
    change dist x 0 ≤ 2 * G.radius
    linarith [G.radius_pos]
  have hmap : MapsTo f G.disc G.coordinates.chart.target := G.graph_in_chart.mono hsub (Set.Subset.refl _)
  have he : G.coordinates.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
    ⟨G.coordinates.smooth.mdifferentiableOn (by simp),
      G.coordinates.inverse_smooth.mdifferentiableOn (by simp)⟩
  refine ⟨G.coordinates.inverse_smooth.comp hf.contMDiffOn hmap, ?_⟩
  intro x hx
  have hdx := (A3_same_graph_smooth G).contDiffAt (Metric.isOpen_ball.mem_nhds hx)
  have hw : DifferentiableAt ℝ G.height x := hdx.differentiableAt (by simp)
  have hfd : HasFDerivAt f (G.plane + (fderiv ℝ G.height x).smulRight G.normal) x := by
    convert ((hasFDerivAt_const _ x).add G.plane.hasFDerivAt).add
      (hw.hasFDerivAt.smul_const G.normal) using 1 <;> first | rfl | simp only [zero_add]
  have hlin : Function.Injective (fderiv ℝ f x) := by
    rw [hfd.fderiv]
    intro v w hvw
    have hpair : (v, fderiv ℝ G.height x v) = (w, fderiv ℝ G.height x w) :=
      G.splitting.1 hvw
    exact congrArg Prod.fst hpair
  have hm : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E3) f x := hfd.differentiableAt.mdifferentiableAt
  change Function.Injective (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) (G.coordinates.chart.symm ∘ f) x)
  rw [mfderiv_comp x (he.mdifferentiableAt_symm (hmap hx)) hm]
  apply (he.symm.mfderiv_injective (hmap hx)).comp
  rw [mfderiv_eq_fderiv]
  exact (NormedSpace.fromTangentSpace (f x)).symm.injective.comp
    (hlin.comp (NormedSpace.fromTangentSpace x).injective)

/-- Chart invariance of minimality, quantified over every actual ambient chart
as required by the protected IsMinimalPatch definition. -/
theorem A3_same_graph_all_chart_minimality (G : A3SharedGraph D) :
    ∀ c : SmoothAmbientChart N,
      IsMinimalParametrizationOn (actualChartTensor h c) (c.chart ∘ G.parameter)
        (G.disc ∩ G.parameter ⁻¹' c.chart.source) := by
  exact A3RecoveryGeometryBridges.same_graph_minimality_in_every_actual_chart G
    (A3_same_graph_coordinate_minimal G) (A3_same_graph_smooth_immersion G)

/-- Recovery of a smooth minimal embedded surface, using the same chart,
metric, graph and disc. -/
theorem A3_same_graph_minimal_embedding (G : A3SharedGraph D) :
    IsEmbedding (fun x : G.disc => G.parameter x) ∧
    IsMinimalPatch h G.parameter G.disc := by
  let f := graphMap (G.coordinates.chart (D.edge D.pointParameter))
    G.plane G.normal G.height
  let L : (E2 × ℝ) →L[ℝ] E3 :=
    G.plane.comp (ContinuousLinearMap.fst ℝ E2 ℝ) +
      (ContinuousLinearMap.snd ℝ E2 ℝ).smulRight G.normal
  have hL : Function.Bijective L := G.splitting
  let e : (E2 × ℝ) ≃L[ℝ] E3 := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hL.1) (LinearMap.range_eq_top.mpr hL.2)
  let q : E3 → E2 := fun y => (e.symm (y - G.coordinates.chart (D.edge D.pointParameter))).1
  have hq : Continuous q := continuous_fst.comp
    (e.symm.continuous.comp (continuous_id.sub continuous_const))
  have hqf : ∀ x : G.disc, q (f x) = x := by
    intro x
    have he : f x - G.coordinates.chart (D.edge D.pointParameter) = e (x, G.height x) := by
      change G.coordinates.chart (D.edge D.pointParameter) + G.plane x +
        G.height x • G.normal - G.coordinates.chart (D.edge D.pointParameter) =
        G.plane x + G.height x • G.normal
      abel
    change (e.symm (f x - G.coordinates.chart (D.edge D.pointParameter))).1 = x
    rw [he, e.symm_apply_apply]
  have hsub : G.disc ⊆ Metric.closedBall 0 (2 * G.radius) := by
    intro x hx
    have hx' : dist x 0 < G.radius := hx
    change dist x 0 ≤ 2 * G.radius
    linarith [G.radius_pos]
  have hf : ContinuousOn f G.disc :=
    (continuousOn_const.add G.plane.continuous.continuousOn).add
      ((G.height_C1.mono hsub).continuousOn.smul continuousOn_const)
  have hfr : Continuous (fun x : G.disc => f x) :=
    hf.comp_continuous continuous_subtype_val (fun x => x.property)
  have hfemb : IsEmbedding (fun x : G.disc => f x) := by
    apply IsEmbedding.of_comp hfr hq
    have heq : q ∘ (fun x : G.disc => f x) = Subtype.val := funext hqf
    rw [heq]
    exact IsEmbedding.subtypeVal
  have hmap : MapsTo f G.disc G.coordinates.chart.target :=
    G.graph_in_chart.mono hsub (Set.Subset.refl _)
  have hsrc : ∀ x : G.disc, G.parameter x ∈ G.coordinates.chart.source :=
    fun x => G.coordinates.chart.symm.map_source (hmap x.property)
  let r : G.disc → G.coordinates.chart.source := fun x => ⟨G.parameter x, hsrc x⟩
  have hr : Continuous r :=
    (G.coordinates.chart.symm.continuousOn.comp_continuous hfr
      (fun x => hmap x.property)).subtype_mk hsrc
  have hremb : IsEmbedding r := by
    apply IsEmbedding.of_comp hr G.coordinates.chart.isEmbedding_restrict.continuous
    have heq : (fun y : G.coordinates.chart.source => G.coordinates.chart y) ∘ r =
        (fun x : G.disc => f x) := by
      funext x
      exact G.coordinates.chart.right_inv (hmap x.property)
    change IsEmbedding ((fun y : G.coordinates.chart.source => G.coordinates.chart y) ∘ r)
    rw [heq]
    exact hfemb
  refine ⟨IsEmbedding.subtypeVal.comp hremb, ?_⟩
  exact ⟨(A3_same_graph_smooth_immersion G).1, (A3_same_graph_smooth_immersion G).2,
    A3_same_graph_all_chart_minimality G⟩

/-- Exact original union and original basepoint; no replacement sheet or
neighborhood is permitted. -/
theorem A3_same_graph_exact_original_union (G : A3SharedGraph D) :
    G.parameter 0 = D.edge D.pointParameter ∧
    G.parameter '' G.disc = (D.sheetOne.image ∪ D.sheetTwo.image) ∩ G.neighborhood := by
  constructor
  · simp only [A3SharedGraph.parameter, Function.comp_apply, graphMap,
      map_zero, G.height_zero, zero_smul, add_zero]
    exact G.coordinates.chart.left_inv G.point_in_chart
  · change G.parameter '' G.disc = _
    rw [A3SharedGraph.disc, ← G.sides_cover, Set.image_union]
    exact (congrArg₂ (· ∪ ·) G.sheetOne_exact G.sheetTwo_exact).trans
      (by ext x; simp only [Set.mem_union, Set.mem_inter_iff]; tauto)

end SeifertSurfaces.OriginalEndpoints
