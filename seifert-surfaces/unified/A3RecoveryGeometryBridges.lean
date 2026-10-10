import A3MetricPDE
import A3FirstVariationIdentity

set_option autoImplicit false
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace SeifertSurfaces.OriginalEndpoints.A3RecoveryGeometryBridges
open SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

universe u v
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N]
variable {h : AmbientMetric N} {M : Set N} {D : A3OriginalData.{u,v} h M}

/-- The actual area Euler--Lagrange equation of the fixed smooth shared graph
implies tangency of its metric covariant trace. The operator control refers to
the same attained jets and positive Gram determinants as the equation. -/
theorem actual_area_residual_implies_covariant_trace_tangent
    (G : A3SharedGraph D) (C : G.OperatorControl)
    (hsmooth : ContDiffOn ℝ ∞ G.height G.disc)
    (hclassical : ∀ x ∈ G.disc, G.classicalResidual x = 0) :
    ∀ x ∈ G.disc,
      tracedAcceleration (actualChartTensor h G.coordinates)
        (graphMap (G.coordinates.chart (D.edge D.pointParameter))
          G.plane G.normal G.height) x ∈
      LinearMap.range
        (fderiv ℝ (graphMap (G.coordinates.chart (D.edge D.pointParameter))
          G.plane G.normal G.height) x).toLinearMap := by
  classical
  let f := graphMap (G.coordinates.chart (D.edge D.pointParameter))
    G.plane G.normal G.height
  have hf : ContDiffOn ℝ ∞ f G.disc :=
    (contDiffOn_const.add G.plane.contDiff.contDiffOn).add (hsmooth.smul_const G.normal)
  intro x hx
  have hw : DifferentiableAt ℝ G.height x :=
    (hsmooth.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
  have hfd : HasFDerivAt f (G.plane + (fderiv ℝ G.height x).smulRight G.normal) x := by
    convert ((hasFDerivAt_const _ x).add G.plane.hasFDerivAt).add
      (hw.hasFDerivAt.smul_const G.normal) using 1 <;> first | rfl | simp only [zero_add]
  have htangent (i : Fin 2) : graphTangent f x i =
      G.jetTangent (planarGradient G.height x) i := by
    simp only [graphTangent, hfd.fderiv, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, A3SharedGraph.jetTangent,
      A3SharedGraph.attainedJet]
    have hgrad : planarGradient G.height x i = fderiv ℝ G.height x (coordinateVector 2 i) := by
      fin_cases i <;> simp [planarGradient, coordinateVector, PiLp.single_apply]
    rw [hgrad]
  have hmetric : inducedMetric (actualChartTensor h G.coordinates) f x =
      G.jetMetric (G.attainedJet x) := by
    ext i j
    simp only [inducedMetric, htangent, A3SharedGraph.jetMetric, A3SharedGraph.attainedJet,
      A3SharedGraph.jetPoint]
    rfl
  have hdet : 0 < Matrix.det (inducedMetric (actualChartTensor h G.coordinates) f x) := by
    rw [hmetric]
    exact C.positiveGram _ (C.attained x hx)
  let L : (E2 × ℝ) →L[ℝ] E3 :=
    G.plane.comp (ContinuousLinearMap.fst ℝ E2 ℝ) +
      (ContinuousLinearMap.snd ℝ E2 ℝ).smulRight G.normal
  have hL : Function.Bijective L := G.splitting
  let e : (E2 × ℝ) ≃L[ℝ] E3 := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hL.1) (LinearMap.range_eq_top.mpr hL.2)
  let π : E3 →L[ℝ] E2 := (ContinuousLinearMap.fst ℝ E2 ℝ).comp e.symm.toContinuousLinearMap
  let τ : E3 →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ E2 ℝ).comp e.symm.toContinuousLinearMap
  let q : E3 →L[ℝ] ℝ := τ - (fderiv ℝ G.height x).comp π
  have heval (v : E2) (z : ℝ) : e (v,z) = G.plane v + z • G.normal := rfl
  have hinverse (v : E2) (z : ℝ) : e.symm (G.plane v + z • G.normal) = (v,z) := by
    rw [← heval, e.symm_apply_apply]
  have hdecomp (v : E3) : v = G.plane (π v) + τ v • G.normal := by
    change v = e (e.symm v)
    exact (e.apply_symm_apply v).symm
  have hrange (v : E3) : v ∈ LinearMap.range (fderiv ℝ f x).toLinearMap ↔ q v = 0 := by
    rw [hfd.fderiv]
    constructor
    · rintro ⟨w, rfl⟩
      change (e.symm (G.plane w + fderiv ℝ G.height x w • G.normal)).2 -
        fderiv ℝ G.height x (e.symm (G.plane w + fderiv ℝ G.height x w • G.normal)).1 = 0
      rw [hinverse]
      exact sub_self _
    · intro hv
      refine ⟨π v, ?_⟩
      change G.plane (π v) + fderiv ℝ G.height x (π v) • G.normal = v
      have hτ : τ v = fderiv ℝ G.height x (π v) := sub_eq_zero.mp hv
      rw [← hτ]
      exact (hdecomp v).symm
  apply (hrange _).mpr
  have hc := hclassical x hx
  let p := planarGradient G.height x
  let y := f x
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    ∑ a : Fin 3, ∑ b : Fin 3,
      actualChartTensor h G.coordinates y a b •
        (PiLp.proj 2 (fun _ : Fin 3 => ℝ) a).smulRight
          (PiLp.proj 2 (fun _ : Fin 3 => ℝ) b)
  have hinner (v w : E3) :
      coordinateInner (actualChartTensor h G.coordinates) y v w = B v w := by
    simp only [B, coordinateInner, sum_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, smul_eq_mul, mul_assoc]
  let P (i : Fin 2) : E2 →L[ℝ] E3 :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i).smulRight G.normal
  have hTi (i : Fin 2) : HasFDerivAt (fun z => G.jetTangent z i) (P i) p := by
    convert (hasFDerivAt_const (G.plane (coordinateVector 2 i)) p).add (P i).hasFDerivAt using 1
    · rfl
    · simp only [zero_add]
  have hA (i k : Fin 2) : HasFDerivAt
      (fun z => G.jetMetric (x, G.height x, z) i k)
      ((B (G.jetTangent p i)).comp (P k) +
        (B.comp (P i)).flip (G.jetTangent p k)) p := by
    convert (B.hasFDerivAt.comp p (hTi i)).clm_apply (hTi k) using 1
    · funext z
      exact hinner _ _
    · rfl
  let A : Matrix (Fin 2) (Fin 2) ℝ := G.jetMetric (G.attainedJet x)
  have hAdet : HasFDerivAt (fun z => Matrix.det (G.jetMetric (x, G.height x, z)))
      (G.jetMetric (x, G.height x, p) 0 0 •
        ((B (G.jetTangent p 1)).comp (P 1) + (B.comp (P 1)).flip (G.jetTangent p 1)) +
      G.jetMetric (x, G.height x, p) 1 1 •
        ((B (G.jetTangent p 0)).comp (P 0) + (B.comp (P 0)).flip (G.jetTangent p 0)) -
      (G.jetMetric (x, G.height x, p) 0 1 •
        ((B (G.jetTangent p 1)).comp (P 0) + (B.comp (P 1)).flip (G.jetTangent p 0)) +
      G.jetMetric (x, G.height x, p) 1 0 •
        ((B (G.jetTangent p 0)).comp (P 1) + (B.comp (P 0)).flip (G.jetTangent p 1)))) p := by
    convert ((hA 0 0).mul (hA 1 1)).sub ((hA 0 1).mul (hA 1 0)) using 1
    funext z
    exact Matrix.det_fin_two _
  have hpos : 0 < Matrix.det (G.jetMetric (x, G.height x, p)) :=
    C.positiveGram _ (C.attained x hx)
  have hF := hAdet.sqrt hpos.ne'
  have hBsym (v w : E3) : B v w = B w v := by
    rw [← hinner, ← hinner]
    unfold coordinateInner
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [show actualChartTensor h G.coordinates y b a =
      actualChartTensor h G.coordinates y a b from h.symm _ _ _]
    ring
  have hAsym : A 0 1 = A 1 0 := by
    change coordinateInner (actualChartTensor h G.coordinates) y (G.jetTangent p 0)
      (G.jetTangent p 1) = coordinateInner (actualChartTensor h G.coordinates) y
        (G.jetTangent p 1) (G.jetTangent p 0)
    rw [hinner, hinner, hBsym]
  have hflux0 : G.metricFlux (G.attainedJet x) 0 =
      (A 1 1 * B G.normal (G.jetTangent p 0) -
        A 0 1 * B G.normal (G.jetTangent p 1)) / Real.sqrt A.det := by
    change planarGradient (fun z => G.areaDensity (x, G.height x, z)) p 0 = _
    have hgradient : planarGradient (fun z => G.areaDensity (x, G.height x, z)) p 0 =
        fderiv ℝ (fun z => G.areaDensity (x, G.height x, z)) p (coordinateVector 2 0) := by
      simp [planarGradient, coordinateVector]
    rw [hgradient]
    simp only [A3SharedGraph.areaDensity]
    rw [hF.fderiv]
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    simp only [P, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply,
      coordinateVector, EuclideanSpace.single, PiLp.single_apply]
    norm_num only [Fin.reduceEq, ite_true, ite_false, zero_smul, one_smul, map_zero,
      mul_zero, zero_add, add_zero, zero_apply]
    change 1 / (2 * Real.sqrt A.det) *
      (A 1 1 * (B (G.jetTangent p 0) G.normal + B G.normal (G.jetTangent p 0)) -
        (A 0 1 * B (G.jetTangent p 1) G.normal +
          A 1 0 * B G.normal (G.jetTangent p 1))) = _
    rw [hBsym (G.jetTangent p 0) G.normal, hBsym (G.jetTangent p 1) G.normal, ← hAsym]
    have hroot : Real.sqrt A.det ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    field_simp [hroot]
    <;> ring
  have hflux1 : G.metricFlux (G.attainedJet x) 1 =
      (A 0 0 * B G.normal (G.jetTangent p 1) -
        A 0 1 * B G.normal (G.jetTangent p 0)) / Real.sqrt A.det := by
    change planarGradient (fun z => G.areaDensity (x, G.height x, z)) p 1 = _
    have hgradient : planarGradient (fun z => G.areaDensity (x, G.height x, z)) p 1 =
        fderiv ℝ (fun z => G.areaDensity (x, G.height x, z)) p (coordinateVector 2 1) := by
      simp [planarGradient, coordinateVector]
    rw [hgradient]
    simp only [A3SharedGraph.areaDensity]
    rw [hF.fderiv]
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    simp only [P, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply,
      coordinateVector, EuclideanSpace.single, PiLp.single_apply]
    norm_num only [Fin.reduceEq, ite_true, ite_false, zero_smul, one_smul, map_zero,
      mul_zero, zero_add, add_zero, zero_apply]
    change 1 / (2 * Real.sqrt A.det) *
      (A 0 0 * (B (G.jetTangent p 1) G.normal + B G.normal (G.jetTangent p 1)) -
        (A 0 1 * B G.normal (G.jetTangent p 0) +
          A 1 0 * B (G.jetTangent p 0) G.normal)) = _
    rw [hBsym (G.jetTangent p 1) G.normal, hBsym (G.jetTangent p 0) G.normal, ← hAsym]
    have hroot : Real.sqrt A.det ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    field_simp [hroot]
    <;> ring
  have hprops
      (h : AmbientMetric N) (c : SmoothAmbientChart N) :
      (∀ a b, ContDiffOn ℝ ∞ (fun y => actualChartTensor h c y a b) c.chart.target) ∧
      (∀ y ∈ c.chart.target, ∀ a b,
        actualChartTensor h c y a b = actualChartTensor h c y b a) ∧
      (∀ y ∈ c.chart.target, ∀ v : E3, v ≠ 0 →
        0 < coordinateInner (actualChartTensor h c) y v v) := by
    classical
    have hchartMD : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
      ⟨c.smooth.mdifferentiableOn (by simp),
        c.inverse_smooth.mdifferentiableOn (by simp)⟩
    have hvector (v : E3) :
        ContMDiffOn 𝓘(ℝ, E3) (𝓘(ℝ, E3).tangent) ∞
          (fun y => Bundle.TotalSpace.mk' E3 (c.chart.symm y)
            (inverseChartDifferential c y v)) c.chart.target := by
      have hconst : ContMDiff 𝓘(ℝ, E3) (𝓘(ℝ, E3).tangent) ∞
          (fun y : E3 => Bundle.TotalSpace.mk' E3 y
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v)) := by
        apply (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (E := E3)
          (V := fun y => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v)).mpr
        change ContDiff ℝ ∞ (fun _ : E3 => v)
        exact contDiff_const
      have htm := c.inverse_smooth.contMDiffOn_tangentMapWithin
        (m := ∞) (by simp) c.chart.open_target.uniqueMDiffOn
      have hv := htm.comp (f := fun y : E3 => Bundle.TotalSpace.mk' E3 y
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v))
        hconst.contMDiffOn (s := c.chart.target) (by
        intro y hy
        exact hy)
      apply hv.congr
      intro y hy
      have hd := mfderivWithin_eq_mfderiv
        (c.chart.open_target.uniqueMDiffOn y hy)
        ((c.inverse_smooth.contMDiffAt (c.chart.open_target.mem_nhds hy)).mdifferentiableAt
          (by simp))
      change Bundle.TotalSpace.mk' E3 (c.chart.symm y)
          ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm y)
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v)) =
        Bundle.TotalSpace.mk' E3 (c.chart.symm y)
          ((mfderivWithin 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm c.chart.target y)
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v))
      rw [hd]
    refine ⟨?_, ?_, ?_⟩
    · intro a b y hy
      have hh : ContMDiffWithinAt 𝓘(ℝ, E3) (𝓘(ℝ, E3).prod 𝓘(ℝ)) ∞
          (fun y => Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial N ℝ) (c.chart.symm y)
            (actualChartTensor h c y a b)) c.chart.target y := by
        apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := E3) (F₂ := E3)
        · exact h.contMDiff.contMDiffAt.comp_contMDiffWithinAt y (c.inverse_smooth y hy)
        · exact hvector (coordinateVector 3 a) y hy
        · exact hvector (coordinateVector 3 b) y hy
      exact (Bundle.contMDiffWithinAt_totalSpace.mp hh).2.contDiffWithinAt
    · intro y hy a b
      exact h.symm _ _ _
    · intro y hy v hv
      have hInner : coordinateInner (actualChartTensor h c) y v v =
          h.inner (c.chart.symm y) (inverseChartDifferential c y v)
            (inverseChartDifferential c y v) := by
        have hsum (v : E3) : (∑ i : Fin 3, v i • coordinateVector 3 i) = v := by
          ext j
          simp [coordinateVector, EuclideanSpace.single, Pi.single_apply]
        have hdiff (v : E3) : inverseChartDifferential c y v =
            ∑ i : Fin 3, v i • inverseChartDifferential c y (coordinateVector 3 i) := by
          simpa only [map_sum, map_smul] using
            congrArg (inverseChartDifferential c y) (hsum v).symm
        unfold coordinateInner actualChartTensor
        rw [hdiff v, map_sum]
        simp only [map_smul, sum_apply, smul_apply, map_sum, smul_eq_mul]
        simp only [Finset.mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
      rw [hInner]
      have hinj : Function.Injective (inverseChartDifferential c y) :=
        ((hchartMD.symm.mfderiv_bijective hy).comp
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm.bijective).injective
      exact h.pos _ _ (fun hz => hv (hinj (hz.trans (map_zero _).symm)))
  have hqnormal : q G.normal = 1 := by
    have hn := hinverse 0 1
    simp only [map_zero, zero_add, one_smul] at hn
    change (e.symm G.normal).2 - fderiv ℝ G.height x (e.symm G.normal).1 = 1
    rw [hn]
    simp
  have hqtangent (v : E2) : q (fderiv ℝ f x v) = 0 :=
    (hrange _).mp ⟨v, rfl⟩
  have hgraphnormal (v : E3) :
      v = fderiv ℝ f x (π v) + q v • G.normal := by
    rw [hfd.fderiv]
    change v = G.plane (π v) + fderiv ℝ G.height x (π v) • G.normal +
      (τ v - fderiv ℝ G.height x (π v)) • G.normal
    rw [sub_smul]
    calc
      v = G.plane (π v) + τ v • G.normal := hdecomp v
      _ = _ := by abel
  let V : Fin 2 → E3 := fun i => graphTangent f x i
  have hAV (i j : Fin 2) : B (V i) (V j) = A i j := by
    rw [← hinner]
    exact congrFun (congrFun hmetric i) j
  let ν : E3 := G.normal - ∑ i : Fin 2, ∑ j : Fin 2,
    (A⁻¹ i j * B (V j) G.normal) • V i
  have horth (k : Fin 2) : B (V k) ν = 0 := by
    simp only [ν,map_sub,map_sum,map_smul,smul_eq_mul,hAV]
    have heq : (∑ i : Fin 2, ∑ j : Fin 2,
        A⁻¹ i j * B (V j) G.normal * A k i) =
        ∑ j : Fin 2, (A * A⁻¹) k j * B (V j) G.normal := by
      simp only [Matrix.mul_apply,Fin.sum_univ_two]
      ring
    rw [heq,Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hpos.ne')]
    change B (V k) G.normal - (∑ j : Fin 2, (if k = j then 1 else 0) * B (V j) G.normal) = 0
    simp
  have hqν : q ν = 1 := by
    simp only [ν,map_sub,map_sum,map_smul,smul_eq_mul,hqnormal]
    have hz (i : Fin 2) : q (V i) = 0 := hqtangent _
    simp only [hz,mul_zero,Finset.sum_const_zero,sub_zero]
  have hνne : ν ≠ 0 := by
    intro heq
    simpa [heq] using hqν
  have hgraph : y ∈ G.coordinates.chart.target := by
    apply G.graph_in_chart
    have hdist : dist x 0 < G.radius := hx
    change dist x 0 ≤ 2 * G.radius
    linarith [G.radius_pos]
  have hνpos : 0 < B ν ν := by
    rw [← hinner]
    exact (hprops h G.coordinates).2.2 y hgraph ν hνne
  have hnν : B G.normal ν = B ν ν := by
    change B G.normal ν = B (G.normal - ∑ i : Fin 2, ∑ j : Fin 2,
      (A⁻¹ i j * B (V j) G.normal) • V i) ν
    simp only [map_sub,map_sum,map_smul,sub_apply,sum_apply,smul_apply,
      smul_eq_mul,horth,mul_zero,Finset.sum_const_zero,sub_zero]
  have hForth (v : E2) : B (fderiv ℝ f x v) ν = 0 := by
    have hv : v = ∑ i : Fin 2,v i • coordinateVector 2 i := by
      ext i
      fin_cases i <;> simp [coordinateVector,EuclideanSpace.single,PiLp.single_apply]
    rw [hv]
    simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul]
    change (∑ i : Fin 2,v i * B (V i) ν) = 0
    simp only [horth,mul_zero,Finset.sum_const_zero]
  have hprojected (H : E3) :
      B H G.normal - ∑ i : Fin 2, ∑ j : Fin 2,
        A⁻¹ i j * B H (V i) * B (V j) G.normal = q H * B ν ν := by
    have hpair : B H ν = q H * B ν ν := by
      conv_lhs => rw [hgraphnormal H]
      simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul,hForth,zero_add,hnν]
    rw [← hpair]
    simp only [ν,map_sub,map_sum,map_smul,map_add,smul_eq_mul,Fin.sum_univ_two]
    ring
  have hidentity : G.classicalResidual x = Real.sqrt A.det *
      (B (tracedAcceleration (actualChartTensor h G.coordinates) f x) G.normal -
        ∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j *
          B (tracedAcceleration (actualChartTensor h G.coordinates) f x) (V i) *
          B (V j) G.normal) := by
    have hh := SeifertSurfaces.OriginalEndpoints.A3FirstVariation.actual_graph_first_variation_identity
      G G.disc Metric.isOpen_ball Set.Subset.rfl hsmooth x hx
    change G.classicalResidual x = Real.sqrt A.det *
      (coordinateInner (actualChartTensor h G.coordinates) y
        (tracedAcceleration (actualChartTensor h G.coordinates) f x) G.normal -
        ∑ i : Fin 2, ∑ j : Fin 2,
          (inducedMetric (actualChartTensor h G.coordinates) f x)⁻¹ i j *
          coordinateInner (actualChartTensor h G.coordinates) y
            (tracedAcceleration (actualChartTensor h G.coordinates) f x) (V i) *
          coordinateInner (actualChartTensor h G.coordinates) y (V j) G.normal) at hh
    rw [hmetric] at hh
    simpa only [hinner] using hh
  rw [hprojected] at hidentity
  have hprod := hidentity.symm.trans hc
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left
    (Real.sqrt_pos.mpr hpos).ne')).resolve_right hνpos.ne'

/-- Minimality of the same immersed shared graph in its constructing chart
transports to every actual smooth ambient chart for the same ambient metric,
on the disc restricted to that chart's source. -/
theorem same_graph_minimality_in_every_actual_chart
    (G : A3SharedGraph D)
    (hcoordinate :
      IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
        (graphMap (G.coordinates.chart (D.edge D.pointParameter))
          G.plane G.normal G.height) G.disc)
    (hregular :
      ContMDiffOn 𝓘(ℝ, E2) 𝓘(ℝ, E3) ∞ G.parameter G.disc ∧
      (∀ x ∈ G.disc, Function.Injective
        (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) G.parameter x))) :
    ∀ c : SmoothAmbientChart N,
      IsMinimalParametrizationOn (actualChartTensor h c) (c.chart ∘ G.parameter)
        (G.disc ∩ G.parameter ⁻¹' c.chart.source) := by
  intro c
  refine ⟨?_, ?_⟩
  · exact (c.smooth.comp (hregular.1.mono Set.inter_subset_left)
      (fun x hx => hx.2)).contDiffOn
  · intro x hx
    let f := graphMap (G.coordinates.chart (D.edge D.pointParameter))
      G.plane G.normal G.height
    let T := c.chart ∘ G.coordinates.chart.symm
    have hsub : G.disc ⊆ Metric.closedBall 0 (2 * G.radius) := by
      intro y hy
      have hy' : dist y 0 < G.radius := hy
      change dist y 0 ≤ 2 * G.radius
      linarith [G.radius_pos]
    have hgraph : f x ∈ G.coordinates.chart.target := G.graph_in_chart (hsub hx.1)
    have hsource : G.parameter x ∈ G.coordinates.chart.source :=
      G.coordinates.chart.symm.map_source hgraph
    have hrecover : G.coordinates.chart (G.parameter x) = f x :=
      G.coordinates.chart.right_inv hgraph
    have hct := hcoordinate.2 x hx.1
    have hgMD : G.coordinates.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
      ⟨G.coordinates.smooth.mdifferentiableOn (by simp),
        G.coordinates.inverse_smooth.mdifferentiableOn (by simp)⟩
    have hcMD : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
      ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
    have hmT : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) T (f x) :=
      (hcMD.mdifferentiableAt hx.2).comp (f x) (hgMD.mdifferentiableAt_symm hgraph)
    have hchartEq : T (f x) = c.chart (G.parameter x) := rfl
    have hdT : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) T (f x) =
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart (G.parameter x)).comp
          (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) G.coordinates.chart.symm (f x)) :=
      mfderiv_comp _ (hcMD.mdifferentiableAt hx.2) (hgMD.mdifferentiableAt_symm hgraph)
    have hfMD : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E3) f x :=
      (hcoordinate.1.contMDiffOn.contMDiffAt (Metric.isOpen_ball.mem_nhds hx.1)).mdifferentiableAt (by simp)
    have hdComp : mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) (c.chart ∘ G.parameter) x =
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) T (f x)).comp
          (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) f x) :=
      mfderiv_comp _ hmT hfMD
    have hdEuclidean : fderiv ℝ (c.chart ∘ G.parameter) x =
        (fderiv ℝ T (f x)).comp (fderiv ℝ f x) :=
      fderiv_comp _ hmT.differentiableAt hfMD.differentiableAt
    have htransition : Function.Injective (fderiv ℝ T (f x)) := by
      have hmi : Function.Injective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) T (f x)) := by
        rw [hdT]
        exact (hcMD.mfderiv_injective hx.2).comp (hgMD.symm.mfderiv_injective hgraph)
      rw [mfderiv_eq_fderiv] at hmi
      intro v w hvw
      apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).symm.injective
      apply hmi
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.coe_coe] using
        congrArg ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (T (f x))).symm) hvw
    have hdTvector (v : E3) :
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) (T (f x))).symm (fderiv ℝ T (f x) v) =
          (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart (G.parameter x))
            ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) G.coordinates.chart.symm (f x))
              ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).symm v)) := by
      have he := congrArg (fun A => A ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).symm v)) hdT
      rw [mfderiv_eq_fderiv] at he
      change (NormedSpace.fromTangentSpace (𝕜 := ℝ) (T (f x))).symm
        (fderiv ℝ T (f x) ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x))
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).symm v))) = _ at he
      rw [ContinuousLinearEquiv.apply_symm_apply] at he
      exact he
    have hinvDiff (v : E3) :
        inverseChartDifferential c (T (f x)) (fderiv ℝ T (f x) v) =
          inverseChartDifferential G.coordinates (f x) v := by
      change (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm (T (f x)))
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (T (f x))).symm (fderiv ℝ T (f x) v)) =
          (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) G.coordinates.chart.symm (f x))
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).symm v)
      rw [hdTvector]
      change ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm (c.chart (G.parameter x))).comp
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart (G.parameter x)))
          ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) G.coordinates.chart.symm (f x))
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).symm v)) = _
      rw [hcMD.symm_comp_deriv hx.2]
      rfl
    have hinner (a : SmoothAmbientChart N) (y v w : E3) :
        coordinateInner (actualChartTensor h a) y v w =
          h.inner (a.chart.symm y) (inverseChartDifferential a y v)
            (inverseChartDifferential a y w) := by
      have hsum (v : E3) : (∑ i : Fin 3, v i • coordinateVector 3 i) = v := by
        ext j
        simp [coordinateVector, EuclideanSpace.single, Pi.single_apply]
      have hdiff (v : E3) : inverseChartDifferential a y v =
          ∑ i : Fin 3, v i • inverseChartDifferential a y (coordinateVector 3 i) := by
        simpa only [map_sum, map_smul] using
          congrArg (inverseChartDifferential a y) (hsum v).symm
      unfold coordinateInner actualChartTensor
      rw [hdiff v, hdiff w, map_sum]
      simp only [map_smul, sum_apply, smul_apply, map_sum, smul_eq_mul]
      simp only [Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    have hpullback (v w : E3) :
        coordinateInner (actualChartTensor h c) (T (f x))
          (fderiv ℝ T (f x) v) (fderiv ℝ T (f x) w) =
          coordinateInner (actualChartTensor h G.coordinates) (f x) v w := by
      rw [hinner, hinner, hinvDiff, hinvDiff]
      have hpoint : c.chart.symm (T (f x)) = G.coordinates.chart.symm (f x) :=
        c.chart.left_inv hx.2
      rw [hpoint]
    have hGram : inducedMetric (actualChartTensor h c) (c.chart ∘ G.parameter) x =
        inducedMetric (actualChartTensor h G.coordinates) f x := by
      ext i j
      simp only [inducedMetric, graphTangent, hdEuclidean, ContinuousLinearMap.comp_apply]
      exact hpullback _ _
    suffices hcov : ∀ i j : Fin 2,
        covariantAcceleration (actualChartTensor h c) (c.chart ∘ G.parameter) x i j =
          fderiv ℝ T (f x)
            (covariantAcceleration (actualChartTensor h G.coordinates) f x i j) by
      have htrace : tracedAcceleration (actualChartTensor h c) (c.chart ∘ G.parameter) x =
          fderiv ℝ T (f x)
            (tracedAcceleration (actualChartTensor h G.coordinates) f x) := by
        simp only [tracedAcceleration, hGram, map_sum, map_smul, hcov]
      rcases hct with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      change fderiv ℝ (c.chart ∘ G.parameter) x v = _
      rw [hdEuclidean, htrace]
      exact congrArg (fderiv ℝ T (f x)) hv
    intro i j
    have hfAt : ContDiffAt ℝ ∞ f x :=
      hcoordinate.1.contDiffAt (Metric.isOpen_ball.mem_nhds hx.1)
    have hTAt : ContDiffAt ℝ ∞ T (f x) :=
      ((c.smooth.contMDiffAt (c.chart.open_source.mem_nhds hx.2)).comp (f x)
        (G.coordinates.inverse_smooth.contMDiffAt
          (G.coordinates.chart.open_target.mem_nhds hgraph))).contDiffAt
    have hfD : DifferentiableAt ℝ (fderiv ℝ f) x :=
      (hfAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hTD : DifferentiableAt ℝ (fderiv ℝ T) (f x) :=
      (hTAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have heq : (fun z => graphTangent (c.chart ∘ G.parameter) z j) =ᶠ[𝓝 x]
        (fun z => fderiv ℝ T (f z) (graphTangent f z j)) := by
      have heT : ∀ᶠ y in 𝓝 (f x), DifferentiableAt ℝ T y :=
        ((hTAt.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).eventually
          (by norm_num)).mono (fun _ hy => hy.differentiableAt (by norm_num))
      have heF : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ f z :=
        ((hfAt.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).eventually
          (by norm_num)).mono (fun _ hz => hz.differentiableAt (by norm_num))
      filter_upwards [hfMD.differentiableAt.continuousAt heT, heF] with z hzT hzf
      simp only [graphTangent]
      rw [show (c.chart ∘ G.parameter) = T ∘ f from rfl, fderiv_comp z hzT hzf]
      rfl
    have hsecond :
        fderiv ℝ (fun z => graphTangent (c.chart ∘ G.parameter) z j) x
            (coordinateVector 2 i) =
          fderiv ℝ T (f x)
            (fderiv ℝ (fun z => graphTangent f z j) x (coordinateVector 2 i)) +
          fderiv ℝ (fderiv ℝ T) (f x) (graphTangent f x i) (graphTangent f x j) := by
      have hdcomp : DifferentiableAt ℝ (fun z => fderiv ℝ T (f z)) x :=
        hTD.comp x hfMD.differentiableAt
      have hdt : DifferentiableAt ℝ (fun z => graphTangent f z j) x :=
        hfD.clm_apply (differentiableAt_const _)
      rw [heq.fderiv_eq, fderiv_clm_apply hdcomp hdt]
      rw [show fderiv ℝ (fun z => fderiv ℝ T (f z)) x =
        (fderiv ℝ (fderiv ℝ T) (f x)).comp (fderiv ℝ f x) from
          fderiv_comp x hTD hfMD.differentiableAt]
      rfl
    let u := graphTangent f x i
    let v := graphTangent f x j
    have htangentNew (k : Fin 2) : graphTangent (c.chart ∘ G.parameter) x k =
        fderiv ℝ T (f x) (graphTangent f x k) := by
      simp only [graphTangent, hdEuclidean, ContinuousLinearMap.comp_apply]
    suffices hΓ :
        fderiv ℝ (fderiv ℝ T) (f x) u v +
          (∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3,
            christoffel (actualChartTensor h c) (T (f x)) a b k *
              (fderiv ℝ T (f x) u) a * (fderiv ℝ T (f x) v) b) •
                coordinateVector 3 k) =
        fderiv ℝ T (f x)
          (∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3,
            christoffel (actualChartTensor h G.coordinates) (f x) a b k * u a * v b) •
              coordinateVector 3 k) by
      simp only [covariantAcceleration, hsecond, htangentNew, map_add]
      rw [add_assoc]
      exact congrArg
        (fun z => fderiv ℝ T (f x)
          (fderiv ℝ (fun z => graphTangent f z j) x (coordinateVector 2 i)) + z) hΓ
    have hCov (d e : SmoothAmbientChart N) (y : E3)
        (hy : y ∈ d.chart.target) (he : d.chart.symm y ∈ e.chart.source)
        (u v : E3) :
        fderiv ℝ (fderiv ℝ (e.chart ∘ d.chart.symm)) y u v +
          (∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3,
            christoffel (actualChartTensor h e) (e.chart (d.chart.symm y)) a b k *
              (fderiv ℝ (e.chart ∘ d.chart.symm) y u) a *
              (fderiv ℝ (e.chart ∘ d.chart.symm) y v) b) • coordinateVector 3 k) =
        fderiv ℝ (e.chart ∘ d.chart.symm) y
          (∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3,
            christoffel (actualChartTensor h d) y a b k * u a * v b) •
              coordinateVector 3 k) := by
      classical
      have hprops
          (h : AmbientMetric N) (c : SmoothAmbientChart N) :
          (∀ a b, ContDiffOn ℝ ∞ (fun y => actualChartTensor h c y a b) c.chart.target) ∧
          (∀ y ∈ c.chart.target, ∀ a b,
            actualChartTensor h c y a b = actualChartTensor h c y b a) ∧
          (∀ y ∈ c.chart.target, ∀ v : E3, v ≠ 0 →
            0 < coordinateInner (actualChartTensor h c) y v v) := by
        classical
        have hchartMD : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
          ⟨c.smooth.mdifferentiableOn (by simp),
            c.inverse_smooth.mdifferentiableOn (by simp)⟩
        have hvector (v : E3) :
            ContMDiffOn 𝓘(ℝ, E3) (𝓘(ℝ, E3).tangent) ∞
              (fun y => Bundle.TotalSpace.mk' E3 (c.chart.symm y)
                (inverseChartDifferential c y v)) c.chart.target := by
          have hconst : ContMDiff 𝓘(ℝ, E3) (𝓘(ℝ, E3).tangent) ∞
              (fun y : E3 => Bundle.TotalSpace.mk' E3 y
                ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v)) := by
            apply (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (E := E3)
              (V := fun y => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v)).mpr
            change ContDiff ℝ ∞ (fun _ : E3 => v)
            exact contDiff_const
          have htm := c.inverse_smooth.contMDiffOn_tangentMapWithin
            (m := ∞) (by simp) c.chart.open_target.uniqueMDiffOn
          have hv := htm.comp (f := fun y : E3 => Bundle.TotalSpace.mk' E3 y
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v))
            hconst.contMDiffOn (s := c.chart.target) (by
            intro y hy
            exact hy)
          apply hv.congr
          intro y hy
          have hd := mfderivWithin_eq_mfderiv
            (c.chart.open_target.uniqueMDiffOn y hy)
            ((c.inverse_smooth.contMDiffAt (c.chart.open_target.mem_nhds hy)).mdifferentiableAt
              (by simp))
          change Bundle.TotalSpace.mk' E3 (c.chart.symm y)
              ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm y)
                ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v)) =
            Bundle.TotalSpace.mk' E3 (c.chart.symm y)
              ((mfderivWithin 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm c.chart.target y)
                ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v))
          rw [hd]
        refine ⟨?_, ?_, ?_⟩
        · intro a b y hy
          have hh : ContMDiffWithinAt 𝓘(ℝ, E3) (𝓘(ℝ, E3).prod 𝓘(ℝ)) ∞
              (fun y => Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial N ℝ) (c.chart.symm y)
                (actualChartTensor h c y a b)) c.chart.target y := by
            apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := E3) (F₂ := E3)
            · exact h.contMDiff.contMDiffAt.comp_contMDiffWithinAt y (c.inverse_smooth y hy)
            · exact hvector (coordinateVector 3 a) y hy
            · exact hvector (coordinateVector 3 b) y hy
          exact (Bundle.contMDiffWithinAt_totalSpace.mp hh).2.contDiffWithinAt
        · intro y hy a b
          exact h.symm _ _ _
        · intro y hy v hv
          have hInner : coordinateInner (actualChartTensor h c) y v v =
              h.inner (c.chart.symm y) (inverseChartDifferential c y v)
                (inverseChartDifferential c y v) := by
            have hsum (v : E3) : (∑ i : Fin 3, v i • coordinateVector 3 i) = v := by
              ext j
              simp [coordinateVector, EuclideanSpace.single, Pi.single_apply]
            have hdiff (v : E3) : inverseChartDifferential c y v =
                ∑ i : Fin 3, v i • inverseChartDifferential c y (coordinateVector 3 i) := by
              simpa only [map_sum, map_smul] using
                congrArg (inverseChartDifferential c y) (hsum v).symm
            unfold coordinateInner actualChartTensor
            rw [hdiff v, map_sum]
            simp only [map_smul, sum_apply, smul_apply, map_sum, smul_eq_mul]
            simp only [Finset.mul_sum]
            conv_rhs => rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro b hb
            ring
          rw [hInner]
          have hinj : Function.Injective (inverseChartDifferential c y) :=
            ((hchartMD.symm.mfderiv_bijective hy).comp
              (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm.bijective).injective
          exact h.pos _ _ (fun hz => hv (hinj (hz.trans (map_zero _).symm)))
      have htransition (h : AmbientMetric N) (c d : SmoothAmbientChart N) (y : E3)
          (hy : y ∈ c.chart.target) (hd : c.chart.symm y ∈ d.chart.source) :
          ContDiffAt ℝ ∞ (d.chart ∘ c.chart.symm) y ∧
          Function.Bijective (fderiv ℝ (d.chart ∘ c.chart.symm) y) ∧
          ∀ᶠ z in 𝓝 y, ∀ v w : E3,
            coordinateInner (actualChartTensor h c) z v w =
              coordinateInner (actualChartTensor h d) (d.chart (c.chart.symm z))
                (fderiv ℝ (d.chart ∘ c.chart.symm) z v)
                (fderiv ℝ (d.chart ∘ c.chart.symm) z w) := by
        classical
        have hcMD : c.chart.MDifferentiable 𝓘(ℝ,E3) 𝓘(ℝ,E3) :=
          ⟨c.smooth.mdifferentiableOn (by simp),c.inverse_smooth.mdifferentiableOn (by simp)⟩
        have hdMD : d.chart.MDifferentiable 𝓘(ℝ,E3) 𝓘(ℝ,E3) :=
          ⟨d.smooth.mdifferentiableOn (by simp),d.inverse_smooth.mdifferentiableOn (by simp)⟩
        have hT : ContDiffAt ℝ ∞ (d.chart ∘ c.chart.symm) y :=
          ((d.smooth.contMDiffAt (d.chart.open_source.mem_nhds hd)).comp y
            (c.inverse_smooth.contMDiffAt (c.chart.open_target.mem_nhds hy))).contDiffAt
        have hder (z : E3) (hz : z ∈ c.chart.target)
            (hdz : c.chart.symm z ∈ d.chart.source) :
            fderiv ℝ (d.chart ∘ c.chart.symm) z =
              (mfderiv 𝓘(ℝ,E3) 𝓘(ℝ,E3) d.chart (c.chart.symm z)).comp
                (mfderiv 𝓘(ℝ,E3) 𝓘(ℝ,E3) c.chart.symm z) := by
          have hh := mfderiv_comp z (hdMD.mdifferentiableAt hdz)
            (hcMD.mdifferentiableAt_symm hz)
          rw [mfderiv_eq_fderiv] at hh
          exact hh
        refine ⟨hT,?_,?_⟩
        · rw [hder y hy hd]
          exact (hdMD.mfderiv_bijective hd).comp (hcMD.symm.mfderiv_bijective hy)
        · have hcN : ∀ᶠ z in 𝓝 y, z ∈ c.chart.target := c.chart.open_target.mem_nhds hy
          have hdN : ∀ᶠ z in 𝓝 y, c.chart.symm z ∈ d.chart.source :=
            (c.chart.continuousAt_symm hy).preimage_mem_nhds (d.chart.open_source.mem_nhds hd)
          filter_upwards [hcN,hdN] with z hz hdz
          have hsum (v : E3) : (∑ i : Fin 3,v i • coordinateVector 3 i) = v := by
            ext j
            simp [coordinateVector,EuclideanSpace.single,Pi.single_apply]
          have hInner (e : SmoothAmbientChart N) (x a b : E3) :
              coordinateInner (actualChartTensor h e) x a b =
                h.inner (e.chart.symm x) (inverseChartDifferential e x a)
                  (inverseChartDifferential e x b) := by
            have hdiff (v : E3) : inverseChartDifferential e x v =
                ∑ i : Fin 3,v i • inverseChartDifferential e x (coordinateVector 3 i) := by
              simpa only [map_sum,map_smul] using
                congrArg (inverseChartDifferential e x) (hsum v).symm
            unfold coordinateInner actualChartTensor
            rw [hdiff a,hdiff b,map_sum]
            simp only [map_smul,sum_apply,smul_apply,map_sum,smul_eq_mul,Finset.mul_sum]
            conv_rhs => rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
          intro v w
          rw [hInner,hInner]
          have hinv (v : E3) : inverseChartDifferential d (d.chart (c.chart.symm z))
              (fderiv ℝ (d.chart ∘ c.chart.symm) z v) = inverseChartDifferential c z v := by
            rw [hder z hz hdz]
            change (mfderiv 𝓘(ℝ,E3) 𝓘(ℝ,E3) d.chart.symm (d.chart (c.chart.symm z)))
              ((mfderiv 𝓘(ℝ,E3) 𝓘(ℝ,E3) d.chart (c.chart.symm z))
                ((mfderiv 𝓘(ℝ,E3) 𝓘(ℝ,E3) c.chart.symm z) v)) = _
            exact congrArg (fun L : E3 →L[ℝ] E3 => L
              ((mfderiv 𝓘(ℝ,E3) 𝓘(ℝ,E3) c.chart.symm z) v)) (hdMD.symm_comp_deriv hdz)
          rw [hinv,hinv,d.chart.left_inv hdz]
      have hLowerAlg (G J : Matrix (Fin 3) (Fin 3) ℝ)
          (dG H dg : Fin 3 → Fin 3 → Fin 3 → ℝ)
          (hG : ∀ i j, G i j = G j i)
          (hdG : ∀ a i j, dG a i j = dG a j i)
          (hH : ∀ k a b, H k a b = H k b a)
          (hdg : ∀ a l b, dg a l b =
            (∑ m : Fin 3, ∑ n : Fin 3, ∑ p : Fin 3,
              dG m n p * J m a * J n l * J p b) +
            ∑ n : Fin 3, ∑ p : Fin 3, G n p *
              (H n a l * J p b + J n l * H p a b))
          (a b l : Fin 3) :
          dg a l b + dg b l a - dg l a b =
            2 * (∑ s : Fin 3, ∑ t : Fin 3, G s t * H s a b * J t l) +
            ∑ s : Fin 3, ∑ t : Fin 3, ∑ m : Fin 3,
              (dG s m t + dG t m s - dG m s t) * J s a * J t b * J m l := by
        simp only [hdg, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
        simp only [hG,hdG,hH]
        ring
      have hGammaAlg (g G J : Matrix (Fin 3) (Fin 3) ℝ)
          (L lG H : Fin 3 → Fin 3 → Fin 3 → ℝ)
          (hg : IsUnit g.det) (hG : IsUnit G.det) (hJ : IsUnit J)
          (hmet : g = J.transpose * G * J)
          (hLower : ∀ a b l, L a b l =
            2 * (∑ s : Fin 3, ∑ t : Fin 3, G t s * H s a b * J t l) +
            ∑ s : Fin 3, ∑ t : Fin 3, ∑ m : Fin 3,
              lG s t m * J s a * J t b * J m l)
          (a b k : Fin 3) :
          (∑ i : Fin 3, J k i * ((1 / 2 : ℝ) * ∑ l : Fin 3, g⁻¹ i l * L a b l)) =
            H k a b + ∑ s : Fin 3, ∑ t : Fin 3,
              ((1 / 2 : ℝ) * ∑ m : Fin 3, G⁻¹ k m * lG s t m) * J s a * J t b := by
        classical
        let γ : Fin 3 → ℝ := (1 / 2 : ℝ) • (Matrix.mulVec g⁻¹ (L a b))
        let Γ (s t : Fin 3) : Fin 3 → ℝ := (1 / 2 : ℝ) • (Matrix.mulVec G⁻¹ (lG s t))
        let Z : Fin 3 → ℝ := (fun k => H k a b) +
          ∑ s : Fin 3, ∑ t : Fin 3, (J s a * J t b) • Γ s t
        have hγ : Matrix.mulVec g γ = (1 / 2 : ℝ) • L a b := by
          simp only [γ,Matrix.mulVec_smul,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hg,
            Matrix.one_mulVec]
        have hΓ (s t : Fin 3) : Matrix.mulVec G (Γ s t) = (1 / 2 : ℝ) • lG s t := by
          simp only [Γ,Matrix.mulVec_smul,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hG,
            Matrix.one_mulVec]
        have hZ : Matrix.mulVec (J.transpose * G) Z = (1 / 2 : ℝ) • L a b := by
          rw [← Matrix.mulVec_mulVec]
          simp only [Z,Matrix.mulVec_add,Matrix.mulVec_sum,Matrix.mulVec_smul,hΓ]
          ext l
          simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Pi.add_apply,
            Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hLower,
            Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
          ring
        have heq : Matrix.mulVec (J.transpose * G) (Matrix.mulVec J γ) = Matrix.mulVec (J.transpose * G) Z := by
          rw [Matrix.mulVec_mulVec,← hmet,hγ,hZ]
        have hJT : IsUnit J.transpose := (Matrix.isUnit_iff_isUnit_det _).mpr (by
          simpa only [Matrix.det_transpose] using (Matrix.isUnit_iff_isUnit_det _).mp hJ)
        have hJG : IsUnit (J.transpose * G) := hJT.mul ((Matrix.isUnit_iff_isUnit_det _).mpr hG)
        have hh := Matrix.mulVec_injective_iff_isUnit.mpr hJG heq
        have hk := congrFun hh k
        simpa only [γ,Γ,Z,Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply,
          Pi.smul_apply,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hk
      have hMetricDeriv (G q : MetricTensor) (T : E3 → E3) (y : E3)
          (hG : ∀ n p, DifferentiableAt ℝ (fun z => G z n p) (T y))
          (hT : DifferentiableAt ℝ T y)
          (hq : ∀ n b, DifferentiableAt ℝ (fun z => q z n b) y)
          (a l b : Fin 3) :
          partial3 (fun z => ∑ n : Fin 3, ∑ p : Fin 3,
            G (T z) n p * q z n l * q z p b) y a =
          (∑ m : Fin 3, ∑ n : Fin 3, ∑ p : Fin 3,
            partial3 (fun z => G z n p) (T y) m *
              (fderiv ℝ T y (coordinateVector 3 a)) m * q y n l * q y p b) +
          ∑ n : Fin 3, ∑ p : Fin 3, G (T y) n p *
            (partial3 (fun z => q z n l) y a * q y p b +
              q y n l * partial3 (fun z => q z p b) y a) := by
        classical
        have hsum (v : E3) : (∑ i : Fin 3, v i • coordinateVector 3 i) = v := by
          ext j
          simp [coordinateVector,EuclideanSpace.single,Pi.single_apply]
        have hexpand (f : E3 → ℝ) (x v : E3) :
            fderiv ℝ f x v = ∑ i : Fin 3, partial3 f x i * v i := by
          conv_lhs => rw [← hsum v]
          simp only [map_sum,map_smul,smul_eq_mul,partial3]
          congr 1
          ext i
          rw [mul_comm]
        have hterm (n p : Fin 3) :
            partial3 (fun z => G (T z) n p * q z n l * q z p b) y a =
            (∑ m : Fin 3, partial3 (fun z => G z n p) (T y) m *
              (fderiv ℝ T y (coordinateVector 3 a)) m) * q y n l * q y p b +
            G (T y) n p * (partial3 (fun z => q z n l) y a * q y p b +
              q y n l * partial3 (fun z => q z p b) y a) := by
          have hh := (((hG n p).hasFDerivAt.comp y hT.hasFDerivAt).mul
            (hq n l).hasFDerivAt).mul (hq p b).hasFDerivAt
          change HasFDerivAt (fun z => G (T z) n p * q z n l * q z p b) _ y at hh
          have hv := congrArg (fun L : E3 →L[ℝ] ℝ => L (coordinateVector 3 a)) hh.fderiv
          simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.comp_apply,smul_eq_mul] at hv
          change _ = _ at hv
          rw [hexpand (fun z => G z n p) (T y) (fderiv ℝ T y (coordinateVector 3 a))] at hv
          change partial3 _ y a = _ at hv
          simp only [partial3,Function.comp_def,Pi.mul_apply] at hv ⊢
          rw [hv]
          ring
        have hd (n p : Fin 3) : DifferentiableAt ℝ
            (fun z => G (T z) n p * q z n l * q z p b) y :=
          (((hG n p).comp y hT).mul (hq n l)).mul (hq p b)
        unfold partial3 at *
        rw [fderiv_fun_sum (fun n _ => DifferentiableAt.fun_sum (fun p _ => hd n p))]
        simp only [ContinuousLinearMap.sum_apply]
        simp_rw [fderiv_fun_sum (fun p _ => hd _ p),ContinuousLinearMap.sum_apply,hterm]
        simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
        ring
      have hJacobian (T : E3 → E3) (y : E3) (hT : ContDiffAt ℝ ∞ T y) :
          (∀ k b : Fin 3, ContDiffAt ℝ ∞
            (fun z => (fderiv ℝ T z (coordinateVector 3 b)) k) y) ∧
          (∀ k a b : Fin 3,
            partial3 (fun z => (fderiv ℝ T z (coordinateVector 3 b)) k) y a =
              (fderiv ℝ (fderiv ℝ T) y (coordinateVector 3 a) (coordinateVector 3 b)) k) ∧
          (∀ k a b : Fin 3,
            partial3 (fun z => (fderiv ℝ T z (coordinateVector 3 b)) k) y a =
              partial3 (fun z => (fderiv ℝ T z (coordinateVector 3 a)) k) y b) := by
        have hF : ContDiffAt ℝ ∞ (fderiv ℝ T) y := hT.fderiv_right (by simp)
        have hj (k b : Fin 3) : ContDiffAt ℝ ∞
            (fun z => (fderiv ℝ T z (coordinateVector 3 b)) k) y :=
          (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.contDiffAt.comp y
            (hF.clm_apply contDiffAt_const)
        have heq (k a b : Fin 3) :
            partial3 (fun z => (fderiv ℝ T z (coordinateVector 3 b)) k) y a =
              (fderiv ℝ (fderiv ℝ T) y (coordinateVector 3 a) (coordinateVector 3 b)) k := by
          have hd := (hF.differentiableAt (by simp)).hasFDerivAt.clm_apply
            (hasFDerivAt_const (coordinateVector 3 b) y)
          have hp := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp y hd
          have hv := congrArg (fun L : E3 →L[ℝ] ℝ => L (coordinateVector 3 a)) hp.fderiv
          simpa only [Function.comp_def,EuclideanSpace.coe_proj,partial3,ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,
            ContinuousLinearMap.zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply] using hv
        refine ⟨hj,heq,?_⟩
        intro k a b
        rw [heq,heq]
        exact congrArg (fun v : E3 => v k) ((hT.isSymmSndFDerivAt (by norm_num)).eq _ _)
      let T : E3 → E3 := e.chart ∘ d.chart.symm
      let g₀ : MetricTensor := actualChartTensor h d
      let g₁ : MetricTensor := actualChartTensor h e
      let J : MetricTensor := fun z k a => (fderiv ℝ T z (coordinateVector 3 a)) k
      let H : Fin 3 → Fin 3 → Fin 3 → ℝ := fun k a b => partial3 (fun z => J z k b) y a
      let dG : Fin 3 → Fin 3 → Fin 3 → ℝ := fun a i j => partial3 (fun z => g₁ z i j) (T y) a
      let dg : Fin 3 → Fin 3 → Fin 3 → ℝ := fun a i j => partial3 (fun z => g₀ z i j) y a
      obtain ⟨hT,hTbij,hPull⟩ := htransition h d e y hy he
      change ContDiffAt ℝ ∞ T y at hT
      change Function.Bijective (fderiv ℝ T y) at hTbij
      have hTy : T y ∈ e.chart.target := e.chart.map_source he
      have hGdiff (i j : Fin 3) : DifferentiableAt ℝ (fun z => g₁ z i j) (T y) :=
        (((hprops h e).1 i j).contDiffAt
          (e.chart.open_target.mem_nhds hTy)).differentiableAt (by simp)
      have hJdiff (k a : Fin 3) : DifferentiableAt ℝ (fun z => J z k a) y :=
        ((hJacobian T y hT).1 k a).differentiableAt (by simp)
      have hHsym (k a b : Fin 3) : H k a b = H k b a := (hJacobian T y hT).2.2 k a b
      have hGsym (i j : Fin 3) : g₁ (T y) i j = g₁ (T y) j i := h.symm _ _ _
      have hdGsym (a i j : Fin 3) : dG a i j = dG a j i := by
        have he : (fun z => g₁ z i j) = (fun z => g₁ z j i) := funext (fun _ => h.symm _ _ _)
        simp only [dG,he]
      have hEntry (i j : Fin 3) : (fun z => g₀ z i j) =ᶠ[𝓝 y]
          (fun z => ∑ n : Fin 3, ∑ p : Fin 3, g₁ (T z) n p * J z n i * J z p j) := by
        filter_upwards [hPull] with z hz
        have hh := hz (coordinateVector 3 i) (coordinateVector 3 j)
        simpa [g₀,g₁,T,J,coordinateInner,coordinateVector,EuclideanSpace.single,
          PiLp.single_apply] using hh
      have hdg (a l b : Fin 3) : dg a l b =
          (∑ m : Fin 3, ∑ n : Fin 3, ∑ p : Fin 3,
            dG m n p * J y m a * J y n l * J y p b) +
          ∑ n : Fin 3, ∑ p : Fin 3, g₁ (T y) n p *
            (H n a l * J y p b + J y n l * H p a b) := by
        change fderiv ℝ (fun z => g₀ z l b) y (coordinateVector 3 a) = _
        rw [(hEntry l b).fderiv_eq]
        exact hMetricDeriv g₁ J T y hGdiff (hT.differentiableAt (by simp)) hJdiff a l b
      have hmetric : g₀ y = (J y).transpose * g₁ (T y) * J y := by
        ext i j
        change g₀ y i j = _
        calc
          g₀ y i j = ∑ n : Fin 3,∑ p : Fin 3,g₁ (T y) n p * J y n i * J y p j := (hEntry i j).self_of_nhds
          _ = _ := by
            simp only [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
              Fin.sum_univ_zero,add_zero]
            ring
      have hsum (v : E3) : (∑ i : Fin 3, v i • coordinateVector 3 i) = v := by
        ext j
        simp [coordinateVector,EuclideanSpace.single,Pi.single_apply]
      have hrepr (v : E3) (k : Fin 3) : (fderiv ℝ T y v) k =
          ∑ i : Fin 3, J y k i * v i := by
        conv_lhs => rw [← hsum v]
        simp only [map_sum,map_smul,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,J]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have hJunit : IsUnit (J y) := by
        apply Matrix.mulVec_injective_iff_isUnit.mp
        intro v w hvw
        have hh : (WithLp.toLp 2 v : E3) = WithLp.toLp 2 w := by
          apply hTbij.injective
          ext k
          rw [hrepr,hrepr]
          exact congrFun hvw k
        exact WithLp.toLp_injective 2 hh
      have hdet (e : SmoothAmbientChart N) (x : E3) (hx : x ∈ e.chart.target) :
          IsUnit (actualChartTensor h e x).det := by
        have hp : (actualChartTensor h e x).PosDef := by
          apply Matrix.PosDef.of_dotProduct_mulVec_pos
          · ext i j
            simpa only [Matrix.conjTranspose_apply,star_trivial,actualChartTensor] using h.symm _
              (inverseChartDifferential e x (coordinateVector 3 j))
              (inverseChartDifferential e x (coordinateVector 3 i))
          · intro ξ hξ
            let v : E3 := WithLp.toLp 2 ξ
            have hv : v ≠ 0 := fun hv => hξ (WithLp.toLp_injective 2 hv)
            have hpositive := (hprops h e).2.2 x hx v hv
            convert hpositive using 1
            simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,v,
              coordinateInner,Fin.sum_univ_succ]
            ring
        exact isUnit_iff_ne_zero.mpr (ne_of_gt hp.det_pos)
      have hLower (a b l : Fin 3) : dg a l b + dg b l a - dg l a b =
          2 * (∑ s : Fin 3, ∑ t : Fin 3, g₁ (T y) t s * H s a b * J y t l) +
          ∑ s : Fin 3, ∑ t : Fin 3, ∑ m : Fin 3,
            (dG s m t + dG t m s - dG m s t) * J y s a * J y t b * J y m l := by
        simpa only [hGsym] using hLowerAlg (g₁ (T y)) (J y) dG H dg hGsym hdGsym hHsym hdg a b l
      have hGamma (a b k : Fin 3) :
          (∑ i : Fin 3, J y k i * christoffel g₀ y a b i) =
            H k a b + ∑ s : Fin 3, ∑ t : Fin 3,
              christoffel g₁ (T y) s t k * J y s a * J y t b := by
        exact hGammaAlg (g₀ y) (g₁ (T y)) (J y)
          (fun a b l => dg a l b + dg b l a - dg l a b)
          (fun s t m => dG s m t + dG t m s - dG m s t) H
          (hdet d y hy) (hdet e (T y) hTy) hJunit hmetric hLower a b k
      have hsnd (u v : E3) (k : Fin 3) :
          (fderiv ℝ (fderiv ℝ T) y u v) k =
            ∑ a : Fin 3, ∑ b : Fin 3, H k a b * u a * v b := by
        conv_lhs => rw [← hsum u, ← hsum v]
        simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,
          ContinuousLinearMap.smul_apply,WithLp.ofLp_sum,Finset.sum_apply,
          PiLp.smul_apply,smul_eq_mul]
        simp only [H,J,(hJacobian T y hT).2.1]
        simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
        ring
      have hsumcoord (a : Fin 3 → ℝ) (k : Fin 3) :
          (∑ i : Fin 3, a i • coordinateVector 3 i) k = a k := by
        exact congrArg (fun z : E3 => z k) (hsum (WithLp.toLp 2 a))
      change fderiv ℝ (fderiv ℝ T) y u v +
        (∑ k : Fin 3,(∑ a : Fin 3,∑ b : Fin 3,
          christoffel g₁ (T y) a b k * (fderiv ℝ T y u) a *
            (fderiv ℝ T y v) b) • coordinateVector 3 k) =
        fderiv ℝ T y (∑ k : Fin 3,(∑ a : Fin 3,∑ b : Fin 3,
          christoffel g₀ y a b k * u a * v b) • coordinateVector 3 k)
      ext k
      simp only [PiLp.add_apply,hsumcoord,hsnd,hrepr]
      calc
        _ = ∑ a : Fin 3, ∑ b : Fin 3,
            (H k a b + ∑ s : Fin 3, ∑ t : Fin 3,
              christoffel g₁ (T y) s t k * J y s a * J y t b) * u a * v b := by
          simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
          ring
        _ = ∑ a : Fin 3, ∑ b : Fin 3,
            (∑ i : Fin 3,J y k i * christoffel g₀ y a b i) * u a * v b := by
          simp_rw [hGamma]
        _ = _ := by
          simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
          ring
    exact hCov G.coordinates c (f x) hgraph hx.2 u v

end SeifertSurfaces.OriginalEndpoints.A3RecoveryGeometryBridges
