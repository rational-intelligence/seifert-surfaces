import EndpointGeometry
import A4Coordinate

noncomputable section
open Set Topology Function
open scoped Manifold ContDiff

namespace SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N]

/-- Source A.4 data in the actual two-sided ambient extension. The plane
lives in T_p N=T_p M, and its frame merely identifies the planar region with E2.
The supplied chart is first-order compatible with this frame; local radius,
actual graph, metric, region and boundary intersection are all retained. -/
structure A4OriginalData (h : AmbientMetric N) (M : Set N)
    (C : WarpedBoundaryCollar h M) where
  p : N
  p_boundary : p ∈ frontier M
  p_collar : p ∈ C.coordinates.chart.source
  plane : Submodule ℝ (TangentSpace 𝓘(ℝ, E3) p)
  planeFrame : E2 ≃L[ℝ] plane
  normal : TangentSpace 𝓘(ℝ, E3) p
  normal_nonzero : normal ≠ 0
  normal_orthogonal : ∀ v ∈ plane, h.inner p v normal = 0
  graphCoordinates : SmoothAmbientChart N
  p_chart : p ∈ graphCoordinates.chart.source
  region : Set E2
  region_closed : IsClosed region
  zero_boundary : (0 : E2) ∈ frontier region
  sphere_condition : InteriorSphereAt region 0
  delta : ℝ
  delta_pos : 0 < delta
  height : E2 → ℝ
  height_C1 : ContDiffOn ℝ 1 height (region ∩ Metric.ball 0 delta)
  height_zero : height 0 = 0
  height_flat : HasFDerivWithinAt height (0 : E2 →L[ℝ] ℝ)
    (region ∩ Metric.ball 0 delta) 0
  graph_in_chart : MapsTo
    (graphMap (graphCoordinates.chart p)
      ((chartDifferential graphCoordinates p).comp
        (plane.subtypeL.comp planeFrame.toContinuousLinearMap))
      (chartDifferential graphCoordinates p normal) height)
    (region ∩ Metric.ball 0 delta) graphCoordinates.chart.target
  graph_in_manifold : MapsTo
    (graphCoordinates.chart.symm ∘ graphMap (graphCoordinates.chart p)
      ((chartDifferential graphCoordinates p).comp
        (plane.subtypeL.comp planeFrame.toContinuousLinearMap))
      (chartDifferential graphCoordinates p normal) height)
    (region ∩ Metric.ball 0 delta) M
  minimal_interior : IsMinimalPatch h
    (graphCoordinates.chart.symm ∘ graphMap (graphCoordinates.chart p)
      ((chartDifferential graphCoordinates p).comp
        (plane.subtypeL.comp planeFrame.toContinuousLinearMap))
      (chartDifferential graphCoordinates p normal) height)
    (interior region ∩ Metric.ball 0 delta)
  boundary_only : ∀ x ∈ region ∩ Metric.ball 0 delta,
    graphCoordinates.chart.symm
      (graphMap (graphCoordinates.chart p)
        ((chartDifferential graphCoordinates p).comp
          (plane.subtypeL.comp planeFrame.toContinuousLinearMap))
        (chartDifferential graphCoordinates p normal) height x) ∈ frontier M →
      x ∈ frontier region

/-- Lemma A.4, original manifold conclusion, with the same collar differential
restricted to the actual supplied plane and its equivalent boundary-plane form. -/
theorem A4_original {h : AmbientMetric N} {M : Set N}
    {C : WarpedBoundaryCollar h M} (D : A4OriginalData h M C) :
    ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) C.radial D.p).comp D.plane.subtypeL ≠ 0) ∧
    (D.plane ≠ boundaryTangentPlane C D.p D.p_collar) ∧
    (((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) C.radial D.p).comp D.plane.subtypeL ≠ 0) ↔
      D.plane ≠ boundaryTangentPlane C D.p D.p_collar) := by
  set_option maxHeartbeats 0 in
  exact (by
    have hchartMD (c : SmoothAmbientChart N) :
        c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
      ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
    have hchartComp (c : SmoothAmbientChart N) (p : N) (hp : p ∈ c.chart.source)
        (v : E3) :
        chartDifferential c p (inverseChartDifferential c (c.chart p) v) = v := by
      have hc := (hchartMD c).comp_symm_deriv (c.chart.map_source hp)
      rw [c.chart.left_inv hp] at hc
      exact congrArg (fun f => f v) hc
    have hinverseComp (c : SmoothAmbientChart N) (p : N) (hp : p ∈ c.chart.source)
        (v : TangentSpace 𝓘(ℝ, E3) p) :
        inverseChartDifferential c (c.chart p) (chartDifferential c p v) = v := by
      exact congrArg (fun f => f v) ((hchartMD c).symm_comp_deriv hp)
    have hInner (c : SmoothAmbientChart N) (y v w : E3) :
        coordinateInner (actualChartTensor h c) y v w =
          h.inner (c.chart.symm y) (inverseChartDifferential c y v)
            (inverseChartDifferential c y w) := by
      have hsum (v : E3) : (∑ i : Fin 3, v i • coordinateVector 3 i) = v := by
        ext j
        simp [coordinateVector, EuclideanSpace.single, Pi.single_apply]
      have hdiff (v : E3) :
          inverseChartDifferential c y v =
            ∑ i : Fin 3, v i • inverseChartDifferential c y (coordinateVector 3 i) := by
        simpa only [map_sum, map_smul] using congrArg (inverseChartDifferential c y) (hsum v).symm
      unfold coordinateInner actualChartTensor
      rw [hdiff v, hdiff w, map_sum]
      simp only [map_smul, sum_apply, smul_apply,
        map_sum, smul_eq_mul]
      simp only [Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    have hinnerChart (c : SmoothAmbientChart N) (p : N) (hp : p ∈ c.chart.source)
        (v w : TangentSpace 𝓘(ℝ, E3) p) :
        coordinateInner (actualChartTensor h c) (c.chart p)
          (chartDifferential c p v) (chartDifferential c p w) = h.inner p v w := by
      rw [hInner, hinverseComp c p hp v, hinverseComp c p hp w]
      rw [c.chart.left_inv hp]
    have hrformula (p : N) (hp : p ∈ C.coordinates.chart.source) :
        mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) C.radial p =
          (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)).comp
            (chartDifferential C.coordinates p) := by
      let P : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)
      have he : C.radial =ᶠ[𝓝 p] P ∘ C.coordinates.chart := by
        filter_upwards [C.coordinates.chart.open_source.mem_nhds hp] with q hq
        exact C.radial_coordinate q hq
      rw [he.mfderiv_eq]
      have hchart := (hchartMD C.coordinates).mdifferentiableAt hp
      rw [mfderiv_comp p P.differentiableAt.mdifferentiableAt hchart]
      rw [mfderiv_eq_fderiv, P.fderiv]
      rfl
    have hboundaryCast (p : N) (hp : p ∈ C.coordinates.chart.source) :
        boundaryTangentPlane C p hp =
          LinearMap.range ((inverseChartDifferential C.coordinates (C.coordinates.chart p)).comp
            levelInclusion).toLinearMap := by
      change (Eq.rec (motive := fun (_ : N)
          (_ : C.coordinates.chart.symm (C.coordinates.chart p) = _) => Submodule ℝ E3)
        (LinearMap.range ((inverseChartDifferential C.coordinates (C.coordinates.chart p)).comp
          levelInclusion).toLinearMap) (C.coordinates.chart.left_inv hp)) = _
      simp only [eq_rec_constant]
      rfl
    have hboundaryKer (p : N) (hp : p ∈ C.coordinates.chart.source) :
        boundaryTangentPlane C p hp =
          LinearMap.ker (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) C.radial p).toLinearMap := by
      rw [hboundaryCast p hp]
      ext v
      constructor
      · rintro ⟨x, rfl⟩
        change mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) C.radial p
          (inverseChartDifferential C.coordinates (C.coordinates.chart p) (levelInclusion x)) = 0
        rw [hrformula p hp]
        change (chartDifferential C.coordinates p
          (inverseChartDifferential C.coordinates (C.coordinates.chart p) (levelInclusion x))) 0 = 0
        rw [hchartComp C.coordinates p hp]
        simp [levelInclusion, coordinateVector, EuclideanSpace.single]
      · intro hv
        change mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) C.radial p v = 0 at hv
        rw [hrformula p hp] at hv
        have hproj : (chartDifferential C.coordinates p v) 0 = 0 := hv
        refine ⟨levelCoordinates (chartDifferential C.coordinates p v), ?_⟩
        apply ((NormedSpace.fromTangentSpace (C.coordinates.chart p)).bijective.comp
          ((hchartMD C.coordinates).mfderiv_bijective hp)).1
        change chartDifferential C.coordinates p
          (inverseChartDifferential C.coordinates (C.coordinates.chart p)
            (levelInclusion (levelCoordinates (chartDifferential C.coordinates p v)))) = _
        rw [hchartComp C.coordinates p hp]
        change levelInclusion (levelCoordinates (chartDifferential C.coordinates p v)) =
          chartDifferential C.coordinates p v
        ext i
        fin_cases i <;> simp [levelInclusion, levelCoordinates, coordinateVector,
          EuclideanSpace.single, hproj]
    have hdr : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) C.radial D.p ≠ 0 := by
      intro heq
      have hv := congrArg (fun f =>
        f (inverseChartDifferential C.coordinates (C.coordinates.chart D.p)
          (coordinateVector 3 0))) heq
      rw [hrformula D.p D.p_collar] at hv
      change (chartDifferential C.coordinates D.p
        (inverseChartDifferential C.coordinates (C.coordinates.chart D.p)
          (coordinateVector 3 0))) 0 = 0 at hv
      rw [hchartComp C.coordinates D.p D.p_collar] at hv
      norm_num [coordinateVector, EuclideanSpace.single] at hv
    have hplaneRank : Module.finrank ℝ D.plane = 2 := by
      have h := D.planeFrame.toLinearEquiv.finrank_eq
      simpa [E2] using h.symm
    have hambientRank : Module.finrank ℝ (TangentSpace 𝓘(ℝ, E3) D.p) = 3 := by
      let e := ((hchartMD C.coordinates).mfderiv D.p_collar).trans
        (NormedSpace.fromTangentSpace (C.coordinates.chart D.p))
      simpa [E3] using e.toLinearEquiv.finrank_eq
    have hkernelRank : Module.finrank ℝ
        (LinearMap.ker (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) C.radial D.p).toLinearMap) = 2 := by
      have hdr' : (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) C.radial D.p).toLinearMap ≠ 0 := by
        intro hz
        apply hdr
        ext v
        exact LinearMap.congr_fun hz v
      have h := Module.Dual.finrank_ker_add_one_of_ne_zero
        (V₁ := TangentSpace 𝓘(ℝ, E3) D.p) hdr'
      rw [hambientRank] at h
      exact Nat.add_right_cancel h
    have hplaneEquivalence :
        ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) C.radial D.p).comp D.plane.subtypeL ≠ 0) ↔
          D.plane ≠ boundaryTangentPlane C D.p D.p_collar := by
      rw [hboundaryKer D.p D.p_collar]
      constructor
      · intro hn heq
        apply hn
        ext v
        have hv := v.property
        have hv := (le_of_eq heq) hv
        exact hv
      · intro hne hz
        apply hne
        apply Submodule.eq_of_le_of_finrank_eq
        · intro v hv
          change mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) C.radial D.p v = 0
          exact congrArg (fun f => f ⟨v, hv⟩) hz
        · exact hplaneRank.trans hkernelRank.symm
    have hlocalDomain :
        let G := graphMap (D.graphCoordinates.chart D.p)
          ((chartDifferential D.graphCoordinates D.p).comp
            (D.plane.subtypeL.comp D.planeFrame.toContinuousLinearMap))
          (chartDifferential D.graphCoordinates D.p D.normal) D.height
        let Φ := D.graphCoordinates.chart.symm ∘ G
        ∃ a : ℝ, 0 < a ∧ a < D.delta ∧
          MapsTo Φ (D.region ∩ Metric.closedBall 0 a) C.coordinates.chart.source ∧
          (∀ x ∈ D.region ∩ Metric.closedBall 0 a, 0 ≤ C.radial (Φ x)) ∧
          (∀ x ∈ interior D.region ∩ Metric.closedBall 0 a, 0 < C.radial (Φ x)) := by
      dsimp only
      let K := D.region ∩ Metric.ball 0 D.delta
      let L := (chartDifferential D.graphCoordinates D.p).comp
        (D.plane.subtypeL.comp D.planeFrame.toContinuousLinearMap)
      let n := chartDifferential D.graphCoordinates D.p D.normal
      let G := graphMap (D.graphCoordinates.chart D.p) L n D.height
      let Φ := D.graphCoordinates.chart.symm ∘ G
      have hzero : G 0 = D.graphCoordinates.chart D.p := by
        simp [G, graphMap, D.height_zero]
      have hΦzero : Φ 0 = D.p := by
        change D.graphCoordinates.chart.symm (G 0) = D.p
        rw [hzero, D.graphCoordinates.chart.left_inv D.p_chart]
      have hG : ContinuousWithinAt G K 0 := by
        exact ((continuousWithinAt_const.add L.continuous.continuousWithinAt).add
          (D.height_flat.continuousWithinAt.smul continuousWithinAt_const))
      have hΦ : ContinuousWithinAt Φ K 0 := by
        apply ContinuousWithinAt.comp
          (D.graphCoordinates.chart.symm.continuousOn.continuousWithinAt ?_) hG
          D.graph_in_chart
        rw [hzero]
        exact D.graphCoordinates.chart.map_source D.p_chart
      have hn : Φ ⁻¹' C.coordinates.chart.source ∈ 𝓝[K] 0 :=
        hΦ.preimage_mem_nhdsWithin
          (by rw [hΦzero]; exact C.coordinates.chart.open_source.mem_nhds D.p_collar)
      obtain ⟨e, he, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hn
      let a := min e D.delta / 2
      have ha : 0 < a := half_pos (lt_min he D.delta_pos)
      have hae : a < e := (half_lt_self (lt_min he D.delta_pos)).trans_le (min_le_left _ _)
      have haδ : a < D.delta :=
        (half_lt_self (lt_min he D.delta_pos)).trans_le (min_le_right _ _)
      have hK : D.region ∩ Metric.closedBall 0 a ⊆ K := by
        intro x hx
        refine ⟨hx.1, Metric.mem_ball.mpr ?_⟩
        exact (Metric.mem_closedBall.mp hx.2).trans_lt haδ
      have hcollar : MapsTo Φ (D.region ∩ Metric.closedBall 0 a)
          C.coordinates.chart.source := by
        intro x hx
        apply hsub
        exact ⟨Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx.2).trans_lt hae), hK hx⟩
      refine ⟨a, ha, haδ, hcollar, ?_, ?_⟩
      · intro x hx
        exact (C.region_identification (Φ x) (hcollar hx)).mp (D.graph_in_manifold (hK hx))
      · intro x hx
        have hxK : x ∈ D.region ∩ Metric.closedBall 0 a := ⟨interior_subset hx.1, hx.2⟩
        have hnonneg := (C.region_identification (Φ x) (hcollar hxK)).mp
          (D.graph_in_manifold (hK hxK))
        apply lt_of_le_of_ne hnonneg
        intro heq
        have hb : Φ x ∈ frontier M :=
          (C.boundary_identification (Φ x) (hcollar hxK)).mpr heq.symm
        have hfront := D.boundary_only x (hK hxK) hb
        exact hfront.2 hx.1
    have hsphereFinite (a : ℝ) (ha : 0 < a) :
        InteriorSphereAt (D.region ∩ Metric.closedBall 0 a) 0 := by
      obtain ⟨c, R, hR, hB, hc⟩ := D.sphere_condition
      have hcn : ‖c‖ = R := by simpa [dist_zero_left] using hc
      let t := min 1 (a / (4 * R))
      have ht : 0 < t := lt_min zero_lt_one (div_pos ha (by positivity))
      have ht1 : t ≤ 1 := min_le_left _ _
      have htR : 2 * t * R < a := by
        have hbound : t ≤ a / (4 * R) := min_le_right _ _
        have hbound' := (le_div_iff₀ (show 0 < 4 * R by positivity)).mp hbound
        nlinarith
      refine ⟨t • c, t * R, mul_pos ht hR, ?_, ?_⟩
      · intro x hx
        have hdist : dist x (t • c) < t * R := Metric.mem_ball.mp hx
        have hshift : dist (t • c) c = (1 - t) * R := by
          have hsub : t • c - c = (t - 1) • c := by
            simp [sub_smul]
          rw [dist_eq_norm, hsub, norm_smul, hcn]
          rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr ht1)]
          ring
        have hxB : x ∈ Metric.ball c R := by
          apply Metric.mem_ball.mpr
          have hd := dist_triangle x (t • c) c
          rw [hshift] at hd
          nlinarith
        have hxnorm : ‖x‖ < a := by
          have hd := norm_le_norm_add_norm_sub (t • c) x
          have htc : ‖t • c‖ = t * R := by
            rw [norm_smul, hcn, Real.norm_eq_abs, abs_of_pos ht]
          rw [htc, norm_sub_rev] at hd
          rw [dist_eq_norm] at hdist
          nlinarith
        rw [interior_inter]
        exact ⟨hB hxB, Metric.ball_subset_interior_closedBall (by simpa using hxnorm)⟩
      · rw [dist_zero_left, norm_smul, hcn, Real.norm_eq_abs, abs_of_pos ht]
    have hminimalFinite (a : ℝ) (ha : a < D.delta) :
        IsMinimalParametrizationOn (actualChartTensor h D.graphCoordinates)
          (graphMap (D.graphCoordinates.chart D.p)
            ((chartDifferential D.graphCoordinates D.p).comp
              (D.plane.subtypeL.comp D.planeFrame.toContinuousLinearMap))
            (chartDifferential D.graphCoordinates D.p D.normal) D.height)
          (interior (D.region ∩ Metric.closedBall 0 a)) := by
      let G := graphMap (D.graphCoordinates.chart D.p)
        ((chartDifferential D.graphCoordinates D.p).comp
          (D.plane.subtypeL.comp D.planeFrame.toContinuousLinearMap))
        (chartDifferential D.graphCoordinates D.p D.normal) D.height
      let Φ := D.graphCoordinates.chart.symm ∘ G
      let Ω := interior (D.region ∩ Metric.closedBall 0 a)
      have hK : D.region ∩ Metric.closedBall 0 a ⊆ D.region ∩ Metric.ball 0 D.delta := by
        intro x hx
        exact ⟨hx.1, Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx.2).trans_lt ha)⟩
      have hΩ : Ω ⊆ interior D.region ∩ Metric.ball 0 D.delta := by
        intro x hx
        exact ⟨interior_mono inter_subset_left hx, (hK (interior_subset hx)).2⟩
      have heq : EqOn (D.graphCoordinates.chart ∘ Φ) G (D.region ∩ Metric.ball 0 D.delta) := by
        intro x hx
        exact D.graphCoordinates.chart.right_inv (D.graph_in_chart hx)
      have hsub : Ω ⊆ (interior D.region ∩ Metric.ball 0 D.delta) ∩
          Φ ⁻¹' D.graphCoordinates.chart.source := by
        intro x hx
        refine ⟨hΩ hx, ?_⟩
        exact D.graphCoordinates.chart.map_target (D.graph_in_chart (hK (interior_subset hx)))
      have hminimal := D.minimal_interior.2.2 D.graphCoordinates
      constructor
      · exact (hminimal.1.mono hsub).congr (fun x hx => (heq (hK (interior_subset hx))).symm)
      · intro x hx
        have he : (D.graphCoordinates.chart ∘ Φ) =ᶠ[𝓝 x] G := by
          filter_upwards [isOpen_interior.mem_nhds hx] with y hy
          exact heq (hK (interior_subset hy))
        have hfd := he.fderiv_eq (𝕜 := ℝ)
        have ht (j : Fin 2) :
            (fun z => graphTangent (D.graphCoordinates.chart ∘ Φ) z j) =ᶠ[𝓝 x]
              (fun z => graphTangent G z j) :=
          (he.fderiv (𝕜 := ℝ)).mono (fun _ hz => congrArg (fun T => T (coordinateVector 2 j)) hz)
        have hsecond (j : Fin 2) := (ht j).fderiv_eq (𝕜 := ℝ)
        have hvalue := he.eq_of_nhds
        have hacc (i j : Fin 2) :
            covariantAcceleration (actualChartTensor h D.graphCoordinates)
              (D.graphCoordinates.chart ∘ Φ) x i j =
            covariantAcceleration (actualChartTensor h D.graphCoordinates) G x i j := by
          unfold covariantAcceleration
          rw [hsecond j]
          simp only [graphTangent, hvalue, hfd]
        have hgram : inducedMetric (actualChartTensor h D.graphCoordinates)
            (D.graphCoordinates.chart ∘ Φ) x =
            inducedMetric (actualChartTensor h D.graphCoordinates) G x := by
          ext i j
          simp only [inducedMetric, graphTangent, hvalue, hfd]
        have htrace : tracedAcceleration (actualChartTensor h D.graphCoordinates)
            (D.graphCoordinates.chart ∘ Φ) x =
            tracedAcceleration (actualChartTensor h D.graphCoordinates) G x := by
          simp only [tracedAcceleration, hgram, hacc]
        have h := hminimal.2 x (hsub hx)
        rw [htrace, hfd] at h
        exact h
    have hRadialSmooth (c : SmoothAmbientChart N) :
        ContDiffOn ℝ ∞ (C.radial ∘ c.chart.symm)
          (c.chart.target ∩ c.chart.symm ⁻¹' C.coordinates.chart.source) := by
      exact (C.radial_smooth.comp (c.inverse_smooth.mono inter_subset_left)
        (fun _ hx => hx.2)).contDiffOn
    have hscalarDiff (c : SmoothAmbientChart N) (p : N) (hp : p ∈ c.chart.source)
        (hpC : p ∈ C.coordinates.chart.source) :
        (fderiv ℝ (C.radial ∘ c.chart.symm) (c.chart p)).comp (chartDifferential c p) =
          mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) C.radial p := by
      have he : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
        ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
      have hr : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ) C.radial p :=
        (C.radial_smooth.contMDiffAt (C.coordinates.chart.open_source.mem_nhds hpC)).mdifferentiableAt (by simp)
      have hcomp := mfderiv_comp_of_eq hr (he.mdifferentiableAt_symm (c.chart.map_source hp))
        (c.chart.left_inv hp)
      rw [mfderiv_eq_fderiv] at hcomp
      rw [c.chart.left_inv hp] at hcomp
      have hfd : fderiv ℝ (C.radial ∘ c.chart.symm) (c.chart p) =
          (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) C.radial p).comp (inverseChartDifferential c (c.chart p)) := by
        ext v
        exact congrArg (fun f => f v) hcomp
      ext v
      rw [ContinuousLinearMap.comp_apply, hfd]
      change mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) C.radial p
        (inverseChartDifferential c (c.chart p) (chartDifferential c p v)) = _
      have hinv : inverseChartDifferential c (c.chart p) (chartDifferential c p v) = v :=
        congrArg (fun f => f v) (he.symm_comp_deriv hp)
      rw [hinv]
      rfl
    have hmetricBridge (c : SmoothAmbientChart N) :
        (∀ a b, ContDiffOn ℝ ∞ (fun y => actualChartTensor h c y a b) c.chart.target) ∧
        (∀ y ∈ c.chart.target, ∀ a b, actualChartTensor h c y a b = actualChartTensor h c y b a) ∧
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
    have hHessianBridge (c : SmoothAmbientChart N) (y : E3) (hy : y ∈ c.chart.target)
        (hcollar : c.chart.symm y ∈ C.coordinates.chart.source)
        (hside : 0 ≤ C.radial (c.chart.symm y)) (v : E3) :
        hessianQuadratic (actualChartTensor h c) (C.radial ∘ c.chart.symm) y v ≤ 0 := by
      have hcollarSign (y : E3) (hy : y ∈ C.coordinates.chart.target)
          (hside : 0 ≤ y 0) (v : E3) :
          hessianQuadratic (actualChartTensor h C.coordinates)
            (C.radial ∘ C.coordinates.chart.symm) y v ≤ 0 := by
        have hformula : hessianQuadratic (actualChartTensor h C.coordinates)
            (fun z : E3 => z 0) y v = C.phi (y 0) * deriv C.phi (y 0) *
              (∑ i : Fin 2, ∑ j : Fin 2,
                C.levelMetric (levelCoordinates y) i j * levelVector v i * levelVector v j) := by
          have hentries : ∀ z ∈ C.coordinates.chart.target,
              actualChartTensor h C.coordinates z =
                !![1, 0, 0;
                  0, C.phi (z 0)^2 * C.levelMetric (levelCoordinates z) 0 0,
                     C.phi (z 0)^2 * C.levelMetric (levelCoordinates z) 0 1;
                  0, C.phi (z 0)^2 * C.levelMetric (levelCoordinates z) 1 0,
                     C.phi (z 0)^2 * C.levelMetric (levelCoordinates z) 1 1] := by
            intro z hz
            ext i j
            have hm := C.warped_metric z hz (coordinateVector 3 i) (coordinateVector 3 j)
            fin_cases i <;> fin_cases j <;>
              simpa [coordinateInner, coordinateVector, EuclideanSpace.single, PiLp.single_apply,
                Fin.sum_univ_succ, levelVector, levelCoordinates] using hm
          have hinvrow : ∀ j : Fin 3, (actualChartTensor h C.coordinates y)⁻¹ 0 j =
              if j = 0 then 1 else 0 := by
            have hLpos : (C.levelMetric (levelCoordinates y)).PosDef := by
              apply Matrix.PosDef.of_dotProduct_mulVec_pos
              · ext i j
                simpa only [Matrix.conjTranspose_apply, star_trivial] using
                  C.levelMetric_symmetric (levelCoordinates y) j i
              · intro ξ hξ
                let v : E2 := WithLp.toLp 2 ξ
                have hv : v ≠ 0 := by
                  intro hv
                  exact hξ (WithLp.toLp_injective 2 hv)
                have hp := C.levelMetric_positive (levelCoordinates y) v hv
                convert hp using 1
                simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, v, Fin.sum_univ_succ]
                ring
            have hphi : 0 < C.phi (y 0) :=
              C.phi_positive _ (abs_lt.mp (C.target_radial_range y hy))
            have hdet : 0 < (actualChartTensor h C.coordinates y).det := by
              have heq : (actualChartTensor h C.coordinates y).det =
                  C.phi (y 0)^4 * (C.levelMetric (levelCoordinates y)).det := by
                rw [hentries y hy, Matrix.det_fin_three, Matrix.det_fin_two]
                simp
                ring
              rw [heq]
              exact mul_pos (pow_pos hphi _) hLpos.det_pos
            have hmul := Matrix.mul_nonsing_inv (actualChartTensor h C.coordinates y)
              (isUnit_iff_ne_zero.mpr (ne_of_gt hdet))
            intro j
            have hrow := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 0 j) hmul
            simpa [Matrix.mul_apply, hentries y hy, Fin.sum_univ_succ, Matrix.one_apply, eq_comm] using hrow
          have hpartial : ∀ i j : Fin 2,
              partial3 (fun z => actualChartTensor h C.coordinates z i.succ j.succ) y 0 =
                2 * C.phi (y 0) * deriv C.phi (y 0) * C.levelMetric (levelCoordinates y) i j := by
            have hentry (z : E3) (hz : z ∈ C.coordinates.chart.target) (i j : Fin 2) :
                actualChartTensor h C.coordinates z i.succ j.succ =
                  C.phi (z 0)^2 * C.levelMetric (levelCoordinates z) i j := by
              rw [hentries z hz]
              fin_cases i <;> fin_cases j <;> rfl
            let P : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0
            let L : E3 →L[ℝ] E2 :=
              (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1).smulRight (coordinateVector 2 0) +
              (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2).smulRight (coordinateVector 2 1)
            have hL : ∀ z, L z = levelCoordinates z := fun _ => rfl
            have hLzero : L (coordinateVector 3 0) = 0 := by
              simp [L, coordinateVector, EuclideanSpace.single, PiLp.single_apply]
            intro i j
            have hgerm : (fun z => actualChartTensor h C.coordinates z i.succ j.succ) =ᶠ[𝓝 y]
                (fun z => C.phi (z 0)^2 * C.levelMetric (levelCoordinates z) i j) := by
              filter_upwards [C.coordinates.chart.open_target.mem_nhds hy] with z hz
              exact hentry z hz i j
            have hphi := ((C.phi_smooth.differentiable (by simp)) (y 0)).hasDerivAt.comp_hasFDerivAt y
              P.hasFDerivAt
            have hlevel := (((C.levelMetric_smooth i j).differentiable (by simp)) (L y)).hasFDerivAt.comp y
              L.hasFDerivAt
            have hprod := (hphi.pow 2).mul hlevel
            dsimp only [Function.comp_def, Pi.mul_apply] at hprod
            change fderiv ℝ (fun z => actualChartTensor h C.coordinates z i.succ j.succ) y
              (coordinateVector 3 0) = _
            rw [hgerm.fderiv_eq]
            change fderiv ℝ (fun z => C.phi (P z)^2 * C.levelMetric (L z) i j) y
              (coordinateVector 3 0) = _
            have heq := hprod.fderiv
            change fderiv ℝ (fun z => C.phi (P z)^2 * C.levelMetric (L z) i j) y = _ at heq
            rw [heq]
            simp [hLzero, ContinuousLinearMap.comp_apply, P, hL, levelCoordinates, coordinateVector,
              EuclideanSpace.single, PiLp.single_apply]
            ring
          have hrow (z : E3) (hz : z ∈ C.coordinates.chart.target) (j : Fin 3) :
              actualChartTensor h C.coordinates z 0 j = if j = 0 then 1 else 0 := by
            rw [hentries z hz]
            fin_cases j <;> rfl
          have hcol (z : E3) (hz : z ∈ C.coordinates.chart.target) (i : Fin 3) :
              actualChartTensor h C.coordinates z i 0 = if i = 0 then 1 else 0 := by
            rw [hentries z hz]
            fin_cases i <;> rfl
          have hdrow (i j : Fin 3) :
              partial3 (fun z => actualChartTensor h C.coordinates z 0 j) y i = 0 := by
            have hgerm : (fun z => actualChartTensor h C.coordinates z 0 j) =ᶠ[𝓝 y]
                (fun _ => if j = 0 then 1 else 0) := by
              filter_upwards [C.coordinates.chart.open_target.mem_nhds hy] with z hz
              exact hrow z hz j
            unfold partial3
            rw [hgerm.fderiv_eq]
            simp
          have hdcol (i j : Fin 3) :
              partial3 (fun z => actualChartTensor h C.coordinates z j 0) y i = 0 := by
            have hgerm : (fun z => actualChartTensor h C.coordinates z j 0) =ᶠ[𝓝 y]
                (fun _ => if j = 0 then 1 else 0) := by
              filter_upwards [C.coordinates.chart.open_target.mem_nhds hy] with z hz
              exact hcol z hz j
            unfold partial3
            rw [hgerm.fderiv_eq]
            simp
          have hChrist (a b : Fin 3) : christoffel (actualChartTensor h C.coordinates) y a b 0 =
              -(1 / 2 : ℝ) * partial3 (fun z => actualChartTensor h C.coordinates z a b) y 0 := by
            simp only [christoffel, hinvrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
              Finset.mem_univ, ite_true, hdrow]
            ring
          have hp (z : E3) (a : Fin 3) :
              partial3 (fun z : E3 => z 0) z a = if a = 0 then 1 else 0 := by
            change fderiv ℝ (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0) z (coordinateVector 3 a) = _
            rw [ContinuousLinearMap.fderiv]
            simp [coordinateVector, EuclideanSpace.single, PiLp.single_apply, eq_comm]
          have hsecond (a b : Fin 3) :
              partial3 (fun z => partial3 (fun z : E3 => z 0) z b) y a = 0 := by
            simp only [hp]
            simp [partial3]
          unfold hessianQuadratic hessianCoefficient
          simp only [hsecond]
          simp only [hp]
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          simp only [hChrist, zero_sub, neg_mul, neg_neg]
          simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hpartial ⊢
          simp only [hdrow, hdcol, mul_zero, zero_mul, zero_add, add_zero]
          have hp00 := hpartial 0 0
          have hp01 := hpartial 0 1
          have hp10 := hpartial 1 0
          have hp11 := hpartial 1 1
          norm_num at hp00 hp01 hp10 hp11
          simp only [hp00, hp01, hp10, hp11]
          simp [levelVector, levelCoordinates, coordinateVector, EuclideanSpace.single,
            PiLp.single_apply, PiLp.add_apply, PiLp.smul_apply]
          ring
        have hcongr (g : MetricTensor) (y : E3) (r s : E3 → ℝ) (v : E3)
            (hrs : r =ᶠ[𝓝 y] s) : hessianQuadratic g r y v = hessianQuadratic g s y v := by
          have hfirst : ∀ a, partial3 r y a = partial3 s y a := by
            intro a
            exact congrArg (fun D : E3 →L[ℝ] ℝ => D (coordinateVector 3 a)) hrs.fderiv_eq
          have hsecond : ∀ a b, partial3 (fun z => partial3 r z b) y a =
              partial3 (fun z => partial3 s z b) y a := by
            intro a b
            have hp : (fun z => partial3 r z b) =ᶠ[𝓝 y] (fun z => partial3 s z b) := by
              filter_upwards [hrs.eventuallyEq_nhds] with z hz
              exact congrArg (fun D : E3 →L[ℝ] ℝ => D (coordinateVector 3 b)) hz.fderiv_eq
            exact congrArg (fun D : E3 →L[ℝ] ℝ => D (coordinateVector 3 a)) hp.fderiv_eq
          simp only [hessianQuadratic, hessianCoefficient, hfirst, hsecond]
        have hgerm : C.radial ∘ C.coordinates.chart.symm =ᶠ[𝓝 y] (fun z : E3 => z 0) := by
          filter_upwards [C.coordinates.chart.open_target.mem_nhds hy] with z hz
          change C.radial (C.coordinates.chart.symm z) = z 0
          rw [C.radial_coordinate _ (C.coordinates.chart.map_target hz),
            C.coordinates.chart.right_inv hz]
        rw [hcongr _ _ _ _ _ hgerm, hformula]
        have hbound := C.target_radial_range y hy
        have hr : y 0 ∈ Ioo (-C.epsilon) C.epsilon := abs_lt.mp hbound
        have hphi : 0 < C.phi (y 0) := C.phi_positive _ hr
        have hd : deriv C.phi (y 0) ≤ 0 := C.phi_decreasing _ ⟨hside, hr.2.le⟩
        have hq : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2,
            C.levelMetric (levelCoordinates y) i j * levelVector v i * levelVector v j := by
          by_cases hv : levelVector v = 0
          · simp [hv]
          · exact (C.levelMetric_positive _ _ hv).le
        exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hphi.le hd) hq
      have htransport :
          hessianQuadratic (actualChartTensor h c) (C.radial ∘ c.chart.symm) y v =
            hessianQuadratic (actualChartTensor h C.coordinates)
              (C.radial ∘ C.coordinates.chart.symm)
              (C.coordinates.chart (c.chart.symm y))
              (fderiv ℝ (C.coordinates.chart ∘ c.chart.symm) y v) := by
        set_option maxHeartbeats 0 in
        exact (by
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
          have hScalarJet (T : E3 → E3) (y : E3) (hT : ContDiffAt ℝ ∞ T y) :
              (∀ a : Fin 3, partial3 (fun z => T z 0) y a =
                (fderiv ℝ T y (coordinateVector 3 a)) 0) ∧
              (∀ a b : Fin 3, partial3 (fun z => partial3 (fun x => T x 0) z b) y a =
                partial3 (fun z => (fderiv ℝ T z (coordinateVector 3 b)) 0) y a) := by
            have hfirst (z : E3) (hz : DifferentiableAt ℝ T z) (a : Fin 3) :
                partial3 (fun z => T z 0) z a = (fderiv ℝ T z (coordinateVector 3 a)) 0 := by
              have hp := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt.comp z hz.hasFDerivAt
              exact congrArg (fun L : E3 →L[ℝ] ℝ => L (coordinateVector 3 a)) hp.fderiv
            refine ⟨hfirst y (hT.differentiableAt (by simp)),?_⟩
            intro a b
            have hn : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ T z :=
              ((hT.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by norm_num)).mono
                (fun z hz => hz.differentiableAt (by norm_num))
            have heq : (fun z => partial3 (fun x => T x 0) z b) =ᶠ[𝓝 y]
                (fun z => (fderiv ℝ T z (coordinateVector 3 b)) 0) :=
              hn.mono (fun z hz => hfirst z hz b)
            exact congrArg (fun L : E3 →L[ℝ] ℝ => L (coordinateVector 3 a)) heq.fderiv_eq
          
          have hHessianGerm (g : MetricTensor) (r s : E3 → ℝ) (y v : E3)
              (hrs : r =ᶠ[𝓝 y] s) : hessianQuadratic g r y v = hessianQuadratic g s y v := by
            have hp (a : Fin 3) : partial3 r y a = partial3 s y a :=
              congrArg (fun L : E3 →L[ℝ] ℝ => L (coordinateVector 3 a)) hrs.fderiv_eq
            have hpp (a b : Fin 3) : partial3 (fun z => partial3 r z b) y a =
                partial3 (fun z => partial3 s z b) y a := by
              have heq : (fun z => partial3 r z b) =ᶠ[𝓝 y] (fun z => partial3 s z b) :=
                hrs.fderiv.mono (fun z hz => congrArg (fun L : E3 →L[ℝ] ℝ =>
                  L (coordinateVector 3 b)) hz)
              exact congrArg (fun L : E3 →L[ℝ] ℝ => L (coordinateVector 3 a)) heq.fderiv_eq
            simp only [hessianQuadratic,hessianCoefficient,hp,hpp]
          let T : E3 → E3 := C.coordinates.chart ∘ c.chart.symm
          let g : MetricTensor := actualChartTensor h c
          let G : MetricTensor := actualChartTensor h C.coordinates
          let J : MetricTensor := fun z k a => (fderiv ℝ T z (coordinateVector 3 a)) k
          let H : Fin 3 → Fin 3 → Fin 3 → ℝ := fun k a b => partial3 (fun z => J z k b) y a
          let dG : Fin 3 → Fin 3 → Fin 3 → ℝ := fun a i j => partial3 (fun z => G z i j) (T y) a
          let dg : Fin 3 → Fin 3 → Fin 3 → ℝ := fun a i j => partial3 (fun z => g z i j) y a
          obtain ⟨hT,hTbij,hPull⟩ := htransition h c C.coordinates y hy hcollar
          change ContDiffAt ℝ ∞ T y at hT
          change Function.Bijective (fderiv ℝ T y) at hTbij
          have hTy : T y ∈ C.coordinates.chart.target := C.coordinates.chart.map_source hcollar
          have hGdiff (i j : Fin 3) : DifferentiableAt ℝ (fun z => G z i j) (T y) :=
            (((hprops h C.coordinates).1 i j).contDiffAt
              (C.coordinates.chart.open_target.mem_nhds hTy)).differentiableAt (by simp)
          have hJdiff (k a : Fin 3) : DifferentiableAt ℝ (fun z => J z k a) y :=
            ((hJacobian T y hT).1 k a).differentiableAt (by simp)
          have hHsym (k a b : Fin 3) : H k a b = H k b a := (hJacobian T y hT).2.2 k a b
          have hGsym (i j : Fin 3) : G (T y) i j = G (T y) j i := h.symm _ _ _
          have hdGsym (a i j : Fin 3) : dG a i j = dG a j i := by
            have he : (fun z => G z i j) = (fun z => G z j i) := funext (fun _ => h.symm _ _ _)
            simp only [dG,he]
          have hEntry (i j : Fin 3) : (fun z => g z i j) =ᶠ[𝓝 y]
              (fun z => ∑ n : Fin 3, ∑ p : Fin 3, G (T z) n p * J z n i * J z p j) := by
            filter_upwards [hPull] with z hz
            have hh := hz (coordinateVector 3 i) (coordinateVector 3 j)
            simpa [g,G,T,J,coordinateInner,coordinateVector,EuclideanSpace.single,
              PiLp.single_apply] using hh
          have hdg (a l b : Fin 3) : dg a l b =
              (∑ m : Fin 3, ∑ n : Fin 3, ∑ p : Fin 3,
                dG m n p * J y m a * J y n l * J y p b) +
              ∑ n : Fin 3, ∑ p : Fin 3, G (T y) n p *
                (H n a l * J y p b + J y n l * H p a b) := by
            change fderiv ℝ (fun z => g z l b) y (coordinateVector 3 a) = _
            rw [(hEntry l b).fderiv_eq]
            exact hMetricDeriv G J T y hGdiff (hT.differentiableAt (by simp)) hJdiff a l b
          have hmetric : g y = (J y).transpose * G (T y) * J y := by
            ext i j
            change g y i j = _
            calc
              g y i j = ∑ n : Fin 3,∑ p : Fin 3,G (T y) n p * J y n i * J y p j := (hEntry i j).self_of_nhds
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
              2 * (∑ s : Fin 3, ∑ t : Fin 3, G (T y) t s * H s a b * J y t l) +
              ∑ s : Fin 3, ∑ t : Fin 3, ∑ m : Fin 3,
                (dG s m t + dG t m s - dG m s t) * J y s a * J y t b * J y m l := by
            simpa only [hGsym] using hLowerAlg (G (T y)) (J y) dG H dg hGsym hdGsym hHsym hdg a b l
          have hGamma (a b k : Fin 3) :
              (∑ i : Fin 3, J y k i * christoffel g y a b i) =
                H k a b + ∑ s : Fin 3, ∑ t : Fin 3,
                  christoffel G (T y) s t k * J y s a * J y t b := by
            exact hGammaAlg (g y) (G (T y)) (J y)
              (fun a b l => dg a l b + dg b l a - dg l a b)
              (fun s t m => dG s m t + dG t m s - dG m s t) H
              (hdet c y hy) (hdet C.coordinates (T y) hTy) hJunit hmetric hLower a b k
          have hrs : (C.radial ∘ c.chart.symm) =ᶠ[𝓝 y] (fun z => T z 0) := by
            have hn : ∀ᶠ z in 𝓝 y, c.chart.symm z ∈ C.coordinates.chart.source :=
              (c.chart.continuousAt_symm hy).preimage_mem_nhds
                (C.coordinates.chart.open_source.mem_nhds hcollar)
            exact hn.mono (fun z hz => C.radial_coordinate _ hz)
          have hrt : (C.radial ∘ C.coordinates.chart.symm) =ᶠ[𝓝 (T y)]
              (fun z : E3 => z 0) := by
            filter_upwards [C.coordinates.chart.open_target.mem_nhds hTy] with z hz
            change C.radial (C.coordinates.chart.symm z) = z 0
            rw [C.radial_coordinate _ (C.coordinates.chart.map_target hz),C.coordinates.chart.right_inv hz]
          change hessianQuadratic g (C.radial ∘ c.chart.symm) y v =
            hessianQuadratic G (C.radial ∘ C.coordinates.chart.symm) (T y) (fderiv ℝ T y v)
          rw [hHessianGerm g _ _ y v hrs,hHessianGerm G _ _ (T y) (fderiv ℝ T y v) hrt]
          have hsource (a b : Fin 3) : hessianCoefficient g (fun z => T z 0) y a b =
              -(∑ s : Fin 3, ∑ t : Fin 3,
                christoffel G (T y) s t 0 * J y s a * J y t b) := by
            rw [hessianCoefficient,(hScalarJet T y hT).2 a b]
            simp only [(hScalarJet T y hT).1]
            change H 0 a b - (∑ k : Fin 3,christoffel g y a b k * J y 0 k) = _
            have hh := hGamma a b 0
            have hcomm : (∑ k : Fin 3,christoffel g y a b k * J y 0 k) =
                ∑ k : Fin 3,J y 0 k * christoffel g y a b k := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
            rw [hcomm,hh]
            ring
          have hp (z : E3) (a : Fin 3) :
              partial3 (fun z : E3 => z 0) z a = if a = 0 then 1 else 0 := by
            change fderiv ℝ (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0) z (coordinateVector 3 a) = _
            rw [ContinuousLinearMap.fderiv]
            simp [coordinateVector,EuclideanSpace.single,PiLp.single_apply,eq_comm]
          have htarget (a b : Fin 3) : hessianCoefficient G (fun z : E3 => z 0) (T y) a b =
              -christoffel G (T y) a b 0 := by
            unfold hessianCoefficient
            simp only [hp]
            simp [partial3]
          simp only [hessianQuadratic,hsource,htarget,hrepr]
          simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
          ring
        )
      rw [htransport]
      apply hcollarSign _ (C.coordinates.chart.map_source hcollar)
      rwa [← C.radial_coordinate _ hcollar]
    have hnonzero :
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) C.radial D.p).comp D.plane.subtypeL ≠ 0 := by
      obtain ⟨a, ha, haδ, hcollar, hnonnegative, hpositive⟩ := hlocalDomain
      let c := D.graphCoordinates
      let p0 := c.chart D.p
      let L := (chartDifferential c D.p).comp
        (D.plane.subtypeL.comp D.planeFrame.toContinuousLinearMap)
      let n := chartDifferential c D.p D.normal
      let G := graphMap p0 L n D.height
      let Φ := c.chart.symm ∘ G
      let U := D.region ∩ Metric.closedBall 0 a
      let V := c.chart.target ∩ c.chart.symm ⁻¹' C.coordinates.chart.source
      let r := C.radial ∘ c.chart.symm
      have hV : IsOpen V := c.chart.symm.continuousOn.isOpen_inter_preimage
        c.chart.open_target C.coordinates.chart.open_source
      have hVK : V ⊆ c.chart.target := inter_subset_left
      let g : CoordinateMetric V := {
        tensor := actualChartTensor h c
        smooth := fun i j => ((hmetricBridge c).1 i j).mono hVK
        symmetric := fun y hy => (hmetricBridge c).2.1 y hy.1
        positive := fun y hy => (hmetricBridge c).2.2 y hy.1 }
      have hUK : U ⊆ D.region ∩ Metric.ball 0 D.delta := by
        intro x hx
        exact ⟨hx.1, Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx.2).trans_lt haδ)⟩
      have hUclosed : IsClosed U := D.region_closed.inter Metric.isClosed_closedBall
      have hUzero : (0 : E2) ∈ U := by
        refine ⟨?_, ?_⟩
        · exact D.region_closed.closure_eq ▸ D.zero_boundary.1
        · simp [Metric.mem_closedBall, ha.le]
      have hUfrontier : (0 : E2) ∈ frontier U := by
        refine ⟨subset_closure hUzero, ?_⟩
        intro hi
        exact D.zero_boundary.2 (interior_mono inter_subset_left hi)
      have hp0 : p0 ∈ V := by
        refine ⟨c.chart.map_source D.p_chart, ?_⟩
        change c.chart.symm (c.chart D.p) ∈ C.coordinates.chart.source
        rw [c.chart.left_inv D.p_chart]
        exact D.p_collar
      have hchartInjective : Injective (chartDifferential c D.p) :=
        ((NormedSpace.fromTangentSpace (c.chart D.p)).bijective.comp
          ((hchartMD c).mfderiv_bijective D.p_chart)).1
      have hn : n ≠ 0 := by
        intro hz
        apply D.normal_nonzero
        exact hchartInjective (by simpa [n] using hz)
      have hL : Injective L := hchartInjective.comp
        (Subtype.coe_injective.comp D.planeFrame.injective)
      have horth (v : E2) : coordinateInner g.tensor p0 (L v) n = 0 := by
        change coordinateInner (actualChartTensor h c) (c.chart D.p)
          (chartDifferential c D.p (D.planeFrame v)) (chartDifferential c D.p D.normal) = 0
        rw [hinnerChart c D.p D.p_chart]
        exact D.normal_orthogonal _ (D.planeFrame v).property
      have hgraph : MapsTo G U V := by
        intro x hx
        exact ⟨D.graph_in_chart (hUK hx), hcollar hx⟩
      have hminimal : IsMinimalParametrizationOn g.tensor G (interior U) := hminimalFinite a haδ
      have hrSmooth : ContDiffOn ℝ ∞ r V := hRadialSmooth c
      have hrzero : r p0 = 0 := by
        change C.radial (c.chart.symm (c.chart D.p)) = 0
        rw [c.chart.left_inv D.p_chart]
        exact (C.boundary_identification D.p D.p_collar).mp D.p_boundary
      have hrNonnegative : ∀ x ∈ U, 0 ≤ r (G x) := hnonnegative
      have hrPositive : ∀ x ∈ interior U, 0 < r (G x) := by
        intro x hx
        apply hpositive x
        exact ⟨interior_mono inter_subset_left hx, (interior_subset hx).2⟩
      have hHess : ∀ x ∈ interior U, ∀ v : E3,
          hessianQuadratic g.tensor r (G x) v ≤ 0 := by
        intro x hx v
        have hxU := interior_subset hx
        exact hHessianBridge c (G x) (hgraph hxU).1 (hgraph hxU).2 (hrNonnegative x hxU) v
      have hncoord := A4_hopf_coordinate V hV g U hUclosed hUfrontier
        (hsphereFinite a ha) p0 n hp0 hn L hL horth D.height D.height_zero
        (D.height_C1.mono hUK) (D.height_flat.mono hUK) hgraph hminimal r
        hrSmooth hrzero hrNonnegative hrPositive hHess
      intro hz
      apply hncoord
      ext v
      have hf := congrArg (fun f => f (D.planeFrame v))
        (hscalarDiff c D.p D.p_chart D.p_collar)
      change fderiv ℝ r p0 (L v) = 0
      change fderiv ℝ r p0 (L v) =
        mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) C.radial D.p (D.planeFrame v) at hf
      exact hf.trans (congrArg (fun f => f (D.planeFrame v)) hz)
    exact ⟨hnonzero, hplaneEquivalence.mp hnonzero, hplaneEquivalence⟩
  )

end SeifertSurfaces.OriginalEndpoints
