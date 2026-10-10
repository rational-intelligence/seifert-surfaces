import B1FiniteIntegerOrder_v468
import B1DensityReflection_v468
import B1SourceCore_v468
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem actual_distance_two_excludes_local_zero (D : B1OriginalData g J)
    (s : Circle) (W : CollarWindow D s)
    (hzero : ∃ U : Set E2, IsOpen U ∧ U.Nonempty ∧ U ⊆ halfDisc W.R ∧
      ∀ x ∈ U, localHeight D s x = 0) : False := by
  have himage := actual_minimizers_local_agreement_propagates D s W hzero
  have hsurface : surfaceImageOf E D.A = surfaceImageOf E D.B := Subtype.ext himage
  have hdist := D.distance_two
  rw [hsurface, SimpleGraph.dist_self] at hdist
  norm_num at hdist
theorem same_reflected_gradient_not_identically_zero (D : B1OriginalData g J)
    (s : Circle) (W : CollarWindow D s) (N : PositiveNormalization W)
    (F : BoundaryIsothermalPatch N) :
    ¬ (∀ z ∈ Metric.ball (0 : ℂ) F.targetR, F.w z = 0) := by
  intro hw
  have hopen : ∀ r : ℝ, IsOpen (halfDisc r) := by
    intro r
    exact Metric.isOpen_ball.inter (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  have hsourceR : F.sourceR < W.R := by
    have hR := N.R_inside
    have hs := F.sourceR_inside
    have hp := N.R_pos
    linarith
  have hhalfclosed : ∀ {r : ℝ}, halfDisc r ⊆ closedHalfDisc r := by
    intro r x hx
    exact ⟨Metric.ball_subset_closedBall hx.1, hx.2.le⟩
  have hcoordinate : ∀ (u : E2 → ℝ) (x : E2) (i : Fin 2),
      planarGradient u x i = fderiv ℝ u x (coordinateVector 2 i) := by
    intro u x i
    fin_cases i <;> simp [planarGradient, coordinateVector, PiLp.single_apply]
  have hd : ∀ x ∈ disc F.targetR, fderiv ℝ F.reflectedV x = 0 := by
    intro x hx
    let z : ℂ := ⟨x 0, x 1⟩
    have hpoint : complexPoint z = x := by
      ext i
      fin_cases i <;> simp [complexPoint, z]
    have hnorm : ‖z‖ = ‖x‖ := by
      rw [Complex.norm_def, EuclideanSpace.norm_eq]
      simp [z, Complex.normSq_apply, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, pow_two]
    have hz : z ∈ Metric.ball (0 : ℂ) F.targetR := by
      simpa only [disc, Metric.mem_ball, dist_zero_right, hnorm] using hx
    have hgrad : planarGradient F.reflectedV x = 0 := by
      have h := hw z hz
      have hr := congrArg Complex.re h
      have hi := congrArg Complex.im h
      ext i
      fin_cases i
      · simpa [BoundaryIsothermalPatch.w, complexGradient, hpoint] using hr
      · simpa [BoundaryIsothermalPatch.w, complexGradient, hpoint] using hi
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = ∑ i : Fin 2, v i • coordinateVector 2 i := by
      ext i
      fin_cases i <;> simp [Fin.sum_univ_two, coordinateVector, PiLp.single_apply]
    rw [hv, map_sum]
    simp only [map_smul, zero_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [← hcoordinate, hgrad]
    simp
  have hC1 := (same_boundary_odd_reflected_weak_equation D s W N F).1
  have hbase : F.reflectedV 0 = 0 := by
    have hsource0 : (0 : E2) ∈ F.chart.source := F.source_contains
      ⟨by simpa [closedDisc] using F.sourceR_pos.le, by simp⟩
    have hinverse0 : F.chart.symm 0 = 0 := by
      simpa only [F.base] using F.chart.left_inv hsource0
    simp [BoundaryIsothermalPatch.reflectedV, oddReflect, BoundaryIsothermalPatch.vhat,
      hinverse0, PositiveNormalization.v, localHeight, D.f_boundary_zero]
  have hvzero : ∀ z ∈ halfDisc F.targetR, F.vhat z = 0 := by
    intro z hz
    have hconst := (convex_ball (0 : E2) F.targetR).is_const_of_fderivWithin_eq_zero
      (hC1.differentiableOn (by norm_num))
      (fun x hx => (fderivWithin_of_isOpen Metric.isOpen_ball hx).trans (hd x hx))
      hz.1 (Metric.mem_ball_self F.targetR_pos)
    rw [hbase] at hconst
    simpa only [BoundaryIsothermalPatch.reflectedV, oddReflect, ite_eq_left hz.2.le] using hconst
  let U : Set E2 := halfDisc F.sourceR ∩ F.chart ⁻¹' halfDisc F.targetR
  have hUopen : IsOpen U :=
    (F.chart.continuousOn.mono (hhalfclosed.trans F.source_contains)).isOpen_inter_preimage
      (hopen F.sourceR) (hopen F.targetR)
  have hUne : U.Nonempty := by
    let z : E2 := (F.targetR / 2) • coordinateVector 2 1
    have hz : z ∈ halfDisc F.targetR := by
      constructor
      · rw [disc, Metric.mem_ball, dist_zero_right]
        simp only [z, norm_smul, Real.norm_eq_abs]
        have hn : ‖coordinateVector 2 1‖ = 1 := by
          simp [coordinateVector, EuclideanSpace.single, PiLp.norm_single]
        rw [hn, mul_one, abs_of_pos (half_pos F.targetR_pos)]
        linarith [F.targetR_pos]
      · simpa [z, coordinateVector, PiLp.single_apply] using half_pos F.targetR_pos
    refine ⟨F.chart.symm z, F.inverse_interior z hz, ?_⟩
    change F.chart (F.chart.symm z) ∈ halfDisc F.targetR
    simpa only [F.chart.right_inv (F.target_contains (hhalfclosed hz))] using hz
  apply actual_distance_two_excludes_local_zero D s W
  refine ⟨U, hUopen, hUne, ?_, ?_⟩
  · intro x hx
    exact ⟨Metric.ball_subset_ball hsourceR.le hx.1.1, hx.1.2⟩
  · intro x hx
    have hv := hvzero (F.chart x) hx.2
    have hxs := F.source_contains (hhalfclosed hx.1)
    have hin : x ∈ closedHalfDisc N.R := by
      refine ⟨Metric.ball_subset_closedBall (Metric.ball_subset_ball ?_ hx.1.1), hx.1.2.le⟩
      have := F.sourceR_inside
      have := N.R_pos
      linarith
    have hh : N.h x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (N.h_lower_bound x hin))
    have heq : F.chart.symm (F.chart x) = x := F.chart.left_inv hxs
    simp only [BoundaryIsothermalPatch.vhat, PositiveNormalization.v, heq] at hv
    exact (div_eq_zero_iff).mp hv |>.resolve_right hh


set_option maxHeartbeats 1500000 in
/-- Integer-order estimates transported to the supplied local difference,
including the h-gradient error term and strict positivity on a punctured
closed half-neighbourhood. No DF derivative beyond C1 is used. -/

theorem finite_order_transport_to_same_difference (D : B1OriginalData g J)
    (s : Circle) (W : CollarWindow D s) (N : PositiveNormalization W)
    (F : BoundaryIsothermalPatch N) (S : SimilarityFactorization F.targetR F.w)
    (hcritical : mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
      (fun p : Circle × ℝ => D.f p.1 p.2) (s, 0) = 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ delta c1 c2 C : ℝ,
      0 < delta ∧ delta < F.sourceR ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < C ∧
      ∀ x ∈ closedHalfDisc delta, x ≠ 0 →
        c1 * ‖x‖ ^ m - c2 * ‖x‖ ^ (m + 1) ≤ ‖planarGradient (localHeight D s) x‖ ∧
        0 < c1 * ‖x‖ ^ m - c2 * ‖x‖ ^ (m + 1) ∧
        |localHeight D s x| ≤ C * ‖x‖ ^ (m + 1) := by
  have critical_local_height_derivative (D : B1OriginalData g J) (s : Circle)
      (hcritical : mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
        (fun p : Circle × ℝ => D.f p.1 p.2) (s, 0) = 0) :
      fderiv ℝ (localHeight D s) 0 = 0 := by
    let c : E2 → Circle × ℝ := fun x => (localCircle D s (x 0), x 1)
    have hc0 : c 0 = (s, 0) := by simp [c, localCircle]
    have hc : ContMDiff 𝓘(ℝ, E2) ((𝓡 1).prod 𝓘(ℝ)) ∞ c := by
      apply ContMDiff.prodMk
      · change ContMDiff 𝓘(ℝ, E2) (𝓡 1) ∞ (fun x : E2 => s * Circle.exp (2 * Real.pi * x 0 / D.leafLength))
        apply ContMDiff.mul contMDiff_const
        apply contMDiff_circleExp.comp
        apply ContDiff.contMDiff
        fun_prop
      · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.contMDiff
    have hmem : (s, (0 : ℝ)) ∈ D.extendedDomain :=
      D.extendedDomain_contains ⟨le_rfl, D.r0_pos.le⟩
    have hf := (D.f_smooth.contMDiffAt (D.extendedDomain_open.mem_nhds hmem)).mdifferentiableAt (by simp)
    have hdf : HasMFDerivAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
        (fun p : Circle × ℝ => D.f p.1 p.2) (c 0) 0 := by
      rw [hc0]
      simpa only [hcritical] using hf.hasMFDerivAt
    have hcomp := hdf.comp 0 ((hc.mdifferentiable (by simp)) 0).hasMFDerivAt
    have hmder := hcomp.mfderiv
    have hfun : (fun p : Circle × ℝ => D.f p.1 p.2) ∘ c = localHeight D s := by
      funext x
      rfl
    rw [hfun] at hmder
    have hmder0 := hmder
    rw [ContinuousLinearMap.zero_comp] at hmder0
    rw [mfderiv_eq_fderiv] at hmder0
    apply ContinuousLinearMap.ext
    intro v
    have hvalue := congrArg
      (fun L => (NormedSpace.fromTangentSpace (𝕜 := ℝ) (localHeight D s (0 : E2)))
        (L ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : E2)).symm v))) hmder0
    convert hvalue using 1 <;> rfl

  have critical_normalized_derivative (D : B1OriginalData g J) (s : Circle)
      (W : CollarWindow D s) (N : PositiveNormalization W)
      (hcritical : mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
        (fun p : Circle × ℝ => D.f p.1 p.2) (s, 0) = 0) :
      fderiv ℝ N.v 0 = 0 := by
    have hzW : (0 : E2) ∈ closedHalfDisc W.R :=
      ⟨by simpa [closedDisc] using W.R_pos.le, by simp⟩
    have hzN : (0 : E2) ∈ closedHalfDisc N.R :=
      ⟨by simpa [closedDisc] using N.R_pos.le, by simp⟩
    have hzNhalf : (0 : E2) ∈ closedHalfDisc (N.R / 2) :=
      ⟨by simpa [closedDisc] using (half_pos N.R_pos).le, by simp⟩
    have hf : DifferentiableAt ℝ (localHeight D s) 0 :=
      (W.height_smooth.contDiffAt (W.U_open.mem_nhds (W.U_contains hzW))).differentiableAt (by simp)
    have hh : DifferentiableAt ℝ N.h 0 :=
      (N.h_smooth_near_base.contDiffAt (N.N_open.mem_nhds (N.N_contains hzNhalf))).differentiableAt (by simp)
    have hn : N.h 0 ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (N.h_lower_bound 0 hzN))
    have hf0 : localHeight D s 0 = 0 := by simp [localHeight, D.f_boundary_zero]
    have hd := critical_local_height_derivative D s hcritical
    change fderiv ℝ (fun x => localHeight D s x / N.h x) 0 = 0
    simp only [div_eq_mul_inv]
    simpa only [Pi.inv_apply, hd, hf0, zero_smul, smul_zero, add_zero] using
      fderiv_fun_mul hf (hh.inv hn)

  have closedHalfDisc_uniqueDiff (r : ℝ) (hr : 0 < r) :
      UniqueDiffOn ℝ (closedHalfDisc r) := by
    have hconv : Convex ℝ (closedHalfDisc r) := by
      exact (convex_closedBall (0 : E2) r).inter
        ((convex_Ici (0 : ℝ)).linear_preimage (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).toLinearMap)
    have hopen : IsOpen (halfDisc r) :=
      Metric.isOpen_ball.inter (isOpen_lt continuous_const
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
    have hsub : halfDisc r ⊆ closedHalfDisc r := fun x hx =>
      ⟨Metric.ball_subset_closedBall hx.1, hx.2.le⟩
    apply uniqueDiffOn_convex hconv
    refine ⟨(r / 2) • coordinateVector 2 1, interior_mono hsub ?_⟩
    rw [hopen.interior_eq]
    constructor
    · rw [disc, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
      have hn : ‖coordinateVector 2 1‖ = 1 := by
        simp [coordinateVector, EuclideanSpace.single, PiLp.norm_single]
      rw [hn, mul_one, abs_of_pos (half_pos hr)]
      linarith
    · simpa [coordinateVector, PiLp.single_apply] using half_pos hr

  have differentiableAt_of_jacobian_det {f : E2 → E2} {x : E2}
      (hdet : Matrix.det (jacobian f x) ≠ 0) : DifferentiableAt ℝ f x := by
    by_contra h
    apply hdet
    have hz := fderiv_zero_of_not_differentiableAt h
    change Matrix.det (fun i j : Fin 2 => (fderiv ℝ f x (coordinateVector 2 j)) i) = 0
    rw [hz]
    change Matrix.det (0 : Matrix (Fin 2) (Fin 2) ℝ) = 0
    exact Matrix.det_zero

  have critical_reflected_gradient (D : B1OriginalData g J) (s : Circle)
      (W : CollarWindow D s) (N : PositiveNormalization W) (F : BoundaryIsothermalPatch N)
      (hcritical : mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
        (fun p : Circle × ℝ => D.f p.1 p.2) (s, 0) = 0) : F.w 0 = 0 := by
    have hzS : (0 : E2) ∈ closedHalfDisc F.sourceR :=
      ⟨by simpa [closedDisc] using F.sourceR_pos.le, by simp⟩
    have hzT : (0 : E2) ∈ closedHalfDisc F.targetR :=
      ⟨by simpa [closedDisc] using F.targetR_pos.le, by simp⟩
    have hi0 : F.chart.symm 0 = 0 := by
      simpa only [F.base] using F.chart.left_inv (F.source_contains hzS)
    have hinv := differentiableAt_of_jacobian_det (F.inverse_det 0 (F.target_contains hzT))
    have hzW : (0 : E2) ∈ closedHalfDisc W.R :=
      ⟨by simpa [closedDisc] using W.R_pos.le, by simp⟩
    have hzN : (0 : E2) ∈ closedHalfDisc N.R :=
      ⟨by simpa [closedDisc] using N.R_pos.le, by simp⟩
    have hzNhalf : (0 : E2) ∈ closedHalfDisc (N.R / 2) :=
      ⟨by simpa [closedDisc] using (half_pos N.R_pos).le, by simp⟩
    have hf : DifferentiableAt ℝ (localHeight D s) 0 :=
      (W.height_smooth.contDiffAt (W.U_open.mem_nhds (W.U_contains hzW))).differentiableAt (by simp)
    have hh : DifferentiableAt ℝ N.h 0 :=
      (N.h_smooth_near_base.contDiffAt (N.N_open.mem_nhds (N.N_contains hzNhalf))).differentiableAt (by simp)
    have hn : N.h 0 ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (N.h_lower_bound 0 hzN))
    have hv : DifferentiableAt ℝ N.v 0 := by
      change DifferentiableAt ℝ (fun x => localHeight D s x / N.h x) 0
      simp only [div_eq_mul_inv]
      exact hf.mul (hh.inv hn)
    have hvder : HasFDerivAt N.v (0 : E2 →L[ℝ] ℝ) (F.chart.symm 0) := by
      rw [hi0]
      simpa only [critical_normalized_derivative D s W N hcritical] using hv.hasFDerivAt
    have hvhat : HasFDerivAt F.vhat (0 : E2 →L[ℝ] ℝ) 0 := by
      convert hvder.comp 0 hinv.hasFDerivAt using 1
      · rfl
      · exact (ContinuousLinearMap.zero_comp _).symm
    have heq : EqOn F.reflectedV F.vhat (closedHalfDisc F.targetR) := by
      intro x hx
      simp only [BoundaryIsothermalPatch.reflectedV, oddReflect, if_pos hx.2]
    have hrefl := hvhat.hasFDerivWithinAt.congr' heq hzT
    have hC1 := (same_boundary_odd_reflected_weak_equation D s W N F).1
    have hrd := (hC1.contDiffAt (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self F.targetR_pos))).differentiableAt (by norm_num)
    have hd : fderiv ℝ F.reflectedV 0 = 0 :=
      (closedHalfDisc_uniqueDiff F.targetR F.targetR_pos 0 hzT).eq
        hrd.hasFDerivAt.hasFDerivWithinAt hrefl
    have hcp : complexPoint (0 : ℂ) = 0 := by ext i; fin_cases i <;> simp [complexPoint]
    simp [BoundaryIsothermalPatch.w, complexGradient, hcp, planarGradient, hd]

  have planarGradient_norm (u : E2 → ℝ) (x : E2) :
      ‖planarGradient u x‖ = ‖fderiv ℝ u x‖ := by
    have heq : innerSL ℝ (planarGradient u x) = fderiv ℝ u x := by
      apply ContinuousLinearMap.ext
      intro y
      have hy : y = ∑ i : Fin 2, y i • coordinateVector 2 i := by
        ext i
        fin_cases i <;> simp [Fin.sum_univ_two, coordinateVector]
      rw [hy]
      simp only [map_sum, map_smul]
      congr 1
      funext i
      congr 1
      simp [innerSL_apply_apply, EuclideanSpace.inner_eq_star_dotProduct,
        planarGradient, coordinateVector, dotProduct, Fin.sum_univ_two]
      fin_cases i <;> simp
    rw [← heq, innerSL_apply_norm]

  have closedHalfDisc_compact (r : ℝ) : IsCompact (closedHalfDisc r) :=
    (isCompact_closedBall (0 : E2) r).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)

  have derivative_bound_halfDisc {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
      {u : E2 → G} {r : ℝ} (hr : 0 < r)
      (hu : ContDiffOn ℝ 1 u (closedHalfDisc r))
      (hd : ∀ x ∈ closedHalfDisc r, DifferentiableAt ℝ u x) :
      ∃ C : ℝ, 0 < C ∧ ∀ x ∈ closedHalfDisc r, ‖fderiv ℝ u x‖ ≤ C := by
    have hc : ContinuousOn (fderiv ℝ u) (closedHalfDisc r) :=
      (hu.continuousOn_fderivWithin (closedHalfDisc_uniqueDiff r hr) le_rfl).congr
        (fun x hx => ((hd x hx).fderivWithin (closedHalfDisc_uniqueDiff r hr x hx)).symm)
    obtain ⟨C, hC⟩ := (closedHalfDisc_compact r).exists_bound_of_continuousOn hc
    exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
      fun x hx => (hC x hx).trans (le_max_left _ _)⟩

  have complexGradient_norm (u : E2 → ℝ) (z : ℂ) :
      ‖complexGradient u z‖ = ‖fderiv ℝ u (complexPoint z)‖ := by
    rw [← planarGradient_norm]
    rw [Complex.norm_def, EuclideanSpace.norm_eq]
    congr 1
    simp [complexGradient, Complex.normSq_apply, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, pow_two]

  have complexPoint_norm (z : ℂ) : ‖complexPoint z‖ = ‖z‖ := by
    rw [Complex.norm_def, EuclideanSpace.norm_eq]
    simp [complexPoint, Complex.normSq_apply, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, pow_two]

  have reflected_finite_scalar_bound (D : B1OriginalData g J) (s : Circle)
      (W : CollarWindow D s) (N : PositiveNormalization W) (F : BoundaryIsothermalPatch N)
      (m : ℕ) (d C : ℝ) (hd : 0 < d) (hdR : d < F.targetR) (hC : 0 < C)
      (hb : ∀ z ∈ Metric.ball (0 : ℂ) d, ‖F.w z‖ ≤ C * ‖z‖ ^ m) :
      ∀ z ∈ disc d, |F.reflectedV z| ≤ C * ‖z‖ ^ (m + 1) := by
    have hdiff : ∀ z ∈ disc F.targetR, DifferentiableAt ℝ F.reflectedV z := by
      intro z hz
      exact ((same_boundary_odd_reflected_weak_equation D s W N F).1.contDiffAt
        (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by norm_num)
    have hbase : F.reflectedV 0 = 0 := by
      have hsource0 : (0 : E2) ∈ F.chart.source := F.source_contains
        ⟨by simpa [closedDisc] using F.sourceR_pos.le, by simp⟩
      have hi0 : F.chart.symm 0 = 0 := by
        simpa only [F.base] using F.chart.left_inv hsource0
      simp [BoundaryIsothermalPatch.reflectedV, oddReflect, BoundaryIsothermalPatch.vhat,
        hi0, PositiveNormalization.v, localHeight, D.f_boundary_zero]
    have hbound : ∀ x ∈ disc d, ‖fderiv ℝ F.reflectedV x‖ ≤ C * ‖x‖ ^ m := by
      intro x hx
      let z : ℂ := ⟨x 0, x 1⟩
      have hp : complexPoint z = x := by ext i; fin_cases i <;> simp [complexPoint, z]
      have hn : ‖z‖ = ‖x‖ := by simpa only [hp] using (complexPoint_norm z).symm
      have h := hb z (by simpa only [disc, Metric.mem_ball, dist_zero_right, hn] using hx)
      simpa only [BoundaryIsothermalPatch.w, complexGradient_norm, hp, hn] using h
    intro z hz
    have hsub : Metric.closedBall (0 : E2) ‖z‖ ⊆ disc d := by
      intro x hx
      exact (Metric.mem_closedBall.mp hx).trans_lt (by simpa only [disc, Metric.mem_ball, dist_zero_right] using hz)
    have hnorm := (convex_closedBall (0 : E2) ‖z‖).norm_image_sub_le_of_norm_fderiv_le
      (fun x hx => hdiff x (Metric.ball_subset_ball hdR.le (hsub hx)))
      (fun x hx => (hbound x (hsub hx)).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (by simpa using hx) m) hC.le))
      (Metric.mem_closedBall_self (norm_nonneg z)) (by simp : z ∈ Metric.closedBall (0 : E2) ‖z‖)
    simpa only [hbase, sub_zero, Real.norm_eq_abs, pow_succ, mul_assoc] using hnorm

  have normalized_differentiable (D : B1OriginalData g J) (s : Circle)
      (W : CollarWindow D s) (N : PositiveNormalization W) {x : E2}
      (hx : x ∈ closedHalfDisc (N.R / 2)) : DifferentiableAt ℝ N.v x := by
    have hxW : x ∈ closedHalfDisc W.R := by
      refine ⟨Metric.closedBall_subset_closedBall ?_ hx.1, hx.2⟩
      have := N.R_inside
      have := N.R_pos
      linarith
    have hxN : x ∈ closedHalfDisc N.R :=
      ⟨Metric.closedBall_subset_closedBall (by linarith [N.R_pos]) hx.1, hx.2⟩
    have hf := (W.height_smooth.contDiffAt
      (W.U_open.mem_nhds (W.U_contains hxW))).differentiableAt (by simp)
    have hh := (N.h_smooth_near_base.contDiffAt
      (N.N_open.mem_nhds (N.N_contains hx))).differentiableAt (by simp)
    have hn : N.h x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (N.h_lower_bound x hxN))
    change DifferentiableAt ℝ (fun x => localHeight D s x / N.h x) x
    simp only [div_eq_mul_inv]
    exact hf.mul (hh.inv hn)

  have reflected_derivative_inverse_chain (D : B1OriginalData g J) (s : Circle)
      (W : CollarWindow D s) (N : PositiveNormalization W) (F : BoundaryIsothermalPatch N)
      {z : E2} (hz : z ∈ halfDisc F.targetR ∪ flatArc F.targetR) :
      fderiv ℝ F.reflectedV z =
        (fderiv ℝ N.v (F.chart.symm z)).comp (fderiv ℝ F.chart.symm z) := by
    have hzdisc : z ∈ disc F.targetR := hz.elim And.left And.left
    have hzpos : 0 ≤ z 1 := hz.elim (fun h => h.2.le) (fun h => h.2.ge)
    have hzt : z ∈ closedHalfDisc F.targetR := ⟨Metric.ball_subset_closedBall hzdisc, hzpos⟩
    have hxs := F.inverse_half_disc z hzt
    have hxn : F.chart.symm z ∈ closedHalfDisc (N.R / 2) :=
      ⟨Metric.closedBall_subset_closedBall F.sourceR_inside.le hxs.1, hxs.2⟩
    have hdv := normalized_differentiable D s W N hxn
    have hdi := differentiableAt_of_jacobian_det (F.inverse_det z (F.target_contains hzt))
    have hcomp := hdv.hasFDerivAt.comp z hdi.hasFDerivAt
    have hwithin : HasFDerivWithinAt F.reflectedV
        ((fderiv ℝ N.v (F.chart.symm z)).comp (fderiv ℝ F.chart.symm z))
        (closedHalfDisc F.targetR) z := by
      apply hcomp.hasFDerivWithinAt.congr'
      · intro y hy
        simp only [BoundaryIsothermalPatch.reflectedV, oddReflect, ite_eq_left hy.2,
          BoundaryIsothermalPatch.vhat, Function.comp_apply]
      · exact hzt
    have hrd := ((same_boundary_odd_reflected_weak_equation D s W N F).1.contDiffAt
      (Metric.isOpen_ball.mem_nhds hzdisc)).differentiableAt (by norm_num)
    exact (closedHalfDisc_uniqueDiff F.targetR F.targetR_pos z hzt).eq
      hrd.hasFDerivAt.hasFDerivWithinAt hwithin

  obtain ⟨m, hm, d, l, u, hd, hdR, hl, hu, hb⟩ :=
    (similarity_finite_integer_order F.targetR F.targetR_pos F.w S
      (critical_reflected_gradient D s W N F hcritical)).resolve_left
      (same_reflected_gradient_not_identically_zero D s W N F)
  obtain ⟨I, hI, hIbound⟩ := derivative_bound_halfDisc F.targetR_pos
    (F.inverse_C1.mono F.target_contains)
    (fun z hz => differentiableAt_of_jacobian_det (F.inverse_det z (F.target_contains hz)))
  obtain ⟨lo, hi, hlo, hhi, hbi⟩ := F.biLipschitz
  have hsourceN : closedHalfDisc F.sourceR ⊆ closedHalfDisc (N.R / 2) :=
    fun x hx => ⟨Metric.closedBall_subset_closedBall F.sourceR_inside.le hx.1, hx.2⟩
  have hhd : ∀ x ∈ closedHalfDisc F.sourceR, DifferentiableAt ℝ N.h x := by
    intro x hx
    exact (N.h_smooth_near_base.contDiffAt
      (N.N_open.mem_nhds (N.N_contains (hsourceN hx)))).differentiableAt (by simp)
  obtain ⟨H0, hH0⟩ := (closedHalfDisc_compact F.sourceR).exists_bound_of_continuousOn
    (N.h_smooth_near_base.continuousOn.mono (hsourceN.trans N.N_contains))
  let H := max H0 1
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hHbound : ∀ x ∈ closedHalfDisc F.sourceR, |N.h x| ≤ H := by
    intro x hx
    exact (hH0 x hx).trans (le_max_left _ _)
  obtain ⟨Dh, hDh, hDhbound⟩ := derivative_bound_halfDisc F.sourceR_pos
    ((N.h_smooth_near_base.of_le (by simp)).mono (hsourceN.trans N.N_contains)) hhd
  let e := min (F.sourceR / 2) (d / (2 * hi))
  have he : 0 < e := lt_min (half_pos F.sourceR_pos) (div_pos hd (mul_pos (by norm_num) hhi))
  have heS : e < F.sourceR := (min_le_left _ _).trans_lt (by linarith [F.sourceR_pos])
  have hied : hi * e < d := by
    have h := min_le_right (F.sourceR / 2) (d / (2 * hi))
    have hh : e * (2 * hi) ≤ d := (le_div_iff₀ (mul_pos (by norm_num) hhi)).mp h
    have hp := mul_pos hhi he
    nlinarith
  let V := u * hi ^ (m + 1)
  have hV : 0 < V := mul_pos hu (pow_pos hhi _)
  let a := l * lo ^ m / (2 * I)
  have ha : 0 < a := div_pos (mul_pos hl (pow_pos hlo _)) (mul_pos (by norm_num) hI)
  let b := V * Dh
  have hbpos : 0 < b := mul_pos hV hDh
  have hzS : (0 : E2) ∈ closedHalfDisc F.sourceR :=
    ⟨by simpa [closedDisc] using F.sourceR_pos.le, by simp⟩
  have hpre : ∀ x ∈ closedHalfDisc e,
      a * ‖x‖ ^ m - b * ‖x‖ ^ (m + 1) ≤ ‖planarGradient (localHeight D s) x‖ ∧
      |localHeight D s x| ≤ H * V * ‖x‖ ^ (m + 1) := by
    intro x hx
    have hxs : x ∈ closedHalfDisc F.sourceR :=
      ⟨Metric.closedBall_subset_closedBall heS.le hx.1, hx.2⟩
    have hxnorm : ‖x‖ ≤ e := by simpa [closedDisc] using hx.1
    have hxdisc : x ∈ disc F.sourceR := by simpa [disc] using hxnorm.trans_lt heS
    have hxh : x ∈ closedHalfDisc N.R :=
      ⟨Metric.closedBall_subset_closedBall (by linarith [F.sourceR_inside, N.R_pos]) hxs.1, hx.2⟩
    have hhpos : 0 < N.h x := lt_of_lt_of_le (by norm_num) (N.h_lower_bound x hxh)
    have hnv : DifferentiableAt ℝ N.v x := normalized_differentiable D s W N (hsourceN hxs)
    let z := F.chart x
    have hzx : F.chart.symm z = x := F.chart.left_inv (F.source_contains hxs)
    have hnormbounds : lo * ‖x‖ ≤ ‖z‖ ∧ ‖z‖ ≤ hi * ‖x‖ := by
      simpa only [F.base, dist_zero_right] using hbi x hxs 0 hzS
    have hzdisc : z ∈ disc d := by
      have hzlt := hnormbounds.2.trans_lt ((mul_le_mul_of_nonneg_left hxnorm hhi.le).trans_lt hied)
      simpa only [disc, Metric.mem_ball, dist_zero_right] using hzlt
    have hzR : z ∈ disc F.targetR := Metric.ball_subset_ball hdR.le hzdisc
    have hzpos : 0 ≤ z 1 := by
      by_cases hx0 : x 1 = 0
      · exact ((F.forward_boundary x hxs).mpr hx0).ge
      · exact (F.forward_interior x ⟨hxdisc, lt_of_le_of_ne hx.2 (Ne.symm hx0)⟩).le
    have hzt : z ∈ closedHalfDisc F.targetR := ⟨Metric.ball_subset_closedBall hzR, hzpos⟩
    have hzunion : z ∈ halfDisc F.targetR ∪ flatArc F.targetR := by
      rcases lt_or_eq_of_le hzpos with hpos | heq
      · exact Or.inl ⟨hzR, hpos⟩
      · exact Or.inr ⟨hzR, heq.symm⟩
    have hrefval : F.reflectedV z = N.v x := by
      simp only [BoundaryIsothermalPatch.reflectedV, oddReflect, ite_eq_left hzpos,
        BoundaryIsothermalPatch.vhat, hzx]
    have hvbound : |N.v x| ≤ V * ‖x‖ ^ (m + 1) := by
      have hs := reflected_finite_scalar_bound D s W N F m d u hd hdR hu
        (fun z hz => (hb z hz).2) z hzdisc
      rw [hrefval] at hs
      apply hs.trans
      calc
        u * ‖z‖ ^ (m + 1) ≤ u * (hi * ‖x‖) ^ (m + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnormbounds.2 _) hu.le
        _ = V * ‖x‖ ^ (m + 1) := by simp only [V, mul_pow, mul_assoc]
    have hlowref : l * (lo * ‖x‖) ^ m ≤ ‖fderiv ℝ F.reflectedV z‖ := by
      let c : ℂ := ⟨z 0, z 1⟩
      have hcp : complexPoint c = z := by ext i; fin_cases i <;> simp [complexPoint, c]
      have hcn : ‖c‖ = ‖z‖ := by simpa only [hcp] using (complexPoint_norm c).symm
      have h := (hb c (by simpa only [disc, Metric.mem_ball, dist_zero_right, hcn] using hzdisc)).1
      have h' : l * ‖z‖ ^ m ≤ ‖fderiv ℝ F.reflectedV z‖ := by
        simpa only [BoundaryIsothermalPatch.w, complexGradient_norm, hcp, hcn] using h
      exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg hlo.le (norm_nonneg _)) hnormbounds.1 m) hl.le).trans h'
    have hchain := reflected_derivative_inverse_chain D s W N F hzunion
    rw [hzx] at hchain
    have hrefupper : ‖fderiv ℝ F.reflectedV z‖ ≤ ‖fderiv ℝ N.v x‖ * I := by
      rw [hchain]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (hIbound z hzt) (norm_nonneg _))
    have hlownv : a * ‖x‖ ^ m ≤ N.h x * ‖fderiv ℝ N.v x‖ := by
      have h := hlowref.trans hrefupper
      rw [mul_pow] at h
      have haeq : a * (2 * I) = l * lo ^ m := by
        exact div_mul_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) hI))
      have hlower := N.h_lower_bound x hxh
      have hnorm := norm_nonneg (fderiv ℝ N.v x)
      have hmul : (1 / 2 : ℝ) * ‖fderiv ℝ N.v x‖ ≤ N.h x * ‖fderiv ℝ N.v x‖ :=
        mul_le_mul_of_nonneg_right hlower hnorm
      have hdivide : a * ‖x‖ ^ m ≤ (1 / 2 : ℝ) * ‖fderiv ℝ N.v x‖ := by
        have haeqpow := congrArg (fun t : ℝ => t * ‖x‖ ^ m) haeq
        nlinarith
      exact hdivide.trans hmul
    have hprod : (fun y => N.h y * N.v y) =ᶠ[𝓝 x] localHeight D s := by
      filter_upwards [(hhd x hxs).continuousAt.eventually_ne (ne_of_gt hhpos)] with y hy
      dsimp [PositiveNormalization.v]
      exact mul_div_cancel₀ _ hy
    have hderprod := hprod.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_fun_mul (hhd x hxs) hnv] at hderprod
    have hnormlower : N.h x * ‖fderiv ℝ N.v x‖ - |N.v x| * ‖fderiv ℝ N.h x‖ ≤
        ‖fderiv ℝ (localHeight D s) x‖ := by
      have h := norm_sub_norm_le (N.h x • fderiv ℝ N.v x)
        (-N.v x • fderiv ℝ N.h x)
      simpa only [neg_smul, sub_neg_eq_add, norm_neg, norm_smul, Real.norm_eq_abs, abs_neg,
        abs_of_pos hhpos, hderprod] using h
    have herr : |N.v x| * ‖fderiv ℝ N.h x‖ ≤ b * ‖x‖ ^ (m + 1) := by
      calc
        _ ≤ (V * ‖x‖ ^ (m + 1)) * Dh :=
          mul_le_mul hvbound (hDhbound x hxs) (norm_nonneg _) (by positivity)
        _ = b * ‖x‖ ^ (m + 1) := by dsimp [b]; ring
    constructor
    · rw [planarGradient_norm]
      linarith
    · have hvprod : localHeight D s x = N.h x * N.v x := (hprod.eq_of_nhds).symm
      rw [hvprod, abs_mul]
      calc
        _ ≤ H * (V * ‖x‖ ^ (m + 1)) := mul_le_mul (hHbound x hxs) hvbound (abs_nonneg _) hH.le
        _ = H * V * ‖x‖ ^ (m + 1) := by ring
  let delta := min e (a / (2 * b))
  have hdelta : 0 < delta := lt_min he (div_pos ha (mul_pos (by norm_num) hbpos))
  refine ⟨m, hm, delta, a, b, H * V, hdelta,
    (min_le_left _ _).trans_lt heS, ha, hbpos, mul_pos hH hV, ?_⟩
  intro x hx hne
  have hxe : x ∈ closedHalfDisc e :=
    ⟨Metric.closedBall_subset_closedBall (min_le_left _ _) hx.1, hx.2⟩
  obtain ⟨hgrad, hval⟩ := hpre x hxe
  refine ⟨hgrad, ?_, hval⟩
  have hxnorm : ‖x‖ ≤ delta := by simpa [closedDisc] using hx.1
  have hnormpos := norm_pos_iff.mpr hne
  have hsmall : b * ‖x‖ < a := by
    have h := (le_div_iff₀ (mul_pos (by norm_num) hbpos)).mp
      (hxnorm.trans (min_le_right _ _))
    nlinarith
  rw [pow_succ]
  nlinarith [mul_pos (sub_pos.mpr hsmall) (pow_pos hnormpos m)]
end SeifertSurfaces.OriginalEndpoints.B1Tangency
