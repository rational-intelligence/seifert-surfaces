import B1InteriorChartTranslation_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- A local normalized isothermal chart is constructed from the original
coefficient data on a compact ball.  The artificial half-domain is translated
so the actual working point lies in its interior. -/
theorem native_interior_normalized_chart_exists_v475
    (N : InteriorNormalizationData_v475) (p : E2) (hp : p ∈ N.O) :
    ∃ F : NativeInteriorChart_v475, ∃ R : ℝ,
      0 < R ∧ p ∈ F.chart.source ∧ F.chart.source ⊆ N.O ∧
      F.chart.target = disc R ∧ BoundedOn (F.bhat N.normalizedB) F.chart.target ∧
      (∀ z ∈ F.chart.target, densityLeading N.normalizedA F.chart (F.chart.symm z) = 1) := by
  classical
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp N.isOpen_O p hp
  let δ := ε/2
  have hδ : 0 < δ := half_pos hε
  let K := Metric.closedBall p δ
  have hKO : K ⊆ N.O := by
    intro x hx
    apply hball
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by dsimp [δ]; linarith)
  obtain ⟨hE,hLip,hB,hDet,hFactor⟩ := native_interior_normalized_coefficients_v475 N K
    (isCompact_closedBall _ _) (convex_closedBall _ _) ⟨p,Metric.mem_closedBall_self hδ.le⟩ hKO
  obtain ⟨ha,hb,hc,hsym,ell,C,hell,hC,hbounds⟩ := hE
  let r := δ/4
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨Ω⟩ := smooth_flat_jordan_domain r hr
  let x₀ : E2 := (Ω.localR/2) • coordinateVector 2 1
  let q := p-x₀
  have hx₀norm : ‖x₀‖ = Ω.localR/2 := by
    have he : ‖coordinateVector 2 1‖ = 1 := by simp [coordinateVector]
    rw [show x₀ = (Ω.localR/2) • coordinateVector 2 1 from rfl,norm_smul,
      Real.norm_eq_abs,abs_of_pos (half_pos Ω.localR_pos),he,mul_one]
  have hx₀half : x₀ ∈ halfDisc Ω.localR := by
    constructor
    · change x₀ ∈ Metric.ball (0 : E2) Ω.localR
      rw [Metric.mem_ball,dist_zero_right,hx₀norm]
      linarith [Ω.localR_pos]
    · change 0 < ((Ω.localR/2) • coordinateVector 2 1) 1
      simpa [coordinateVector] using half_pos Ω.localR_pos
  have hx₀Ω : x₀ ∈ Ω.domain := by
    have hx : x₀ ∈ Ω.domain ∩ disc Ω.localR := Ω.inward_side.symm ▸ hx₀half
    exact hx.1
  have hτK (x : E2) (hx : x ∈ closedHalfDisc r) : x+q ∈ K := by
    have hxn : ‖x‖ ≤ r := by simpa only [closedDisc,Metric.mem_closedBall,dist_zero_right] using hx.1
    have he : x+q-p=x-x₀ := by dsimp [q]; abel
    rw [Metric.mem_closedBall,dist_eq_norm,he]
    have hlocalr := Ω.localR_inside
    dsimp [r] at hlocalr
    exact (norm_sub_le _ _).trans (by rw [hx₀norm]; dsimp [r] at hxn; linarith)
  let A : E2 → Mat2 := fun x => N.normalizedA (x+q)
  let B : E2 → E2 := fun x => N.normalizedB (x+q)
  have hSym : SymmetricOn A (closedHalfDisc r) := fun x hx => hsym _ (hτK x hx)
  have hEll : UniformEllipticOn A (closedHalfDisc r) :=
    ⟨ell,C,hell,hC,fun x hx v => hbounds _ (hτK x hx) v⟩
  have hAlip : ∀ i j, LipschitzBoundOn (fun x => A x i j) (closedHalfDisc r) := by
    intro i j
    obtain ⟨L,hL,hbound⟩ := hLip i j
    refine ⟨L,hL,?_⟩
    intro x hx y hy
    simpa only [dist_add_right] using hbound _ (hτK x hx) _ (hτK y hy)
  have hAdet : ∀ x ∈ closedHalfDisc r, Matrix.det (A x) = 1 :=
    fun x hx => hDet _ (hτK x hx)
  obtain ⟨G⟩ := inverse_det_one_metric_data r hr A hSym hEll hAlip hAdet
  obtain ⟨P⟩ := boundary_metric_conformal_provider r A G Ω
  obtain ⟨F,hFs,hFt,hForward,hInverse,hDensity⟩ :=
    native_metric_parametrization_interior_chart_v475 G Ω P
      (fun x hx => hAdet x (Ω.closure_inside hx))
  have hBcont : ContinuousOn B F.chart.source := by
    apply (hb.continuousOn.comp (continuous_id.add continuous_const).continuousOn _).mono
      (show F.chart.source ⊆ (fun x : E2 => x+q) ⁻¹' K from ?_)
    · intro x hx
      exact hx
    · intro x hx
      exact hτK x (Ω.closure_inside (subset_closure (hFs ▸ hx)))
  obtain ⟨F₀,R,hR,hpF₀,hF₀F,hTarget,hBound,hDensity₀⟩ :=
    native_interior_centered_chart_v475 F x₀ (hFs.symm ▸ hx₀Ω) A B hBcont hDensity
  obtain ⟨H,hHs,hHt,hHi,hHB,hHD⟩ := native_interior_chart_translate_v475 F₀ q
    N.normalizedA N.normalizedB hDensity₀ hBound
  refine ⟨H,R,hR,?_,?_,hHt.trans hTarget,hHB,hHD⟩
  · rw [hHs]
    change p-q ∈ F₀.chart.source
    have he : p-q=x₀ := by dsimp [q]; abel
    rwa [he]
  · intro x hx
    rw [hHs] at hx
    have hdom : x-q ∈ Ω.domain := hFs ▸ hF₀F hx
    have hh := hKO (hτK (x-q) (Ω.closure_inside (subset_closure hdom)))
    simpa only [sub_add_cancel] using hh

#print axioms native_interior_normalized_chart_exists_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
