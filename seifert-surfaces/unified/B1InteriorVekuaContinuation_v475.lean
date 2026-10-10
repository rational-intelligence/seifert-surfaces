import B1FiniteIntegerOrder_v468
import B1WeakTransportReflection
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open WeakTransport
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- A full-disc Laplace-plus-drift equation vanishes everywhere when it vanishes
on any nonempty open subdomain.  This consumes the actual weak Vekua similarity
factorization, without a reflected boundary or a sign condition. -/
theorem native_interior_laplace_drift_zero_continuation_v475
    (R : ℝ) (hR : 0 < R) (u : E2 → ℝ) (b : E2 → E2)
    (hu : ContDiffOn ℝ 1 u (disc R))
    (heq : WeakLinearEquationOn (disc R) (fun _ => 1) b (fun _ => 0)
      u (planarGradient u))
    (hb : BoundedOn b (disc R))
    (hbLp : MemLp b ⊤ (volume.restrict (disc R)))
    (V : Set E2) (hV : IsOpen V) (hne : V.Nonempty) (hsub : V ⊆ disc R)
    (hzero : EqOn u (fun _ => 0) V) : EqOn u (fun _ => 0) (disc R) := by
  obtain ⟨hw,hveq,-,hLp⟩ := C1_real_weak_to_vekua R hR u b hu heq hb hbLp
  obtain ⟨S⟩ := weak_vekua_similarity R hR (complexGradient u) (vekuaA b) (vekuaB b)
    hw hveq 3 (by norm_num) (hLp 3 (by norm_num)).1 (hLp 3 (by norm_num)).2
  let e : ℂ ≃ₗᵢ[ℝ] E2 := Complex.orthonormalBasisOneI.repr
  have he (z : ℂ) : e z = complexPoint z := rfl
  have hball (z : ℂ) : complexPoint z ∈ disc R ↔ z ∈ Metric.ball (0:ℂ) R := by
    change e z ∈ Metric.ball 0 R ↔ _
    simpa only [Metric.mem_ball,dist_zero_right,map_zero] using
      (show ‖e z‖ < R ↔ ‖z‖ < R by rw [e.norm_map])
  have hdV (x : E2) (hx : x ∈ V) : fderiv ℝ u x = 0 := by
    have hev : u =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hV.mem_nhds hx] with y hy
      exact hzero hy
    rw [hev.fderiv_eq (𝕜 := ℝ)]
    simp
  have hwV (z : ℂ) (hz : complexPoint z ∈ V) : complexGradient u z = 0 := by
    simp [complexGradient,planarGradient,hdV _ hz]
  obtain ⟨q,hq⟩ := hne
  let z₀ := e.symm q
  have hzq : complexPoint z₀ = q := by change e (e.symm q) = q; exact e.apply_symm_apply q
  have hzR : z₀ ∈ Metric.ball (0:ℂ) R := (hball z₀).mp (hzq ▸ hsub hq)
  have hPhi : ∀ᶠ z in 𝓝 z₀, S.Phi z = 0 := by
    have hn : e ⁻¹' V ∈ 𝓝 z₀ := e.continuous.continuousAt.preimage_mem_nhds
      (by simpa only [z₀,e.apply_symm_apply] using hV.mem_nhds hq)
    filter_upwards [hn] with z hz
    have hzV : complexPoint z ∈ V := hz
    have hh := S.same_w z ((hball z).mp (hsub hzV))
    rw [hwV z hzV] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_right (Complex.exp_ne_zero _)
  have hPhiAll := (S.holomorphic.analyticOnNhd Metric.isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0:ℂ) R).isPreconnected hzR hPhi
  have hwAll (z : ℂ) (hz : z ∈ Metric.ball (0:ℂ) R) : complexGradient u z = 0 := by
    rw [S.same_w z hz,hPhiAll hz,Pi.zero_apply,zero_mul]
  have hdAll (x : E2) (hx : x ∈ disc R) : fderiv ℝ u x = 0 := by
    let z := e.symm x
    have hzx : complexPoint z = x := by change e (e.symm x) = x; exact e.apply_symm_apply x
    have hwz := hwAll z ((hball z).mp (hzx ▸ hx))
    have hgrad : planarGradient u x = 0 := by
      have hr := congrArg Complex.re hwz
      have hi := congrArg Complex.im hwz
      ext i
      fin_cases i
      · simpa [complexGradient,hzx] using hr
      · simpa [complexGradient,hzx] using hi
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = ∑ i : Fin 2, v i • coordinateVector 2 i := by
      ext i
      fin_cases i <;> simp [Fin.sum_univ_two,coordinateVector,PiLp.single_apply]
    rw [hv,map_sum]
    simp only [map_smul,zero_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hc : planarGradient u x i = fderiv ℝ u x (coordinateVector 2 i) := by
      fin_cases i <;> simp [planarGradient,coordinateVector,Fin.sum_univ_two]
    rw [← hc,hgrad]
    simp
  intro x hx
  have hconst := (convex_ball (0:E2) R).is_const_of_fderivWithin_eq_zero
    (hu.differentiableOn (by norm_num))
    (fun y hy => (fderivWithin_of_isOpen Metric.isOpen_ball hy).trans (hdAll y hy))
    hx (hsub hq)
  exact hconst.trans (hzero hq)

#print axioms native_interior_laplace_drift_zero_continuation_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
