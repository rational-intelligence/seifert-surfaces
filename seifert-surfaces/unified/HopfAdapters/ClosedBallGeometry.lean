import HopfAdapters.Definitions

noncomputable section
open Set Metric Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.AppendixACoordinates.HopfAdapters

theorem exists_closed_tangent_ball (U : Set E2) (hU : IsClosed U)
    (hsphere : InteriorSphereAt U 0) :
    ∃ c : E2, ∃ R : ℝ, 0 < R ∧ ball c R ⊆ interior U ∧ dist 0 c = R ∧
      closedBall c R ⊆ U ∧ (0 : E2) ∈ closedBall c R ∧
      IsCompact (closedBall c R) ∧ Convex ℝ (closedBall c R) ∧
      UniqueDiffOn ℝ (closedBall c R) := by
  obtain ⟨c, R, hR, hball, hdist⟩ := hsphere
  have hK : closedBall c R ⊆ U := by
    rw [← closure_ball c hR.ne']
    exact hU.closure_subset_iff.mpr (hball.trans interior_subset)
  refine ⟨c, R, hR, hball, hdist, hK, ?_, isCompact_closedBall c R,
    convex_closedBall c R, ?_⟩
  · exact mem_closedBall.mpr hdist.le
  · apply uniqueDiffOn_convex (convex_closedBall c R)
    exact ⟨c, ball_subset_interior_closedBall (mem_ball_self hR)⟩

theorem boundary_fderiv_continuous (U : Set E2) (w : E2 → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w U) (c : E2) (R : ℝ) (hR : 0 < R)
    (hK : closedBall c R ⊆ U) :
    ContinuousOn (fderivWithin ℝ w (closedBall c R)) (closedBall c R) := by
  apply (hwC1.mono hK).continuousOn_fderivWithin _ le_rfl
  apply uniqueDiffOn_convex (convex_closedBall c R)
  exact ⟨c, ball_subset_interior_closedBall (mem_ball_self hR)⟩

theorem boundary_fderiv_eq_interior (U : Set E2) (w : E2 → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w U) (c : E2) (R : ℝ)
    (hK : closedBall c R ⊆ U) (x : E2) (hx : x ∈ ball c R) :
    fderivWithin ℝ w (closedBall c R) x = fderiv ℝ w x := by
  exact fderivWithin_of_mem_nhds (closedBall_mem_nhds_of_mem hx)

theorem boundary_fderiv_zero (U : Set E2) (w : E2 → ℝ)
    (hwflat : HasFDerivWithinAt w (0 : E2 →L[ℝ] ℝ) U 0)
    (c : E2) (R : ℝ) (hR : 0 < R) (hK : closedBall c R ⊆ U)
    (h0 : (0 : E2) ∈ closedBall c R) :
    fderivWithin ℝ w (closedBall c R) 0 = 0 := by
  apply (hwflat.mono hK).fderivWithin
  have hdiff := uniqueDiffOn_convex (convex_closedBall c R)
    ⟨c, ball_subset_interior_closedBall (mem_ball_self hR)⟩
  exact hdiff 0 h0

theorem boundary_graph_linearization_continuous (U : Set E2)
    (L : E2 →L[ℝ] E3) (normal : E3) (w : E2 → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w U) (c : E2) (R : ℝ) (hR : 0 < R)
    (hK : closedBall c R ⊆ U) :
    ContinuousOn (boundaryGraphLinearization (closedBall c R) L normal w)
      (closedBall c R) := by
  have hD := boundary_fderiv_continuous U w hwC1 c R hR hK
  exact continuousOn_const.add
    ((ContinuousLinearMap.smulRightL ℝ E2 E3).continuous.comp_continuousOn hD
      |>.clm_apply continuousOn_const)

theorem boundary_graph_linearization_eq_fderiv (U : Set E2) (p : E3)
    (L : E2 →L[ℝ] E3) (normal : E3) (w : E2 → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w U) (c : E2) (R : ℝ)
    (hK : closedBall c R ⊆ U) (x : E2) (hx : x ∈ ball c R) :
    boundaryGraphLinearization (closedBall c R) L normal w x =
      fderiv ℝ (graphMap p L normal w) x := by
  have hball : ball c R ⊆ U := ball_subset_closedBall.trans hK
  have hw : DifferentiableAt ℝ w x :=
    ((hwC1.mono hball).differentiableOn (by norm_num) x hx).differentiableAt
      (isOpen_ball.mem_nhds hx)
  have hderiv : HasFDerivAt (graphMap p L normal w)
      (L + (fderiv ℝ w x).smulRight normal) x := by
    convert ((hasFDerivAt_const p x).add L.hasFDerivAt).add
      (hw.hasFDerivAt.smul_const normal) using 1 <;> first | rfl | simp only [zero_add]
  rw [hderiv.fderiv]
  unfold boundaryGraphLinearization
  rw [boundary_fderiv_eq_interior U w hwC1 c R hK x hx]

theorem boundary_graph_linearization_injective (V : Set E3) (g : CoordinateMetric V)
    (p normal : E3) (hp : p ∈ V) (hnormal : normal ≠ 0)
    (L : E2 →L[ℝ] E3) (hL : Injective L)
    (horth : ∀ v : E2, coordinateInner g.tensor p (L v) normal = 0)
    (K : Set E2) (w : E2 → ℝ) (x : E2) :
    Injective (boundaryGraphLinearization K L normal w x) := by
  exact graph_linearization_injective V g p normal hp hnormal L hL horth _

theorem exists_graph_projection (V : Set E3) (g : CoordinateMetric V)
    (p normal : E3) (hp : p ∈ V) (hnormal : normal ≠ 0)
    (L : E2 →L[ℝ] E3) (hL : Injective L)
    (horth : ∀ v : E2, coordinateInner g.tensor p (L v) normal = 0) :
    Nonempty (GraphProjection L normal) := by
  let A : E2 × ℝ →L[ℝ] E3 := L.coprod
    ((ContinuousLinearMap.id ℝ ℝ).smulRight normal)
  have hA : Injective A := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨v, t⟩ hvt
    change L v + t • normal = 0 at hvt
    have hinner : coordinateInner g.tensor p (L v + t • normal) normal = 0 := by
      rw [hvt]
      exact coordinateInner_zero_left g.tensor p normal
    rw [coordinateInner_add_left, horth, zero_add, coordinateInner_smul_left] at hinner
    have ht : t = 0 := (mul_eq_zero.mp hinner).resolve_right
      (ne_of_gt (g.positive p hp normal hnormal))
    have hv : v = 0 := hL (by simpa [ht] using hvt)
    simp [hv, ht]
  have hdim : Module.finrank ℝ (E2 × ℝ) = Module.finrank ℝ E3 := by
    simp [E2, E3, Module.finrank_prod, finrank_euclideanSpace]
  let e : (E2 × ℝ) ≃L[ℝ] E3 :=
    (A.toLinearMap.linearEquivOfInjective hA hdim).toContinuousLinearEquiv
  let P : E3 →L[ℝ] E2 := (ContinuousLinearMap.fst ℝ E2 ℝ).comp
    e.symm.toContinuousLinearMap
  have hleft : ∀ v : E2, P (L v) = v := by
    intro v
    have h := e.symm_apply_apply (v, 0)
    change e.symm (A (v, 0)) = (v, 0) at h
    have he : A (v, 0) = L v := by simp [A]
    rw [he] at h
    change (e.symm (L v)).1 = v
    exact congrArg Prod.fst h
  have hnormalP : P normal = 0 := by
    have h := e.symm_apply_apply (0, 1)
    change e.symm (A (0, 1)) = (0, 1) at h
    have he : A (0, 1) = normal := by simp [A]
    rw [he] at h
    change (e.symm normal).1 = 0
    exact congrArg Prod.fst h
  refine ⟨⟨P, ?_, hnormalP⟩⟩
  apply ContinuousLinearMap.ext
  intro v
  exact hleft v

theorem graph_projection_affine (p : E3) (L : E2 →L[ℝ] E3) (normal : E3)
    (P : GraphProjection L normal) (w : E2 → ℝ) (x : E2) :
    P.map (graphMap p L normal w x) = P.map p + x := by
  have hPL : P.map (L x) = x := by
    exact congrArg (fun T : E2 →L[ℝ] E2 => T x) P.leftInverse
  simp only [graphMap, map_add, map_smul, hPL, P.killsNormal, smul_zero, add_zero]

theorem graph_projection_fderiv (p : E3) (L : E2 →L[ℝ] E3) (normal : E3)
    (P : GraphProjection L normal) (w : E2 → ℝ) (x : E2)
    (hw : DifferentiableAt ℝ w x) :
    P.map.comp (fderiv ℝ (graphMap p L normal w) x) =
      ContinuousLinearMap.id ℝ E2 := by
  have hderiv : HasFDerivAt (graphMap p L normal w)
      (L + (fderiv ℝ w x).smulRight normal) x := by
    convert ((hasFDerivAt_const p x).add L.hasFDerivAt).add
      (hw.hasFDerivAt.smul_const normal) using 1 <;> first | rfl | simp only [zero_add]
  rw [hderiv.fderiv]
  ext v
  have hPL : P.map (L v) = v :=
    congrArg (fun T : E2 →L[ℝ] E2 => T v) P.leftInverse
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul,
    hPL, P.killsNormal, smul_zero, add_zero, ContinuousLinearMap.id_apply]

theorem graph_projection_second_derivative (p : E3) (L : E2 →L[ℝ] E3)
    (normal : E3) (P : GraphProjection L normal) (w : E2 → ℝ)
    (Ω : Set E2) (hΩ : IsOpen Ω) (hΦ : ContDiffOn ℝ 2 (graphMap p L normal w) Ω)
    (x : E2) (hx : x ∈ Ω) (i j : Fin 2) :
    P.map (fderiv ℝ (fun z => graphTangent (graphMap p L normal w) z j) x
      (coordinateVector 2 i)) = 0 := by
  let Φ := graphMap p L normal w
  have hΦdiff : DifferentiableOn ℝ Φ Ω := hΦ.differentiableOn (by norm_num)
  have hproject : ∀ z ∈ Ω,
      P.map.comp (fderiv ℝ Φ z) = ContinuousLinearMap.id ℝ E2 := by
    intro z hz
    have hd := (hΦdiff z hz).differentiableAt (hΩ.mem_nhds hz)
    have hc := (P.map.hasFDerivAt.comp z hd.hasFDerivAt).fderiv
    have he : (fun t => P.map (Φ t)) = fun t => P.map p + t := by
      funext t
      exact graph_projection_affine p L normal P w t
    change fderiv ℝ (fun t => P.map (Φ t)) z = P.map.comp (fderiv ℝ Φ z) at hc
    rw [he] at hc
    have ha : HasFDerivAt (fun t : E2 => P.map p + t)
        (ContinuousLinearMap.id ℝ E2) z := by
      convert (hasFDerivAt_const (P.map p) z).add (hasFDerivAt_id z) using 1 <;>
        first | rfl | simp only [zero_add]
    rw [ha.fderiv] at hc
    exact hc.symm
  have hT : DifferentiableAt ℝ (fun z => graphTangent Φ z j) x := by
    have hD : ContDiffOn ℝ 1 (fderiv ℝ Φ) Ω := hΦ.fderiv_of_isOpen hΩ (by norm_num)
    exact ((hD.clm_apply contDiffOn_const).differentiableOn (by norm_num) x hx).differentiableAt
      (hΩ.mem_nhds hx)
  have heq : (fun z => P.map (graphTangent Φ z j)) =ᶠ[𝓝 x]
      fun _ => coordinateVector 2 j := by
    filter_upwards [hΩ.mem_nhds hx] with z hz
    exact congrArg (fun T : E2 →L[ℝ] E2 => T (coordinateVector 2 j)) (hproject z hz)
  have hc := (P.map.hasFDerivAt.comp x hT.hasFDerivAt).fderiv
  have hz : fderiv ℝ (fun z => P.map (graphTangent Φ z j)) x = 0 := by
    rw [heq.fderiv_eq]
    exact congrFun (fderiv_const (coordinateVector 2 j)) x
  have hzero : P.map.comp (fderiv ℝ (fun z => graphTangent Φ z j) x) = 0 := by
    rw [← hc]
    exact hz
  exact congrArg (fun T : E2 →L[ℝ] E2 => T (coordinateVector 2 i)) hzero

end SeifertSurfaces.AppendixACoordinates.HopfAdapters
