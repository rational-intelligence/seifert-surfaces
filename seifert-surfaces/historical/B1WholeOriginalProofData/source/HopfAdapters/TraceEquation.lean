import HopfAdapters.ClosedBallGeometry
import EllipticPdes.Existence.ClassicalMaximum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
open Set Metric Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.AppendixACoordinates.HopfAdapters

theorem christoffel_lower_symmetric (V : Set E3) (hV : IsOpen V)
    (g : CoordinateMetric V) (y : E3) (hy : y ∈ V) (a b k : Fin 3) :
    christoffel g.tensor y a b k = christoffel g.tensor y b a k := by
  have heq : (fun z => g.tensor z a b) =ᶠ[𝓝 y] (fun z => g.tensor z b a) := by
    filter_upwards [hV.mem_nhds hy] with z hz
    exact g.symmetric z hz a b
  unfold christoffel
  have hp : partial3 (fun z => g.tensor z a b) y =
      partial3 (fun z => g.tensor z b a) y := by
    funext l
    exact congrArg (fun D : E3 →L[ℝ] ℝ => D (coordinateVector 3 l)) heq.fderiv_eq
  simp only [hp, add_comm]

theorem hessian_coefficient_symmetric (V : Set E3) (hV : IsOpen V)
    (g : CoordinateMetric V) (r : E3 → ℝ) (hr : ContDiffOn ℝ ∞ r V)
    (y : E3) (hy : y ∈ V) (a b : Fin 3) :
    hessianCoefficient g.tensor r y a b = hessianCoefficient g.tensor r y b a := by
  have hrAt := hr.contDiffAt (hV.mem_nhds hy)
  have hrD : ContDiffOn ℝ 1 (fderiv ℝ r) V := hr.fderiv_of_isOpen hV (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ r) y :=
    (hrD.contDiffAt (hV.mem_nhds hy)).differentiableAt (by norm_num)
  have hpartial (u v : Fin 3) : partial3 (fun z => partial3 r z v) y u =
      fderiv ℝ (fderiv ℝ r) y (coordinateVector 3 u) (coordinateVector 3 v) := by
    unfold partial3
    rw [fderiv_clm_apply hD (differentiableAt_const _)]
    simp
  unfold hessianCoefficient
  rw [hpartial a b, hpartial b a,
    (hrAt.isSymmSndFDerivAt (by norm_num)).eq (coordinateVector 3 a) (coordinateVector 3 b)]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [christoffel_lower_symmetric V hV g y hy a b k]

theorem pullback_hessian_neg_posSemidef (V : Set E3) (hV : IsOpen V)
    (g : CoordinateMetric V) (r : E3 → ℝ) (hr : ContDiffOn ℝ ∞ r V)
    (Φ : E2 → E3) (x : E2) (hx : Φ x ∈ V)
    (hHess : ∀ v : E3, hessianQuadratic g.tensor r (Φ x) v ≤ 0) :
    (-pullbackHessian g.tensor r Φ x).PosSemidef := by
  apply EllipticPdes.Classical.posSemidef_of_forall
  · intro i j
    simp only [Matrix.neg_apply]
    congr 1
    unfold pullbackHessian hessianBilinear
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hessian_coefficient_symmetric V hV g r hr (Φ x) hx b a]
    ring
  · intro ξ
    have h := hHess (∑ i : Fin 2, ξ i • graphTangent Φ x i)
    have heq : (∑ i : Fin 2, ∑ j : Fin 2,
        (-pullbackHessian g.tensor r Φ x) i j * ξ i * ξ j) =
        -hessianQuadratic g.tensor r (Φ x) (∑ i : Fin 2, ξ i • graphTangent Φ x i) := by
      simp [Fin.sum_univ_succ, Matrix.neg_apply, pullbackHessian, hessianBilinear,
        hessianQuadratic, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact neg_nonneg.mpr h

/-- Weighted matrix contraction, rather than an unweighted frame trace. -/
theorem matrix_trace_nonpositive (a H : Matrix (Fin 2) (Fin 2) ℝ)
    (ha : a.PosSemidef) (hH : (-H).PosSemidef) :
    ∑ i, ∑ j, a i j * H i j ≤ 0 := by
  exact EllipticPdes.Classical.sum_mul_nonpos_of_posSemidef ha hH

theorem graph_height_second_chain (V : Set E3) (hV : IsOpen V)
    (g : CoordinateMetric V) (r : E3 → ℝ) (hr : ContDiffOn ℝ ∞ r V)
    (Ω : Set E2) (hΩ : IsOpen Ω) (Φ : E2 → E3)
    (hΦ : ContDiffOn ℝ ∞ Φ Ω) (hgraph : MapsTo Φ Ω V)
    (x : E2) (hx : x ∈ Ω) (i j : Fin 2) :
    partialD i (partialD j (graphHeight r Φ)) x =
      pullbackHessian g.tensor r Φ x i j +
        fderiv ℝ r (Φ x) (covariantAcceleration g.tensor Φ x i j) := by
  have hrD : ContDiffOn ℝ 1 (fderiv ℝ r) V := hr.fderiv_of_isOpen hV (by norm_num)
  have hΦD : ContDiffOn ℝ 1 (fderiv ℝ Φ) Ω := hΦ.fderiv_of_isOpen hΩ (by norm_num)
  have hdΦ := (hΦ.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
  have hdr := (hr.contDiffAt (hV.mem_nhds (hgraph hx))).differentiableAt (by simp)
  have hdDr := (hrD.contDiffAt (hV.mem_nhds (hgraph hx))).differentiableAt (by norm_num)
  have hdDΦ := (hΦD.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)
  have hdT : DifferentiableAt ℝ (fun z => graphTangent Φ z j) x :=
    hdDΦ.clm_apply (differentiableAt_const _)
  have heq : partialD j (graphHeight r Φ) =ᶠ[𝓝 x]
      (fun z => fderiv ℝ r (Φ z) (graphTangent Φ z j)) := by
    filter_upwards [hΩ.mem_nhds hx] with z hz
    unfold partialD graphHeight graphTangent coordinateVector
    change fderiv ℝ (r ∘ Φ) z (EuclideanSpace.single j 1) = _
    rw [fderiv_comp z
      ((hr.contDiffAt (hV.mem_nhds (hgraph hz))).differentiableAt (by simp))
      ((hΦ.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp))]
    rfl
  have hsecond : partialD i (partialD j (graphHeight r Φ)) x =
      fderiv ℝ r (Φ x) (fderiv ℝ (fun z => graphTangent Φ z j) x (coordinateVector 2 i)) +
      fderiv ℝ (fderiv ℝ r) (Φ x) (graphTangent Φ x i) (graphTangent Φ x j) := by
    change fderiv ℝ (partialD j (graphHeight r Φ)) x (coordinateVector 2 i) = _
    have hdcomp : DifferentiableAt ℝ (fun z => fderiv ℝ r (Φ z)) x := hdDr.comp x hdΦ
    rw [heq.fderiv_eq, fderiv_clm_apply hdcomp hdT,
      show fderiv ℝ (fun z => fderiv ℝ r (Φ z)) x =
        (fderiv ℝ (fderiv ℝ r) (Φ x)).comp (fderiv ℝ Φ x) from
        fderiv_comp x hdDr hdΦ]
    rfl
  have hpartial (a b : Fin 3) : partial3 (fun z => partial3 r z b) (Φ x) a =
      fderiv ℝ (fderiv ℝ r) (Φ x) (coordinateVector 3 a) (coordinateVector 3 b) := by
    unfold partial3
    rw [fderiv_clm_apply hdDr (differentiableAt_const _)]
    simp
  have hvec (v : E3) : (∑ a : Fin 3, v a • coordinateVector 3 a) = v := by
    ext k
    fin_cases k <;> simp [Fin.sum_univ_succ, coordinateVector, EuclideanSpace.single, PiLp.single_apply]
  have hraw : (∑ a : Fin 3, ∑ b : Fin 3,
      partial3 (fun z => partial3 r z b) (Φ x) a *
        graphTangent Φ x i a * graphTangent Φ x j b) =
      fderiv ℝ (fderiv ℝ r) (Φ x) (graphTangent Φ x i) (graphTangent Φ x j) := by
    simp only [hpartial]
    conv_rhs => rw [← hvec (graphTangent Φ x i), ← hvec (graphTangent Φ x j)]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hsecond, ← hraw]
  simp only [pullbackHessian, hessianBilinear, hessianCoefficient,
    covariantAcceleration, map_add, map_sum, map_smul, smul_eq_mul]
  simp only [Fin.sum_univ_succ, partial3]
  ring

theorem graph_height_first_chain (V : Set E3) (hV : IsOpen V)
    (r : E3 → ℝ) (hr : ContDiffOn ℝ ∞ r V)
    (Ω : Set E2) (hΩ : IsOpen Ω) (Φ : E2 → E3)
    (hΦ : ContDiffOn ℝ ∞ Φ Ω) (hgraph : MapsTo Φ Ω V)
    (x : E2) (hx : x ∈ Ω) :
    fderiv ℝ (graphHeight r Φ) x = (fderiv ℝ r (Φ x)).comp (fderiv ℝ Φ x) := by
  exact fderiv_comp x
    ((hr.contDiffAt (hV.mem_nhds (hgraph hx))).differentiableAt (by simp))
    ((hΦ.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))

theorem projected_traced_acceleration (g : MetricTensor) (p : E3)
    (L : E2 →L[ℝ] E3) (normal : E3) (P : GraphProjection L normal)
    (w : E2 → ℝ) (Ω : Set E2) (hΩ : IsOpen Ω)
    (hΦ : ContDiffOn ℝ ∞ (graphMap p L normal w) Ω)
    (x : E2) (hx : x ∈ Ω) :
    P.map (tracedAcceleration g (graphMap p L normal w) x) =
      P.map (interiorChristoffelTrace g (graphMap p L normal w) x) := by
  unfold tracedAcceleration interiorChristoffelTrace tracedChristoffel
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  unfold covariantAcceleration christoffelVector
  rw [map_add, graph_projection_second_derivative p L normal P w Ω hΩ
    (hΦ.of_le (by norm_num)) x hx i j, zero_add]
  rfl

/-- The traced acceleration is tangential; it need not vanish in graph coordinates. -/
theorem minimal_traced_acceleration_eq_tangent_drift (g : MetricTensor) (p : E3)
    (L : E2 →L[ℝ] E3) (normal : E3) (P : GraphProjection L normal)
    (w : E2 → ℝ) (Ω : Set E2) (hΩ : IsOpen Ω)
    (hminimal : IsMinimalParametrizationOn g (graphMap p L normal w) Ω)
    (x : E2) (hx : x ∈ Ω) :
    tracedAcceleration g (graphMap p L normal w) x =
      fderiv ℝ (graphMap p L normal w) x
        (P.map (interiorChristoffelTrace g (graphMap p L normal w) x)) := by
  obtain ⟨v, hv⟩ := hminimal.2 x hx
  have hD : P.map.comp (fderiv ℝ (graphMap p L normal w) x) =
      ContinuousLinearMap.id ℝ E2 := by
    have heq : (fun z => P.map (graphMap p L normal w z)) = (fun z => P.map p + z) := by
      funext z
      exact graph_projection_affine p L normal P w z
    have hd := (hminimal.1.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
    have hc := (P.map.hasFDerivAt.comp x hd.hasFDerivAt).fderiv
    change fderiv ℝ (fun z => P.map (graphMap p L normal w z)) x =
      P.map.comp (fderiv ℝ (graphMap p L normal w) x) at hc
    have ha : HasFDerivAt (fun z : E2 => P.map p + z)
        (ContinuousLinearMap.id ℝ E2) x := by
      convert (hasFDerivAt_const (P.map p) x).add (hasFDerivAt_id x) using 1 <;>
        first | rfl | simp only [zero_add]
    rw [heq, ha.fderiv] at hc
    simpa only [zero_add] using hc.symm
  have hv' : fderiv ℝ (graphMap p L normal w) x v =
      tracedAcceleration g (graphMap p L normal w) x := hv
  have hp := congrArg P.map hv'
  change P.map.comp (fderiv ℝ (graphMap p L normal w) x) v = _ at hp
  rw [hD, ContinuousLinearMap.id_apply,
    projected_traced_acceleration g p L normal P w Ω hΩ hminimal.1 x hx] at hp
  rw [← hp]
  exact hv'.symm

theorem graph_height_trace_equation (V : Set E3) (hV : IsOpen V)
    (g : CoordinateMetric V) (p : E3) (L : E2 →L[ℝ] E3) (normal : E3)
    (P : GraphProjection L normal) (w : E2 → ℝ)
    (Ω : Set E2) (hΩ : IsOpen Ω)
    (hgraph : MapsTo (graphMap p L normal w) Ω V)
    (hminimal : IsMinimalParametrizationOn g.tensor (graphMap p L normal w) Ω)
    (r : E3 → ℝ) (hr : ContDiffOn ℝ ∞ r V) (x : E2) (hx : x ∈ Ω) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      (inducedMetric g.tensor (graphMap p L normal w) x)⁻¹ i j *
        partialD i (partialD j (graphHeight r (graphMap p L normal w))) x) -
      fderiv ℝ (graphHeight r (graphMap p L normal w)) x
        (P.map (interiorChristoffelTrace g.tensor (graphMap p L normal w) x)) =
      ∑ i : Fin 2, ∑ j : Fin 2,
        (inducedMetric g.tensor (graphMap p L normal w) x)⁻¹ i j *
          pullbackHessian g.tensor r (graphMap p L normal w) x i j := by
  have hchain := graph_height_first_chain V hV r hr Ω hΩ (graphMap p L normal w)
    hminimal.1 hgraph x hx
  rw [hchain]
  have htrace := minimal_traced_acceleration_eq_tangent_drift g.tensor p L normal P w Ω hΩ hminimal x hx
  have hsum : (∑ i : Fin 2, ∑ j : Fin 2,
      (inducedMetric g.tensor (graphMap p L normal w) x)⁻¹ i j *
        fderiv ℝ r (graphMap p L normal w x)
          (covariantAcceleration g.tensor (graphMap p L normal w) x i j)) =
      fderiv ℝ r (graphMap p L normal w x)
        (fderiv ℝ (graphMap p L normal w) x
          (P.map (interiorChristoffelTrace g.tensor (graphMap p L normal w) x))) := by
    rw [← htrace]
    simp only [tracedAcceleration, map_sum, map_smul, smul_eq_mul]
  let A : Matrix (Fin 2) (Fin 2) ℝ := (inducedMetric g.tensor (graphMap p L normal w) x)⁻¹
  change (∑ i : Fin 2, ∑ j : Fin 2, A i j *
      partialD i (partialD j (graphHeight r (graphMap p L normal w))) x) -
    ((fderiv ℝ r (graphMap p L normal w x)).comp (fderiv ℝ (graphMap p L normal w) x))
      (P.map (interiorChristoffelTrace g.tensor (graphMap p L normal w) x)) =
    ∑ i : Fin 2, ∑ j : Fin 2, A i j * pullbackHessian g.tensor r (graphMap p L normal w) x i j
  change (∑ i : Fin 2, ∑ j : Fin 2, A i j *
    fderiv ℝ r (graphMap p L normal w x) (covariantAcceleration g.tensor (graphMap p L normal w) x i j)) = _ at hsum
  simp_rw [graph_height_second_chain V hV g r hr Ω hΩ (graphMap p L normal w)
    hminimal.1 hgraph x hx, mul_add]
  simp_rw [Finset.sum_add_distrib]
  rw [hsum]
  simp only [ContinuousLinearMap.comp_apply, add_sub_cancel_right]

/-- Exact sign bridge for v = -s and b = P C. -/
theorem nondivOp_negative_height (a : E2 → Matrix (Fin 2) (Fin 2) ℝ)
    (b : E2 → E2) (s : E2 → ℝ) (x : E2) (hs : ContDiffAt ℝ 2 s x) :
    nondivOp a (fun z i => b z i) (fun _ => 0) (fun z => -s z) x =
      (∑ i : Fin 2, ∑ j : Fin 2, a x i j * partialD i (partialD j s) x) -
        fderiv ℝ s x (b x) := by
  have hneg (i : Fin 2) : partialD i (fun z => -s z) = fun z => -partialD i s z := by
    funext z
    simp [partialD, fderiv_fun_neg]
  have hsecond (i j : Fin 2) : partialD i (partialD j (fun z => -s z)) x =
      -partialD i (partialD j s) x := by
    rw [hneg j]
    simp [partialD, fderiv_fun_neg]
    rfl
  have hb : (∑ i : Fin 2, b x i * partialD i s x) = fderiv ℝ s x (b x) := by
    have heq : (∑ i : Fin 2, b x i • coordinateVector 2 i) = b x := by
      ext k
      fin_cases k <;> simp [coordinateVector, EuclideanSpace.single, PiLp.single_apply]
    rw [← heq]
    simp [map_sum, map_smul, partialD, coordinateVector, smul_eq_mul]
  unfold nondivOp
  simp only [hsecond]
  simp only [hneg, mul_neg, Finset.sum_neg_distrib,
    neg_neg, zero_mul, add_zero, neg_zero]
  rw [hb]
  rfl

theorem interior_christoffel_eq_boundary (U : Set E2) (g : MetricTensor)
    (p : E3) (L : E2 →L[ℝ] E3) (normal : E3) (w : E2 → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w U) (c : E2) (R : ℝ)
    (hK : closedBall c R ⊆ U) (x : E2) (hx : x ∈ ball c R) :
    interiorChristoffelTrace g (graphMap p L normal w) x =
      tracedChristoffel g (graphMap p L normal w)
        (boundaryGraphLinearization (closedBall c R) L normal w)
        (inverseGram g (graphMap p L normal w)
          (boundaryGraphLinearization (closedBall c R) L normal w)) x := by
  have hF := boundary_graph_linearization_eq_fderiv U p L normal w hwC1 c R hK x hx
  unfold interiorChristoffelTrace tracedChristoffel inverseGram extendedGram inducedMetric graphTangent
  simp only [hF]

theorem negative_graph_height_subsolution (V : Set E3) (hV : IsOpen V)
    (g : CoordinateMetric V) (U : Set E2) (p normal : E3) (hp : p ∈ V)
    (hnormal : normal ≠ 0) (L : E2 →L[ℝ] E3) (hL : Injective L)
    (horth : ∀ v : E2, coordinateInner g.tensor p (L v) normal = 0)
    (P : GraphProjection L normal) (w : E2 → ℝ) (hwC1 : ContDiffOn ℝ 1 w U)
    (hgraph : MapsTo (graphMap p L normal w) U V)
    (hminimal : IsMinimalParametrizationOn g.tensor (graphMap p L normal w) (interior U))
    (r : E3 → ℝ) (hr : ContDiffOn ℝ ∞ r V)
    (hHess : ∀ x ∈ interior U, ∀ v : E3,
      hessianQuadratic g.tensor r (graphMap p L normal w x) v ≤ 0)
    (c : E2) (R : ℝ) (hK : closedBall c R ⊆ U) (hB : ball c R ⊆ interior U) :
    let Φ := graphMap p L normal w
    let F := boundaryGraphLinearization (closedBall c R) L normal w
    let a := inverseGram g.tensor Φ F
    let C := tracedChristoffel g.tensor Φ F a
    ∀ x ∈ ball c R,
      nondivOp a (fun z i => graphDrift P.map C z i) (fun _ => 0)
        (fun z => -graphHeight r Φ z) x ≤ 0 := by
  dsimp only
  intro x hx
  let Φ := graphMap p L normal w
  have hxU := hB hx
  have hxV : Φ x ∈ V := hgraph (interior_subset hxU)
  have hgraphI : MapsTo Φ (interior U) V := hgraph.mono_left interior_subset
  have hΦAt := hminimal.1.contDiffAt (isOpen_interior.mem_nhds hxU)
  have hrAt := hr.contDiffAt (hV.mem_nhds hxV)
  have hs : ContDiffAt ℝ 2 (graphHeight r Φ) x :=
    (hrAt.comp x hΦAt).of_le (by norm_num)
  have hF := boundary_graph_linearization_eq_fderiv U p L normal w hwC1 c R hK x hx
  have ha : inverseGram g.tensor Φ (boundaryGraphLinearization (closedBall c R) L normal w) x =
      (inducedMetric g.tensor Φ x)⁻¹ := by
    unfold inverseGram extendedGram inducedMetric graphTangent
    simp only [hF]
    dsimp [Φ]
  have hC := interior_christoffel_eq_boundary U g.tensor p L normal w hwC1 c R hK x hx
  have hop := nondivOp_negative_height
    (inverseGram g.tensor Φ (boundaryGraphLinearization (closedBall c R) L normal w))
    (graphDrift P.map (tracedChristoffel g.tensor Φ
      (boundaryGraphLinearization (closedBall c R) L normal w)
      (inverseGram g.tensor Φ (boundaryGraphLinearization (closedBall c R) L normal w))))
    (graphHeight r Φ) x hs
  rw [hop]
  simp only [ha, graphDrift]
  rw [← hC, graph_height_trace_equation V hV g p L normal P w
    (interior U) isOpen_interior hgraphI hminimal r hr x hxU]
  apply matrix_trace_nonpositive
  · apply Matrix.PosSemidef.inv
    apply EllipticPdes.Classical.posSemidef_of_forall
    · intro i j
      unfold inducedMetric coordinateInner
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [g.symmetric (Φ x) hxV b a]
      ring
    · intro ξ
      let v : E3 := ∑ i : Fin 2, ξ i • graphTangent Φ x i
      have hnonneg : 0 ≤ coordinateInner g.tensor (Φ x) v v := by
        by_cases hv : v = 0
        · simp [hv, coordinateInner]
        · exact (g.positive (Φ x) hxV v hv).le
      have heq : (∑ i : Fin 2, ∑ j : Fin 2,
          inducedMetric g.tensor Φ x i j * ξ i * ξ j) =
          coordinateInner g.tensor (Φ x) v v := by
        simp [v, inducedMetric, coordinateInner, Fin.sum_univ_succ,
          PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      rw [heq]
      exact hnonneg
  · exact pullback_hessian_neg_posSemidef V hV g r hr Φ x hxV (hHess x hxU)

end SeifertSurfaces.AppendixACoordinates.HopfAdapters
