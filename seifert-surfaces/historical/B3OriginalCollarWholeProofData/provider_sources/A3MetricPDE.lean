import A3SharedGraph
import SourceReparametrization
import CurvedSignedDivergenceFinal

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u v
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N]
variable {h : AmbientMetric N} {M : Set N} {D : A3OriginalData.{u,v} h M}

namespace A3SharedGraph
-- Jet = x × (height × gradient). The metric, chart, origin, plane and normal
-- are fixed by G. The Euler--Lagrange sign is div(d_p F) - d_z F = 0.
def jetPoint (G : A3SharedGraph D) (j : Jet) : E3 :=
  G.coordinates.chart (D.edge D.pointParameter) + G.plane j.1 + j.2.1 • G.normal

def jetTangent (G : A3SharedGraph D) (p : E2) (i : Fin 2) : E3 :=
  G.plane (coordinateVector 2 i) + p i • G.normal

def jetMetric (G : A3SharedGraph D) (j : Jet) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i k => coordinateInner (actualChartTensor h G.coordinates) (G.jetPoint j)
    (G.jetTangent j.2.2 i) (G.jetTangent j.2.2 k)

def areaDensity (G : A3SharedGraph D) (j : Jet) : ℝ :=
  Real.sqrt (Matrix.det (G.jetMetric j))

def metricFlux (G : A3SharedGraph D) (j : Jet) : E2 :=
  planarGradient (fun p : E2 => G.areaDensity (j.1, j.2.1, p)) j.2.2

def metricLowerOrder (G : A3SharedGraph D) (j : Jet) : ℝ :=
  -deriv (fun z : ℝ => G.areaDensity (j.1, z, j.2.2)) j.2.1

def attainedJet (G : A3SharedGraph D) (x : E2) : Jet :=
  (x, G.height x, planarGradient G.height x)

def attainedFlux (G : A3SharedGraph D) (x : E2) : E2 :=
  G.metricFlux (G.attainedJet x)

def attainedLowerOrder (G : A3SharedGraph D) (x : E2) : ℝ :=
  G.metricLowerOrder (G.attainedJet x)

def classicalResidual (G : A3SharedGraph D) (x : E2) : ℝ :=
  (∑ i : Fin 2, fderiv ℝ (fun y : E2 => G.attainedFlux y i) x (coordinateVector 2 i)) +
    G.attainedLowerOrder x

/-- These are the Euclidean outward normals of the two *same* projected sides,
fixed by their signed defining function; no free boundary/normal witness. -/
def sideOneNormal (G : A3SharedGraph D) (x : E2) : E2 :=
  ‖planarGradient G.signedSide x‖⁻¹ • planarGradient G.signedSide x

def sideTwoNormal (G : A3SharedGraph D) (x : E2) : E2 := -G.sideOneNormal x

/-- Line integral pulled back along the same regular projected edge, restricted
exactly to its part in the disc; speed is its Euclidean arc-length density. -/
def interfaceIntegral (G : A3SharedGraph D) (f : E2 → ℝ) : ℝ :=
  ∫ t in {t ∈ Ioo G.edgeLeft G.edgeRight | G.projectedEdge t ∈ G.disc},
    f (G.projectedEdge t) * ‖fderiv ℝ G.projectedEdge t 1‖

/-- Input package for the already-paid analytic theorem: all coefficient fields
are equal to the formula above. These are obligations to construct, not public
A3 premises; in particular neither a weak solution nor smoothness is a field. -/
structure OperatorControl (G : A3SharedGraph D) where
  jetDomain : Set Jet
  jetDomain_open : IsOpen jetDomain
  jetDomain_bounded : Bornology.IsBounded jetDomain
  compactChartControl : IsCompact (closure (G.jetPoint '' jetDomain))
  chartControl : closure (G.jetPoint '' jetDomain) ⊆ G.coordinates.chart.target
  attained : ∀ x ∈ G.disc, G.attainedJet x ∈ jetDomain
  positiveGram : ∀ j ∈ jetDomain, 0 < Matrix.det (G.jetMetric j)
  flux_smooth : ContDiffOn ℝ ∞ G.metricFlux jetDomain
  lowerOrder_smooth : ContDiffOn ℝ ∞ G.metricLowerOrder jetDomain
  elliptic : UniformlyEllipticOn jetDomain G.metricFlux

/-- Formula-preserving bundling, with no chosen or arbitrary operator. -/
def operator (G : A3SharedGraph D) (C : G.OperatorControl) :
    SmoothQuasilinearOperator C.jetDomain where
  flux := G.metricFlux
  lowerOrder := G.metricLowerOrder
  flux_smooth := C.flux_smooth
  lowerOrder_smooth := C.lowerOrder_smooth
end A3SharedGraph

/-- Actual metric smoothness/positive-definiteness in the chosen smooth chart. -/
theorem A3_actual_chart_metric (G : A3SharedGraph D) :
    (∀ i j, ContDiffOn ℝ ∞ (fun y => actualChartTensor h G.coordinates y i j)
      G.coordinates.chart.target) ∧
    (∀ y ∈ G.coordinates.chart.target, ∀ i j,
      actualChartTensor h G.coordinates y i j = actualChartTensor h G.coordinates y j i) ∧
    (∀ y ∈ G.coordinates.chart.target, ∀ w : E3, w ≠ 0 →
      0 < coordinateInner (actualChartTensor h G.coordinates) y w w) := by
  let c := G.coordinates
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    letI : Bundle.RiemannianBundle (fun p : N => TangentSpace 𝓘(ℝ, E3) p) :=
      ⟨h.toRiemannianMetric⟩
    have hv (k : Fin 3) : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, E3).tangent ∞
        (fun y => (⟨c.chart.symm y, inverseChartDifferential c y (coordinateVector 3 k)⟩ :
          TangentBundle 𝓘(ℝ, E3) N)) c.chart.target := by
      have hs : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3).tangent ∞
          (fun y => (⟨y, (NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k)⟩ :
            TangentBundle 𝓘(ℝ, E3) E3)) :=
        contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
      have ht := c.inverse_smooth.contMDiffOn_tangentMapWithin
        (m := ∞) (by simp) c.chart.open_target.uniqueMDiffOn
      have hc := ht.comp hs.contMDiffOn (by intro y hy; exact hy)
      apply hc.congr
      intro y hy
      change (⟨c.chart.symm y, (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm y)
        ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k))⟩ : TangentBundle 𝓘(ℝ, E3) N) =
          ⟨c.chart.symm y, (mfderivWithin 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm c.chart.target y)
            ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k))⟩
      rw [mfderivWithin_eq_mfderiv (c.chart.open_target.uniqueMDiffOn y hy)
        (((c.inverse_smooth y hy).mdifferentiableWithinAt (by simp)).mdifferentiableAt
          (c.chart.open_target.mem_nhds hy))]
    exact (open scoped Bundle in (hv i |>.inner_bundle (hv j)).contDiffOn)
  · intro y hy i j
    exact h.symm _ _ _
  · intro y hy w hw
    have he : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
      ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
    have hinj : Function.Injective (inverseChartDifferential c y) :=
      (he.symm.mfderiv_injective hy).comp (NormedSpace.fromTangentSpace y).symm.injective
    have hn : inverseChartDifferential c y w ≠ 0 := by
      intro hh
      apply hw
      apply hinj
      simpa only [map_zero] using hh
    have hid (v w : E3) : coordinateInner (actualChartTensor h c) y v w =
        h.inner (c.chart.symm y) (inverseChartDifferential c y v)
          (inverseChartDifferential c y w) := by
      have hsum (v : E3) : (∑ i : Fin 3, v i • coordinateVector 3 i) = v := by
        ext j
        simp [coordinateVector, EuclideanSpace.single, Pi.single_apply]
      have hdiff (v : E3) : inverseChartDifferential c y v =
          ∑ i : Fin 3, v i • inverseChartDifferential c y (coordinateVector 3 i) := by
        simpa only [map_sum, map_smul] using congrArg (inverseChartDifferential c y) (hsum v).symm
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
    rw [hid]
    exact h.pos _ _ hn

set_option maxHeartbeats 0 in
/-- Local bounded-gradient uniformly elliptic control, from the larger C1 disc. -/
theorem A3_actual_metric_operator_control (G : A3SharedGraph D) :
    Nonempty G.OperatorControl := by
  classical
  open Matrix in
  let slopeGram (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
      (n : E3) (p : E2) : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => coordinateInner (fun _ => B) 0
      (L (coordinateVector 2 i) + p i • n)
      (L (coordinateVector 2 j) + p j • n)
  
  
  let splittingGram (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
      (n : E3) : Matrix (Fin 3) (Fin 3) ℝ :=
    fun i j => coordinateInner (fun _ => B) 0
      (if i = 0 then L (coordinateVector 2 0)
        else if i = 1 then L (coordinateVector 2 1) else n)
      (if j = 0 then L (coordinateVector 2 0)
        else if j = 1 then L (coordinateVector 2 1) else n)
  
  let slopeArea (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
      (n : E3) (p : E2) : ℝ :=
    Real.sqrt (Matrix.det (slopeGram B L n p))
  
  let slopeFlux (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
      (n : E3) (p : E2) : E2 :=
    planarGradient (slopeArea B L n) p
  
  
  let slopeHessian (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
      (n : E3) (p : E2) : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => fderiv ℝ (fun q : E2 => slopeFlux B L n q i) p
      (coordinateVector 2 j)
  
  have hhess
      (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef)
      (L : E2 →L[ℝ] E3) (n : E3)
      (hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n))
      (p : E2) (i j : Fin 2) :
      slopeHessian B L n p i j =
        Matrix.det (splittingGram B L n) / slopeArea B L n p *
          (slopeGram B L n p)⁻¹ i j := by
    classical
    have hgram (q : E2) : (slopeGram B L n q).PosDef := by
      let v : Fin 2 → E3 := fun i => L (coordinateVector 2 i) + q i • n
      have hli : LinearIndependent ℝ v := by
        apply Fintype.linearIndependent_iff.mpr
        intro a ha
        have hs : L (∑ i : Fin 2, a i • coordinateVector 2 i) +
            (∑ i : Fin 2, a i * q i) • n = 0 := by
          simpa only [v, smul_add, Finset.sum_add_distrib,
            map_sum, map_smul, mul_smul, Finset.sum_smul] using ha
        have he : ((∑ i : Fin 2, a i • coordinateVector 2 i), ∑ i : Fin 2, a i * q i) =
            ((0 : E2), (0 : ℝ)) := by
          apply hsplit.injective
          simpa only [map_zero, zero_smul, add_zero] using hs
        have hz := congrArg Prod.fst he
        intro i
        have heval := congrArg (fun z : E2 => z i) hz
        fin_cases i <;> simpa [coordinateVector, EuclideanSpace.single, Pi.single_apply] using heval
      let V : Matrix (Fin 3) (Fin 2) ℝ := fun a i => v i a
      have hV : Function.Injective V.mulVec := by
        intro x y hxy
        have hsum : ∑ i, (x i - y i) • v i = 0 := by
          ext a
          have hh := congrFun hxy a
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh
          simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply,
            smul_eq_mul, sub_mul, PiLp.zero_apply] using (by
              dsimp [V] at hh
              nlinarith [hh] : (x 0 - y 0) * v 0 a + (x 1 - y 1) * v 1 a = 0)
        have he := Fintype.linearIndependent_iff.mp hli _ hsum
        funext i
        exact sub_eq_zero.mp (he i)
      have heq : slopeGram B L n q = V.conjTranspose * B * V := by
        ext i j
        change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
          ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
        simp only [Fin.sum_univ_three]
        ring
      rw [heq]
      exact hB.conjTranspose_mul_mul_same hV
    let ci : E3 → E3 → ℝ := coordinateInner (fun _ => B) 0
    have hsym (v w : E3) : ci v w = ci w v := by
      dsimp [ci, coordinateInner]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have hb : B b a = B a b := hB.isHermitian.apply a b
      rw [hb]
      ring
    have hbil (v w : E3) (s t : ℝ) :
        ci (v + s • n) (w + t • n) = ci v w + s * ci n w +
          t * ci v n + s*t*ci n n := by
      simp only [ci, coordinateInner, Fin.sum_univ_three, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul]
      ring
    let a := ci (L (coordinateVector 2 0)) (L (coordinateVector 2 0))
    let b := ci (L (coordinateVector 2 0)) (L (coordinateVector 2 1))
    let c := ci (L (coordinateVector 2 1)) (L (coordinateVector 2 1))
    let d := ci (L (coordinateVector 2 0)) n
    let e := ci (L (coordinateVector 2 1)) n
    let f := ci n n
    have g00 (q : E2) : slopeGram B L n q 0 0 = a + 2*d*q 0 + f*(q 0)^2 := by
      change ci _ _ = _
      rw [hbil, hsym n (L (coordinateVector 2 0))]
      dsimp [a, d, f]
      ring
    have g01 (q : E2) : slopeGram B L n q 0 1 = b+e*q 0+d*q 1+f*q 0*q 1 := by
      change ci _ _ = _
      rw [hbil, hsym n (L (coordinateVector 2 1))]
      dsimp [b, d, e, f]
      ring
    have g10 (q : E2) : slopeGram B L n q 1 0 = b+e*q 0+d*q 1+f*q 0*q 1 := by
      change ci _ _ = _
      rw [hsym]
      exact g01 q
    have g11 (q : E2) : slopeGram B L n q 1 1 = c + 2*e*q 1 + f*(q 1)^2 := by
      change ci _ _ = _
      rw [hbil, hsym n (L (coordinateVector 2 1))]
      dsimp [c, e, f]
      ring
    let Q : E2 → ℝ := fun q => Matrix.det (slopeGram B L n q)
    have hQpos (q : E2) : 0 < Q q := (hgram q).det_pos
    have hQdef (q : E2) : Q q = (c*f-e^2)*(q 0)^2 +
        2*(d*e-b*f)*q 0*q 1+(a*f-d^2)*(q 1)^2+
        2*(c*d-b*e)*q 0+2*(a*e-b*d)*q 1+(a*c-b^2) := by
      dsimp [Q]
      rw [Matrix.det_fin_two, g00, g01, g10, g11]
      ring
    have hsplitdet : Matrix.det (splittingGram B L n) =
        a*c*f-a*e^2-b^2*f+2*b*d*e-c*d^2 := by
      rw [Matrix.det_fin_three]
      change a*c*f-a*e*ci n (L (coordinateVector 2 1))-
        b*ci (L (coordinateVector 2 1)) (L (coordinateVector 2 0))*f+
        b*e*ci n (L (coordinateVector 2 0))+
        d*ci (L (coordinateVector 2 1)) (L (coordinateVector 2 0))*ci n (L (coordinateVector 2 1))-
        d*c*ci n (L (coordinateVector 2 0)) = _
      rw [hsym n (L (coordinateVector 2 0)), hsym n (L (coordinateVector 2 1)),
        hsym (L (coordinateVector 2 1)) (L (coordinateVector 2 0))]
      change a*c*f-a*e*e-b*b*f+b*e*d+d*b*e-d*c*d = _
      ring
    have hquad (a b c d e f : ℝ) (Q : E2 → ℝ)
        (hQdef : ∀ x, Q x = a * (x 0)^2 + 2*b*x 0*x 1 + c*(x 1)^2 + 2*d*x 0 + 2*e*x 1+f)
        (hpos : ∀ x, 0 < Q x) (p : E2) (i j : Fin 2) :
        fderiv ℝ (fun q : E2 => planarGradient (fun x => Real.sqrt (Q x)) q i) p
          (coordinateVector 2 j) =
        (if i = j then (if i = 0 then a else c) else b) / Real.sqrt (Q p) -
          (if i = 0 then a*p 0+b*p 1+d else b*p 0+c*p 1+e) *
          (if j = 0 then a*p 0+b*p 1+d else b*p 0+c*p 1+e) / (Real.sqrt (Q p))^3 := by
      let π0 : E2 →L[ℝ] ℝ := EuclideanSpace.proj 0
      let π1 : E2 →L[ℝ] ℝ := EuclideanSpace.proj 1
      let N0 := fun x : E2 => a*x 0+b*x 1+d
      let N1 := fun x : E2 => b*x 0+c*x 1+e
      have hQ (x : E2) : HasFDerivAt Q ((2*N0 x) • π0 + (2*N1 x) • π1) x := by
        have h0 : HasFDerivAt (fun x : E2 => x 0) π0 x := π0.hasFDerivAt
        have h1 : HasFDerivAt (fun x : E2 => x 1) π1 x := π1.hasFDerivAt
        have h := (((((h0.mul h0).const_mul a).add (((h0.const_mul (2*b)).mul h1))).add
          ((h1.mul h1).const_mul c)).add (h0.const_mul (2*d))).add (h1.const_mul (2*e))
        convert h.add_const f using 1
        · funext y
          rw [hQdef]
          simp only [Pi.add_apply, Pi.mul_apply]
          ring
        · ext v
          simp [N0, N1, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.smulRight_apply, smul_eq_mul]
          <;> ring
      have hF (x : E2) := (hQ x).sqrt (ne_of_gt (hpos x))
      have hsqrt (x : E2) : Real.sqrt (Q x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hpos x))
      have hgrad (x : E2) (k : Fin 2) :
          planarGradient (fun x => Real.sqrt (Q x)) x k =
            (if k = 0 then N0 x else N1 x) / Real.sqrt (Q x) := by
        unfold planarGradient
        rw [(hF x).fderiv]
        fin_cases k <;>
          simp [Fin.sum_univ_two, coordinateVector, EuclideanSpace.single, π0, π1,
            Pi.single_apply, N0, N1] <;> field_simp (disch := first | exact hsqrt _ | exact ne_of_gt (hpos _) | positivity | norm_num) <;> ring
      have hN0 (x : E2) : HasFDerivAt N0 (a • π0 + b • π1) x := by
        exact ((π0.hasFDerivAt.const_mul a).add (π1.hasFDerivAt.const_mul b)).add_const d
      have hN1 (x : E2) : HasFDerivAt N1 (b • π0 + c • π1) x := by
        exact ((π0.hasFDerivAt.const_mul b).add (π1.hasFDerivAt.const_mul c)).add_const e
      have hi := (hasDerivAt_inv (hsqrt p)).comp_hasFDerivAt p (hF p)
      have h0 := (hN0 p).mul hi
      have h1 := (hN1 p).mul hi
      change HasFDerivAt (fun q : E2 => N0 q * (Real.sqrt (Q q))⁻¹) _ p at h0
      change HasFDerivAt (fun q : E2 => N1 q * (Real.sqrt (Q q))⁻¹) _ p at h1
      have heq : (fun q : E2 => planarGradient (fun x => Real.sqrt (Q x)) q i) =
          (fun q => (if i = 0 then N0 q else N1 q) * (Real.sqrt (Q q))⁻¹) := by
        funext q
        rw [hgrad, div_eq_mul_inv]
      rw [heq]
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceEq, ite_true, ite_false] <;>
        first | rw [h0.fderiv] | rw [h1.fderiv]
      all_goals
        simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
          coordinateVector, π0, π1, EuclideanSpace.single, Pi.single_apply, N0, N1]
        <;> field_simp (disch := first | exact hsqrt _ | exact ne_of_gt (hpos _) | positivity | norm_num) <;> ring
    have h := hquad (c*f-e^2) (d*e-b*f) (a*f-d^2) (c*d-b*e) (a*e-b*d)
      (a*c-b^2) Q hQdef hQpos p i j
    change slopeHessian B L n p i j = _
    change fderiv ℝ (fun q : E2 => planarGradient (fun x => Real.sqrt (Q x)) q i) p
      (coordinateVector 2 j) = _
    rw [h, Matrix.inv_def, Matrix.adjugate_fin_two, hsplitdet]
    have hs : Real.sqrt (Q p) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hQpos p))
    have hsq : Real.sqrt (Q p)^2 = Q p := Real.sq_sqrt (hQpos p).le
    have hpow : Real.sqrt (Q p)^3 = Real.sqrt (Q p) * Q p := by
      rw [pow_succ, hsq]
      ring
    change _ = (a*c*f-a*e^2-b^2*f+2*b*d*e-c*d^2) / Real.sqrt (Q p) *
      ((Ring.inverse (Q p)) • !![slopeGram B L n p 1 1, -slopeGram B L n p 0 1;
        -slopeGram B L n p 1 0, slopeGram B L n p 0 0]) i j
    rw [Ring.inverse_eq_inv, hpow]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ite_true, ite_false,
        Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, g00, g01, g10, g11]
    all_goals
      field_simp (disch := first | assumption | exact ne_of_gt (hQpos p) | positivity | norm_num)
      rw [hQdef]
      ring
  
  have hposdef
      (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef)
      (L : E2 →L[ℝ] E3) (n : E3)
      (hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n))
      (p : E2) :
      (slopeHessian B L n p).PosDef := by
    classical
    have hgram (q : E2) : (slopeGram B L n q).PosDef := by
      let v : Fin 2 → E3 := fun i => L (coordinateVector 2 i) + q i • n
      have hli : LinearIndependent ℝ v := by
        apply Fintype.linearIndependent_iff.mpr
        intro a ha
        have hs : L (∑ i : Fin 2, a i • coordinateVector 2 i) +
            (∑ i : Fin 2, a i * q i) • n = 0 := by
          simpa only [v, smul_add, Finset.sum_add_distrib,
            map_sum, map_smul, mul_smul, Finset.sum_smul] using ha
        have he : ((∑ i : Fin 2, a i • coordinateVector 2 i), ∑ i : Fin 2, a i * q i) =
            ((0 : E2), (0 : ℝ)) := by
          apply hsplit.injective
          simpa only [map_zero, zero_smul, add_zero] using hs
        have hz := congrArg Prod.fst he
        intro i
        have heval := congrArg (fun z : E2 => z i) hz
        fin_cases i <;> simpa [coordinateVector, EuclideanSpace.single, Pi.single_apply] using heval
      let V : Matrix (Fin 3) (Fin 2) ℝ := fun a i => v i a
      have hV : Function.Injective V.mulVec := by
        intro x y hxy
        have hsum : ∑ i, (x i - y i) • v i = 0 := by
          ext a
          have hh := congrFun hxy a
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh
          simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply,
            smul_eq_mul, sub_mul, PiLp.zero_apply] using (by
              dsimp [V] at hh
              nlinarith [hh] : (x 0 - y 0) * v 0 a + (x 1 - y 1) * v 1 a = 0)
        have he := Fintype.linearIndependent_iff.mp hli _ hsum
        funext i
        exact sub_eq_zero.mp (he i)
      have heq : slopeGram B L n q = V.conjTranspose * B * V := by
        ext i j
        change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
          ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
        simp only [Fin.sum_univ_three]
        ring
      rw [heq]
      exact hB.conjTranspose_mul_mul_same hV
    let v : Fin 3 → E3 := fun i => if i = 0 then L (coordinateVector 2 0)
      else if i = 1 then L (coordinateVector 2 1) else n
    let V : Matrix (Fin 3) (Fin 3) ℝ := fun a i => v i a
    have hV : Function.Injective V.mulVec := by
      intro x y hxy
      have hs : L ((x 0-y 0) • coordinateVector 2 0 + (x 1-y 1) • coordinateVector 2 1) +
          (x 2-y 2) • n = 0 := by
        ext a
        have hh := congrFun hxy a
        simp [Matrix.mulVec, dotProduct, V, v, Fin.sum_univ_three] at hh
        simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
        nlinarith [hh]
      have he : (((x 0-y 0) • coordinateVector 2 0 + (x 1-y 1) • coordinateVector 2 1), x 2-y 2) =
          ((0 : E2), (0 : ℝ)) := by
        apply hsplit.injective
        simpa only [map_zero, zero_smul, add_zero] using hs
      have h0 := congrArg (fun z : E2 × ℝ => z.1 0) he
      have h1 := congrArg (fun z : E2 × ℝ => z.1 1) he
      have h2 := congrArg Prod.snd he
      simp [coordinateVector, EuclideanSpace.single, Pi.single_apply] at h0 h1
      funext i
      fin_cases i
      · exact sub_eq_zero.mp h0
      · exact sub_eq_zero.mp h1
      · exact sub_eq_zero.mp h2
    have heq : splittingGram B L n = V.conjTranspose * B * V := by
      ext i j
      change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
        ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
      simp only [Fin.sum_univ_three]
      ring
    have hf : (splittingGram B L n).PosDef := by
      rw [heq]
      exact hB.conjTranspose_mul_mul_same hV
    have ha : 0 < slopeArea B L n p := Real.sqrt_pos.mpr (hgram p).det_pos
    have hh : slopeHessian B L n p =
        (Matrix.det (splittingGram B L n) / slopeArea B L n p) • (slopeGram B L n p)⁻¹ := by
      ext i j
      exact hhess B hB L n hsplit p i j
    rw [hh]
    exact (hgram p).inv.smul (div_pos hf.det_pos ha)
  
  have hlower
      (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K)
      (hpositive : ∀ B ∈ K, B.PosDef)
      (P : Set E2) (hP : IsCompact P)
      (L : E2 →L[ℝ] E3) (n : E3)
      (hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n)) :
      ∃ d a ℓ : ℝ, 0 < d ∧ 0 < a ∧ 0 < ℓ ∧
        (∀ B ∈ K, d ≤ Matrix.det (splittingGram B L n)) ∧
        (∀ B ∈ K, ∀ p ∈ P, slopeArea B L n p ≤ a ∧
          ∀ ξ : E2,
            (∑ i : Fin 2, ∑ j : Fin 2,
              slopeGram B L n p i j * ξ i * ξ j) ≤ ℓ * ‖ξ‖ ^ 2 ∧
            d / (a * ℓ) * ‖ξ‖ ^ 2 ≤
              inner ℝ (fderiv ℝ (slopeFlux B L n) p ξ) ξ) := by
    classical
    have hgeom (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef) :
        (splittingGram B L n).PosDef ∧ ∀ p, (slopeGram B L n p).PosDef := by
      have hgram (q : E2) : (slopeGram B L n q).PosDef := by
        let v : Fin 2 → E3 := fun i => L (coordinateVector 2 i) + q i • n
        have hli : LinearIndependent ℝ v := by
          apply Fintype.linearIndependent_iff.mpr
          intro a ha
          have hs : L (∑ i : Fin 2, a i • coordinateVector 2 i) +
              (∑ i : Fin 2, a i * q i) • n = 0 := by
            simpa only [v, smul_add, Finset.sum_add_distrib,
              map_sum, map_smul, mul_smul, Finset.sum_smul] using ha
          have he : ((∑ i : Fin 2, a i • coordinateVector 2 i), ∑ i : Fin 2, a i * q i) =
              ((0 : E2), (0 : ℝ)) := by
            apply hsplit.injective
            simpa only [map_zero, zero_smul, add_zero] using hs
          have hz := congrArg Prod.fst he
          intro i
          have heval := congrArg (fun z : E2 => z i) hz
          fin_cases i <;> simpa [coordinateVector, EuclideanSpace.single, Pi.single_apply] using heval
        let V : Matrix (Fin 3) (Fin 2) ℝ := fun a i => v i a
        have hV : Function.Injective V.mulVec := by
          intro x y hxy
          have hsum : ∑ i, (x i - y i) • v i = 0 := by
            ext a
            have hh := congrFun hxy a
            simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh
            simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply,
              smul_eq_mul, sub_mul, PiLp.zero_apply] using (by
                dsimp [V] at hh
                nlinarith [hh] : (x 0 - y 0) * v 0 a + (x 1 - y 1) * v 1 a = 0)
          have he := Fintype.linearIndependent_iff.mp hli _ hsum
          funext i
          exact sub_eq_zero.mp (he i)
        have heq : slopeGram B L n q = V.conjTranspose * B * V := by
          ext i j
          change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
            ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
          simp only [Fin.sum_univ_three]
          ring
        rw [heq]
        exact hB.conjTranspose_mul_mul_same hV
      let v : Fin 3 → E3 := fun i => if i = 0 then L (coordinateVector 2 0)
        else if i = 1 then L (coordinateVector 2 1) else n
      let V : Matrix (Fin 3) (Fin 3) ℝ := fun a i => v i a
      have hV : Function.Injective V.mulVec := by
        intro x y hxy
        have hs : L ((x 0-y 0) • coordinateVector 2 0 + (x 1-y 1) • coordinateVector 2 1) +
            (x 2-y 2) • n = 0 := by
          ext a
          have hh := congrFun hxy a
          simp [Matrix.mulVec, dotProduct, V, v, Fin.sum_univ_three] at hh
          simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
          nlinarith [hh]
        have he : (((x 0-y 0) • coordinateVector 2 0 + (x 1-y 1) • coordinateVector 2 1), x 2-y 2) =
            ((0 : E2), (0 : ℝ)) := by
          apply hsplit.injective
          simpa only [map_zero, zero_smul, add_zero] using hs
        have h0 := congrArg (fun z : E2 × ℝ => z.1 0) he
        have h1 := congrArg (fun z : E2 × ℝ => z.1 1) he
        have h2 := congrArg Prod.snd he
        simp [coordinateVector, EuclideanSpace.single, Pi.single_apply] at h0 h1
        funext i
        fin_cases i
        · exact sub_eq_zero.mp h0
        · exact sub_eq_zero.mp h1
        · exact sub_eq_zero.mp h2
      have heq : splittingGram B L n = V.conjTranspose * B * V := by
        ext i j
        change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
          ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
        simp only [Fin.sum_univ_three]
        ring
      have hf : (splittingGram B L n).PosDef := by
        rw [heq]
        exact hB.conjTranspose_mul_mul_same hV
      exact ⟨hf, hgram⟩
    have hinner (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.PosDef)
      (L : E2 →L[ℝ] E3) (n : E3)
      (hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • n))
      (p ξ : E2) :
      inner ℝ (fderiv ℝ (slopeFlux B L n) p ξ) ξ =
        ∑ i : Fin 2, ∑ j : Fin 2, slopeHessian B L n p i j * ξ i * ξ j := by
      classical
      have hc (i : Fin 2) : DifferentiableAt ℝ (fun q : E2 => slopeFlux B L n q i) p := by
        by_contra hn
        have hp : 0 < slopeHessian B L n p i i :=
          (hposdef B hB L n hsplit p).diag_pos
        change 0 < (fderiv ℝ (fun q : E2 => slopeFlux B L n q i) p) (coordinateVector 2 i) at hp
        rw [fderiv_zero_of_not_differentiableAt hn, ContinuousLinearMap.zero_apply] at hp
        exact (lt_irrefl 0) hp
      have hf : DifferentiableAt ℝ (slopeFlux B L n) p :=
        (differentiableAt_piLp 2).mpr hc
      have hi (i : Fin 2) : fderiv ℝ (fun q : E2 => slopeFlux B L n q i) p =
          (EuclideanSpace.proj i).comp (fderiv ℝ (slopeFlux B L n) p) := by
        exact ((EuclideanSpace.proj i).hasFDerivAt.comp p hf.hasFDerivAt).fderiv
      have hx : ξ = ∑ j : Fin 2, ξ j • coordinateVector 2 j := by
        ext i
        fin_cases i <;> simp [coordinateVector, EuclideanSpace.single]
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      simp only [RCLike.inner_apply, conj_trivial]
      have hh (i : Fin 2) : (fderiv ℝ (slopeFlux B L n) p ξ) i =
          ∑ j : Fin 2, ξ j * slopeHessian B L n p i j := by
        change (EuclideanSpace.proj i) (fderiv ℝ (slopeFlux B L n) p ξ) = _
        rw [← ContinuousLinearMap.comp_apply, ← hi]
        conv_lhs => rw [hx]
        simp only [map_sum, map_smul, smul_eq_mul]
        rfl
      rw [hh 0, hh 1]
      simp only [Fin.sum_univ_two]
      ring
    have hinv (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.PosDef)
      (ℓ : ℝ) (hℓ : 0 < ℓ)
      (hbound : ∀ ξ : E2, (∑ i : Fin 2, ∑ j : Fin 2, A i j * ξ i * ξ j) ≤ ℓ * ‖ξ‖^2)
      (ξ : E2) : ‖ξ‖^2 / ℓ ≤ ∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j * ξ i * ξ j := by
      classical
      have hn : ‖ξ‖^2 = ξ 0 * ξ 0 + ξ 1 * ξ 1 := by
        rw [← real_inner_self_eq_norm_sq ξ, PiLp.inner_apply]
        simp [Fin.sum_univ_two, RCLike.inner_apply, pow_two]
      have hq (M : Matrix (Fin 2) (Fin 2) ℝ) :
          (∑ i : Fin 2, ∑ j : Fin 2, M i j * ξ i * ξ j) =
            dotProduct (star (WithLp.ofLp ξ)) (Matrix.mulVec M (WithLp.ofLp ξ)) := by
        simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
        ring
      have hc := hA.star_dotProduct_mulVec_mul_le (WithLp.ofLp ξ) (Matrix.mulVec A⁻¹ (WithLp.ofLp ξ))
      have he : Matrix.mulVec A (Matrix.mulVec A⁻¹ (WithLp.ofLp ξ)) = WithLp.ofLp ξ := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), Matrix.one_mulVec]
      rw [he] at hc
      have hs : dotProduct (star (Matrix.mulVec A⁻¹ (WithLp.ofLp ξ))) (WithLp.ofLp ξ) =
          dotProduct (star (WithLp.ofLp ξ)) (Matrix.mulVec A⁻¹ (WithLp.ofLp ξ)) := by
        simp only [star_trivial]
        exact dotProduct_comm _ _
      rw [hs, ← hq A, ← hq A⁻¹] at hc
      have hd : dotProduct (star (WithLp.ofLp ξ)) (WithLp.ofLp ξ) = ‖ξ‖^2 := by
        simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, star_trivial, hn]
      rw [hd, star_trivial] at hc
      have hp : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j * ξ i * ξ j := by
        rw [hq]
        exact hA.inv.posSemidef.dotProduct_mulVec_nonneg _
      have hc' := hc.trans (mul_le_mul_of_nonneg_right (hbound ξ) hp)
      by_cases hx : ξ = 0
      · simp [hx]
      · have hnorm : 0 < ‖ξ‖^2 := pow_pos (norm_pos_iff.mpr hx) _
        apply (div_le_iff₀ hℓ).mpr
        nlinarith
    have hbounds :
        ∃ d a ℓ : ℝ, 0 < d ∧ 0 < a ∧ 0 < ℓ ∧
          (∀ B ∈ K, d ≤ Matrix.det (splittingGram B L n)) ∧
          (∀ B ∈ K, ∀ p ∈ P, slopeArea B L n p ≤ a ∧
            ∀ ξ : E2, (∑ i : Fin 2, ∑ j : Fin 2,
              slopeGram B L n p i j * ξ i * ξ j) ≤ ℓ * ‖ξ‖ ^ 2)
        := by
      have hdcont : Continuous (fun B => Matrix.det (splittingGram B L n)) := by
        apply Continuous.matrix_det
        apply continuous_pi; intro i
        apply continuous_pi; intro j
        change Continuous (fun B : Matrix (Fin 3) (Fin 3) ℝ => ∑ a : Fin 3, ∑ b : Fin 3, B a b *
          (if i = 0 then L (coordinateVector 2 0) else if i = 1 then L (coordinateVector 2 1) else n) a *
          (if j = 0 then L (coordinateVector 2 0) else if j = 1 then L (coordinateVector 2 1) else n) b)
        fun_prop
      obtain ⟨d, hd, hdb⟩ := hK.exists_forall_le' hdcont.continuousOn
        (fun B hB => (hgeom B (hpositive B hB)).1.det_pos)
      have hacont : Continuous (fun z : Matrix (Fin 3) (Fin 3) ℝ × E2 => slopeArea z.1 L n z.2) := by
        apply Real.continuous_sqrt.comp
        apply Continuous.matrix_det
        apply continuous_pi; intro i
        apply continuous_pi; intro j
        unfold slopeGram coordinateInner
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        fun_prop
      obtain ⟨a₀, ha₀⟩ := (hK.prod hP).bddAbove_image hacont.continuousOn
      let c := fun z : Matrix (Fin 3) (Fin 3) ℝ × E2 =>
        ∑ i : Fin 2, ∑ j : Fin 2, |slopeGram z.1 L n z.2 i j|
      have hccont : Continuous c := by
        unfold c slopeGram coordinateInner
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        fun_prop
      obtain ⟨ℓ₀, hℓ₀⟩ := (hK.prod hP).bddAbove_image hccont.continuousOn
      refine ⟨d, max a₀ 1, max ℓ₀ 1, hd, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
        lt_of_lt_of_le zero_lt_one (le_max_right _ _), hdb, ?_⟩
      intro B hB p hp
      refine ⟨(ha₀ ⟨(B,p), ⟨hB,hp⟩, rfl⟩).trans (le_max_left _ _), ?_⟩
      intro ξ
      have hnorm (i : Fin 2) : |ξ i| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ i
      have hterm (i j : Fin 2) : slopeGram B L n p i j * ξ i * ξ j ≤
          |slopeGram B L n p i j| * ‖ξ‖^2 := by
        calc
          _ ≤ |slopeGram B L n p i j * ξ i * ξ j| := le_abs_self _
          _ = |slopeGram B L n p i j| * (|ξ i| * |ξ j|) := by rw [abs_mul,abs_mul];ring
          _ ≤ |slopeGram B L n p i j| * (‖ξ‖ * ‖ξ‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hnorm i) (hnorm j) (abs_nonneg _) (norm_nonneg _)) (abs_nonneg _)
          _ = _ := by ring
      calc
        _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, |slopeGram B L n p i j| * ‖ξ‖^2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
        _ = c (B,p) * ‖ξ‖^2 := by simp only [c,Finset.sum_mul]
        _ ≤ max ℓ₀ 1 * ‖ξ‖^2 := mul_le_mul_of_nonneg_right
          ((hℓ₀ ⟨(B,p), ⟨hB,hp⟩, rfl⟩).trans (le_max_left _ _)) (sq_nonneg _)
    obtain ⟨d,a,ℓ,hd,ha,hℓ,hdet,hbounds⟩ := hbounds
    refine ⟨d,a,ℓ,hd,ha,hℓ,hdet,?_⟩
    intro B hB p hp
    refine ⟨(hbounds B hB p hp).1, ?_⟩
    intro ξ
    refine ⟨(hbounds B hB p hp).2 ξ, ?_⟩
    have hA := hgeom B (hpositive B hB)
    have harea : 0 < slopeArea B L n p := Real.sqrt_pos.mpr (hA.2 p).det_pos
    have hratio : d/a ≤ (Matrix.det (splittingGram B L n))/slopeArea B L n p := by
      apply (div_le_div_iff₀ ha harea).mpr
      exact (mul_le_mul_of_nonneg_left (hbounds B hB p hp).1 hd.le).trans
        (mul_le_mul_of_nonneg_right (hdet B hB) ha.le)
    rw [hinner B (hpositive B hB) L n hsplit p ξ]
    have hsum : (∑ i : Fin 2, ∑ j : Fin 2, slopeHessian B L n p i j * ξ i * ξ j) =
        (Matrix.det (splittingGram B L n)/slopeArea B L n p) *
          (∑ i : Fin 2, ∑ j : Fin 2, (slopeGram B L n p)⁻¹ i j * ξ i * ξ j) := by
      simp_rw [hhess B (hpositive B hB) L n hsplit p]
      simp only [Fin.sum_univ_two]
      ring
    rw [hsum]
    calc
      d/(a*ℓ)*‖ξ‖^2 = (d/a)*(‖ξ‖^2/ℓ) := by ring
      _ ≤ (Matrix.det (splittingGram B L n)/slopeArea B L n p)*(‖ξ‖^2/ℓ) :=
        mul_le_mul_of_nonneg_right hratio (div_nonneg (sq_nonneg _) hℓ.le)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hinv (slopeGram B L n p) (hA.2 p) ℓ hℓ (hbounds B hB p hp).2 ξ)
        (div_nonneg hA.1.det_pos.le harea.le)
  
  have helliptic
      (G : A3SharedGraph D) (K : Set Jet) (hK : IsCompact K)
      (hchart : MapsTo G.jetPoint K G.coordinates.chart.target) :
      UniformlyEllipticOn K G.metricFlux := by
    classical
    have hmetric :
        (∀ i j, ContDiffOn ℝ ∞ (fun y => actualChartTensor h G.coordinates y i j)
          G.coordinates.chart.target) ∧
        (∀ y ∈ G.coordinates.chart.target, ∀ i j,
          actualChartTensor h G.coordinates y i j = actualChartTensor h G.coordinates y j i) ∧
        (∀ y ∈ G.coordinates.chart.target, ∀ w : E3, w ≠ 0 →
          0 < coordinateInner (actualChartTensor h G.coordinates) y w w) := by
      let c := G.coordinates
      refine ⟨?_, ?_, ?_⟩
      · intro i j
        letI : Bundle.RiemannianBundle (fun p : N => TangentSpace 𝓘(ℝ, E3) p) :=
          ⟨h.toRiemannianMetric⟩
        have hv (k : Fin 3) : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, E3).tangent ∞
            (fun y => (⟨c.chart.symm y, inverseChartDifferential c y (coordinateVector 3 k)⟩ :
              TangentBundle 𝓘(ℝ, E3) N)) c.chart.target := by
          have hs : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3).tangent ∞
              (fun y => (⟨y, (NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k)⟩ :
                TangentBundle 𝓘(ℝ, E3) E3)) :=
            contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
          have ht := c.inverse_smooth.contMDiffOn_tangentMapWithin
            (m := ∞) (by simp) c.chart.open_target.uniqueMDiffOn
          have hc := ht.comp hs.contMDiffOn (by intro y hy; exact hy)
          apply hc.congr
          intro y hy
          change (⟨c.chart.symm y, (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm y)
            ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k))⟩ : TangentBundle 𝓘(ℝ, E3) N) =
              ⟨c.chart.symm y, (mfderivWithin 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm c.chart.target y)
                ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k))⟩
          rw [mfderivWithin_eq_mfderiv (c.chart.open_target.uniqueMDiffOn y hy)
            (((c.inverse_smooth y hy).mdifferentiableWithinAt (by simp)).mdifferentiableAt
              (c.chart.open_target.mem_nhds hy))]
        exact (open scoped Bundle in (hv i |>.inner_bundle (hv j)).contDiffOn)
      · intro y hy i j
        exact h.symm _ _ _
      · intro y hy w hw
        have he : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
          ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
        have hinj : Function.Injective (inverseChartDifferential c y) :=
          (he.symm.mfderiv_injective hy).comp (NormedSpace.fromTangentSpace y).symm.injective
        have hn : inverseChartDifferential c y w ≠ 0 := by
          intro hh
          apply hw
          apply hinj
          simpa only [map_zero] using hh
        have hid (v w : E3) : coordinateInner (actualChartTensor h c) y v w =
            h.inner (c.chart.symm y) (inverseChartDifferential c y v)
              (inverseChartDifferential c y w) := by
          have hsum (v : E3) : (∑ i : Fin 3, v i • coordinateVector 3 i) = v := by
            ext j
            simp [coordinateVector, EuclideanSpace.single, Pi.single_apply]
          have hdiff (v : E3) : inverseChartDifferential c y v =
              ∑ i : Fin 3, v i • inverseChartDifferential c y (coordinateVector 3 i) := by
            simpa only [map_sum, map_smul] using congrArg (inverseChartDifferential c y) (hsum v).symm
          unfold coordinateInner actualChartTensor
          rw [hdiff v, hdiff w, map_sum]
          simp only [map_smul, _root_.sum_apply, _root_.smul_apply, map_sum, smul_eq_mul]
          simp only [Finset.mul_sum]
          conv_rhs => rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          ring
        rw [hid]
        exact h.pos _ _ hn
    let B := fun j : Jet => actualChartTensor h G.coordinates (G.jetPoint j)
    have hjcont : Continuous G.jetPoint := by
      unfold A3SharedGraph.jetPoint
      fun_prop
    have hBcont : ContinuousOn B K := by
      apply continuousOn_pi.mpr; intro i
      apply continuousOn_pi.mpr; intro j
      exact ((hmetric.1 i j).continuousOn).comp hjcont.continuousOn hchart
    have hBpos : ∀ b ∈ B '' K, b.PosDef := by
      rintro b ⟨j,hj,rfl⟩
      apply Matrix.PosDef.of_dotProduct_mulVec_pos
      · ext a c
        exact (hmetric.2.1 (G.jetPoint j) (hchart hj) c a)
      · intro x hx
        let w : E3 := WithLp.toLp 2 x
        have hw : w ≠ 0 := by
          intro he
          apply hx
          exact congrArg WithLp.ofLp he
        have hp := hmetric.2.2 (G.jetPoint j) (hchart hj) w hw
        convert hp using 1
        simp only [coordinateInner, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
          Pi.star_apply, star_trivial]
        dsimp [B,w]
        ring
    have hP : IsCompact ((fun j : Jet => j.2.2) '' K) :=
      hK.image (continuous_snd.comp continuous_snd)
    obtain ⟨d,a,ℓ,hd,ha,hℓ,hdet,hbound⟩ :=
      hlower (B '' K) (hK.image_of_continuousOn hBcont)
        hBpos ((fun j : Jet => j.2.2) '' K) hP G.plane G.normal G.splitting
    refine ⟨d/(a*ℓ), div_pos hd (mul_pos ha hℓ), ?_⟩
    intro x z p ξ hj
    have hh := (hbound (B (x,z,p)) (mem_image_of_mem B hj) p
      (mem_image_of_mem (fun j : Jet => j.2.2) hj)).2 ξ |>.2
    convert hh using 1
    rfl
  
  have hsmooth (G : A3SharedGraph D) (U : Set Jet) (hU : IsOpen U)
      (hchart : MapsTo G.jetPoint U G.coordinates.chart.target)
      (hpos : ∀ j ∈ U, 0 < Matrix.det (G.jetMetric j)) :
      ContDiffOn ℝ ∞ G.areaDensity U ∧
      ContDiffOn ℝ ∞ G.metricFlux U ∧
      ContDiffOn ℝ ∞ G.metricLowerOrder U := by
  
    classical
    have hp : ContDiff ℝ ∞ G.jetPoint := by
      unfold A3SharedGraph.jetPoint
      fun_prop
    have ht (i : Fin 2) (a : Fin 3) : ContDiff ℝ ∞
        (fun j : Jet => G.jetTangent j.2.2 i a) := by
      unfold A3SharedGraph.jetTangent
      fun_prop
    have hg (i k : Fin 2) : ContDiffOn ℝ ∞ (fun j => G.jetMetric j i k) U := by
      unfold A3SharedGraph.jetMetric coordinateInner
      apply ContDiffOn.sum
      intro a ha
      apply ContDiffOn.sum
      intro b hb
      exact ((((A3_actual_chart_metric G).1 a b).comp hp.contDiffOn hchart).mul
        (ht i a).contDiffOn).mul (ht k b).contDiffOn
    have hdet : ContDiffOn ℝ ∞ (fun j => Matrix.det (G.jetMetric j)) U := by
      simp only [Matrix.det_fin_two]
      exact ((hg 0 0).mul (hg 1 1)).sub ((hg 0 1).mul (hg 1 0))
    have ha : ContDiffOn ℝ ∞ G.areaDensity U := hdet.sqrt (fun j hj => ne_of_gt (hpos j hj))
    have hd : ContDiffOn ℝ ∞ (fderiv ℝ G.areaDensity) U :=
      ha.fderiv_of_isOpen hU (by simp)
    refine ⟨ha, ?_, ?_⟩
    · have hgrad : ContDiffOn ℝ ∞
          (fun j : Jet => ∑ i : Fin 2,
            (fderiv ℝ G.areaDensity j) ((0 : E2), (0 : ℝ), coordinateVector 2 i) • coordinateVector 2 i) U := by
        apply ContDiffOn.sum
        intro i hi
        exact (hd.clm_apply contDiffOn_const).smul contDiffOn_const
      apply hgrad.congr
      intro j hj
      unfold A3SharedGraph.metricFlux planarGradient
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      have hder := (ha.contDiffAt (hU.mem_nhds hj)).differentiableAt (by simp)
      have hinj : HasFDerivAt (fun p : E2 => (j.1, j.2.1, p))
          ((0 : E2 →L[ℝ] E2).prod ((0 : E2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E2))) j.2.2 :=
        (hasFDerivAt_const j.1 j.2.2).prodMk
          ((hasFDerivAt_const j.2.1 j.2.2).prodMk (hasFDerivAt_id j.2.2))
      exact congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i))
        (hder.hasFDerivAt.comp j.2.2 hinj).fderiv
    · have hz : ContDiffOn ℝ ∞
          (fun j : Jet => -((fderiv ℝ G.areaDensity j) ((0 : E2), (1 : ℝ), (0 : E2)))) U :=
        (hd.clm_apply contDiffOn_const).neg
      apply hz.congr
      intro j hj
      unfold A3SharedGraph.metricLowerOrder
      congr 1
      have hder := (ha.contDiffAt (hU.mem_nhds hj)).differentiableAt (by simp)
      have hinj : HasDerivAt (fun z : ℝ => (j.1, z, j.2.2))
          ((0 : E2), (1 : ℝ), (0 : E2)) j.2.1 :=
        (hasDerivAt_const j.2.1 j.1).prodMk
          ((hasDerivAt_id j.2.1).prodMk (hasDerivAt_const j.2.1 j.2.2))
      exact (hder.hasFDerivAt.comp_hasDerivAt j.2.1 hinj).deriv
  have hgram (G : A3SharedGraph D) (j : Jet)
      (hy : G.jetPoint j ∈ G.coordinates.chart.target) :
      0 < Matrix.det (G.jetMetric j) := by
  
    have hli : LinearIndependent ℝ (G.jetTangent j.2.2) := by
      apply Fintype.linearIndependent_iff.mpr
      intro a ha
      have hs : G.plane (∑ i : Fin 2, a i • coordinateVector 2 i) +
          (∑ i : Fin 2, a i * j.2.2 i) • G.normal = 0 := by
        dsimp only [A3SharedGraph.jetTangent] at ha
        simpa only [smul_add, Finset.sum_add_distrib,
          map_sum, map_smul, mul_smul, Finset.sum_smul] using ha
      have he : ((∑ i : Fin 2, a i • coordinateVector 2 i), ∑ i : Fin 2, a i * j.2.2 i) =
          ((0 : E2), (0 : ℝ)) := by
        apply G.splitting.injective
        simpa only [map_zero, zero_smul, add_zero] using hs
      have hz := congrArg Prod.fst he
      intro i
      have heval := congrArg (fun z : E2 => z i) hz
      fin_cases i <;> simpa [coordinateVector, EuclideanSpace.single, Pi.single_apply] using heval
    have hsym (v w : E3) : coordinateInner (actualChartTensor h G.coordinates) (G.jetPoint j) v w =
        coordinateInner (actualChartTensor h G.coordinates) (G.jetPoint j) w v := by
      unfold coordinateInner
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [(A3_actual_chart_metric G).2.1 (G.jetPoint j) hy b a]
      ring
    have herm : (G.jetMetric j).IsHermitian := by
      ext a b
      change G.jetMetric j b a = G.jetMetric j a b
      exact hsym _ _
    have hpos : (G.jetMetric j).PosDef := by
      apply Matrix.PosDef.of_dotProduct_mulVec_pos herm
      intro ξ hξ
      let v : E3 := ∑ i : Fin 2, ξ i • G.jetTangent j.2.2 i
      have hv : v ≠ 0 := by
        intro hz
        apply hξ
        funext i
        exact Fintype.linearIndependent_iff.mp hli ξ hz i
      have hp := (A3_actual_chart_metric G).2.2 (G.jetPoint j) hy v hv
      convert hp using 1
      unfold A3SharedGraph.jetMetric
      simp only [Matrix.mulVec, dotProduct, Pi.star_apply,
        star_trivial, coordinateInner, v, Fin.sum_univ_two, Fin.sum_univ_three]
      simp only [PiLp.add_apply, PiLp.smul_apply]
      ring
    exact hpos.det_pos

  have hbig : ContDiffOn ℝ 1 G.height (Metric.ball 0 (2 * G.radius)) :=
    G.height_C1.mono Metric.ball_subset_closedBall
  have hgrad : ContinuousOn (planarGradient G.height) (Metric.ball 0 (2 * G.radius)) := by
    apply continuousOn_finsetSum
    intro i hi
    exact ((hbig.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply
      continuousOn_const).smul continuousOn_const
  have hsmall : Metric.closedBall (0 : E2) G.radius ⊆ Metric.ball 0 (2 * G.radius) := by
    intro x hx
    change dist x 0 ≤ G.radius at hx
    change dist x 0 < 2 * G.radius
    linarith [G.radius_pos]
  have hjet : ContinuousOn G.attainedJet (Metric.closedBall 0 G.radius) :=
    continuousOn_id.prodMk ((hbig.continuousOn.mono hsmall).prodMk (hgrad.mono hsmall))
  let K := G.attainedJet '' Metric.closedBall (0 : E2) G.radius
  have hK : IsCompact K := (isCompact_closedBall (0 : E2) G.radius).image_of_continuousOn hjet
  have hjp : Continuous G.jetPoint := by
    unfold A3SharedGraph.jetPoint
    fun_prop
  have hKU : K ⊆ G.jetPoint ⁻¹' G.coordinates.chart.target := by
    rintro j ⟨x,hx,rfl⟩
    apply G.graph_in_chart
    change dist x 0 ≤ G.radius at hx
    change dist x 0 ≤ 2 * G.radius
    linarith [G.radius_pos]
  obtain ⟨J,hJo,hKJ,hJc,hJcomp⟩ := exists_open_between_and_isCompact_closure hK
    (G.coordinates.chart.open_target.preimage hjp) hKU
  have himage : closure (G.jetPoint '' J) ⊆ G.jetPoint '' closure J :=
    closure_minimal (image_mono subset_closure) (hJcomp.image hjp).isClosed
  have hpositive : ∀ j ∈ J, 0 < Matrix.det (G.jetMetric j) :=
    fun j hj => hgram G j (hJc (subset_closure hj))
  have hcoeff := hsmooth G J hJo (fun j hj => hJc (subset_closure hj)) hpositive
  obtain ⟨κ,hκ,hbound⟩ := helliptic G (closure J) hJcomp hJc
  refine ⟨{
    jetDomain := J
    jetDomain_open := hJo
    jetDomain_bounded := hJcomp.isBounded.subset subset_closure
    compactChartControl := (hJcomp.image hjp).of_isClosed_subset isClosed_closure himage
    chartControl := ?_
    attained := ?_
    positiveGram := hpositive
    flux_smooth := hcoeff.2.1
    lowerOrder_smooth := hcoeff.2.2
    elliptic := ⟨κ,hκ,fun x z p ξ hj => hbound x z p ξ (subset_closure hj)⟩ }⟩
  · intro y hy
    obtain ⟨j,hj,rfl⟩ := himage hy
    exact hJc hj
  · intro x hx
    apply hKJ
    exact ⟨x,Metric.ball_subset_closedBall hx,rfl⟩

/-- Reparametrization from the original two minimal sheets, still in the same
actual metric; smoothness on each side is supplied by the geometric producer. -/
theorem A3_original_side_minimality (G : A3SharedGraph D) :
    IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap (G.coordinates.chart (D.edge D.pointParameter)) G.plane G.normal G.height)
      (interior G.sideOne) ∧
    IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap (G.coordinates.chart (D.edge D.pointParameter)) G.plane G.normal G.height)
      (interior G.sideTwo) := by
  let Φ := graphMap (G.coordinates.chart (D.edge D.pointParameter)) G.plane G.normal G.height
  have hgraph (U : Set E2) (hU : IsOpen U) (hUd : U ⊆ G.disc)
      (hw : ContDiffOn ℝ ∞ G.height U) : ContDiffOn ℝ ∞ Φ U :=
    (contDiffOn_const.add G.plane.contDiff.contDiffOn).add (hw.smul_const G.normal)
  have himage : MapsTo Φ G.disc G.coordinates.chart.target := by
    intro x hx
    apply G.graph_in_chart
    change dist x 0 < G.radius at hx
    change dist x 0 ≤ 2 * G.radius
    linarith [G.radius_pos]
  have hinj (U : Set E2) (hU : IsOpen U) (hUd : U ⊆ G.disc)
      (hw : ContDiffOn ℝ ∞ G.height U) (x : E2) (hx : x ∈ U) :
      Function.Injective (fderiv ℝ Φ x) := by
    have hd := (hw.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hder : HasFDerivAt Φ (G.plane + (fderiv ℝ G.height x).smulRight G.normal) x :=
      (G.plane.hasFDerivAt.const_add _).add (hd.hasFDerivAt.smul_const G.normal)
    rw [hder.fderiv]
    intro v w hvw
    have he : (v, fderiv ℝ G.height x v) = (w, fderiv ℝ G.height x w) :=
      G.splitting.injective hvw
    exact congrArg Prod.fst he
  have hside (P : EmbeddedSheet.{u,v} N) (hm : P.Minimal h) (U : Set E2)
      (hU : IsOpen U) (hUd : U ⊆ G.disc) (hw : ContDiffOn ℝ ∞ G.height U)
      (hPI : MapsTo G.parameter U P.image) :
      IsMinimalParametrizationOn (actualChartTensor h G.coordinates) Φ U := by
    have hΦ := hgraph U hU hUd hw
    have hΨ : ContMDiffOn 𝓘(ℝ, E2) 𝓘(ℝ, E3) ∞ G.parameter U :=
      G.coordinates.inverse_smooth.comp hΦ.contMDiffOn (fun x hx => himage (hUd hx))
    have hΨinj (x : E2) (hx : x ∈ U) :
        Function.Injective (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) G.parameter x) := by
      have hmd : G.coordinates.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
        ⟨G.coordinates.smooth.mdifferentiableOn (by simp),
          G.coordinates.inverse_smooth.mdifferentiableOn (by simp)⟩
      have hΦd := (hΦ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
      unfold A3SharedGraph.parameter
      rw [mfderiv_comp x
        ((G.coordinates.inverse_smooth.contMDiffAt
          (G.coordinates.chart.open_target.mem_nhds (himage (hUd hx)))).mdifferentiableAt (by simp))
        hΦd.mdifferentiableAt, mfderiv_eq_fderiv]
      exact (hmd.symm.mfderiv_injective (himage (hUd hx))).comp
        ((NormedSpace.fromTangentSpace (Φ x)).symm.injective.comp
          ((hinj U hU hUd hw x hx).comp (NormedSpace.fromTangentSpace x).injective))
    have hsource : MapsTo G.parameter U G.coordinates.chart.source :=
      fun x hx => G.coordinates.chart.map_target (himage (hUd hx))
    have hset : U ∩ G.parameter ⁻¹' G.coordinates.chart.source = U :=
      inter_eq_left.mpr hsource
    have hminimal := SourceReparametrization.immersed_map_in_original_minimal_sheet
      P hm U hU G.parameter hΨ hΨinj hPI G.coordinates
    rw [hset] at hminimal
    refine ⟨?_, ?_⟩
    · exact hΦ
    · intro x hx
      have heq : G.coordinates.chart ∘ G.parameter =ᶠ[𝓝 x] Φ := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact G.coordinates.chart.right_inv (himage (hUd hy))
      have hderiv := heq.fderiv_eq (𝕜 := ℝ)
      have htangent : ∀ j : Fin 2,
          (fun z => graphTangent (G.coordinates.chart ∘ G.parameter) z j) =ᶠ[𝓝 x]
            (fun z => graphTangent Φ z j) := by
        intro j
        filter_upwards [heq.fderiv (𝕜 := ℝ)] with z hz
        exact congrArg (fun F : E2 →L[ℝ] E3 => F (coordinateVector 2 j)) hz
      have htraceeq : tracedAcceleration (actualChartTensor h G.coordinates)
          (G.coordinates.chart ∘ G.parameter) x =
            tracedAcceleration (actualChartTensor h G.coordinates) Φ x := by
        have hv := heq.eq_of_nhds
        dsimp only [tracedAcceleration]
        have hgram : inducedMetric (actualChartTensor h G.coordinates)
            (G.coordinates.chart ∘ G.parameter) x =
              inducedMetric (actualChartTensor h G.coordinates) Φ x := by
          change (fun i j => coordinateInner (actualChartTensor h G.coordinates)
            ((G.coordinates.chart ∘ G.parameter) x)
            (fderiv ℝ (G.coordinates.chart ∘ G.parameter) x (coordinateVector 2 i))
            (fderiv ℝ (G.coordinates.chart ∘ G.parameter) x (coordinateVector 2 j))) = _
          rw [hv, hderiv]
          rfl
        rw [hgram]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        dsimp only [covariantAcceleration]
        rw [(htangent j).fderiv_eq (𝕜 := ℝ), hv]
        have hti := (htangent i).eq_of_nhds
        have htj := (htangent j).eq_of_nhds
        rw [hti, htj]
      have htrace := hminimal.2 x hx
      rw [htraceeq, hderiv] at htrace
      exact htrace

  constructor
  · apply hside D.sheetOne D.minimalOne (interior G.sideOne) isOpen_interior
      (interior_subset.trans G.sideOne_in_disc) (G.height_smooth_one.mono interior_subset)
    intro x hx
    have hi : G.parameter x ∈ G.parameter '' G.sideOne := ⟨x, interior_subset hx, rfl⟩
    change G.parameter x ∈ (G.coordinates.chart.symm ∘ Φ) '' G.sideOne at hi
    rw [G.sheetOne_exact] at hi
    exact hi.1
  · apply hside D.sheetTwo D.minimalTwo (interior G.sideTwo) isOpen_interior
      (interior_subset.trans G.sideTwo_in_disc) (G.height_smooth_two.mono interior_subset)
    intro x hx
    have hi : G.parameter x ∈ G.parameter '' G.sideTwo := ⟨x, interior_subset hx, rfl⟩
    change G.parameter x ∈ (G.coordinates.chart.symm ∘ Φ) '' G.sideTwo at hi
    rw [G.sheetTwo_exact] at hi
    exact hi.1

set_option maxHeartbeats 0 in
/-- The actual area Euler--Lagrange equation on both original sides. -/
theorem A3_classical_equation_on_sides (G : A3SharedGraph D) :
    (∀ x ∈ interior G.sideOne, G.classicalResidual x = 0) ∧
    (∀ x ∈ interior G.sideTwo, G.classicalResidual x = 0) := by
  classical
  open Matrix in
  have hfirst
      (G : A3SharedGraph D) (Ω : Set E2) (hΩ : IsOpen Ω)
      (hΩdisc : Ω ⊆ G.disc) (hsmooth : ContDiffOn ℝ ∞ G.height Ω) :
      let g := actualChartTensor h G.coordinates
      let Φ := graphMap (G.coordinates.chart (D.edge D.pointParameter))
        G.plane G.normal G.height
      ∀ x ∈ Ω,
        G.classicalResidual x = G.areaDensity (G.attainedJet x) *
          (coordinateInner g (Φ x) (tracedAcceleration g Φ x) G.normal -
            ∑ i : Fin 2, ∑ j : Fin 2, (inducedMetric g Φ x)⁻¹ i j *
              coordinateInner g (Φ x) (tracedAcceleration g Φ x) (graphTangent Φ x i) *
              coordinateInner g (Φ x) (graphTangent Φ x j) G.normal) := by
    classical
    dsimp only
    let f := graphMap (G.coordinates.chart (D.edge D.pointParameter))
      G.plane G.normal G.height
    have hf : ContDiffOn ℝ ∞ f Ω :=
      (contDiffOn_const.add G.plane.contDiff.contDiffOn).add (hsmooth.smul_const G.normal)
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
          simp only [map_smul, _root_.sum_apply, _root_.smul_apply, map_sum, smul_eq_mul]
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
    have hGram (x₀ : E2) (hx₀ : x₀ ∈ Ω) :
        (G.jetMetric (G.attainedJet x₀)).PosDef := by
      let g := actualChartTensor h G.coordinates
      let y := f x₀
      let v : Fin 2 → E3 := fun i => G.jetTangent (planarGradient G.height x₀) i
      have hy : y ∈ G.coordinates.chart.target := by
        apply G.graph_in_chart
        have hd : dist x₀ 0 < G.radius := hΩdisc hx₀
        change dist x₀ 0 ≤ 2 * G.radius
        linarith [G.radius_pos]
      have hB : (g y).PosDef := by
        apply Matrix.PosDef.of_dotProduct_mulVec_pos
        · ext i j
          exact h.symm _ _ _
        · intro ξ hξ
          have hp := (hprops h G.coordinates).2.2 y hy (WithLp.toLp 2 ξ)
            (fun hz => hξ (WithLp.toLp_injective 2 hz))
          convert hp using 1
          simp only [coordinateInner,dotProduct,Matrix.mulVec,Fin.sum_univ_three,
            Pi.star_apply,star_trivial]
          dsimp [g]
          ring
      have hli : LinearIndependent ℝ v := by
        apply Fintype.linearIndependent_iff.mpr
        intro a ha
        have hs : G.plane (∑ i : Fin 2, a i • coordinateVector 2 i) +
            (∑ i : Fin 2, a i * planarGradient G.height x₀ i) • G.normal = 0 := by
          try dsimp only [v,A3SharedGraph.jetTangent] at ha ⊢
          simpa only [smul_add,Finset.sum_add_distrib,map_sum,map_smul,mul_smul,Finset.sum_smul] using ha
        have he : ((∑ i : Fin 2, a i • coordinateVector 2 i),
            ∑ i : Fin 2, a i * planarGradient G.height x₀ i) = ((0 : E2),(0 : ℝ)) := by
          apply G.splitting.injective
          simpa only [map_zero,zero_smul,add_zero] using hs
        have hz := congrArg Prod.fst he
        intro i
        have heval := congrArg (fun z : E2 => z i) hz
        fin_cases i <;> simpa [coordinateVector,EuclideanSpace.single,Pi.single_apply] using heval
      let W : Matrix (Fin 3) (Fin 2) ℝ := fun a i => v i a
      have hW : Function.Injective W.mulVec := by
        intro x y hxy
        have hsum : ∑ i, (x i-y i) • v i = 0 := by
          ext a
          have hh := congrFun hxy a
          simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two] at hh
          simpa only [Fin.sum_univ_two,PiLp.add_apply,PiLp.smul_apply,
            smul_eq_mul,sub_mul,PiLp.zero_apply] using (by
              dsimp [W] at hh
              nlinarith [hh] : (x 0-y 0)*v 0 a+(x 1-y 1)*v 1 a=0)
        have he := Fintype.linearIndependent_iff.mp hli _ hsum
        funext i
        exact sub_eq_zero.mp (he i)
      have heq : G.jetMetric (G.attainedJet x₀) = W.conjTranspose * g y * W := by
        ext i j
        change (∑ a : Fin 3,∑ b : Fin 3,g y a b * v i a * v j b) =
          ∑ b : Fin 3,(∑ a : Fin 3,v i a * g y a b)*v j b
        simp only [Fin.sum_univ_three]
        ring
      rw [heq]
      exact hB.conjTranspose_mul_mul_same hW
    intro x hx
    have hw : DifferentiableAt ℝ G.height x :=
      (hsmooth.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
    have hfd : HasFDerivAt f (G.plane + (fderiv ℝ G.height x).smulRight G.normal) x := by
      convert ((hasFDerivAt_const _ x).add G.plane.hasFDerivAt).add
        (hw.hasFDerivAt.smul_const G.normal) using 1 <;> first | rfl | simp only [zero_add]
    have htangent (i : Fin 2) : graphTangent f x i =
        G.jetTangent (planarGradient G.height x) i := by
      try dsimp only [graphTangent,A3SharedGraph.jetTangent,A3SharedGraph.attainedJet]
      simp only [hfd.fderiv,ContinuousLinearMap.add_apply,ContinuousLinearMap.smulRight_apply]
      have hgrad : planarGradient G.height x i = fderiv ℝ G.height x (coordinateVector 2 i) := by
        fin_cases i <;> simp [planarGradient, coordinateVector, PiLp.single_apply]
      rw [hgrad]
    have hmetric : inducedMetric (actualChartTensor h G.coordinates) f x =
        G.jetMetric (G.attainedJet x) := by
      ext i j
      try dsimp only [inducedMetric,A3SharedGraph.jetMetric,A3SharedGraph.attainedJet,A3SharedGraph.jetPoint]
      simp only [htangent]
      rfl
    let p := planarGradient G.height x
    let y := f x
    let B : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
      ∑ a : Fin 3, ∑ b : Fin 3,
        actualChartTensor h G.coordinates y a b •
          (PiLp.proj 2 (fun _ : Fin 3 => ℝ) a).smulRight
            (PiLp.proj 2 (fun _ : Fin 3 => ℝ) b)
    have hinner (v w : E3) :
        coordinateInner (actualChartTensor h G.coordinates) y v w = B v w := by
      simp only [B, coordinateInner, _root_.sum_apply, _root_.smul_apply,
        ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, smul_eq_mul, mul_assoc]
    let A : Matrix (Fin 2) (Fin 2) ℝ := G.jetMetric (G.attainedJet x)
    let V : Fin 2 → E3 := fun i => graphTangent f x i
    have hpos : 0 < A.det := (hGram x hx).det_pos
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
    have hgraph : y ∈ G.coordinates.chart.target := by
      apply G.graph_in_chart
      have hd : dist x 0 < G.radius := hΩdisc hx
      change dist x 0 ≤ 2 * G.radius
      linarith [G.radius_pos]
    have hVarAlg (A : Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ) (b : Fin 2 → ℝ)
        (K : Fin 2 → Fin 2 → Fin 2 → ℝ) (Kn E Z : Matrix (Fin 2) (Fin 2) ℝ)
        (hA : A 1 0 = A 0 1) (hK : ∀ i j k,K i j k = K j i k)
        (hKn : ∀ i j,Kn i j = Kn j i) (hZ : Z 1 0 = Z 0 1)
        (hs : s ≠ 0) (hsquare : s ^ 2 = A.det) :
        let dA := fun k i j => K k i j + K k j i
        let db := fun k i => Kn k i + (1 / 2 : ℝ) * (E k i - E i k + Z k i)
        let ds := fun k => (A 1 1 * dA k 0 0 + A 0 0 * dA k 1 1 -
          2 * A 0 1 * dA k 0 1) / (2 * s)
        ((dA 0 1 1 * b 0 + A 1 1 * db 0 0 -
            (dA 0 0 1 * b 1 + A 0 1 * db 0 1)) * s -
            (A 1 1 * b 0 - A 0 1 * b 1) * ds 0) / s ^ 2 +
        ((dA 1 0 0 * b 1 + A 0 0 * db 1 1 -
            (dA 1 0 1 * b 0 + A 0 1 * db 1 0)) * s -
            (A 0 0 * b 1 - A 0 1 * b 0) * ds 1) / s ^ 2 -
          (A 1 1 * Z 0 0 + A 0 0 * Z 1 1 - 2 * A 0 1 * Z 0 1) / (2 * s) =
          s * ((∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j * Kn i j) -
            ∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j *
              (∑ k : Fin 2, ∑ l : Fin 2, A⁻¹ k l * K k l i) * b j) := by
      classical
      dsimp only
      have hi : A⁻¹ = (s ^ 2)⁻¹ • !![A 1 1,-A 0 1;-A 1 0,A 0 0] := by
        rw [Matrix.inv_def,Matrix.adjugate_fin_two,← hsquare]
        simp only [Ring.inverse_eq_inv]
      rw [hi]
      simp only [Fin.sum_univ_two,Matrix.smul_apply,smul_eq_mul,Matrix.of_apply,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.head_fin_const,
        hA,hK,hKn,hZ]
      have hdet : A 0 0 * A 1 1 - A 0 1 * A 0 1 = s ^ 2 := by
        rw [hsquare,Matrix.det_fin_two,hA]
      field_simp (discharger := first | assumption | positivity | norm_num | simp only [hs])
      have hs4 : s ^ 4 = (A 0 0 * A 1 1 - A 0 1 * A 0 1) ^ 2 := by
        calc
          s ^ 4 = (s ^ 2) ^ 2 := by ring
          _ = _ := by rw [← hdet]
      ring_nf
      simp only [hs4,← hdet]
      ring
    have hConnLower (g : MetricTensor) (y : E3) (hg : IsUnit (g y).det)
        (hsym : ∀ z a b, g z a b = g z b a) (u v w : E3) :
        coordinateInner g y
          (∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3,
            christoffel g y a b k * u a * v b) • coordinateVector 3 k) w =
          (1 / 2 : ℝ) *
            ((∑ a : Fin 3, ∑ b : Fin 3,fderiv ℝ (fun z => g z a b) y u * v a * w b) +
             (∑ a : Fin 3, ∑ b : Fin 3,fderiv ℝ (fun z => g z a b) y v * u a * w b) -
             (∑ a : Fin 3, ∑ b : Fin 3,fderiv ℝ (fun z => g z a b) y w * u a * v b)) := by
      classical
      have hLower (g : MetricTensor) (y : E3) (hg : IsUnit (g y).det)
          (hsym : ∀ a b, g y a b = g y b a) (u v w : E3) :
          coordinateInner g y
            (∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3,
              christoffel g y a b k * u a * v b) • coordinateVector 3 k) w =
            (1 / 2 : ℝ) * (∑ a : Fin 3, ∑ b : Fin 3, ∑ l : Fin 3,
              (partial3 (fun z => g z l b) y a + partial3 (fun z => g z l a) y b -
                partial3 (fun z => g z a b) y l) * u a * v b * w l) := by
        classical
        have hlower (a b l : Fin 3) :
            (∑ k : Fin 3, g y l k * christoffel g y a b k) =
              (1 / 2 : ℝ) * (partial3 (fun z => g z l b) y a +
                partial3 (fun z => g z l a) y b - partial3 (fun z => g z a b) y l) := by
          let R : Fin 3 → ℝ := fun m => partial3 (fun z => g z m b) y a +
            partial3 (fun z => g z m a) y b - partial3 (fun z => g z a b) y m
          change (∑ k : Fin 3, g y l k * ((1 / 2 : ℝ) * ∑ m : Fin 3, (g y)⁻¹ k m * R m)) =
            (1 / 2 : ℝ) * R l
          calc
            _ = (1 / 2 : ℝ) * ∑ m : Fin 3, (g y * (g y)⁻¹) l m * R m := by
              simp only [Matrix.mul_apply,Fin.sum_univ_three]
              ring
            _ = _ := by
              rw [Matrix.mul_nonsing_inv _ hg]
              change (1 / 2 : ℝ) * (∑ m : Fin 3, (if l = m then 1 else 0) * R m) = _
              simp
        have hcoord (s : Fin 3 → ℝ) (k : Fin 3) :
            (∑ i : Fin 3,s i • coordinateVector 3 i) k = s k := by
          simp [coordinateVector,EuclideanSpace.single,Pi.single_apply]
        simp only [coordinateInner,hcoord]
        calc
          _ = ∑ a : Fin 3, ∑ b : Fin 3, ∑ l : Fin 3,
              (∑ k : Fin 3,g y l k * christoffel g y a b k) * u a * v b * w l := by
            simp only [Fin.sum_univ_three,hsym]
            ring
          _ = _ := by
            simp only [hlower,Fin.sum_univ_three]
            ring
      rw [hLower g y hg (hsym y)]
      have hsum (v : E3) : (∑ i : Fin 3,v i • coordinateVector 3 i) = v := by
        ext j
        simp [coordinateVector,EuclideanSpace.single,Pi.single_apply]
      have hexpand (F : E3 → ℝ) (d : E3) : fderiv ℝ F y d =
          ∑ i : Fin 3,partial3 F y i * d i := by
        conv_lhs => rw [← hsum d]
        try dsimp only [partial3]
        simp only [map_sum,map_smul,smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have hdsym (a i j : Fin 3) : partial3 (fun z => g z i j) y a =
          partial3 (fun z => g z j i) y a := by
        have he : (fun z => g z i j) = (fun z => g z j i) := funext (fun z => hsym z i j)
        rw [he]
      simp only [hexpand,Fin.sum_univ_three,hdsym]
      ring
    have hInnerDeriv (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
        (g : MetricTensor) (f U V : X → E3) (x d : X)
        (hg : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) (f x))
        (hf : DifferentiableAt ℝ f x) (hU : DifferentiableAt ℝ U x)
        (hV : DifferentiableAt ℝ V x) :
        fderiv ℝ (fun z => coordinateInner g (f z) (U z) (V z)) x d =
          (∑ a : Fin 3, ∑ b : Fin 3,
            fderiv ℝ (fun z => g z a b) (f x) (fderiv ℝ f x d) * U x a * V x b) +
          coordinateInner g (f x) (fderiv ℝ U x d) (V x) +
          coordinateInner g (f x) (U x) (fderiv ℝ V x d) := by
      classical
      have hterm (a b : Fin 3) :
          fderiv ℝ (fun z => g (f z) a b * U z a * V z b) x d =
            fderiv ℝ (fun z => g z a b) (f x) (fderiv ℝ f x d) * U x a * V x b +
            g (f x) a b * (fderiv ℝ U x d) a * V x b +
            g (f x) a b * U x a * (fderiv ℝ V x d) b := by
        have hp := ((((hg a b).hasFDerivAt.comp x hf.hasFDerivAt).mul
          ((EuclideanSpace.proj (𝕜 := ℝ) a).hasFDerivAt.comp x hU.hasFDerivAt)).mul
          ((EuclideanSpace.proj (𝕜 := ℝ) b).hasFDerivAt.comp x hV.hasFDerivAt))
        change HasFDerivAt (fun z => g (f z) a b * U z a * V z b) _ x at hp
        have he := congrArg (fun L : X →L[ℝ] ℝ => L d) hp.fderiv
        simp only [Function.comp_def,Pi.mul_apply,EuclideanSpace.coe_proj,_root_.add_apply,_root_.smul_apply,
          smul_eq_mul,ContinuousLinearMap.comp_apply] at he
        rw [he]
        ring
      have hdiff (a b : Fin 3) : DifferentiableAt ℝ
          (fun z => g (f z) a b * U z a * V z b) x :=
        (((hg a b).comp x hf).mul
          ((EuclideanSpace.proj (𝕜 := ℝ) a).differentiableAt.comp x hU)).mul
          ((EuclideanSpace.proj (𝕜 := ℝ) b).differentiableAt.comp x hV)
      unfold coordinateInner
      rw [fderiv_fun_sum (fun a _ => DifferentiableAt.fun_sum (fun b _ => hdiff a b))]
      simp only [_root_.sum_apply]
      simp_rw [fderiv_fun_sum (fun b _ => hdiff _ b),_root_.sum_apply,hterm]
      simp only [Fin.sum_univ_three]
      ring
    let g := actualChartTensor h G.coordinates
    let Af : E2 → Matrix (Fin 2) (Fin 2) ℝ := inducedMetric g f
    let bf : E2 → Fin 2 → ℝ := fun z i => coordinateInner g (f z) (graphTangent f z i) G.normal
    let sf : E2 → ℝ := fun z => Real.sqrt (Af z).det
    let md (u v w : E3) := ∑ a : Fin 3,∑ b : Fin 3,
      fderiv ℝ (fun z => g z a b) y u * v a * w b
    let acc (i j : Fin 2) := covariantAcceleration g f x i j
    let K (i j k : Fin 2) := B (acc i j) (V k)
    let Kn (i j : Fin 2) := B (acc i j) G.normal
    let E (i j : Fin 2) := md (V i) (V j) G.normal
    let Z (i j : Fin 2) := md G.normal (V i) (V j)
    have hgdiff (a b : Fin 3) : DifferentiableAt ℝ (fun z => g z a b) y :=
      (((hprops h G.coordinates).1 a b).contDiffAt
        (G.coordinates.chart.open_target.mem_nhds hgraph)).differentiableAt (by simp)
    have hgsym (z : E3) (a b : Fin 3) : g z a b = g z b a := h.symm _ _ _
    have hmdsym (u v w : E3) : md u v w = md u w v := by
      have hd (a b : Fin 3) : fderiv ℝ (fun z => g z a b) y =
          fderiv ℝ (fun z => g z b a) y := by
        congr 1
        exact funext (fun z => hgsym z a b)
      simp only [md,Fin.sum_univ_three,hd]
      ring
    have hZsym : Z 1 0 = Z 0 1 := hmdsym _ _ _
    have hgfpos : (g y).PosDef := by
      apply Matrix.PosDef.of_dotProduct_mulVec_pos
      · ext i j
        simpa only [Matrix.conjTranspose_apply,star_trivial] using hgsym y j i
      · intro ξ hξ
        have hp := (hprops h G.coordinates).2.2 y hgraph (WithLp.toLp 2 ξ)
          (fun hz => hξ (WithLp.toLp_injective 2 hz))
        change 0 < ∑ a : Fin 3,∑ b : Fin 3,g y a b * ξ a * ξ b at hp
        convert hp using 1
        simp only [dotProduct,Matrix.mulVec,coordinateInner,Fin.sum_univ_three,
          Pi.star_apply,star_trivial]
        ring
    have hgg : IsUnit (g y).det := isUnit_iff_ne_zero.mpr hgfpos.det_pos.ne'
    let gam (u v : E3) := ∑ k : Fin 3,(∑ a : Fin 3,∑ b : Fin 3,
      christoffel g y a b k * u a * v b) • coordinateVector 3 k
    have hgam (u v w : E3) : B (gam u v) w =
        (1/2 : ℝ) * (md u v w + md v u w - md w u v) := by
      rw [← hinner]
      exact hConnLower g y hgg hgsym u v w
    have hfAt : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hΩ.mem_nhds hx)
    have hVD (i : Fin 2) : DifferentiableAt ℝ (fun z => graphTangent f z i) x :=
      (hfAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp) |>.clm_apply (differentiableAt_const _)
    have hsecond (i j : Fin 2) :
        fderiv ℝ (fun z => graphTangent f z j) x (coordinateVector 2 i) =
          fderiv ℝ (fderiv ℝ f) x (coordinateVector 2 i) (coordinateVector 2 j) := by
      have hp := ((hfAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.clm_apply
        (hasFDerivAt_const (coordinateVector 2 j) x)
      try dsimp only [graphTangent]
      simpa only [ContinuousLinearMap.comp_apply,_root_.zero_apply,map_zero,_root_.add_apply,zero_add,ContinuousLinearMap.flip_apply] using
        congrArg (fun L : E2 →L[ℝ] E3 => L (coordinateVector 2 i)) hp.fderiv
    have haccsym (i j : Fin 2) : acc i j = acc j i := by
      have hc (a b k : Fin 3) : christoffel g y a b k = christoffel g y b a k := by
        have he : (fun z => g z a b) = (fun z => g z b a) := funext (fun z => hgsym z a b)
        try dsimp only [christoffel]
        simp only [he,add_comm]
      try dsimp only [acc,covariantAcceleration]
      simp only [hsecond]
      change fderiv ℝ (fderiv ℝ f) x (coordinateVector 2 i) (coordinateVector 2 j) + gam (V i) (V j) =
        fderiv ℝ (fderiv ℝ f) x (coordinateVector 2 j) (coordinateVector 2 i) + gam (V j) (V i)
      rw [(hfAt.isSymmSndFDerivAt (by norm_num)).eq]
      congr 1
      unfold gam
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      simp only [Fin.sum_univ_three,hc]
      ring
    have hKsym (i j k : Fin 2) : K i j k = K j i k := by
      change B (acc i j) (V k) = B (acc j i) (V k)
      rw [haccsym]
    have hKnsym (i j : Fin 2) : Kn i j = Kn j i := by
      change B (acc i j) G.normal = B (acc j i) G.normal
      rw [haccsym]
    have hAdiff (i j : Fin 2) : DifferentiableAt ℝ (fun z => Af z i j) x := by
      change DifferentiableAt ℝ (fun z => ∑ a : Fin 3,∑ b : Fin 3,
        g (f z) a b * graphTangent f z i a * graphTangent f z j b) x
      apply DifferentiableAt.fun_sum
      intro a ha
      apply DifferentiableAt.fun_sum
      intro b hb
      exact (((hgdiff a b).comp x hfd.differentiableAt).mul
        ((EuclideanSpace.proj (𝕜 := ℝ) a).differentiableAt.comp x (hVD i))).mul
        ((EuclideanSpace.proj (𝕜 := ℝ) b).differentiableAt.comp x (hVD j))
    have hbDiff (i : Fin 2) : DifferentiableAt ℝ (fun z => bf z i) x := by
      apply DifferentiableAt.fun_sum
      intro a ha
      apply DifferentiableAt.fun_sum
      intro b hb
      exact (((hgdiff a b).comp x hfd.differentiableAt).mul
        ((EuclideanSpace.proj (𝕜 := ℝ) a).differentiableAt.comp x (hVD i))).mul_const _
    have hAD (k i j : Fin 2) : fderiv ℝ (fun z => Af z i j) x (coordinateVector 2 k) =
        K k i j + K k j i := by
      have hd := hInnerDeriv E2 g f (fun z => graphTangent f z i)
        (fun z => graphTangent f z j) x (coordinateVector 2 k) hgdiff
        hfd.differentiableAt (hVD i) (hVD j)
      change fderiv ℝ (fun z => Af z i j) x (coordinateVector 2 k) = _ at hd
      rw [hd]
      try dsimp only [acc,K,covariantAcceleration]
      simp only [map_add,_root_.add_apply]
      change md (V k) (V i) (V j) +
        coordinateInner g y (fderiv ℝ (fun z => graphTangent f z i) x (coordinateVector 2 k)) (V j) +
        coordinateInner g y (V i) (fderiv ℝ (fun z => graphTangent f z j) x (coordinateVector 2 k)) =
        B (fderiv ℝ (fun z => graphTangent f z i) x (coordinateVector 2 k)) (V j) +
        B (gam (V k) (V i)) (V j) +
        (B (fderiv ℝ (fun z => graphTangent f z j) x (coordinateVector 2 k)) (V i) +
        B (gam (V k) (V j)) (V i))
      rw [hinner,hinner,hBsym (V i),hgam,hgam]
      simp only [hmdsym]
      ring
    have hbD (k i : Fin 2) : fderiv ℝ (fun z => bf z i) x (coordinateVector 2 k) =
        Kn k i + (1/2 : ℝ) * (E k i - E i k + Z k i) := by
      have hd := hInnerDeriv E2 g f (fun z => graphTangent f z i)
        (fun _ => G.normal) x (coordinateVector 2 k) hgdiff
        hfd.differentiableAt (hVD i) (differentiableAt_const _)
      change fderiv ℝ (fun z => bf z i) x (coordinateVector 2 k) = _ at hd
      rw [hd]
      simp only [fderiv_const_apply,_root_.zero_apply,PiLp.zero_apply,coordinateInner,mul_zero,Finset.sum_const_zero,add_zero]
      change md (V k) (V i) G.normal +
        coordinateInner g y (fderiv ℝ (fun z => graphTangent f z i) x (coordinateVector 2 k)) G.normal = _
      rw [hinner]
      try dsimp only [acc,Kn,covariantAcceleration]
      simp only [map_add,_root_.add_apply]
      change md (V k) (V i) G.normal + B _ G.normal =
        B _ G.normal + B (gam (V k) (V i)) G.normal + _
      rw [hgam]
      simp only [E,Z]
      ring
    have hFluxFormula (x₀ : E2) (hx₀ : x₀ ∈ Ω) :
        G.attainedFlux x₀ 0 = (Af x₀ 1 1 * bf x₀ 0 - Af x₀ 0 1 * bf x₀ 1) / sf x₀ ∧
        G.attainedFlux x₀ 1 = (Af x₀ 0 0 * bf x₀ 1 - Af x₀ 0 1 * bf x₀ 0) / sf x₀ := by
      have hw : DifferentiableAt ℝ G.height x₀ :=
        (hsmooth.contDiffAt (hΩ.mem_nhds hx₀)).differentiableAt (by simp)
      have hfd : HasFDerivAt f (G.plane + (fderiv ℝ G.height x₀).smulRight G.normal) x₀ := by
        convert ((hasFDerivAt_const _ x₀).add G.plane.hasFDerivAt).add
          (hw.hasFDerivAt.smul_const G.normal) using 1 <;> first | rfl | simp only [zero_add]
      have htangent (i : Fin 2) : graphTangent f x₀ i =
          G.jetTangent (planarGradient G.height x₀) i := by
        try dsimp only [graphTangent,A3SharedGraph.jetTangent,A3SharedGraph.attainedJet]
        simp only [hfd.fderiv,ContinuousLinearMap.add_apply,ContinuousLinearMap.smulRight_apply]
        have hgrad : planarGradient G.height x₀ i = fderiv ℝ G.height x₀ (coordinateVector 2 i) := by
          fin_cases i <;> simp [planarGradient, coordinateVector, PiLp.single_apply]
        rw [hgrad]
      have hmetric : inducedMetric (actualChartTensor h G.coordinates) f x₀ =
          G.jetMetric (G.attainedJet x₀) := by
        ext i j
        try dsimp only [inducedMetric,A3SharedGraph.jetMetric,A3SharedGraph.attainedJet,A3SharedGraph.jetPoint]
        simp only [htangent]
        rfl
      have hdet : 0 < Matrix.det (inducedMetric (actualChartTensor h G.coordinates) f x₀) := by
        rw [hmetric]
        exact (hGram x₀ hx₀).det_pos
      let p := planarGradient G.height x₀
      let y := f x₀
      let B : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
        ∑ a : Fin 3, ∑ b : Fin 3,
          actualChartTensor h G.coordinates y a b •
            (PiLp.proj 2 (fun _ : Fin 3 => ℝ) a).smulRight
              (PiLp.proj 2 (fun _ : Fin 3 => ℝ) b)
      have hinner (v w : E3) :
          coordinateInner (actualChartTensor h G.coordinates) y v w = B v w := by
        simp only [B, coordinateInner, _root_.sum_apply, _root_.smul_apply,
          ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, smul_eq_mul, mul_assoc]
      let P (i : Fin 2) : E2 →L[ℝ] E3 :=
        (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i).smulRight G.normal
      have hTi (i : Fin 2) : HasFDerivAt (fun z => G.jetTangent z i) (P i) p := by
        convert (hasFDerivAt_const (G.plane (coordinateVector 2 i)) p).add (P i).hasFDerivAt using 1
        · rfl
        · simp only [zero_add]
      have hA (i k : Fin 2) : HasFDerivAt
          (fun z => G.jetMetric (x₀, G.height x₀, z) i k)
          ((B (G.jetTangent p i)).comp (P k) +
            (B.comp (P i)).flip (G.jetTangent p k)) p := by
        convert (B.hasFDerivAt.comp p (hTi i)).clm_apply (hTi k) using 1
        · funext z
          exact hinner _ _
        · rfl
      let A : Matrix (Fin 2) (Fin 2) ℝ := G.jetMetric (G.attainedJet x₀)
      have hAdet : HasFDerivAt (fun z => Matrix.det (G.jetMetric (x₀, G.height x₀, z)))
          (G.jetMetric (x₀, G.height x₀, p) 0 0 •
            ((B (G.jetTangent p 1)).comp (P 1) + (B.comp (P 1)).flip (G.jetTangent p 1)) +
          G.jetMetric (x₀, G.height x₀, p) 1 1 •
            ((B (G.jetTangent p 0)).comp (P 0) + (B.comp (P 0)).flip (G.jetTangent p 0)) -
          (G.jetMetric (x₀, G.height x₀, p) 0 1 •
            ((B (G.jetTangent p 1)).comp (P 0) + (B.comp (P 1)).flip (G.jetTangent p 0)) +
          G.jetMetric (x₀, G.height x₀, p) 1 0 •
            ((B (G.jetTangent p 0)).comp (P 1) + (B.comp (P 0)).flip (G.jetTangent p 1)))) p := by
        convert ((hA 0 0).mul (hA 1 1)).sub ((hA 0 1).mul (hA 1 0)) using 1
        funext z
        exact Matrix.det_fin_two _
      have hpos : 0 < Matrix.det (G.jetMetric (x₀, G.height x₀, p)) :=
        (hGram x₀ hx₀).det_pos
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
      have hflux0 : G.metricFlux (G.attainedJet x₀) 0 =
          (A 1 1 * B G.normal (G.jetTangent p 0) -
            A 0 1 * B G.normal (G.jetTangent p 1)) / Real.sqrt A.det := by
        change planarGradient (fun z => G.areaDensity (x₀, G.height x₀, z)) p 0 = _
        have hgradient : planarGradient (fun z => G.areaDensity (x₀, G.height x₀, z)) p 0 =
            fderiv ℝ (fun z => G.areaDensity (x₀, G.height x₀, z)) p (coordinateVector 2 0) := by
          simp [planarGradient, coordinateVector]
        rw [hgradient]
        try dsimp only [A3SharedGraph.areaDensity]
        rw [hF.fderiv]
        simp only [_root_.smul_apply, smul_eq_mul, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
        simp only [P, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply,
          coordinateVector, EuclideanSpace.single, PiLp.single_apply]
        norm_num only [Fin.reduceEq, ite_true, ite_false, zero_smul, one_smul, map_zero,
          mul_zero, zero_add, add_zero, _root_.zero_apply]
        change 1 / (2 * Real.sqrt A.det) *
          (A 1 1 * (B (G.jetTangent p 0) G.normal + B G.normal (G.jetTangent p 0)) -
            (A 0 1 * B (G.jetTangent p 1) G.normal +
              A 1 0 * B G.normal (G.jetTangent p 1))) = _
        rw [hBsym (G.jetTangent p 0) G.normal, hBsym (G.jetTangent p 1) G.normal, ← hAsym]
        have hroot : Real.sqrt A.det ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
        field_simp (discharger := first | assumption | positivity | norm_num | simp only [hroot])
        <;> ring
      have hflux1 : G.metricFlux (G.attainedJet x₀) 1 =
          (A 0 0 * B G.normal (G.jetTangent p 1) -
            A 0 1 * B G.normal (G.jetTangent p 0)) / Real.sqrt A.det := by
        change planarGradient (fun z => G.areaDensity (x₀, G.height x₀, z)) p 1 = _
        have hgradient : planarGradient (fun z => G.areaDensity (x₀, G.height x₀, z)) p 1 =
            fderiv ℝ (fun z => G.areaDensity (x₀, G.height x₀, z)) p (coordinateVector 2 1) := by
          simp [planarGradient, coordinateVector]
        rw [hgradient]
        try dsimp only [A3SharedGraph.areaDensity]
        rw [hF.fderiv]
        simp only [_root_.smul_apply, smul_eq_mul, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
        simp only [P, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply,
          coordinateVector, EuclideanSpace.single, PiLp.single_apply]
        norm_num only [Fin.reduceEq, ite_true, ite_false, zero_smul, one_smul, map_zero,
          mul_zero, zero_add, add_zero, _root_.zero_apply]
        change 1 / (2 * Real.sqrt A.det) *
          (A 0 0 * (B (G.jetTangent p 1) G.normal + B G.normal (G.jetTangent p 1)) -
            (A 0 1 * B G.normal (G.jetTangent p 0) +
              A 1 0 * B (G.jetTangent p 0) G.normal)) = _
        rw [hBsym (G.jetTangent p 1) G.normal, hBsym (G.jetTangent p 0) G.normal, ← hAsym]
        have hroot : Real.sqrt A.det ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
        field_simp (discharger := first | assumption | positivity | norm_num | simp only [hroot])
        <;> ring
      have hAF : Af x₀ = A := hmetric
      have hBF (i : Fin 2) : bf x₀ i = B (G.jetTangent p i) G.normal := by
        change coordinateInner (actualChartTensor h G.coordinates) (f x₀) (graphTangent f x₀ i) G.normal = _
        rw [htangent]
        exact hinner _ _
      constructor
      · change G.metricFlux (G.attainedJet x₀) 0 = _
        rw [hflux0]
        simp only [sf,hAF,hBF,hBsym]
      · change G.metricFlux (G.attainedJet x₀) 1 = _
        rw [hflux1]
        simp only [sf,hAF,hBF,hBsym]
    have hAx : Af x = A := hmetric
    have hbx (i : Fin 2) : bf x i = B (V i) G.normal := hinner _ _
    have hsx : sf x ≠ 0 := by
      change Real.sqrt (Af x).det ≠ 0
      rw [hAx]
      exact (Real.sqrt_pos.mpr hpos).ne'
    have hsquare : (sf x) ^ 2 = A.det := by
      change (Real.sqrt (Af x).det) ^ 2 = _
      rw [hAx]
      exact Real.sq_sqrt hpos.le
    have hsf : HasFDerivAt sf
        ((1 / (2 * sf x)) •
          (Af x 0 0 • fderiv ℝ (fun z => Af z 1 1) x +
           Af x 1 1 • fderiv ℝ (fun z => Af z 0 0) x -
          (Af x 0 1 • fderiv ℝ (fun z => Af z 1 0) x +
           Af x 1 0 • fderiv ℝ (fun z => Af z 0 1) x))) x := by
      have hd := (((hAdiff 0 0).hasFDerivAt.mul (hAdiff 1 1).hasFDerivAt).sub
        ((hAdiff 0 1).hasFDerivAt.mul (hAdiff 1 0).hasFDerivAt)).sqrt
        (show Af x 0 0 * Af x 1 1 - Af x 0 1 * Af x 1 0 ≠ 0 by
          rw [← Matrix.det_fin_two,hAx];exact hpos.ne')
      change HasFDerivAt (fun z => Real.sqrt
        (Af z 0 0 * Af z 1 1 - Af z 0 1 * Af z 1 0)) _ x at hd
      simpa only [sf,Matrix.det_fin_two,Pi.sub_apply,Pi.mul_apply] using hd
    have hsD (k : Fin 2) : fderiv ℝ sf x (coordinateVector 2 k) =
        (A 1 1 * (K k 0 0 + K k 0 0) + A 0 0 * (K k 1 1 + K k 1 1) -
          2 * A 0 1 * (K k 0 1 + K k 1 0)) / (2 * sf x) := by
      rw [hsf.fderiv]
      simp only [_root_.smul_apply,smul_eq_mul,_root_.add_apply,_root_.sub_apply,hAD,hAx,← hAsym]
      ring
    let cH : ℝ → E3 := fun t => G.coordinates.chart (D.edge D.pointParameter) + G.plane x + t • G.normal
    have hcH : HasFDerivAt cH (ContinuousLinearMap.toSpanSingleton ℝ G.normal)
        (G.height x) := by
      exact (ContinuousLinearMap.toSpanSingleton ℝ G.normal).hasFDerivAt.const_add
        (G.coordinates.chart (D.edge D.pointParameter) + G.plane x)
    have hcHy : cH (G.height x) = y := rfl
    have hZD (i j : Fin 2) : HasDerivAt
        (fun t => G.jetMetric (x,t,p) i j) (Z i j) (G.height x) := by
      have ht (i : Fin 2) : G.jetTangent p i = V i := (htangent i).symm
      have hd : DifferentiableAt ℝ (fun t => G.jetMetric (x,t,p) i j) (G.height x) := by
        change DifferentiableAt ℝ (fun t => ∑ a : Fin 3,∑ b : Fin 3,
          g (cH t) a b * G.jetTangent p i a * G.jetTangent p j b) (G.height x)
        apply DifferentiableAt.fun_sum
        intro a ha
        apply DifferentiableAt.fun_sum
        intro b hb
        have hg' : DifferentiableAt ℝ (fun z : E3 => g z a b) (cH (G.height x)) := by
          rw [hcHy]
          exact hgdiff a b
        have hh : DifferentiableAt ℝ (fun t => g (cH t) a b) (G.height x) :=
          DifferentiableAt.comp (f := cH) (g := fun z : E3 => g z a b)
            (G.height x) hg' hcH.differentiableAt
        exact (hh.mul_const _).mul_const _
      convert hd.hasDerivAt using 1
      change Z i j = fderiv ℝ (fun t => coordinateInner g (cH t)
        (G.jetTangent p i) (G.jetTangent p j)) (G.height x) 1
      rw [ht,ht]
      rw [hInnerDeriv ℝ g cH (fun _ => V i) (fun _ => V j) (G.height x) 1
        hgdiff hcH.differentiableAt (differentiableAt_const _) (differentiableAt_const _)]
      simp only [hcH.fderiv,ContinuousLinearMap.toSpanSingleton_apply,ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply,one_smul,fderiv_const_apply,_root_.zero_apply,PiLp.zero_apply,hcHy,
        coordinateInner,mul_zero,zero_mul,Finset.sum_const_zero,add_zero]
      rfl
    have hlower : G.attainedLowerOrder x =
        -(A 1 1 * Z 0 0 + A 0 0 * Z 1 1 - 2 * A 0 1 * Z 0 1) / (2 * sf x) := by
      have hd := (((hZD 0 0).mul (hZD 1 1)).sub ((hZD 0 1).mul (hZD 1 0))).sqrt
        (show G.jetMetric (x,G.height x,p) 0 0 * G.jetMetric (x,G.height x,p) 1 1 -
          G.jetMetric (x,G.height x,p) 0 1 * G.jetMetric (x,G.height x,p) 1 0 ≠ 0 by
          rw [← Matrix.det_fin_two];exact hpos.ne')
      change -deriv (fun t => Real.sqrt (Matrix.det (G.jetMetric (x,t,p)))) (G.height x) = _
      simp only [Matrix.det_fin_two]
      change HasDerivAt (fun t => Real.sqrt (G.jetMetric (x,t,p) 0 0 * G.jetMetric (x,t,p) 1 1 -
        G.jetMetric (x,t,p) 0 1 * G.jetMetric (x,t,p) 1 0)) _ (G.height x) at hd
      rw [hd.deriv]
      change -((Z 0 0 * A 1 1 + A 0 0 * Z 1 1 -
        (Z 0 1 * A 1 0 + A 0 1 * Z 1 0)) / (2 * Real.sqrt
          (A 0 0 * A 1 1 - A 0 1 * A 1 0))) = _
      rw [← Matrix.det_fin_two]
      change -((Z 0 0 * A 1 1 + A 0 0 * Z 1 1 -
        (Z 0 1 * A 1 0 + A 0 1 * Z 1 0)) / (2 * Real.sqrt A.det)) = _
      simp only [sf,hAx,← hAsym,hZsym]
      ring
    have hQuot (a b c d e l k : Fin 2) :
        fderiv ℝ (fun z => (Af z a b * bf z c - Af z d e * bf z l) / sf z) x
          (coordinateVector 2 k) =
        (((K k a b + K k b a) * bf x c + A a b *
            (Kn k c + (1/2 : ℝ) * (E k c - E c k + Z k c)) -
          ((K k d e + K k e d) * bf x l + A d e *
            (Kn k l + (1/2 : ℝ) * (E k l - E l k + Z k l)))) * sf x -
          (A a b * bf x c - A d e * bf x l) *
            ((A 1 1 * (K k 0 0 + K k 0 0) + A 0 0 * (K k 1 1 + K k 1 1) -
              2 * A 0 1 * (K k 0 1 + K k 1 0)) / (2 * sf x))) / (sf x)^2 := by
      have hn := (((hAdiff a b).hasFDerivAt.mul (hbDiff c).hasFDerivAt).sub
        ((hAdiff d e).hasFDerivAt.mul (hbDiff l).hasFDerivAt))
      have hi := (hasFDerivAt_inv hsx).comp x hsf
      have hd := hn.mul hi
      change HasFDerivAt (fun z => (Af z a b * bf z c - Af z d e * bf z l) * (sf z)⁻¹) _ x at hd
      simp only [div_eq_mul_inv]
      have he := congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 k)) hd.fderiv
      simp only [_root_.smul_apply,_root_.add_apply,_root_.sub_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply,hAD,hbD,hAx] at he
      rw [he]
      have heSF := hsD k
      rw [hsf.fderiv] at heSF
      simp only [_root_.smul_apply,smul_eq_mul,_root_.add_apply,_root_.sub_apply,hAD,hAx,← hAsym] at heSF
      simp only [_root_.smul_apply,smul_eq_mul,_root_.add_apply,_root_.sub_apply,hAD,hAx,← hAsym,
        Pi.sub_apply,Pi.mul_apply,Function.comp_apply]
      field_simp (discharger := first | assumption | positivity | norm_num | simp only [hsx])
      <;> ring
    have hflux0germ : (fun z => G.attainedFlux z 0) =ᶠ[𝓝 x]
        (fun z => (Af z 1 1 * bf z 0 - Af z 0 1 * bf z 1) / sf z) :=
      Filter.Eventually.mono (hΩ.mem_nhds hx) (fun z hz => (hFluxFormula z hz).1)
    have hflux1germ : (fun z => G.attainedFlux z 1) =ᶠ[𝓝 x]
        (fun z => (Af z 0 0 * bf z 1 - Af z 0 1 * bf z 0) / sf z) :=
      Filter.Eventually.mono (hΩ.mem_nhds hx) (fun z hz => (hFluxFormula z hz).2)
    have htracePair (w : E3) : B (tracedAcceleration g f x) w =
        ∑ i : Fin 2, ∑ j : Fin 2,A⁻¹ i j * B (acc i j) w := by
      change B (∑ i : Fin 2,∑ j : Fin 2,(Af x)⁻¹ i j • acc i j) w = _
      rw [hAx]
      simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
    have halg := hVarAlg A (sf x) (bf x) K Kn E Z hAsym.symm hKsym hKnsym hZsym hsx hsquare
    change G.classicalResidual x = Real.sqrt A.det *
      (coordinateInner g y (tracedAcceleration g f x) G.normal -
        ∑ i : Fin 2, ∑ j : Fin 2,(Af x)⁻¹ i j *
          coordinateInner g y (tracedAcceleration g f x) (V i) *
          coordinateInner g y (V j) G.normal)
    rw [hAx]
    dsimp only [g]
    simp only [hinner]
    change G.classicalResidual x = Real.sqrt A.det *
      (B (tracedAcceleration g f x) G.normal -
        ∑ i : Fin 2, ∑ j : Fin 2,A⁻¹ i j * B (tracedAcceleration g f x) (V i) * B (V j) G.normal)
    simp only [htracePair]
    unfold A3SharedGraph.classicalResidual
    simp only [Fin.sum_univ_two]
    rw [hflux0germ.fderiv_eq,hflux1germ.fderiv_eq,hQuot,hQuot,hlower]
    simpa only [sf,hAx,hbx,K,Kn,Fin.sum_univ_two,sub_eq_add_neg,neg_div] using halg
  let slopeGram (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
      (n : E3) (p : E2) : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => coordinateInner (fun _ => B) 0
      (L (coordinateVector 2 i) + p i • n)
      (L (coordinateVector 2 j) + p j • n)
  have hresidual
      (G : A3SharedGraph D) (Ω : Set E2) (hΩ : IsOpen Ω)
      (hΩdisc : Ω ⊆ G.disc)
      (hsmooth : ContDiffOn ℝ ∞ G.height Ω)
      (htrace : ∀ x ∈ Ω,
        tracedAcceleration (actualChartTensor h G.coordinates)
          (graphMap (G.coordinates.chart (D.edge D.pointParameter))
            G.plane G.normal G.height) x ∈
        LinearMap.range
          (fderiv ℝ (graphMap (G.coordinates.chart (D.edge D.pointParameter))
            G.plane G.normal G.height) x).toLinearMap) :
      ∀ x ∈ Ω, G.classicalResidual x = 0 := by
    classical
    have hmetric :
        (∀ i j, ContDiffOn ℝ ∞ (fun y => actualChartTensor h G.coordinates y i j)
          G.coordinates.chart.target) ∧
        (∀ y ∈ G.coordinates.chart.target, ∀ i j,
          actualChartTensor h G.coordinates y i j = actualChartTensor h G.coordinates y j i) ∧
        (∀ y ∈ G.coordinates.chart.target, ∀ w : E3, w ≠ 0 →
          0 < coordinateInner (actualChartTensor h G.coordinates) y w w) := by
      let c := G.coordinates
      refine ⟨?_, ?_, ?_⟩
      · intro i j
        letI : Bundle.RiemannianBundle (fun p : N => TangentSpace 𝓘(ℝ, E3) p) :=
          ⟨h.toRiemannianMetric⟩
        have hv (k : Fin 3) : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, E3).tangent ∞
            (fun y => (⟨c.chart.symm y, inverseChartDifferential c y (coordinateVector 3 k)⟩ :
              TangentBundle 𝓘(ℝ, E3) N)) c.chart.target := by
          have hs : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3).tangent ∞
              (fun y => (⟨y, (NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k)⟩ :
                TangentBundle 𝓘(ℝ, E3) E3)) :=
            contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
          have ht := c.inverse_smooth.contMDiffOn_tangentMapWithin
            (m := ∞) (by simp) c.chart.open_target.uniqueMDiffOn
          have hc := ht.comp hs.contMDiffOn (by intro y hy; exact hy)
          apply hc.congr
          intro y hy
          change (⟨c.chart.symm y, (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm y)
            ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k))⟩ : TangentBundle 𝓘(ℝ, E3) N) =
              ⟨c.chart.symm y, (mfderivWithin 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm c.chart.target y)
                ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k))⟩
          rw [mfderivWithin_eq_mfderiv (c.chart.open_target.uniqueMDiffOn y hy)
            (((c.inverse_smooth y hy).mdifferentiableWithinAt (by simp)).mdifferentiableAt
              (c.chart.open_target.mem_nhds hy))]
        exact (open scoped Bundle in (hv i |>.inner_bundle (hv j)).contDiffOn)
      · intro y hy i j
        exact h.symm _ _ _
      · intro y hy w hw
        have he : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
          ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
        have hinj : Function.Injective (inverseChartDifferential c y) :=
          (he.symm.mfderiv_injective hy).comp (NormedSpace.fromTangentSpace y).symm.injective
        have hn : inverseChartDifferential c y w ≠ 0 := by
          intro hh
          apply hw
          apply hinj
          simpa only [map_zero] using hh
        have hid (v w : E3) : coordinateInner (actualChartTensor h c) y v w =
            h.inner (c.chart.symm y) (inverseChartDifferential c y v)
              (inverseChartDifferential c y w) := by
          have hsum (v : E3) : (∑ i : Fin 3, v i • coordinateVector 3 i) = v := by
            ext j
            simp [coordinateVector, EuclideanSpace.single, Pi.single_apply]
          have hdiff (v : E3) : inverseChartDifferential c y v =
              ∑ i : Fin 3, v i • inverseChartDifferential c y (coordinateVector 3 i) := by
            simpa only [map_sum, map_smul] using congrArg (inverseChartDifferential c y) (hsum v).symm
          unfold coordinateInner actualChartTensor
          rw [hdiff v, hdiff w, map_sum]
          simp only [map_smul, _root_.sum_apply, _root_.smul_apply, map_sum, smul_eq_mul]
          simp only [Finset.mul_sum]
          conv_rhs => rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          ring
        rw [hid]
        exact h.pos _ _ hn
    have hann (B : Matrix (Fin 3) (Fin 3) ℝ) (T : E2 →L[ℝ] E3)
      (n : E3) (v : E2)
      (hG : Matrix.PosDef (fun i j : Fin 2 => coordinateInner (fun _ => B) 0
        (T (coordinateVector 2 i)) (T (coordinateVector 2 j)))) :
      coordinateInner (fun _ => B) 0 (T v) n -
        ∑ i : Fin 2, ∑ j : Fin 2,
          (@Inv.inv (Matrix (Fin 2) (Fin 2) ℝ) Matrix.inv (fun i j : Fin 2 => coordinateInner (fun _ => B) 0
            (T (coordinateVector 2 i)) (T (coordinateVector 2 j)))) i j *
          coordinateInner (fun _ => B) 0 (T v) (T (coordinateVector 2 i)) *
          coordinateInner (fun _ => B) 0 (T (coordinateVector 2 j)) n = 0 := by
      classical
      let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j => coordinateInner (fun _ => B) 0
        (T (coordinateVector 2 i)) (T (coordinateVector 2 j))
      have hv : v = v 0 • coordinateVector 2 0 + v 1 • coordinateVector 2 1 := by
        ext i
        fin_cases i <;> simp [coordinateVector,EuclideanSpace.single]
      have hlin (w : E3) : coordinateInner (fun _ => B) 0 (T v) w =
          ∑ k : Fin 2, v k * coordinateInner (fun _ => B) 0 (T (coordinateVector 2 k)) w := by
        conv_lhs => rw [hv,map_add,map_smul,map_smul]
        simp only [coordinateInner,Fin.sum_univ_two,Fin.sum_univ_three,PiLp.add_apply,
          PiLp.smul_apply,smul_eq_mul]
        ring
      rw [hlin]
      simp_rw [hlin]
      change (∑ k : Fin 2, v k * coordinateInner (fun _ => B) 0 (T (coordinateVector 2 k)) n) -
        (∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j * (∑ k : Fin 2, v k * A k i) *
          coordinateInner (fun _ => B) 0 (T (coordinateVector 2 j)) n) = 0
      have heq : (∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j * (∑ k : Fin 2, v k * A k i) *
          coordinateInner (fun _ => B) 0 (T (coordinateVector 2 j)) n) =
          ∑ k : Fin 2, ∑ j : Fin 2, v k * (A*A⁻¹) k j *
            coordinateInner (fun _ => B) 0 (T (coordinateVector 2 j)) n := by
        simp only [Matrix.mul_apply,Fin.sum_univ_two]
        ring
      rw [heq, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hG.det_pos.ne')]
      simp
    let g := actualChartTensor h G.coordinates
    let Φ := graphMap (G.coordinates.chart (D.edge D.pointParameter)) G.plane G.normal G.height
    have hvariation (x : E2) (hx : x ∈ Ω) :
        G.classicalResidual x = G.areaDensity (G.attainedJet x) *
          (coordinateInner g (Φ x) (tracedAcceleration g Φ x) G.normal -
            ∑ i : Fin 2, ∑ j : Fin 2, (inducedMetric g Φ x)⁻¹ i j *
              coordinateInner g (Φ x) (tracedAcceleration g Φ x) (graphTangent Φ x i) *
              coordinateInner g (Φ x) (graphTangent Φ x j) G.normal) := by
      exact hfirst G Ω hΩ hΩdisc hsmooth x hx
    intro x hx
    have hu : DifferentiableAt ℝ G.height x :=
      ((hsmooth x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
    have hΦ : HasFDerivAt Φ (G.plane + (fderiv ℝ G.height x).smulRight G.normal) x := by
      exact (G.plane.hasFDerivAt.const_add _).add (hu.hasFDerivAt.smul_const G.normal)
    have hpg (i : Fin 2) : planarGradient G.height x i =
        fderiv ℝ G.height x (coordinateVector 2 i) := by
      unfold planarGradient
      fin_cases i <;> simp [coordinateVector,EuclideanSpace.single]
    have ht (i : Fin 2) : graphTangent Φ x i =
        G.plane (coordinateVector 2 i) + planarGradient G.height x i • G.normal := by
      unfold graphTangent
      rw [hΦ.fderiv,hpg]
      rfl
    have hchartx : Φ x ∈ G.coordinates.chart.target := by
      apply G.graph_in_chart
      have hxdisc := hΩdisc hx
      change dist x 0 < G.radius at hxdisc
      change dist x 0 ≤ 2*G.radius
      linarith [G.radius_pos]
    have hB : (g (Φ x)).PosDef := by
      apply Matrix.PosDef.of_dotProduct_mulVec_pos
      · ext i j
        exact hmetric.2.1 (Φ x) hchartx j i
      · intro w hw
        have hp := hmetric.2.2 (Φ x) hchartx (WithLp.toLp 2 w) (by
          intro he;apply hw;exact congrArg WithLp.ofLp he)
        convert hp using 1
        simp only [coordinateInner,dotProduct,Matrix.mulVec,Fin.sum_univ_three,
          Pi.star_apply,star_trivial]
        dsimp [g]
        ring
    have hgram : (inducedMetric g Φ x).PosDef := by
      let B := g (Φ x)
      let L := G.plane
      let n := G.normal
      have hsplit := G.splitting
      have hgram (q : E2) : (slopeGram B L n q).PosDef := by
        let v : Fin 2 → E3 := fun i => L (coordinateVector 2 i) + q i • n
        have hli : LinearIndependent ℝ v := by
          apply Fintype.linearIndependent_iff.mpr
          intro a ha
          have hs : L (∑ i : Fin 2, a i • coordinateVector 2 i) +
              (∑ i : Fin 2, a i * q i) • n = 0 := by
            simpa only [v, smul_add, Finset.sum_add_distrib,
              map_sum, map_smul, mul_smul, Finset.sum_smul] using ha
          have he : ((∑ i : Fin 2, a i • coordinateVector 2 i), ∑ i : Fin 2, a i * q i) =
              ((0 : E2), (0 : ℝ)) := by
            apply hsplit.injective
            simpa only [map_zero, zero_smul, add_zero] using hs
          have hz := congrArg Prod.fst he
          intro i
          have heval := congrArg (fun z : E2 => z i) hz
          fin_cases i <;> simpa [coordinateVector, EuclideanSpace.single, Pi.single_apply] using heval
        let V : Matrix (Fin 3) (Fin 2) ℝ := fun a i => v i a
        have hV : Function.Injective V.mulVec := by
          intro x y hxy
          have hsum : ∑ i, (x i - y i) • v i = 0 := by
            ext a
            have hh := congrFun hxy a
            simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh
            simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply,
              smul_eq_mul, sub_mul, PiLp.zero_apply] using (by
                dsimp [V] at hh
                nlinarith [hh] : (x 0 - y 0) * v 0 a + (x 1 - y 1) * v 1 a = 0)
          have he := Fintype.linearIndependent_iff.mp hli _ hsum
          funext i
          exact sub_eq_zero.mp (he i)
        have heq : slopeGram B L n q = V.conjTranspose * B * V := by
          ext i j
          change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
            ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
          simp only [Fin.sum_univ_three]
          ring
        rw [heq]
        exact hB.conjTranspose_mul_mul_same hV
      have heq : inducedMetric g Φ x = slopeGram B L n (planarGradient G.height x) := by
        ext i j
        unfold inducedMetric
        rw [ht i, ht j]
        rfl
      rw [heq]
      exact hgram _
    obtain ⟨v,hv⟩ := htrace x hx
    rw [hvariation x hx]
    have hh := hann (g (Φ x)) (fderiv ℝ Φ x) G.normal v hgram
    change (fderiv ℝ Φ x) v = tracedAcceleration g Φ x at hv
    rw [← hv]
    change G.areaDensity (G.attainedJet x) * _ = 0
    exact mul_eq_zero_of_right _ hh
  
  have hmin := A3_original_side_minimality G
  exact ⟨hresidual G (interior G.sideOne) isOpen_interior
    (interior_subset.trans G.sideOne_in_disc) (G.height_smooth_one.mono interior_subset) hmin.1.2,
    hresidual G (interior G.sideTwo) isOpen_interior
      (interior_subset.trans G.sideTwo_in_disc) (G.height_smooth_two.mono interior_subset) hmin.2.2⟩

/-- The same interface has planar area zero, enabling exact splitting of the
volume integrals over the two open sides. -/
theorem A3_projected_interface_null (G : A3SharedGraph D) :
    volume G.interface = 0 := by
  have hsource : (μH[2] : Measure ℝ) = 0 :=
    Real.hausdorffMeasure_of_finrank_lt (by simp)
  have himage : μH[2] (G.projectedEdge '' Ioo G.edgeLeft G.edgeRight) = 0 :=
    (G.edge_smooth.differentiableOn (by simp)).hausdorffMeasure_image_eq_zero
      (by norm_num) (by rw [hsource]; simp)
  have hvolume : volume (G.projectedEdge '' Ioo G.edgeLeft G.edgeRight) = 0 := by
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2,
      Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
    simp only [Nat.cast_ofNat, himage, smul_zero]
  unfold A3SharedGraph.interface
  rw [G.shared_edge]
  exact measure_mono_null inter_subset_left hvolume

/-- Bochner local integrability on the full disc, plus arc-length integrability
of both fixed interface terms for every admissible test function. -/
theorem A3_actual_flux_integrability (G : A3SharedGraph D) :
    LocallyIntegrableOn G.attainedFlux G.disc ∧
    LocallyIntegrableOn G.attainedLowerOrder G.disc ∧
    ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ G.disc →
      IntegrableOn (fun x => inner ℝ (G.attainedFlux x) (planarGradient φ x) -
        G.attainedLowerOrder x * φ x) G.disc ∧
      IntegrableOn (fun t =>
        inner ℝ (G.attainedFlux (G.projectedEdge t)) (G.sideOneNormal (G.projectedEdge t)) *
          φ (G.projectedEdge t) * ‖fderiv ℝ G.projectedEdge t 1‖)
        {t ∈ Ioo G.edgeLeft G.edgeRight | G.projectedEdge t ∈ G.disc} ∧
      IntegrableOn (fun t =>
        inner ℝ (G.attainedFlux (G.projectedEdge t)) (G.sideTwoNormal (G.projectedEdge t)) *
          φ (G.projectedEdge t) * ‖fderiv ℝ G.projectedEdge t 1‖)
        {t ∈ Ioo G.edgeLeft G.edgeRight | G.projectedEdge t ∈ G.disc} := by
  classical

  obtain ⟨C⟩ := A3_actual_metric_operator_control G
  have hheight : ContDiffOn ℝ 1 G.height G.disc := G.height_C1.mono (by
    intro x hx
    change dist x 0 < G.radius at hx
    change dist x 0 ≤ 2 * G.radius
    linarith [G.radius_pos])
  have hgrad : ContinuousOn (planarGradient G.height) G.disc := by
    apply continuousOn_finsetSum
    intro i hi
    exact ((hheight.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply
      continuousOn_const).smul continuousOn_const
  have hj : ContinuousOn G.attainedJet G.disc :=
    continuousOn_id.prodMk (hheight.continuousOn.prodMk hgrad)
  have hside (U : Set E2) (hU : IsOpen U) (hUd : U ⊆ G.disc)
      (hw : ContDiffOn ℝ ∞ G.height U) : ContDiffOn ℝ ∞ G.attainedFlux U := by
    have hg : ContDiffOn ℝ ∞ (planarGradient G.height) U := by
      apply ContDiffOn.sum
      intro i hi
      exact ((hw.fderiv_of_isOpen hU (by simp)).clm_apply
        contDiffOn_const).smul contDiffOn_const
    have hjet : ContDiffOn ℝ ∞ G.attainedJet U :=
      contDiffOn_id.prodMk (hw.prodMk hg)
    exact C.flux_smooth.comp hjet (fun x hx => C.attained x (hUd hx))
  have hA : ContinuousOn G.attainedFlux G.disc := C.flux_smooth.continuousOn.comp hj C.attained
  have hB : ContinuousOn G.attainedLowerOrder G.disc := C.lowerOrder_smooth.continuousOn.comp hj C.attained
  have hcompact (K : Set E2) (hK : IsCompact K) (hKd : K ⊆ G.disc) :
      IsCompact {t ∈ Ioo G.edgeLeft G.edgeRight | G.projectedEdge t ∈ K} := by
  
    classical
    have hheight : ContinuousOn G.height G.disc := G.height_C1.continuousOn.mono (by
      intro x hx
      change dist x 0 < G.radius at hx
      change dist x 0 ≤ 2 * G.radius
      linarith [G.radius_pos])
    have hΦ : ContinuousOn
        (graphMap (G.coordinates.chart (D.edge D.pointParameter)) G.plane G.normal G.height)
        G.disc :=
      (continuousOn_const.add G.plane.continuous.continuousOn).add
        (hheight.smul continuousOn_const)
    have himage : MapsTo
        (graphMap (G.coordinates.chart (D.edge D.pointParameter)) G.plane G.normal G.height)
        G.disc G.coordinates.chart.target := by
      intro x hx
      apply G.graph_in_chart
      change dist x 0 < G.radius at hx
      change dist x 0 ≤ 2 * G.radius
      linarith [G.radius_pos]
    have hparameter : ContinuousOn G.parameter G.disc :=
      G.coordinates.chart.continuousOn_symm.comp hΦ himage
    let Z := {x ∈ K | G.signedSide x = 0}
    have hZ : IsCompact Z := by
      apply hK.of_isClosed_subset
      · exact (G.signedSide_smooth.continuousOn.mono hKd).preimage_isClosed_of_isClosed
          hK.isClosed (isClosed_singleton (x := (0 : ℝ)))
      · exact fun _ hx => hx.1
    have hZi : Z ⊆ G.interface := by
      intro x hx
      change x ∈ G.sideOne ∩ G.sideTwo
      rw [G.sideOne_signed, G.sideTwo_signed]
      exact ⟨⟨hKd hx.1, le_of_eq hx.2⟩, ⟨hKd hx.1, le_of_eq hx.2.symm⟩⟩
    let S : Set ArcTime := {t | t.val ∈ Ioo G.edgeLeft G.edgeRight ∧ G.projectedEdge t ∈ K}
    have heq : (fun t : ArcTime => D.edge t) '' S = G.parameter '' Z := by
      apply subset_antisymm
      · rintro _ ⟨t, ht, rfl⟩
        refine ⟨G.projectedEdge t, ?_, (G.edge_exact t ht.1)⟩
        refine ⟨ht.2, ?_⟩
        have hi : G.projectedEdge t ∈ G.sideOne ∩ G.sideTwo := by
          rw [G.shared_edge]
          exact ⟨⟨t, ht.1, rfl⟩, hKd ht.2⟩
        rw [G.sideOne_signed, G.sideTwo_signed] at hi
        exact le_antisymm hi.1.2 hi.2.2
      · rintro _ ⟨x, hx, rfl⟩
        have hi := hZi hx
        change x ∈ G.sideOne ∩ G.sideTwo at hi
        rw [G.shared_edge] at hi
        obtain ⟨t, ht, rfl⟩ := hi.1
        let ta : ArcTime := ⟨t, lt_trans G.edgeLeft_lower ht.1, lt_trans ht.2 G.edgeRight_upper⟩
        refine ⟨ta, ⟨ht, hx.1⟩, ?_⟩
        exact (G.edge_exact t ht).symm
    have hS : IsCompact S := D.edge_embedding.isCompact_iff.mpr (by
      rw [heq]
      exact hZ.image_of_continuousOn (hparameter.mono (fun _ hx => hKd hx.1)))
    have hval : Subtype.val '' S = {t ∈ Ioo G.edgeLeft G.edgeRight | G.projectedEdge t ∈ K} := by
      apply subset_antisymm
      · rintro _ ⟨t, ht, rfl⟩
        exact ht
      · intro t ht
        refine ⟨⟨t, lt_trans G.edgeLeft_lower ht.1.1, lt_trans ht.1.2 G.edgeRight_upper⟩, ht, rfl⟩
    rw [← hval]
    exact hS.image continuous_subtype_val
  have hgeom : CurvedDivergence.SignedArcGeometry G.disc G.signedSide G.projectedEdge
      G.edgeLeft G.edgeRight := by
    refine ⟨Metric.isOpen_ball,G.signedSide_smooth,G.signedSide_regular,
      G.edge_smooth,G.edge_embedding,G.edge_regular,?_,hcompact⟩
    change {x ∈ Metric.ball 0 G.radius | G.signedSide x = 0} =
      (G.projectedEdge '' Ioo G.edgeLeft G.edgeRight) ∩ Metric.ball 0 G.radius
    rw [← G.shared_edge,G.sideOne_signed,G.sideTwo_signed]
    ext x
    constructor
    · intro hx
      exact ⟨⟨hx.1,le_of_eq hx.2⟩,⟨hx.1,le_of_eq hx.2.symm⟩⟩
    · intro hx
      exact ⟨hx.1.1,le_antisymm hx.1.2 hx.2.2⟩
  refine ⟨hA.locallyIntegrableOn Metric.isOpen_ball.measurableSet,
    hB.locallyIntegrableOn Metric.isOpen_ball.measurableSet,?_⟩
  intro φ hφ hc hs
  have harc := CurvedDivergence.compact_arc_test_integrability G.disc G.signedSide
    G.projectedEdge G.edgeLeft G.edgeRight hgeom G.attainedFlux hA φ hφ hc hs
  refine ⟨(flux_integrand_integrable G.disc G.attainedFlux G.attainedLowerOrder φ hA hB hφ hc hs).integrableOn,?_,?_⟩
  · exact harc false
  · exact harc true

/-- Curved-domain divergence theorem with compactly supported tests. There is no
outer-circle boundary term because the test support lies inside the full disc. -/
theorem A3_integration_by_parts_on_sides (G : A3SharedGraph D)
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ G.disc) :
    (∫ x in interior G.sideOne,
      inner ℝ (G.attainedFlux x) (planarGradient φ x) - G.attainedLowerOrder x * φ x) =
      G.interfaceIntegral (fun x => inner ℝ (G.attainedFlux x) (G.sideOneNormal x) * φ x) ∧
    (∫ x in interior G.sideTwo,
      inner ℝ (G.attainedFlux x) (planarGradient φ x) - G.attainedLowerOrder x * φ x) =
      G.interfaceIntegral (fun x => inner ℝ (G.attainedFlux x) (G.sideTwoNormal x) * φ x) := by
  classical

  obtain ⟨C⟩ := A3_actual_metric_operator_control G
  have hheight : ContDiffOn ℝ 1 G.height G.disc := G.height_C1.mono (by
    intro x hx
    change dist x 0 < G.radius at hx
    change dist x 0 ≤ 2 * G.radius
    linarith [G.radius_pos])
  have hgrad : ContinuousOn (planarGradient G.height) G.disc := by
    apply continuousOn_finsetSum
    intro i hi
    exact ((hheight.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply
      continuousOn_const).smul continuousOn_const
  have hj : ContinuousOn G.attainedJet G.disc :=
    continuousOn_id.prodMk (hheight.continuousOn.prodMk hgrad)
  have hside (U : Set E2) (hU : IsOpen U) (hUd : U ⊆ G.disc)
      (hw : ContDiffOn ℝ ∞ G.height U) : ContDiffOn ℝ ∞ G.attainedFlux U := by
    have hg : ContDiffOn ℝ ∞ (planarGradient G.height) U := by
      apply ContDiffOn.sum
      intro i hi
      exact ((hw.fderiv_of_isOpen hU (by simp)).clm_apply
        contDiffOn_const).smul contDiffOn_const
    have hjet : ContDiffOn ℝ ∞ G.attainedJet U :=
      contDiffOn_id.prodMk (hw.prodMk hg)
    exact C.flux_smooth.comp hjet (fun x hx => C.attained x (hUd hx))
  have hA : ContinuousOn G.attainedFlux G.disc := C.flux_smooth.continuousOn.comp hj C.attained
  have hB : ContinuousOn G.attainedLowerOrder G.disc := C.lowerOrder_smooth.continuousOn.comp hj C.attained
  have hcompact (K : Set E2) (hK : IsCompact K) (hKd : K ⊆ G.disc) :
      IsCompact {t ∈ Ioo G.edgeLeft G.edgeRight | G.projectedEdge t ∈ K} := by
  
    classical
    have hheight : ContinuousOn G.height G.disc := G.height_C1.continuousOn.mono (by
      intro x hx
      change dist x 0 < G.radius at hx
      change dist x 0 ≤ 2 * G.radius
      linarith [G.radius_pos])
    have hΦ : ContinuousOn
        (graphMap (G.coordinates.chart (D.edge D.pointParameter)) G.plane G.normal G.height)
        G.disc :=
      (continuousOn_const.add G.plane.continuous.continuousOn).add
        (hheight.smul continuousOn_const)
    have himage : MapsTo
        (graphMap (G.coordinates.chart (D.edge D.pointParameter)) G.plane G.normal G.height)
        G.disc G.coordinates.chart.target := by
      intro x hx
      apply G.graph_in_chart
      change dist x 0 < G.radius at hx
      change dist x 0 ≤ 2 * G.radius
      linarith [G.radius_pos]
    have hparameter : ContinuousOn G.parameter G.disc :=
      G.coordinates.chart.continuousOn_symm.comp hΦ himage
    let Z := {x ∈ K | G.signedSide x = 0}
    have hZ : IsCompact Z := by
      apply hK.of_isClosed_subset
      · exact (G.signedSide_smooth.continuousOn.mono hKd).preimage_isClosed_of_isClosed
          hK.isClosed (isClosed_singleton (x := (0 : ℝ)))
      · exact fun _ hx => hx.1
    have hZi : Z ⊆ G.interface := by
      intro x hx
      change x ∈ G.sideOne ∩ G.sideTwo
      rw [G.sideOne_signed, G.sideTwo_signed]
      exact ⟨⟨hKd hx.1, le_of_eq hx.2⟩, ⟨hKd hx.1, le_of_eq hx.2.symm⟩⟩
    let S : Set ArcTime := {t | t.val ∈ Ioo G.edgeLeft G.edgeRight ∧ G.projectedEdge t ∈ K}
    have heq : (fun t : ArcTime => D.edge t) '' S = G.parameter '' Z := by
      apply subset_antisymm
      · rintro _ ⟨t, ht, rfl⟩
        refine ⟨G.projectedEdge t, ?_, (G.edge_exact t ht.1)⟩
        refine ⟨ht.2, ?_⟩
        have hi : G.projectedEdge t ∈ G.sideOne ∩ G.sideTwo := by
          rw [G.shared_edge]
          exact ⟨⟨t, ht.1, rfl⟩, hKd ht.2⟩
        rw [G.sideOne_signed, G.sideTwo_signed] at hi
        exact le_antisymm hi.1.2 hi.2.2
      · rintro _ ⟨x, hx, rfl⟩
        have hi := hZi hx
        change x ∈ G.sideOne ∩ G.sideTwo at hi
        rw [G.shared_edge] at hi
        obtain ⟨t, ht, rfl⟩ := hi.1
        let ta : ArcTime := ⟨t, lt_trans G.edgeLeft_lower ht.1, lt_trans ht.2 G.edgeRight_upper⟩
        refine ⟨ta, ⟨ht, hx.1⟩, ?_⟩
        exact (G.edge_exact t ht).symm
    have hS : IsCompact S := D.edge_embedding.isCompact_iff.mpr (by
      rw [heq]
      exact hZ.image_of_continuousOn (hparameter.mono (fun _ hx => hKd hx.1)))
    have hval : Subtype.val '' S = {t ∈ Ioo G.edgeLeft G.edgeRight | G.projectedEdge t ∈ K} := by
      apply subset_antisymm
      · rintro _ ⟨t, ht, rfl⟩
        exact ht
      · intro t ht
        refine ⟨⟨t, lt_trans G.edgeLeft_lower ht.1.1, lt_trans ht.1.2 G.edgeRight_upper⟩, ht, rfl⟩
    rw [← hval]
    exact hS.image continuous_subtype_val
  have hgeom : CurvedDivergence.SignedArcGeometry G.disc G.signedSide G.projectedEdge
      G.edgeLeft G.edgeRight := by
    refine ⟨Metric.isOpen_ball,G.signedSide_smooth,G.signedSide_regular,
      G.edge_smooth,G.edge_embedding,G.edge_regular,?_,hcompact⟩
    change {x ∈ Metric.ball 0 G.radius | G.signedSide x = 0} =
      (G.projectedEdge '' Ioo G.edgeLeft G.edgeRight) ∩ Metric.ball 0 G.radius
    rw [← G.shared_edge,G.sideOne_signed,G.sideTwo_signed]
    ext x
    constructor
    · intro hx
      exact ⟨⟨hx.1,le_of_eq hx.2⟩,⟨hx.1,le_of_eq hx.2.symm⟩⟩
    · intro hx
      exact ⟨hx.1.1,le_antisymm hx.1.2 hx.2.2⟩
  have hinteriors : interior G.sideOne = CurvedDivergence.signedDomain G.disc G.signedSide false ∧
      interior G.sideTwo = CurvedDivergence.signedDomain G.disc G.signedSide true := by
  
    classical
    have hnegopen : IsOpen {x ∈ G.disc | G.signedSide x < 0} :=
      G.signedSide_smooth.continuousOn.isOpen_inter_preimage Metric.isOpen_ball isOpen_Iio
    have hposopen : IsOpen {x ∈ G.disc | 0 < G.signedSide x} :=
      G.signedSide_smooth.continuousOn.isOpen_inter_preimage Metric.isOpen_ball isOpen_Ioi
    have hzero : ∀ x ∈ G.disc, G.signedSide x = 0 →
        x ∉ interior G.sideOne ∧ x ∉ interior G.sideTwo := by
      intro x hx hz
      have hd := (G.signedSide_smooth.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
      have hgradzero : fderiv ℝ G.signedSide x = 0 → planarGradient G.signedSide x = 0 := by
        intro he
        unfold planarGradient
        rw [he]
        simp only [_root_.zero_apply,zero_smul,Finset.sum_const_zero]
      refine ⟨?_, ?_⟩
      · intro hi
        have hmax : IsLocalMax G.signedSide x := by
          filter_upwards [mem_interior_iff_mem_nhds.mp hi] with y hy
          rw [G.sideOne_signed] at hy
          exact hz ▸ hy.2
        exact G.signedSide_regular x hx hz (hgradzero (hmax.fderiv_eq_zero))
      · intro hi
        have hmin : IsLocalMin G.signedSide x := by
          filter_upwards [mem_interior_iff_mem_nhds.mp hi] with y hy
          rw [G.sideTwo_signed] at hy
          exact hz ▸ hy.2
        exact G.signedSide_regular x hx hz (hgradzero (hmin.fderiv_eq_zero))
    constructor
    · apply subset_antisymm
      · intro x hx
        have hm := interior_subset hx
        rw [G.sideOne_signed] at hm
        exact ⟨hm.1, lt_of_le_of_ne hm.2 (fun he => (hzero x hm.1 he).1 hx)⟩
      · apply interior_maximal
        · intro x hx
          rw [G.sideOne_signed]
          exact ⟨hx.1, hx.2.le⟩
        · exact hnegopen
    · apply subset_antisymm
      · intro x hx
        have hm := interior_subset hx
        rw [G.sideTwo_signed] at hm
        exact ⟨hm.1, lt_of_le_of_ne hm.2 (fun he => (hzero x hm.1 he.symm).2 hx)⟩
      · apply interior_maximal
        · intro x hx
          rw [G.sideTwo_signed]
          exact ⟨hx.1, hx.2.le⟩
        · exact hposopen
  have hflux : ∀ p : Bool, ContDiffOn ℝ 1 G.attainedFlux
      (CurvedDivergence.signedDomain G.disc G.signedSide p) := by
    intro p
    cases p
    · rw [← hinteriors.1]
      exact (hside _ isOpen_interior (interior_subset.trans G.sideOne_in_disc)
        (G.height_smooth_one.mono interior_subset)).of_le (by simp)
    · rw [← hinteriors.2]
      exact (hside _ isOpen_interior (interior_subset.trans G.sideTwo_in_disc)
        (G.height_smooth_two.mono interior_subset)).of_le (by simp)
  have hclassical := A3_classical_equation_on_sides G
  have hdivEq : ∀ p : Bool, ∀ x ∈ CurvedDivergence.signedDomain G.disc G.signedSide p,
      CurvedDivergence.planarDivergence G.attainedFlux x = -G.attainedLowerOrder x := by
    intro p x hx
    cases p
    · rw [← hinteriors.1] at hx
      exact eq_neg_of_add_eq_zero_left (hclassical.1 x hx)
    · rw [← hinteriors.2] at hx
      exact eq_neg_of_add_eq_zero_left (hclassical.2 x hx)
  have hBφ : IntegrableOn (fun x => G.attainedLowerOrder x * φ x) G.disc := by
    apply (((hB.mono hs).mul hφ.continuous.continuousOn).integrableOn_compact hc).of_forall_sdiff_eq_zero
      Metric.isOpen_ball.measurableSet
    intro x hx
    change G.attainedLowerOrder x * φ x = 0
    rw [image_eq_zero_of_notMem_tsupport hx.2,mul_zero]
  have hmeas (p : Bool) : MeasurableSet (CurvedDivergence.signedDomain G.disc G.signedSide p) := by
    cases p
    · exact (G.signedSide_smooth.continuousOn.isOpen_inter_preimage Metric.isOpen_ball isOpen_Iio).measurableSet
    · exact (G.signedSide_smooth.continuousOn.isOpen_inter_preimage Metric.isOpen_ball isOpen_Ioi).measurableSet
  have hdiv : ∀ p : Bool, IntegrableOn
      (fun x => CurvedDivergence.planarDivergence G.attainedFlux x * φ x)
      (CurvedDivergence.signedDomain G.disc G.signedSide p) := by
    intro p
    apply (hBφ.neg.mono_set (fun _ hx => hx.1)).congr_fun
    · intro x hx
      dsimp only [Pi.neg_apply]
      rw [hdivEq p x hx]
      ring
    · exact hmeas p
  have hIBP := CurvedDivergence.signed_curved_integration_by_parts G.disc G.signedSide
    G.projectedEdge G.edgeLeft G.edgeRight hgeom G.attainedFlux hA hflux φ hφ hc hs hdiv
  have hi (p : Bool) :
      (∫ x in CurvedDivergence.signedDomain G.disc G.signedSide p,
        inner ℝ (G.attainedFlux x) (planarGradient φ x) - G.attainedLowerOrder x * φ x) =
      (∫ t in CurvedDivergence.arcParameters G.disc G.projectedEdge G.edgeLeft G.edgeRight,
        inner ℝ (G.attainedFlux (G.projectedEdge t))
          (CurvedDivergence.signedNormal G.signedSide p (G.projectedEdge t)) *
          φ (G.projectedEdge t) * ‖fderiv ℝ G.projectedEdge t 1‖) := by
    rw [← (hIBP p).2.2]
    apply setIntegral_congr_fun
    · exact hmeas p
    · intro x hx
      dsimp only [Pi.neg_apply]
      rw [hdivEq p x hx]
      ring
  constructor
  · rw [hinteriors.1]
    exact hi false
  · rw [hinteriors.2]
    exact hi true

/-- Continuity across the same edge means both traces are this same attained
flux; the fixed opposite projected normals cancel against the same line measure. -/
theorem A3_projected_flux_cancellation (G : A3SharedGraph D) (φ : E2 → ℝ) :
    G.interfaceIntegral (fun x => inner ℝ (G.attainedFlux x) (G.sideOneNormal x) * φ x) +
    G.interfaceIntegral (fun x => inner ℝ (G.attainedFlux x) (G.sideTwoNormal x) * φ x) = 0 := by
  unfold A3SharedGraph.interfaceIntegral
  have heq :
      (fun t => inner ℝ (G.attainedFlux (G.projectedEdge t))
        (G.sideTwoNormal (G.projectedEdge t)) * φ (G.projectedEdge t) *
          ‖fderiv ℝ G.projectedEdge t 1‖) =
      (fun t => -(inner ℝ (G.attainedFlux (G.projectedEdge t))
        (G.sideOneNormal (G.projectedEdge t)) * φ (G.projectedEdge t) *
          ‖fderiv ℝ G.projectedEdge t 1‖)) := by
    funext t
    change inner ℝ (G.attainedFlux (G.projectedEdge t))
        (-G.sideOneNormal (G.projectedEdge t)) * φ (G.projectedEdge t) *
        ‖fderiv ℝ G.projectedEdge t 1‖ = _
    simp only [inner_neg_right, neg_mul]
  rw [heq, integral_neg]
  exact add_neg_cancel _

/-- The missing weak graph PDE from the original geometry, with actual formula
coefficients and no new endpoint premise. -/
theorem A3_actual_metric_weak_equation (G : A3SharedGraph D) :
    IsWeakDivergenceSolutionOn G.disc G.metricFlux G.metricLowerOrder G.height := by
  intro φ hφ hc hs
  have hneg : {x ∈ G.disc | G.signedSide x < 0} ⊆ interior G.sideOne := by
    apply interior_maximal
    · intro x hx
      rw [G.sideOne_signed]
      exact ⟨hx.1, hx.2.le⟩
    · exact G.signedSide_smooth.continuousOn.isOpen_inter_preimage
        Metric.isOpen_ball isOpen_Iio
  have hpos : {x ∈ G.disc | 0 < G.signedSide x} ⊆ interior G.sideTwo := by
    apply interior_maximal
    · intro x hx
      rw [G.sideTwo_signed]
      exact ⟨hx.1, hx.2.le⟩
    · exact G.signedSide_smooth.continuousOn.isOpen_inter_preimage
        Metric.isOpen_ball isOpen_Ioi
  have hi1 : interior G.sideOne ⊆ G.disc := interior_subset.trans G.sideOne_in_disc
  have hi2 : interior G.sideTwo ⊆ G.disc := interior_subset.trans G.sideTwo_in_disc
  have hdiff : G.disc \ (interior G.sideOne ∪ interior G.sideTwo) ⊆ G.interface := by
    intro x hx
    have hzero : G.signedSide x = 0 := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hn | hp
      · exact hx.2 (Or.inl (hneg ⟨hx.1, hn⟩))
      · exact hx.2 (Or.inr (hpos ⟨hx.1, hp⟩))
    change x ∈ G.sideOne ∩ G.sideTwo
    rw [G.sideOne_signed, G.sideTwo_signed]
    exact ⟨⟨hx.1, hzero.le⟩, ⟨hx.1, hzero.ge⟩⟩
  have hae : G.disc =ᵐ[volume] interior G.sideOne ∪ interior G.sideTwo := by
    apply ae_eq_set.mpr
    constructor
    · exact measure_mono_null hdiff (A3_projected_interface_null G)
    · have hh : (interior G.sideOne ∪ interior G.sideTwo) \ G.disc = ∅ :=
        sdiff_eq_empty.mpr (union_subset hi1 hi2)
      rw [hh]
      exact measure_empty
  have hfi := (A3_actual_flux_integrability G).2.2 φ hφ hc hs |>.1
  have hibp := A3_integration_by_parts_on_sides G φ hφ hc hs
  change (∫ x in G.disc,
    inner ℝ (G.attainedFlux x) (planarGradient φ x) - G.attainedLowerOrder x * φ x) = 0
  rw [setIntegral_congr_set hae,
    setIntegral_union G.interiors_disjoint isOpen_interior.measurableSet
      (hfi.mono_set hi1) (hfi.mono_set hi2), hibp.1, hibp.2]
  exact A3_projected_flux_cancellation G φ
end SeifertSurfaces.OriginalEndpoints
