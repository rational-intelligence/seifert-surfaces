import B1MetricVariationalInterfaces
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.EpsilonMinimizerVariation.InnerCourant
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
theorem l1_courant_stress_vanishing :
  ∀ a b : E2 → ℝ, IntegrableOn a (disc 1) → IntegrableOn b (disc 1) →
      (∀ η : E2 → E2, ContDiff ℝ ∞ η →
        (∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) →
        (∫ x in disc 1, a x *
          ((fderiv ℝ η x (coordinateVector 2 0)) 0 - (fderiv ℝ η x (coordinateVector 2 1)) 1) +
          b x * ((fderiv ℝ η x (coordinateVector 2 0)) 1 + (fderiv ℝ η x (coordinateVector 2 1)) 0)) = 0) →
      ∀ᵐ x ∂volume.restrict (disc 1), a x = 0 ∧ b x = 0 := by
  intro a b ha hb hstat
  have primitive (p q : ℕ) (c : ℂ) :
      ∃ η : E2 → E2, ContDiff ℝ ∞ η ∧
        (∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) ∧
        ∀ x : E2,
          (((fderiv ℝ η x (coordinateVector 2 0)) 0 -
            (fderiv ℝ η x (coordinateVector 2 1)) 1 : ℝ) : ℂ) +
          Complex.I * (((fderiv ℝ η x (coordinateVector 2 0)) 1 +
            (fderiv ℝ η x (coordinateVector 2 1)) 0 : ℝ) : ℂ) =
          2 * c * ((x 0 : ℂ) + Complex.I * (x 1 : ℂ)) ^ p *
            (starRingEnd ℂ ((x 0 : ℂ) + Complex.I * (x 1 : ℂ))) ^ q := by
    let Z : E2 →L[ℝ] ℂ := Complex.ofRealCLM.comp (EuclideanSpace.proj 0) +
      Complex.I • Complex.ofRealCLM.comp (EuclideanSpace.proj 1)
    let P : ℂ →L[ℝ] E2 := Complex.reCLM.smulRight (coordinateVector 2 0) +
      Complex.imCLM.smulRight (coordinateVector 2 1)
    have hZ (x : E2) : Z x = (x 0 : ℂ) + Complex.I * (x 1 : ℂ) := by
      simp [Z]
    have hP0 (z : ℂ) : (P z) 0 = z.re := by simp [P, coordinateVector]
    have hP1 (z : ℂ) : (P z) 1 = z.im := by simp [P, coordinateVector]
    have hQ : (q : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero q)
    let Q : ℂ := (q : ℂ) + 1
    let F (d : ℂ) (k : ℕ) (x : E2) : ℂ :=
      (c / Q) * (Z x)^p * (starRingEnd ℂ (Z x))^(q+1) - d*(Z x)^k
    have hsmooth (d : ℂ) (k : ℕ) : ContDiff ℝ ∞ (fun x => P (F d k x)) := by
      have hz : ContDiff ℝ ∞ (fun x => Z x) := Z.contDiff
      have hp : ContDiff ℝ ∞ (fun z => P z) := P.contDiff
      have hb : ContDiff ℝ ∞ (fun x => starRingEnd ℂ (Z x)) :=
        Complex.conjCLE.contDiff.comp hz
      exact hp.comp (((contDiff_const.mul (hz.pow p)).mul (hb.pow (q+1))).sub
        (contDiff_const.mul (hz.pow k)))
    have hder (d : ℂ) (k : ℕ) (x : E2) :
        (((fderiv ℝ (fun y => P (F d k y)) x (coordinateVector 2 0)) 0 -
          (fderiv ℝ (fun y => P (F d k y)) x (coordinateVector 2 1)) 1 : ℝ) : ℂ) +
        Complex.I * (((fderiv ℝ (fun y => P (F d k y)) x (coordinateVector 2 0)) 1 +
          (fderiv ℝ (fun y => P (F d k y)) x (coordinateVector 2 1)) 0 : ℝ) : ℂ) =
        2*c*(Z x)^p*(starRingEnd ℂ (Z x))^q := by
      have hz := Z.hasFDerivAt (x := x)
      have hzbar := Complex.conjCLE.hasFDerivAt.comp x hz
      have hf := ((((hz.pow p).const_mul (c / Q)).mul (hzbar.pow (q+1))).sub
        ((hz.pow k).const_mul d))
      have hp := P.hasFDerivAt.comp x hf
      change HasFDerivAt (fun y => P (F d k y)) _ x at hp
      rw [hp.fderiv]
      have he (v w : ℂ) : (((P v) 0 - (P w) 1 : ℝ) : ℂ) +
          Complex.I * (((P v) 1 + (P w) 0 : ℝ) : ℂ) = v + Complex.I * w := by
        apply Complex.ext <;> simp [hP0, hP1, Complex.mul_re, Complex.mul_im] <;> ring
      simp only [ContinuousLinearMap.comp_apply]
      rw [he]
      simp [Z, coordinateVector, Q, Complex.conjCLE_apply]
      field_simp
      ring_nf
      simp [Complex.I_sq]
      ring
    have hnorm (x : E2) (hx : ‖x‖ = 1) : Z x * starRingEnd ℂ (Z x) = 1 := by
      have hn := EuclideanSpace.real_norm_sq_eq x
      have hsq : (x 0)^2+(x 1)^2=1 := by
        simpa only [hx, one_pow, Fin.sum_univ_two] using hn.symm
      apply Complex.ext <;> simp [hZ, Complex.mul_re, Complex.mul_im] <;> nlinarith
    have htangent (x : E2) (v : ℂ) : inner ℝ (P v) x = (v * starRingEnd ℂ (Z x)).re := by
      simp [P, Z, coordinateVector, EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct, Fin.sum_univ_two, Complex.mul_re]
      ring
    rcases le_total p (q+1) with hle | hle
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      refine ⟨fun x => P (F (starRingEnd ℂ (c/Q)) (k+2) x), hsmooth _ _, ?_, ?_⟩
      · intro x hx
        rw [htangent]
        have hz := hnorm x hx
        have hbar : starRingEnd ℂ (Z x) * Z x = 1 := by simpa [mul_comm] using hz
        dsimp [F]
        rw [hk, pow_add]
        have hp : Z x ^ p * starRingEnd ℂ (Z x) ^ p = 1 := by
          rw [← mul_pow, hz, one_pow]
        have ht : ((c / Q) * Z x ^ p *
            (starRingEnd ℂ (Z x) ^ p * starRingEnd ℂ (Z x) ^ k) -
            starRingEnd ℂ (c / Q) * Z x ^ (k + 2)) * starRingEnd ℂ (Z x) =
            (c/Q) * starRingEnd ℂ (Z x)^(k+1) -
            starRingEnd ℂ ((c/Q) * starRingEnd ℂ (Z x)^(k+1)) := by
          simp only [map_mul, map_pow, starRingEnd_self_apply]
          simp only [pow_succ]
          calc
            _ = (c/Q) * (Z x^p * starRingEnd ℂ (Z x)^p) *
                starRingEnd ℂ (Z x)^k * starRingEnd ℂ (Z x) -
                starRingEnd ℂ (c/Q) * (Z x^k*Z x) *
                (Z x*starRingEnd ℂ (Z x)) := by ring
            _ = _ := by rw [hp, hz]; ring
        rw [ht]
        exact sub_self _
      · intro x
        simpa only [hZ] using hder (starRingEnd ℂ (c/Q)) (k+2) x
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      refine ⟨fun x => P (F (c/Q) k x), hsmooth _ _, ?_, ?_⟩
      · intro x hx
        rw [htangent]
        have hz := hnorm x hx
        have hp : Z x^(q+1) * starRingEnd ℂ (Z x)^(q+1) = 1 := by
          rw [← mul_pow, hz, one_pow]
        dsimp [F]
        rw [hk, pow_add]
        have he : (c/Q) * (Z x^(q+1)*Z x^k) * starRingEnd ℂ (Z x)^(q+1) =
            (c/Q)*Z x^k := by
          calc
            _ = (c/Q)*Z x^k*(Z x^(q+1)*starRingEnd ℂ (Z x)^(q+1)) := by ring
            _ = _ := by rw [hp, mul_one]
        rw [he, sub_self, zero_mul]
        rfl
      · intro x
        simpa only [hZ] using hder (c/Q) k x
  have moments (h : E2 → ℂ) (hh : IntegrableOn h (disc 1))
      (hmom : ∀ p q : ℕ, (∫ x in disc 1, h x *
        (((x 0 : ℂ) + Complex.I * (x 1 : ℂ)) ^ p *
          (starRingEnd ℂ ((x 0 : ℂ) + Complex.I * (x 1 : ℂ))) ^ q)) = 0) :
      ∀ᵐ x ∂volume.restrict (disc 1), h x = 0 := by
    have dense {X : Type} [TopologicalSpace X] [CompactSpace X]
        (z : C(X, ℂ)) (hz : Function.Injective z)
        (L : C(X, ℂ) →L[ℂ] ℂ)
        (hL : ∀ p q : ℕ, L (z^p * (star z)^q) = 0) : L = 0 := by
      let S : Set C(X, ℂ) := Set.range (fun pq : ℕ × ℕ => z^pq.1 * (star z)^pq.2)
      let V : Submodule ℂ C(X, ℂ) := Submodule.span ℂ S
      have hm (p q : ℕ) : z^p * (star z)^q ∈ V :=
        Submodule.subset_span ⟨(p,q), rfl⟩
      have h1 : (1 : C(X, ℂ)) ∈ V := by simpa using hm 0 0
      have hmul (f g : C(X, ℂ)) (hf : f ∈ V) (hg : g ∈ V) : f*g ∈ V := by
        induction hf, hg using Submodule.span_induction₂ with
        | mem_mem f g hf hg =>
          obtain ⟨⟨p,q⟩,rfl⟩ := hf
          obtain ⟨⟨r,s⟩,rfl⟩ := hg
          convert hm (p+r) (q+s) using 1 <;> simp only [pow_add] <;> ring
        | zero_left => simpa using V.zero_mem
        | zero_right => simpa using V.zero_mem
        | add_left f g h hf hg hh hfh hgh => simpa [add_mul] using V.add_mem hfh hgh
        | add_right f g h hf hg hh hfg hfh => simpa [mul_add] using V.add_mem hfg hfh
        | smul_left c f g hf hg hfg => simpa [smul_mul_assoc] using V.smul_mem c hfg
        | smul_right c f g hf hg hfg => simpa [mul_smul_comm] using V.smul_mem c hfg
      have hstar (f : C(X, ℂ)) (hf : f ∈ V) : star f ∈ V := by
        induction hf using Submodule.span_induction with
        | mem f hf =>
          obtain ⟨⟨p,q⟩,rfl⟩ := hf
          simpa [star_mul, star_pow, mul_comm] using hm q p
        | zero => simpa using V.zero_mem
        | add f g hf hg hsf hsg => simpa only [star_add] using V.add_mem hsf hsg
        | smul c f hf hsf => simpa only [star_smul] using V.smul_mem (star c) hsf
      let A : StarSubalgebra ℂ C(X, ℂ) :=
        { V.toSubalgebra h1 hmul with star_mem' := fun {f} hf => hstar f hf }
      have hzmem : z ∈ A := by change z ∈ V; simpa using hm 1 0
      have hsep : A.SeparatesPoints := by
        intro x y hxy
        exact ⟨z,⟨z,hzmem,rfl⟩, fun h => hxy (hz h)⟩
      have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
      have hV : V ≤ L.ker := by
        apply Submodule.span_le.mpr
        rintro f ⟨⟨p,q⟩,rfl⟩
        exact hL p q
      have hc : closure (V : Set C(X,ℂ)) ⊆ L.ker :=
        closure_minimal hV L.isClosed_ker
      have hclosure : closure (V : Set C(X,ℂ)) = Set.univ := by
        change (A.topologicalClosure : Set C(X,ℂ)) = Set.univ
        rw [htop]
        rfl
      ext f
      exact hc (hclosure.symm ▸ Set.mem_univ f)
    let K : Set E2 := closedDisc 1
    have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
    letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:E2) 1)
    let μ := volume.restrict (disc 1)
    let ν : Measure K := μ.comap Subtype.val
    have hres : μ.restrict K = μ := by
      apply Measure.restrict_eq_self_of_ae_mem
      filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet)] with x hx
      exact Metric.ball_subset_closedBall hx
    have hν : Integrable (fun x : K => h x) ν := by
      apply (integrableOn_iff_comap_subtypeVal hK).mp
      change Integrable h (μ.restrict K)
      rw [hres]
      exact hh
    have hi (f : C(K,ℂ)) : Integrable (fun x : K => h x * f x) ν :=
      hν.mul_bdd f.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x)
    let l : C(K,ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => ∫ x : K, h x * f x ∂ν
        map_add' := by
          intro f g
          simp only [ContinuousMap.add_apply, mul_add]
          exact integral_add (hi f) (hi g)
        map_smul' := by
          intro c f
          simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by ring }
    have hbound (f : C(K,ℂ)) : ‖l f‖ ≤ (∫ x : K, ‖h x‖ ∂ν) * ‖f‖ := by
      dsimp [l]
      calc
        _ ≤ ∫ x : K, ‖h x‖ * ‖f‖ ∂ν :=
          norm_integral_le_of_norm_le (hν.norm.mul_const ‖f‖)
            (Filter.Eventually.of_forall fun x => by
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _))
        _ = _ := integral_mul_const _ _
    let L : C(K,ℂ) →L[ℂ] ℂ := l.mkContinuous _ hbound
    let z : C(K,ℂ) := ⟨fun x => ((x.val 0 : ℂ) + Complex.I*(x.val 1 : ℂ)), by fun_prop⟩
    have hz : Function.Injective z := by
      intro x y hxy
      apply Subtype.ext
      ext i
      fin_cases i
      · have hr := congrArg Complex.re hxy
        simpa [z] using hr
      · have hi := congrArg Complex.im hxy
        simpa [z] using hi
    have hL : L = 0 := by
      apply dense z hz L
      intro p q
      change (∫ x : K, h x *
        (((x.val 0 : ℂ)+Complex.I*(x.val 1 : ℂ))^p *
        (starRingEnd ℂ ((x.val 0 : ℂ)+Complex.I*(x.val 1 : ℂ)))^q) ∂ν) = 0
      dsimp only [ν]
      rw [integral_subtype_comap hK (fun x : E2 => h x *
        (((x 0 : ℂ)+Complex.I*(x 1 : ℂ))^p *
        (starRingEnd ℂ ((x 0 : ℂ)+Complex.I*(x 1 : ℂ)))^q))]
      change (∫ x, h x * _ ∂μ.restrict K) = 0
      rw [hres]
      exact hmom p q
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hh.locallyIntegrable
    intro g hg hgcompact
    let gc : C(K,ℂ) := ⟨fun x => (g x : ℂ), by fun_prop⟩
    have hgL := congrArg (fun T : C(K,ℂ) →L[ℂ] ℂ => T gc) hL
    change (∫ x : K, h x * (g x : ℂ) ∂ν) = 0 at hgL
    dsimp only [ν] at hgL
    rw [integral_subtype_comap hK (fun x : E2 => h x * (g x : ℂ))] at hgL
    change (∫ x, h x * (g x : ℂ) ∂μ.restrict K) = 0 at hgL
    rw [hres] at hgL
    simpa [Complex.real_smul, mul_comm] using hgL
  let z (x : E2) : ℂ := (x 0 : ℂ) + Complex.I * (x 1 : ℂ)
  let h (x : E2) : ℂ := (a x : ℂ) - Complex.I * (b x : ℂ)
  have hh : IntegrableOn h (disc 1) := ha.ofReal.sub (hb.ofReal.const_mul Complex.I)
  have hm (p q : ℕ) : IntegrableOn (fun x => h x * (z x^p * (starRingEnd ℂ (z x))^q)) (disc 1) := by
    have hc : Continuous (fun x : E2 => z x^p * (starRingEnd ℂ (z x))^q) := by
      dsimp [z]
      fun_prop
    obtain ⟨C,hC⟩ := (isCompact_closedBall (0:E2) 1).exists_bound_of_continuousOn hc.continuousOn
    apply hh.mul_bdd hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet)] with x hx
    exact hC x (Metric.ball_subset_closedBall hx)
  have hv (p q : ℕ) (c : ℂ) :
      (∫ x in disc 1, (h x * (c * z x^p * (starRingEnd ℂ (z x))^q)).re) = 0 := by
    obtain ⟨η,hη,ht,hcoef⟩ := primitive p q c
    have hs := hstat η hη ht
    have he (x : E2) : a x *
        ((fderiv ℝ η x (coordinateVector 2 0)) 0 - (fderiv ℝ η x (coordinateVector 2 1)) 1) +
        b x * ((fderiv ℝ η x (coordinateVector 2 0)) 1 + (fderiv ℝ η x (coordinateVector 2 1)) 0) =
        2 * (h x * (c * z x^p * (starRingEnd ℂ (z x))^q)).re := by
      have he := congrArg (fun v : ℂ => (h x * v).re) (hcoef x)
      dsimp [h, z] at *
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] at he ⊢
      norm_num at he ⊢
      linear_combination he
    have hi : (∫ x in disc 1, a x *
        ((fderiv ℝ η x (coordinateVector 2 0)) 0 - (fderiv ℝ η x (coordinateVector 2 1)) 1) +
        b x * ((fderiv ℝ η x (coordinateVector 2 0)) 1 + (fderiv ℝ η x (coordinateVector 2 1)) 0)) =
        2 * ∫ x in disc 1, (h x * (c * z x^p * (starRingEnd ℂ (z x))^q)).re := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall he)
    linarith
  have hzero : ∀ᵐ x ∂volume.restrict (disc 1), h x = 0 := by
    apply moments h hh
    intro p q
    apply Complex.ext
    · change RCLike.re (∫ x in disc 1, h x * (z x^p * (starRingEnd ℂ (z x))^q)) = 0
      rw [← integral_re (hm p q)]
      simpa only [one_mul, RCLike.re_eq_complex_re] using hv p q 1
    · change RCLike.im (∫ x in disc 1, h x * (z x^p * (starRingEnd ℂ (z x))^q)) = 0
      rw [← integral_im (hm p q)]
      have hi := hv p q Complex.I
      have he (x : E2) :
          (h x * (Complex.I * z x^p * (starRingEnd ℂ (z x))^q)).re =
          -(h x * (z x^p * (starRingEnd ℂ (z x))^q)).im := by
        simp [Complex.mul_re, Complex.mul_im]
        ring
      simp_rw [he] at hi
      rw [integral_neg] at hi
      exact neg_eq_zero.mp hi
  filter_upwards [hzero] with x hx
  constructor
  · have hr := congrArg Complex.re hx
    simpa [h] using hr
  · have hi := congrArg Complex.im hx
    simpa [h] using hi
end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.EpsilonMinimizerVariation.InnerCourant
