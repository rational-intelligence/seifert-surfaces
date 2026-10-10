import B1TangencyCoordinates

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

/-- The metric is literally the nonsingular inverse of the given leading matrix. -/
def inverseMetric (A : E2 → Mat2) (x : E2) : Mat2 := (A x)⁻¹

def SymmetricOn (A : E2 → Mat2) (H : Set E2) : Prop :=
  ∀ x ∈ H, ∀ i j, A x i j = A x j i

def UniformEllipticOn (A : E2 → Mat2) (H : Set E2) : Prop :=
  ∃ ell C : ℝ, 0 < ell ∧ 0 < C ∧ ∀ x ∈ H, ∀ p : E2,
    ell * ‖p‖ ^ 2 ≤ inner ℝ p (matrixAction (A x) p) ∧
    inner ℝ p (matrixAction (A x) p) ≤ C * ‖p‖ ^ 2

/-- H01's inverse metric regularity, on the original closed half-disc. -/
structure InverseMetricData (R : ℝ) (A : E2 → Mat2) where
  radius_pos : 0 < R
  symmetric : SymmetricOn (inverseMetric A) (closedHalfDisc R)
  elliptic : UniformEllipticOn (inverseMetric A) (closedHalfDisc R)
  positive_definite : ∀ x ∈ closedHalfDisc R, ∀ p : E2, p ≠ 0 →
    0 < inner ℝ p (matrixAction (inverseMetric A x) p)
  det_one : ∀ x ∈ closedHalfDisc R, Matrix.det (inverseMetric A x) = 1
  lipschitz : ∀ i j, LipschitzBoundOn (fun x => inverseMetric A x i j) (closedHalfDisc R)
  alpha : ℝ≥0
  alpha_pos : 0 < alpha
  alpha_lt_one : alpha < 1
  holder : ∀ i j, ∃ C : ℝ≥0,
    HolderOnWith C alpha (fun x => inverseMetric A x i j) (closedHalfDisc R)

/-- Algebra/regularity scope independent of the geometric collar construction. -/
theorem inverse_det_one_metric_data (R : ℝ) (hR : 0 < R) (A : E2 → Mat2)
    (hSym : SymmetricOn A (closedHalfDisc R))
    (hEll : UniformEllipticOn A (closedHalfDisc R))
    (hLip : ∀ i j, LipschitzBoundOn (fun x => A x i j) (closedHalfDisc R))
    (hDet : ∀ x ∈ closedHalfDisc R, Matrix.det (A x) = 1) :
    Nonempty (InverseMetricData R A) := by { have hinv (x : E2) (hx : x ∈ closedHalfDisc R) : inverseMetric A x = !![A x 1 1, -A x 0 1; -A x 1 0, A x 0 0] := by { change (A x)⁻¹ = _; rw [Matrix.inv_def, hDet x hx, Ring.inverse_one, one_smul, Matrix.adjugate_fin_two] }; let rotate (p : E2) : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-p 1, p 0]; have hnorm (p : E2) : ‖rotate p‖ ^ 2 = ‖p‖ ^ 2 := by { rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]; simp only [Fin.sum_univ_two]; change (-p 1) ^ 2 + (p 0) ^ 2 = (p 0) ^ 2 + (p 1) ^ 2; ring }; have hquad (x : E2) (hx : x ∈ closedHalfDisc R) (p : E2) : inner ℝ p (matrixAction (inverseMetric A x) p) = inner ℝ (rotate p) (matrixAction (A x) (rotate p)) := by { rw [hinv x hx]; simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]; dsimp only [matrixAction]; simp only [Fin.sum_univ_two, starRingEnd_apply, star_trivial]; change (A x 1 1 * p 0 + -A x 0 1 * p 1) * p 0 + (-A x 1 0 * p 0 + A x 0 0 * p 1) * p 1 = (A x 0 0 * -p 1 + A x 0 1 * p 0) * -p 1 + (A x 1 0 * -p 1 + A x 1 1 * p 0) * p 0; rw [hSym x hx 0 1]; ring }; obtain ⟨ell, C, hell, hC, hbound⟩ := hEll; have helliptic : UniformEllipticOn (inverseMetric A) (closedHalfDisc R) := by { refine ⟨ell, C, hell, hC, ?_⟩; intro x hx p; rw [hquad x hx p]; simpa only [hnorm] using hbound x hx (rotate p) }; have hlip00 : LipschitzBoundOn (fun x => inverseMetric A x 0 0) (closedHalfDisc R) := by { obtain ⟨L, hL, hb⟩ := hLip 1 1; refine ⟨L, hL, ?_⟩; intro x hx y hy; dsimp only; rw [hinv x hx, hinv y hy]; exact hb x hx y hy }; have hlip01 : LipschitzBoundOn (fun x => inverseMetric A x 0 1) (closedHalfDisc R) := by { obtain ⟨L, hL, hb⟩ := hLip 0 1; refine ⟨L, hL, ?_⟩; intro x hx y hy; dsimp only; rw [hinv x hx, hinv y hy]; change dist (-A x 0 1) (-A y 0 1) ≤ _; rw [dist_neg_neg]; exact hb x hx y hy }; have hlip10 : LipschitzBoundOn (fun x => inverseMetric A x 1 0) (closedHalfDisc R) := by { obtain ⟨L, hL, hb⟩ := hLip 1 0; refine ⟨L, hL, ?_⟩; intro x hx y hy; dsimp only; rw [hinv x hx, hinv y hy]; change dist (-A x 1 0) (-A y 1 0) ≤ _; rw [dist_neg_neg]; exact hb x hx y hy }; have hlip11 : LipschitzBoundOn (fun x => inverseMetric A x 1 1) (closedHalfDisc R) := by { obtain ⟨L, hL, hb⟩ := hLip 0 0; refine ⟨L, hL, ?_⟩; intro x hx y hy; dsimp only; rw [hinv x hx, hinv y hy]; exact hb x hx y hy }; have hlipschitz : ∀ i j, LipschitzBoundOn (fun x => inverseMetric A x i j) (closedHalfDisc R) := by { intro i j; fin_cases i <;> fin_cases j <;> assumption }; have hsymmetric : SymmetricOn (inverseMetric A) (closedHalfDisc R) := by { intro x hx i j; rw [hinv x hx]; have h01 : -A x 0 1 = -A x 1 0 := congrArg Neg.neg (hSym x hx 0 1); have h10 : -A x 1 0 = -A x 0 1 := h01.symm; fin_cases i <;> fin_cases j <;> first | rfl | exact h01 | exact h10 }; have hpositive : ∀ x ∈ closedHalfDisc R, ∀ p : E2, p ≠ 0 → 0 < inner ℝ p (matrixAction (inverseMetric A x) p) := by { intro x hx p hp; have hpos : 0 < ell * ‖p‖ ^ 2 := mul_pos hell (sq_pos_of_pos (norm_pos_iff.mpr hp)); rw [hquad x hx p]; exact hpos.trans_le (by simpa only [hnorm] using (hbound x hx (rotate p)).1) }; have hdetinv : ∀ x ∈ closedHalfDisc R, Matrix.det (inverseMetric A x) = 1 := by { intro x hx; change Matrix.det ((A x)⁻¹) = 1; rw [Matrix.det_nonsing_inv, hDet x hx, Ring.inverse_one] }; have hholder : ∀ i j, ∃ C : ℝ≥0, HolderOnWith C (1 / 2) (fun x => inverseMetric A x i j) (closedHalfDisc R) := by { intro i j; obtain ⟨L, hL, hb⟩ := hlipschitz i j; have hf : LipschitzOnWith ⟨L, hL⟩ (fun x => inverseMetric A x i j) (closedHalfDisc R) := LipschitzOnWith.of_dist_le_mul hb; let diam : ℝ≥0 := ⟨2 * R, by positivity⟩; have hdiam : ∀ x ∈ closedHalfDisc R, ∀ y ∈ closedHalfDisc R, edist x y ≤ (diam : ℝ≥0∞) := by { intro x hx y hy; rw [edist_dist, ENNReal.ofReal_le_coe]; change dist x y ≤ 2 * R; have hx' : dist x 0 ≤ R := hx.1; have hy' : dist y 0 ≤ R := hy.1; have htri := dist_triangle_right x y (0 : E2); linarith }; exact ⟨_, HolderOnWith.of_le hdiam hf.holderOnWith (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)⟩ }; exact ⟨⟨hR, hsymmetric, helliptic, hpositive, hdetinv, hlipschitz, 1 / 2, by norm_num, by norm_num, hholder⟩⟩ }

/-- Native H01 binding; normalization remains a separately owned dependency. -/
structure SmoothJordanBoundary (Ω : Set E2) where
  gamma : ℝ → E2
  smooth : ContDiff ℝ ∞ gamma
  periodic : Function.Periodic gamma (2 * Real.pi)
  simple : ∀ t u : ℝ, gamma t = gamma u ↔
    ∃ k : ℤ, t - u = (k : ℝ) * (2 * Real.pi)
  regular : ∀ t : ℝ, deriv gamma t ≠ 0
  image : Set.range gamma = frontier Ω

/-- A finite smooth Jordan half-domain chosen before the conformal map.
Its closure meets the flat boundary; containment is in the CLOSED half-disc. -/
structure SmoothFlatJordanDomain (R : ℝ) where
  domain : Set E2
  open_domain : IsOpen domain
  bounded_domain : Bornology.IsBounded domain
  connected_domain : IsConnected domain
  boundary : SmoothJordanBoundary domain
  closure_inside : closure domain ⊆ closedHalfDisc R
  base_boundary : (0 : E2) ∈ frontier domain
  localR : ℝ
  localR_pos : 0 < localR
  localR_inside : localR < R
  contains_closed_half_disc : closedHalfDisc localR ⊆ closure domain
  inward_side : domain ∩ disc localR = halfDisc localR
  flat_subarc : frontier domain ∩ disc localR = flatArc localR

/-- The finite domain construction in H01 is an obligation, not a premise on C1. -/
theorem smooth_flat_jordan_domain (R : ℝ) (hR : 0 < R) :
    Nonempty (SmoothFlatJordanDomain R) := by
  have profile (a : ℝ) (ha : 0 < a) :
      ∃ q : ℝ → ℝ, ContDiff ℝ ∞ q ∧
        (∀ x, 0 ≤ q x) ∧
        (∀ x, q x ≤ a - Real.sqrt (a^2 - x^2)) ∧
        (∀ x, |x| ≤ a / 4 → q x = a - Real.sqrt (a^2 - x^2)) ∧
        (∀ x, a / 2 ≤ |x| → q x = 0) := by
    let b : ContDiffBump (0 : ℝ) := {
      rIn := a/4
      rOut := a/2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
    let q : ℝ → ℝ := fun x => b x * (a - Real.sqrt (a^2-x^2))
    have lower_nonneg (x : ℝ) : 0 ≤ a - Real.sqrt (a^2-x^2) := by
      have hh : Real.sqrt (a^2-x^2) ≤ Real.sqrt (a^2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
      rw [Real.sqrt_sq ha.le] at hh
      linarith
    have hzero (x : ℝ) (hx : a/2 ≤ |x|) : q x = 0 := by
      have hb : b x = 0 := b.zero_of_le_dist (by simpa [b, Real.dist_eq, sub_zero] using hx)
      simp only [q, hb, zero_mul]
    have hs : ContDiff ℝ ∞ q := by
      rw [contDiff_iff_contDiffAt]
      intro x
      by_cases hx : |x| < a
      · have hsq : 0 < a^2-x^2 := by
          have hh := abs_lt.mp hx
          nlinarith [sq_nonneg x]
        exact b.contDiff.contDiffAt.mul
          (contDiffAt_const.sub ((contDiffAt_const.sub (contDiffAt_id.pow 2)).sqrt hsq.ne'))
      · have hx' : a/2 < |x| := by
          have hh := le_of_not_gt hx
          linarith
        apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [((isOpen_lt continuous_const continuous_abs).mem_nhds hx')] with y hy
        exact hzero y hy.le
    refine ⟨q, hs, ?_, ?_, ?_, hzero⟩
    · intro x
      exact mul_nonneg b.nonneg (lower_nonneg x)
    · intro x
      exact mul_le_of_le_one_left (lower_nonneg x) b.le_one
    · intro x hx
      have hb : b x = 1 := b.one_of_mem_closedBall (by simpa [b, Metric.mem_closedBall, Real.dist_eq] using hx)
      simp only [q, hb, one_mul]
  have algebra (a : ℝ) (ha : 0 < a) (q : ℝ → ℝ)
      (hlo : ∀ x, 0 ≤ q x)
      (hup : ∀ x, q x ≤ a - Real.sqrt (a^2-x^2))
      (hflat : ∀ x, |x| ≤ a/4 → q x = a - Real.sqrt (a^2-x^2)) :
      (∀ x y, x^2 + (y+q x-a)^2 ≤ a^2 →
        0 ≤ y ∧ x^2+y^2 ≤ 5*a^2) ∧
      (∀ x y, x^2+y^2 ≤ (a/8)^2 →
        (x^2+(y+q x-a)^2 ≤ a^2 ↔ 0 ≤ y)) ∧
      (∀ x y, x^2+y^2 < (a/8)^2 →
        (x^2+(y+q x-a)^2 < a^2 ↔ 0 < y)) ∧
      (∀ x y, x^2+y^2 < (a/8)^2 →
        (x^2+(y+q x-a)^2 = a^2 ↔ y = 0)) := by
    have hlocal (x y : ℝ) (hxy : x^2+y^2 ≤ (a/8)^2) :
        q x = a - Real.sqrt (a^2-x^2) ∧
        Real.sqrt (a^2-x^2)^2 = a^2-x^2 ∧
        0 < 2*Real.sqrt (a^2-x^2)-y := by
      have hx : |x| ≤ a/4 := by
        apply abs_le.mpr
        constructor <;> nlinarith [sq_nonneg y]
      have hsq : 0 ≤ a^2-x^2 := by nlinarith [sq_nonneg y]
      have hs := Real.sq_sqrt hsq
      have hspos := Real.sqrt_nonneg (a^2-x^2)
      refine ⟨hflat x hx, hs, ?_⟩
      have hsa : a/2 < Real.sqrt (a^2-x^2) := by nlinarith [sq_nonneg y]
      have hy : y < a/2 := by nlinarith [sq_nonneg x]
      linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x y hxy
      have hx : x^2 ≤ a^2 := by nlinarith [sq_nonneg (y+q x-a)]
      have hs := Real.sq_sqrt (sub_nonneg.mpr hx)
      have hspos := Real.sqrt_nonneg (a^2-x^2)
      have hylo : -Real.sqrt (a^2-x^2) ≤ y+q x-a := by nlinarith
      have hynonneg : 0 ≤ y := by linarith [hup x]
      have hya : y ≤ 2*a := by nlinarith [hlo x]
      exact ⟨hynonneg, by nlinarith⟩
    · intro x y hxy
      obtain ⟨heq, hs, hp⟩ := hlocal x y hxy
      rw [heq]
      constructor <;> intro hh <;> nlinarith
    · intro x y hxy
      obtain ⟨heq, hs, hp⟩ := hlocal x y hxy.le
      rw [heq]
      constructor <;> intro hh <;> nlinarith
    · intro x y hxy
      obtain ⟨heq, hs, hp⟩ := hlocal x y hxy.le
      rw [heq]
      constructor <;> intro hh <;> nlinarith
  have shear (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q) :
      ∃ H : E2 ≃ₜ E2,
        (∀ z, H z 0 = z 0) ∧ (∀ z, H z 1 = z 1 - q (z 0)) ∧
        (∀ z, H.symm z 0 = z 0) ∧ (∀ z, H.symm z 1 = z 1 + q (z 0)) ∧
        ContDiff ℝ ∞ H ∧ ContDiff ℝ ∞ H.symm := by
    let f : E2 → E2 := fun z => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![z 0, z 1-q (z 0)]
    let g : E2 → E2 := fun z => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![z 0, z 1+q (z 0)]
    have hf : ContDiff ℝ ∞ f := by
      rw [contDiff_piLp]
      intro i
      fin_cases i
      · exact contDiff_piLp_apply (i := 0) 2
      · exact (contDiff_piLp_apply (i := 1) 2).sub (hq.comp (contDiff_piLp_apply (i := 0) 2))
    have hg : ContDiff ℝ ∞ g := by
      rw [contDiff_piLp]
      intro i
      fin_cases i
      · exact contDiff_piLp_apply (i := 0) 2
      · exact (contDiff_piLp_apply (i := 1) 2).add (hq.comp (contDiff_piLp_apply (i := 0) 2))
    let H : E2 ≃ₜ E2 := {
      toFun := f
      invFun := g
      left_inv := by
        intro z
        ext i
        fin_cases i <;> simp [f,g]
      right_inv := by
        intro z
        ext i
        fin_cases i <;> simp [f,g]
      continuous_toFun := hf.continuous
      continuous_invFun := hg.continuous }
    exact ⟨H, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, hf, hg⟩
  have circleFacts :
      (∀ t u : ℝ, (Real.cos t = Real.cos u ∧ Real.sin t = Real.sin u) ↔
        ∃ k : ℤ, t-u = (k : ℝ)*(2*Real.pi)) ∧
      (∀ x y a : ℝ, 0 < a → x^2+y^2=a^2 →
        ∃ t : ℝ, a*Real.cos t=x ∧ a*Real.sin t=y) := by
    constructor
    · intro t u
      constructor
      · rintro ⟨hc,hs⟩
        have hh : Real.cos (t-u) = 1 := by
          rw [Real.cos_sub, hc, hs]
          nlinarith [Real.sin_sq_add_cos_sq u]
        obtain ⟨k,hk⟩ := (Real.cos_eq_one_iff (t-u)).mp hh
        exact ⟨k,hk.symm⟩
      · rintro ⟨k,hk⟩
        have heq : t = u + (k:ℝ)*(2*Real.pi) := by linarith
        rw [heq]
        simpa only [zsmul_eq_mul] using And.intro (Real.cos_periodic.zsmul k u) (Real.sin_periodic.zsmul k u)
    · intro x y a ha hxy
      let z : ℂ := ⟨x,y⟩
      have hz : ‖z‖ = a := by
        have hn : ‖z‖^2 = x^2+y^2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          dsimp [z]
          ring
        nlinarith [norm_nonneg z]
      refine ⟨z.arg, ?_, ?_⟩
      · simpa only [hz] using Complex.norm_mul_cos_arg z
      · simpa only [hz] using Complex.norm_mul_sin_arg z
  have round (a : ℝ) (ha : 0 < a)
      (hperiod : ∀ t u : ℝ, (Real.cos t = Real.cos u ∧ Real.sin t = Real.sin u) ↔
        ∃ k : ℤ, t-u = (k : ℝ)*(2*Real.pi))
      (honto : ∀ x y a : ℝ, 0 < a → x^2+y^2=a^2 →
        ∃ t : ℝ, a*Real.cos t=x ∧ a*Real.sin t=y) :
      let c : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0,a]
      Nonempty (SmoothJordanBoundary (Metric.ball c a)) := by
    dsimp only
    let c : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0,a]
    let γ : ℝ → E2 := fun t => (EuclideanSpace.equiv (Fin 2) ℝ).symm
      ![a*Real.cos t,a+a*Real.sin t]
    have hγ : ContDiff ℝ ∞ γ := by
      rw [contDiff_piLp]
      intro i
      fin_cases i
      · exact contDiff_const.mul Real.contDiff_cos
      · exact contDiff_const.add (contDiff_const.mul Real.contDiff_sin)
    have hnorm (x : E2) : ‖x‖^2 = x 0^2 + x 1^2 := by
      simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs]
    refine ⟨{
      gamma := γ
      smooth := hγ
      periodic := ?_
      simple := ?_
      regular := ?_
      image := ?_ }⟩
    · intro t
      ext i
      fin_cases i <;> simp [γ, Real.cos_periodic t, Real.sin_periodic t]
    · intro t u
      rw [← hperiod]
      constructor
      · intro h
        have h0 := congrArg (fun x : E2 => x 0) h
        have h1 := congrArg (fun x : E2 => x 1) h
        change a*Real.cos t=a*Real.cos u at h0
        change a+a*Real.sin t=a+a*Real.sin u at h1
        exact ⟨(mul_left_cancel₀ ha.ne' h0), mul_left_cancel₀ ha.ne' (add_left_cancel h1)⟩
      · rintro ⟨hc,hs⟩
        ext i
        fin_cases i <;> simp [γ,hc,hs]
    · intro t hz
      have hd := (hγ.differentiable (by simp) t).hasDerivAt
      have hd0 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).hasFDerivAt.comp_hasDerivAt t hd
      have hd1 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).hasFDerivAt.comp_hasDerivAt t hd
      change HasDerivAt (fun t => a*Real.cos t) ((deriv γ t) 0) t at hd0
      change HasDerivAt (fun t => a+a*Real.sin t) ((deriv γ t) 1) t at hd1
      have h0 : deriv (fun t => a*Real.cos t) t = 0 := by
        simpa only [hz, PiLp.zero_apply] using hd0.deriv
      have h1 : deriv (fun t => a+a*Real.sin t) t = 0 := by
        simpa only [hz, PiLp.zero_apply] using hd1.deriv
      rw [((Real.hasDerivAt_cos t).const_mul a).deriv] at h0
      rw [((Real.hasDerivAt_sin t).const_mul a |>.const_add a).deriv] at h1
      have hs : Real.sin t = 0 := by nlinarith
      have hc : Real.cos t = 0 := by nlinarith
      nlinarith [Real.sin_sq_add_cos_sq t]
    · rw [frontier_ball c ha.ne']
      ext x
      constructor
      · rintro ⟨t,rfl⟩
        rw [Metric.mem_sphere, dist_eq_norm]
        have hh := hnorm (γ t-c)
        have hh' : ‖γ t-c‖^2 = a^2 := by
          rw [hnorm]
          change (a*Real.cos t-0)^2+(a+a*Real.sin t-a)^2=a^2
          nlinarith [Real.sin_sq_add_cos_sq t]
        nlinarith [norm_nonneg (γ t-c)]
      · intro hx
        rw [Metric.mem_sphere, dist_eq_norm] at hx
        have hn := hnorm (x-c)
        rw [hx] at hn
        have hxy : x 0^2+(x 1-a)^2=a^2 := by simpa [c] using hn.symm
        obtain ⟨t,hc,hs⟩ := honto (x 0) (x 1-a) a ha hxy
        refine ⟨t, ?_⟩
        ext i
        fin_cases i
        · exact hc
        · change a+a*Real.sin t=x 1
          linarith
  have transport (Ω : Set E2) (B : SmoothJordanBoundary Ω) (H : E2 ≃ₜ E2)
      (hf : ContDiff ℝ ∞ H) (hg : ContDiff ℝ ∞ H.symm) :
      Nonempty (SmoothJordanBoundary (H '' Ω)) := by
    refine ⟨{
      gamma := H ∘ B.gamma
      smooth := hf.comp B.smooth
      periodic := fun t => congrArg H (B.periodic t)
      simple := ?_
      regular := ?_
      image := ?_ }⟩
    · intro t u
      exact H.injective.eq_iff.trans (B.simple t u)
    · intro t hz
      have hc := ((hf.comp B.smooth).differentiable (by simp) t).hasDerivAt
      have hback := ((hg.differentiable (by simp)) (H (B.gamma t))).hasFDerivAt.comp_hasDerivAt t hc
      have heq : H.symm ∘ (H ∘ B.gamma) = B.gamma := by
        funext r
        exact H.symm_apply_apply _
      rw [heq, hz, map_zero] at hback
      exact B.regular t hback.deriv
    · rw [Set.range_comp, B.image, H.image_frontier]
  let a := R/4
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨q,hq,hqlo,hqup,hqflat,hqzero⟩ := profile a ha
  obtain ⟨H,hH0,hH1,hHi0,hHi1,hHs,hHis⟩ := shear q hq
  have hA := algebra a ha q hqlo hqup hqflat
  let c : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0,a]
  let Ω : Set E2 := H '' Metric.ball c a
  have hnorm (z : E2) : ‖z‖^2 = z 0^2+z 1^2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs]
  have himage (D : Set E2) (z : E2) : z ∈ H '' D ↔ H.symm z ∈ D := by
    constructor
    · rintro ⟨w,hw,rfl⟩
      simpa only [H.symm_apply_apply] using hw
    · intro hz
      exact ⟨H.symm z,hz,H.apply_symm_apply z⟩
  have hsq (z : E2) : ‖H.symm z-c‖^2 = z 0^2+(z 1+q (z 0)-a)^2 := by
    rw [hnorm]
    change (H.symm z 0-0)^2+(H.symm z 1-a)^2 = _
    rw [hHi0,hHi1,sub_zero]
  have hmem (z : E2) : z ∈ Ω ↔ z 0^2+(z 1+q (z 0)-a)^2 < a^2 := by
    rw [himage,Metric.mem_ball,dist_eq_norm,← sq_lt_sq₀ (norm_nonneg _) ha.le,hsq]
  have hcl : closure Ω = H '' Metric.closedBall c a := by
    rw [← closure_ball c ha.ne', H.image_closure]
  have hcmem (z : E2) : z ∈ closure Ω ↔ z 0^2+(z 1+q (z 0)-a)^2 ≤ a^2 := by
    rw [hcl,himage,Metric.mem_closedBall,dist_eq_norm,← sq_le_sq₀ (norm_nonneg _) ha.le,hsq]
  have hfr : frontier Ω = H '' Metric.sphere c a := by
    rw [← frontier_ball c ha.ne', H.image_frontier]
  have hfmem (z : E2) : z ∈ frontier Ω ↔ z 0^2+(z 1+q (z 0)-a)^2 = a^2 := by
    rw [hfr,himage,Metric.mem_sphere,dist_eq_norm]
    constructor
    · intro hz
      rw [← hsq,hz]
    · intro hz
      rw [← hsq] at hz
      nlinarith [norm_nonneg (H.symm z-c)]
  obtain ⟨B⟩ := round a ha circleFacts.1 circleFacts.2
  obtain ⟨B'⟩ := transport (Metric.ball c a) B H hHs hHis
  refine ⟨{
    domain := Ω
    open_domain := H.isOpenMap _ Metric.isOpen_ball
    bounded_domain := ((isCompact_closedBall c a).image H.continuous).isBounded.subset
      (by intro z hz; exact hcl ▸ subset_closure hz)
    connected_domain := (convex_ball c a).isConnected ⟨c,Metric.mem_ball_self ha⟩ |>.image H H.continuous.continuousOn
    boundary := B'
    closure_inside := ?_
    base_boundary := ?_
    localR := a/8
    localR_pos := by positivity
    localR_inside := by dsimp [a]; linarith
    contains_closed_half_disc := ?_
    inward_side := ?_
    flat_subarc := ?_ }⟩
  · intro z hz
    have hb := hA.1 (z 0) (z 1) ((hcmem z).mp hz)
    refine ⟨?_,hb.1⟩
    change ‖z-0‖ ≤ R
    rw [sub_zero,← sq_le_sq₀ (norm_nonneg _) hR.le,hnorm]
    dsimp [a] at hb
    nlinarith
  · rw [hfmem]
    have hq0 := hqflat 0 (by simp; positivity)
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, Real.sqrt_sq ha.le, sub_self] at hq0
    simp only [PiLp.zero_apply,hq0]
    ring
  · intro z hz
    rw [hcmem]
    have hb : z 0^2+z 1^2 ≤ (a/8)^2 := by
      rw [← hnorm, sq_le_sq₀ (norm_nonneg _) (by positivity)]
      have hh : dist z 0 ≤ a/8 := hz.1
      simpa only [dist_zero_right] using hh
    exact (hA.2.1 (z 0) (z 1) hb).mpr hz.2
  · ext z
    have hb : z ∈ disc (a/8) ↔ z 0^2+z 1^2 < (a/8)^2 := by
      change dist z 0 < a/8 ↔ _
      rw [dist_zero_right,← sq_lt_sq₀ (norm_nonneg _) (by positivity),hnorm]
    constructor
    · rintro ⟨hz,hr⟩
      exact ⟨hr,(hA.2.2.1 (z 0) (z 1) (hb.mp hr)).mp ((hmem z).mp hz)⟩
    · rintro ⟨hr,hz⟩
      exact ⟨(hmem z).mpr ((hA.2.2.1 (z 0) (z 1) (hb.mp hr)).mpr hz),hr⟩
  · ext z
    have hb : z ∈ disc (a/8) ↔ z 0^2+z 1^2 < (a/8)^2 := by
      change dist z 0 < a/8 ↔ _
      rw [dist_zero_right,← sq_lt_sq₀ (norm_nonneg _) (by positivity),hnorm]
    constructor
    · rintro ⟨hz,hr⟩
      exact ⟨hr,(hA.2.2.2 (z 0) (z 1) (hb.mp hr)).mp ((hfmem z).mp hz)⟩
    · rintro ⟨hr,hz⟩
      exact ⟨(hfmem z).mpr ((hA.2.2.2 (z 0) (z 1) (hb.mp hr)).mpr hz),hr⟩

/-- Matrix of the actual within derivative in the existing E2 coordinates. -/
def jacobianWithin (f : E2 → E2) (S : Set E2) (x : E2) : Mat2 :=
  fun i j => (fderivWithin ℝ f S x (coordinateVector 2 j)) i

/-- Closed-disc metric parametrization, including its genuine partial inverse.
Boundary jets are within jets here; ambient extensions are a separate obligation. -/
structure MetricDiscParametrization {R : ℝ} {A : E2 → Mat2}
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) where
  tau : PartialHomeomorph E2 E2
  source_eq : tau.source = closedDisc 1
  target_eq : tau.target = closure Ω.domain
  interior_image : tau '' disc 1 = Ω.domain
  boundary_image : tau '' Metric.sphere (0 : E2) 1 = frontier Ω.domain
  inverse_interior_image : tau.symm '' Ω.domain = disc 1
  inverse_boundary_image : tau.symm '' frontier Ω.domain = Metric.sphere (0 : E2) 1
  forward_C1 : ContDiffOn ℝ 1 tau (closedDisc 1)
  inverse_C1 : ContDiffOn ℝ 1 tau.symm (closure Ω.domain)
  forward_det : ∀ z ∈ closedDisc 1,
    Matrix.det (jacobianWithin tau (closedDisc 1) z) ≠ 0
  inverse_det : ∀ x ∈ closure Ω.domain,
    Matrix.det (jacobianWithin tau.symm (closure Ω.domain) x) ≠ 0
  forward_holder : ∀ i j, ∃ C : ℝ≥0,
    HolderOnWith C G.alpha (fun z => jacobianWithin tau (closedDisc 1) z i j) (closedDisc 1)
  inverse_holder : ∀ i j, ∃ C : ℝ≥0,
    HolderOnWith C G.alpha (fun x => jacobianWithin tau.symm (closure Ω.domain) x i j)
      (closure Ω.domain)
  base : E2
  base_on_circle : base ∈ Metric.sphere (0 : E2) 1
  base_image : tau base = 0
  inverse_base : tau.symm 0 = base
  lambda : E2 → ℝ
  lambda_continuous : ContinuousOn lambda (closedDisc 1)
  lambda_pos : ∀ z ∈ closedDisc 1, 0 < lambda z
  conformal : ∀ z ∈ closedDisc 1,
    (jacobianWithin tau (closedDisc 1) z).transpose * inverseMetric A (tau z) *
      jacobianWithin tau (closedDisc 1) z = lambda z • (1 : Mat2)

/-- H02 analytic debt: Hildebrandt--von der Mosel [9], Theorem 4.1, m=1,
for the actual inverse metric, with its closed-domain boundary interpretation. -/
structure MetricParametrizationExtensions {R : ℝ} {A : E2 → Mat2}
    {G : InverseMetricData R A} {Ω : SmoothFlatJordanDomain R}
    (P : MetricDiscParametrization G Ω) where
  forward : E2 → E2
  inverse : E2 → E2
  forward_neighborhood : Set E2
  inverse_neighborhood : Set E2
  forward_open : IsOpen forward_neighborhood
  inverse_open : IsOpen inverse_neighborhood
  forward_contains : closedDisc 1 ⊆ forward_neighborhood
  inverse_contains : closure Ω.domain ⊆ inverse_neighborhood
  forward_C1 : ContDiffOn ℝ 1 forward forward_neighborhood
  inverse_C1 : ContDiffOn ℝ 1 inverse inverse_neighborhood
  forward_agrees : ∀ z ∈ closedDisc 1, forward z = P.tau z
  inverse_agrees : ∀ x ∈ closure Ω.domain, inverse x = P.tau.symm x
  forward_jet : ∀ z ∈ closedDisc 1,
    jacobian forward z = jacobianWithin P.tau (closedDisc 1) z
  inverse_jet : ∀ x ∈ closure Ω.domain,
    jacobian inverse x = jacobianWithin P.tau.symm (closure Ω.domain) x
  forward_det : ∀ z ∈ forward_neighborhood, Matrix.det (jacobian forward z) ≠ 0
  inverse_det : ∀ x ∈ inverse_neighborhood, Matrix.det (jacobian inverse x) ≠ 0

/-- The smooth-domain extension debt needed to realize native total fderiv. -/
theorem metric_parametrization_ambient_extensions {R : ℝ} {A : E2 → Mat2}
    {G : InverseMetricData R A} {Ω : SmoothFlatJordanDomain R}
    (P : MetricDiscParametrization G Ω) :
    Nonempty (MetricParametrizationExtensions P) := by   { classical   { have hsurj (L : E2 →L[ℝ] E2)       (hdet : Matrix.det (fun i j => (L (coordinateVector 2 j)) i) ≠ 0) :       Function.Surjective L := by     { have hexpand (x : E2) : x = ∑ j : Fin 2, x j • coordinateVector 2 j := by       { ext i; simp [coordinateVector, EuclideanSpace.single, PiLp.single_apply,         Fin.sum_univ_succ]; fin_cases i <;> simp }; have hmatrix (x : E2) (i : Fin 2) :         L x i = Matrix.mulVec (fun i j => L (coordinateVector 2 j) i) (fun j => x j) i := by       { conv_lhs => { rw [hexpand x] }; simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, map_add, map_smul,         PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]; ring }; have hm : Function.Surjective         (Matrix.mulVec (fun i j => L (coordinateVector 2 j) i)) :=       Matrix.mulVec_surjective_iff_isUnit.mpr         ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)); intro y; obtain ⟨v, hv⟩ := hm (fun i => y i); refine ⟨(EuclideanSpace.equiv (Fin 2) ℝ).symm v, ?_⟩; ext i; rw [hmatrix]; exact congrFun hv i }; have hdisc : UniqueDiffOn ℝ (closedDisc 1) := by     { apply uniqueDiffOn_convex (convex_closedBall (0 : E2) 1); rw [interior_closedBall _ (by { norm_num } : (1 : ℝ) ≠ 0)]; exact ⟨0, by { simp }⟩ }; have himage : P.tau '' closedDisc 1 = closure Ω.domain := by     { rw [← P.source_eq, P.tau.image_source_eq_target, P.target_eq] }; have hdomain : UniqueDiffOn ℝ (closure Ω.domain) := by     { rw [← himage]; exact hdisc.image (fun z hz =>       (P.forward_C1.differentiableOn (by { norm_num }) z hz).hasFDerivWithinAt)         (fun z hz => (hsurj (fderivWithin ℝ P.tau (closedDisc 1) z)           (P.forward_det z hz)).denseRange) }; have hjets {S : Set E2} (hS : UniqueDiffOn ℝ S)       {f F : E2 → E2} {U : Set E2} (hU : IsOpen U) (hSU : S ⊆ U)       (hF : ContDiffOn ℝ 1 F U) (hEq : Set.EqOn F f S) :       ∀ x ∈ S, jacobian F x = jacobianWithin f S x := by     { intro x hx; have hDF : DifferentiableAt ℝ F x :=       (hF.contDiffAt (hU.mem_nhds (hSU hx))).differentiableAt (by { norm_num }); have hD : fderiv ℝ F x = fderivWithin ℝ f S x := by       { rw [← fderivWithin_eq_fderiv (hS x hx) hDF,         fderivWithin_congr' hEq hx] }; exact congrArg (fun L : E2 →L[ℝ] E2 =>       fun i j => (L (coordinateVector 2 j)) i) hD }; have hshrink (F : E2 → E2) {S U : Set E2} (hU : IsOpen U)       (hSU : S ⊆ U) (hF : ContDiffOn ℝ 1 F U)       (hdet : ∀ x ∈ S, Matrix.det (jacobian F x) ≠ 0) :       ∃ V : Set E2, IsOpen V ∧ S ⊆ V ∧ V ⊆ U ∧         ContDiffOn ℝ 1 F V ∧ ∀ x ∈ V, Matrix.det (jacobian F x) ≠ 0 := by     { have hDf : ContinuousOn (fderiv ℝ F) U :=       hF.continuousOn_fderiv_of_isOpen hU (by { norm_num }); have hentry (i j : Fin 2) : ContinuousOn (fun x => jacobian F x i j) U := by       { exact ((EuclideanSpace.proj i).continuous.comp_continuousOn         (hDf.clm_apply continuousOn_const)) }; have hdetC : ContinuousOn (fun x => Matrix.det (jacobian F x)) U := by       { simp only [Matrix.det_fin_two]; exact ((hentry 0 0).mul (hentry 1 1)).sub ((hentry 0 1).mul (hentry 1 0)) }; let V : Set E2 := U ∩ (fun x => Matrix.det (jacobian F x)) ⁻¹' ({0} : Set ℝ)ᶜ; refine ⟨V, hdetC.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl,       ?_, inter_subset_left, hF.mono inter_subset_left, ?_⟩; · { intro x hx; exact ⟨hSU hx, hdet x hx⟩ }; · { intro x hx; exact hx.2 } }; have hBall (f : E2 → E2) (hf : ContDiffOn ℝ 1 f (closedDisc 1)) :       ∃ F : E2 → E2, ∃ U : Set E2, IsOpen U ∧ closedDisc 1 ⊆ U ∧         ContDiffOn ℝ 1 F U ∧ Set.EqOn F f (closedDisc 1) := by     { classical     { have hglue {A B : Set E2} (hA : IsClosed A) (hB : IsClosed B)         (hUD : UniqueDiffOn ℝ (A ∪ B)) (f g : E2 → E2)         (Df Dg : E2 → E2 →L[ℝ] E2)         (hDf : ContinuousOn Df A) (hDg : ContinuousOn Dg B)         (hf : ∀ x ∈ A, HasFDerivWithinAt f (Df x) A x)         (hg : ∀ x ∈ B, HasFDerivWithinAt g (Dg x) B x)         (heq : ∀ x ∈ A ∩ B, f x = g x)         (hDeq : ∀ x ∈ A ∩ B, Df x = Dg x) :         ContDiffOn ℝ 1 (fun x => if x ∈ A then f x else g x) (A ∪ B) := by       { let F : E2 → E2 := fun x => if x ∈ A then f x else g x; let D : E2 → E2 →L[ℝ] E2 := fun x => if x ∈ A then Df x else Dg x; have hFa : EqOn F f A := by { intro x hx; simp only [F, ite_eq_left hx] }; have hFb : EqOn F g B := by         { intro x hx; by_cases ha : x ∈ A; · { simp only [F, ite_eq_left ha, heq x ⟨ha, hx⟩] }; · { simp only [F, ite_eq_right ha] } }; have hDa : EqOn D Df A := by { intro x hx; simp only [D, ite_eq_left hx] }; have hDb : EqOn D Dg B := by         { intro x hx; by_cases ha : x ∈ A; · { simp only [D, ite_eq_left ha, hDeq x ⟨ha, hx⟩] }; · { simp only [D, ite_eq_right ha] } }; have hDC : ContinuousOn D (A ∪ B) :=         (hDf.congr hDa).union_of_isClosed (hDg.congr hDb) hA hB; apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUD         (n := (0 : WithTop ℕ∞))).mpr; refine ⟨by { simp }, D, contDiffOn_zero.mpr hDC, ?_⟩; intro x hx; have hfa : HasFDerivWithinAt F (D x) A x := by         { by_cases ha : x ∈ A; · { rw [hDa ha]; exact (hf x ha).congr' hFa ha }; · { exact HasFDerivWithinAt.of_notMem_closure (by { simpa only [hA.closure_eq] using ha }) } }; have hgb : HasFDerivWithinAt F (D x) B x := by         { by_cases hb : x ∈ B; · { rw [hDb hb]; exact (hg x hb).congr' hFb hb }; · { exact HasFDerivWithinAt.of_notMem_closure (by { simpa only [hB.closure_eq] using hb }) } }; exact hfa.union hgb }; let S : Set E2 := {x | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 5/4}; let φ (k : ℝ) (x : E2) : E2 := ((k+1) / ‖x‖ - k) • x; have hScl : IsClosed S :=       (isClosed_le continuous_const continuous_norm).inter         (isClosed_le continuous_norm continuous_const); have hφAt (k : ℝ) {x : E2} (hx : x ≠ 0) : ContDiffAt ℝ 1 (φ k) x :=       ((contDiffAt_const.div (contDiffAt_norm ℝ hx) (norm_pos_iff.mpr hx).ne').sub         contDiffAt_const).smul contDiffAt_id; have hφ (k : ℝ) : ContDiffOn ℝ 1 (φ k) {x | x ≠ 0} := by       { intro x hx; exact (hφAt k hx).contDiffWithinAt }; have hφS (k : ℝ) : ContDiffOn ℝ 1 (φ k) S :=       (hφ k).mono (fun x hx => norm_pos_iff.mp (by { linarith [hx.1] })); have hφmaps (k : ℝ) (hk : 1 ≤ k ∧ k ≤ 2) : MapsTo (φ k) S (closedDisc 1) := by       { intro x hx; change _ ∈ Metric.closedBall (0 : E2) 1; rw [mem_closedBall_zero_iff]; have hxpos : 0 < ‖x‖ := by { linarith [hx.1] }; have hcoeff : 0 ≤ (k + 1) / ‖x‖ - k := by         { rw [sub_nonneg, le_div_iff₀ hxpos]; nlinarith [hk.1, hk.2, hx.2] }; change ‖((k+1) / ‖x‖ - k) • x‖ ≤ 1; rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoeff, sub_mul,         div_mul_cancel₀ _ hxpos.ne']; nlinarith [hk.1, hk.2, hx.1] }; have hφbase (k : ℝ) {x : E2} (hx : ‖x‖ = 1) : φ k x = x := by       { simp [φ, hx] }; have hDφ {x : E2} (hx : ‖x‖ = 1) :         3 • fderiv ℝ (φ 1) x - 2 • fderiv ℝ (φ 2) x =           ContinuousLinearMap.id ℝ E2 := by       { have hx0 : x ≠ 0 := by { intro h; simp [h] at hx }; have hnorm := ((contDiffAt_norm ℝ hx0 : ContDiffAt ℝ 1 norm x).differentiableAt         (by { norm_num })).hasFDerivAt; have hinv := (hasDerivAt_inv (by { rw [hx]; norm_num } : ‖x‖ ≠ 0)).comp_hasFDerivAt x hnorm; have h1 := ((hinv.const_mul 2).sub_const 1).smul (hasFDerivAt_id x); have h2 := ((hinv.const_mul 3).sub_const 2).smul (hasFDerivAt_id x); simp only [Function.comp_apply, id_eq] at h1 h2; have hφ1 : φ 1 = fun y : E2 => (2 / ‖y‖ - 1) • y := by         { funext y; norm_num [φ] }; have hφ2 : φ 2 = fun y : E2 => (3 / ‖y‖ - 2) • y := by         { funext y; norm_num [φ] }; change HasFDerivAt (fun y : E2 => (2 / ‖y‖ - 1) • y) _ x at h1; change HasFDerivAt (fun y : E2 => (3 / ‖y‖ - 2) • y) _ x at h2; rw [hφ1, hφ2]; rw [h1.fderiv, h2.fderiv]; ext y i; simp [hx, ContinuousLinearMap.smulRight_apply]; ring }; have hdisc : UniqueDiffOn ℝ (closedDisc 1) := by       { apply uniqueDiffOn_convex (convex_closedBall (0 : E2) 1); rw [interior_closedBall _ (by { norm_num } : (1 : ℝ) ≠ 0)]; exact ⟨0, by { simp }⟩ }; let Df := fderivWithin ℝ f (closedDisc 1); let g : E2 → E2 := fun x => 3 • f (φ 1 x) - 2 • f (φ 2 x); let Dg : E2 → E2 →L[ℝ] E2 := fun x =>       3 • (Df (φ 1 x)).comp (fderiv ℝ (φ 1) x) -         2 • (Df (φ 2 x)).comp (fderiv ℝ (φ 2) x); have hDC : ContinuousOn Df (closedDisc 1) :=       hf.continuousOn_fderivWithin hdisc (by { norm_num }); have hDφC (k : ℝ) : ContinuousOn (fderiv ℝ (φ k)) S := by       { exact ((hφ k).continuousOn_fderiv_of_isOpen isClosed_singleton.isOpen_compl         (by { norm_num })).mono (fun x hx => norm_pos_iff.mp (by { linarith [hx.1] })) }; have hDgC : ContinuousOn Dg S := by       { exact (((hDC.comp (hφS 1).continuousOn (hφmaps 1 (by { norm_num }))).clm_comp         (hDφC 1)).const_smul 3).sub           (((hDC.comp (hφS 2).continuousOn (hφmaps 2 (by { norm_num }))).clm_comp             (hDφC 2)).const_smul 2) }; have hgd (x : E2) (hx : x ∈ S) : HasFDerivWithinAt g (Dg x) S x := by       { have hd (k : ℝ) (hk : 1 ≤ k ∧ k ≤ 2) :=         ((hf.differentiableOn (by { norm_num }) _ (hφmaps k hk hx)).hasFDerivWithinAt).comp x           ((hφAt k (norm_pos_iff.mp (by { linarith [hx.1] }))).differentiableAt             (by { norm_num })).hasFDerivAt.hasFDerivWithinAt (hφmaps k hk); exact ((hd 1 (by { norm_num })).const_smul 3).sub ((hd 2 (by { norm_num })).const_smul 2) }; have hmatch (x : E2) (hx : x ∈ closedDisc 1 ∩ S) : ‖x‖ = 1 := by       { exact le_antisymm (mem_closedBall_zero_iff.mp hx.1) hx.2.1 }; have hgeq (x : E2) (hx : x ∈ closedDisc 1 ∩ S) : f x = g x := by       { dsimp only [g]; rw [hφbase 1 (hmatch x hx), hφbase 2 (hmatch x hx)]; module }; have hDgeq (x : E2) (hx : x ∈ closedDisc 1 ∩ S) : Df x = Dg x := by       { dsimp only [Dg]; rw [hφbase 1 (hmatch x hx), hφbase 2 (hmatch x hx)]; rw [← ContinuousLinearMap.comp_smul, ← ContinuousLinearMap.comp_smul,         ← ContinuousLinearMap.comp_sub, hDφ (hmatch x hx), ContinuousLinearMap.comp_id] }; have hset : closedDisc 1 ∪ S = closedDisc (5/4) := by       { ext x; change (x ∈ Metric.closedBall (0 : E2) 1 ∨         (1 ≤ ‖x‖ ∧ ‖x‖ ≤ 5/4)) ↔ x ∈ Metric.closedBall (0 : E2) (5/4); rw [mem_closedBall_zero_iff, mem_closedBall_zero_iff]; constructor; · { rintro (hx | hx); · { linarith }; · { exact hx.2 } }; · { intro hx; by_cases h : ‖x‖ ≤ 1; · { exact Or.inl h }; · { exact Or.inr ⟨(not_le.mp h).le, hx⟩ } } }; have hUD : UniqueDiffOn ℝ (closedDisc 1 ∪ S) := by       { rw [hset]; apply uniqueDiffOn_convex (convex_closedBall (0 : E2) (5/4)); rw [interior_closedBall _ (by { norm_num } : (5/4 : ℝ) ≠ 0)]; exact ⟨0, by { simp }⟩ }; have hF := hglue (A := closedDisc 1) Metric.isClosed_closedBall hScl hUD f g Df Dg hDC hDgC       (fun x hx => (hf.differentiableOn (by { norm_num }) x hx).hasFDerivWithinAt)       hgd hgeq hDgeq; rw [hset] at hF; refine ⟨fun x => if x ∈ closedDisc 1 then f x else g x, Metric.ball 0 (5/4),       Metric.isOpen_ball, ?_, hF.mono Metric.ball_subset_closedBall, ?_⟩; · { intro x hx; rw [mem_ball_zero_iff]; have h := mem_closedBall_zero_iff.mp hx; linarith }; · { intro x hx; simp only [ite_eq_left hx] } } }; have hExt :       (∃ F : E2 → E2, ∃ U : Set E2, IsOpen U ∧ closedDisc 1 ⊆ U ∧         ContDiffOn ℝ 1 F U ∧ Set.EqOn F P.tau (closedDisc 1)) ∧       (∃ I : E2 → E2, ∃ V : Set E2, IsOpen V ∧ closure Ω.domain ⊆ V ∧         ContDiffOn ℝ 1 I V ∧ Set.EqOn I P.tau.symm (closure Ω.domain)) := by     { obtain ⟨F, U, hU, hSU, hF, hEq⟩ := hBall P.tau P.forward_C1; have hInverse : ∃ I : E2 → E2, ContDiff ℝ 1 I ∧         Set.EqOn I P.tau.symm (closure Ω.domain) := by       { classical       { have hdisc : UniqueDiffOn ℝ (closedDisc 1) := by         { apply uniqueDiffOn_convex (convex_closedBall (0 : E2) 1); rw [interior_closedBall _ (by { norm_num } : (1 : ℝ) ≠ 0)]; exact ⟨0, by { simp }⟩ }; have hdf (z : E2) (hz : z ∈ closedDisc 1) :           fderiv ℝ F z = fderivWithin ℝ P.tau (closedDisc 1) z := by         { rw [← fderivWithin_eq_fderiv (hdisc z hz)           ((hF.contDiffAt (hU.mem_nhds (hSU hz))).differentiableAt (by { norm_num })),           fderivWithin_congr' hEq hz] }; have hlocal (x : E2) (hx : x ∈ closure Ω.domain) :           ∃ V ∈ 𝓝 x, ∃ I : E2 → E2, ContDiffOn ℝ 1 I V ∧             ∀ y ∈ V, y ∈ closure Ω.domain → I y = P.tau.symm y := by         { let z : E2 := P.tau.symm x; have hxt : x ∈ P.tau.target := P.target_eq.symm ▸ hx; have hz : z ∈ closedDisc 1 := P.source_eq ▸ P.tau.map_target hxt; have hFz : F z = x := (hEq hz).trans (P.tau.right_inv hxt); have hFAt : ContDiffAt ℝ 1 F z := hF.contDiffAt (hU.mem_nhds (hSU hz)); have hs : Surjective (fderiv ℝ F z) := by           { rw [hdf z hz]; exact hsurj _ (P.forward_det z hz) }; have hb : Bijective (fderiv ℝ F z).toLinearMap :=           ⟨LinearMap.injective_iff_surjective.mpr hs, hs⟩; let L : E2 ≃L[ℝ] E2 :=           (LinearEquiv.ofBijective (fderiv ℝ F z).toLinearMap hb).toContinuousLinearEquiv; have hL : (L : E2 →L[ℝ] E2) = fderiv ℝ F z := by { ext q; rfl }; have hFD : HasFDerivAt F (L : E2 →L[ℝ] E2) z := by           { rw [hL]; exact (hFAt.differentiableAt (by { norm_num })).hasFDerivAt }; let I : E2 → E2 := hFAt.localInverse hFD (by { norm_num }); have hI : ContDiffAt ℝ 1 I x := by           { rw [← hFz]; exact hFAt.to_localInverse hFD (by { norm_num }) }; have hleft : ∀ᶠ q in 𝓝 z, I (F q) = q :=           (hFAt.hasStrictFDerivAt' hFD (by { norm_num })).eventually_left_inverse; have hPcont : ContinuousWithinAt P.tau.symm (closure Ω.domain) x := by           { rw [← P.target_eq]; exact P.tau.continuousOn_symm x hxt }; have hEqI : I =ᶠ[𝓝[closure Ω.domain] x] P.tau.symm := by           { filter_upwards [hPcont.tendsto.eventually hleft, self_mem_nhdsWithin] with y hy hyt; have hyt' : y ∈ P.tau.target := P.target_eq.symm ▸ hyt; have hyz : P.tau.symm y ∈ closedDisc 1 := P.source_eq ▸ P.tau.map_target hyt'; rw [(hEq hyz).trans (P.tau.right_inv hyt')] at hy; exact hy }; obtain ⟨V, hV, hIV⟩ := hI.contDiffOn (m := 1) le_rfl (by { norm_num }); obtain ⟨O, hO, hOeq⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hEqI; refine ⟨V ∩ O, Filter.inter_mem hV hO, I, hIV.mono inter_subset_left, ?_⟩; intro y hy hyt; exact hOeq ⟨hy.2, hyt⟩ }; let C : E2 → Set E2 := fun x => {v | x ∈ closure Ω.domain → v = P.tau.symm x}; have hC (x : E2) : Convex ℝ (C x) := by         { rw [convex_iff_add_mem]; intro a ha b hb s t _ _ hsum hx; rw [ha hx, hb hx, ← add_smul, hsum, one_smul] }; have hloc (x : E2) : ∃ V ∈ 𝓝 x, ∃ I : E2 → E2,           ContMDiffOn 𝓘(ℝ, E2) 𝓘(ℝ, E2) 1 I V ∧ ∀ y ∈ V, I y ∈ C y := by         { by_cases hx : x ∈ closure Ω.domain; · { obtain ⟨V, hV, I, hI, hEqI⟩ := hlocal x hx; exact ⟨V, hV, I, hI.contMDiffOn, hEqI⟩ }; · { refine ⟨(closure Ω.domain)ᶜ, isClosed_closure.isOpen_compl.mem_nhds hx,             0, contMDiffOn_const, ?_⟩; intro y hy hyt; exact False.elim (hy hyt) } }; obtain ⟨I, hI⟩ := exists_contMDiffMap_forall_mem_convex_of_local         (I := 𝓘(ℝ, E2)) (n := (1 : ℕ∞)) hC hloc; exact ⟨I, I.contMDiff.contDiff, fun x hx => hI x hx⟩ } }; obtain ⟨I, hI, hIeq⟩ := hInverse; exact ⟨⟨F, U, hU, hSU, hF, hEq⟩,       ⟨I, Set.univ, isOpen_univ, subset_univ _, hI.contDiffOn, hIeq⟩⟩ }; obtain ⟨⟨F, U, hU, hSU, hF, hFeq⟩, ⟨I, V, hV, hTV, hI, hIeq⟩⟩ := hExt; have hFjet := hjets hdisc hU hSU hF hFeq; have hIjet := hjets hdomain hV hTV hI hIeq; have hFdet (z : E2) (hz : z ∈ closedDisc 1) :       Matrix.det (jacobian F z) ≠ 0 := by     { rw [hFjet z hz]; exact P.forward_det z hz }; have hIdet (x : E2) (hx : x ∈ closure Ω.domain) :       Matrix.det (jacobian I x) ≠ 0 := by     { rw [hIjet x hx]; exact P.inverse_det x hx }; obtain ⟨U', hU', hSU', hU'U, hF', hFdet'⟩ := hshrink F hU hSU hF hFdet; obtain ⟨V', hV', hTV', hV'V, hI', hIdet'⟩ := hshrink I hV hTV hI hIdet; exact ⟨{     forward := F, inverse := I, forward_neighborhood := U', inverse_neighborhood := V', forward_open := hU', inverse_open := hV', forward_contains := hSU', inverse_contains := hTV', forward_C1 := hF', inverse_C1 := hI', forward_agrees := hFeq, inverse_agrees := hIeq, forward_jet := hFjet, inverse_jet := hIjet, forward_det := hFdet', inverse_det := hIdet' }⟩ } }

def complexCoordinate (x : E2) : ℂ := (x 0 : ℂ) + Complex.I * (x 1 : ℂ)
def realCoordinate (z : ℂ) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![z.re, z.im]

/-- Cayley/Mobius map with zero at a and pole at -a, where |a|=1. -/
def boundaryMobius (a z : E2) : E2 :=
  realCoordinate (Complex.I * ((-complexCoordinate a) + complexCoordinate z) /
    ((-complexCoordinate a) - complexCoordinate z))

/-- Local H02 restriction/composition, producing ALL native fields on one chart.
The chart is tied pointwise to the actual Mobius map and actual inverse of tau. -/
theorem native_boundary_patch_from_metric_provider (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) (N : PositiveNormalization W)
    (G : InverseMetricData (N.R / 2) N.normalizedA)
    (Ω : SmoothFlatJordanDomain (N.R / 2))
    (P : MetricDiscParametrization G Ω) (X : MetricParametrizationExtensions P) :
    ∃ F : BoundaryIsothermalPatch N,
      F.sourceR < Ω.localR ∧
      (∀ x ∈ closedHalfDisc F.sourceR, F.chart x = boundaryMobius P.base (P.tau.symm x)) ∧
      (∀ x ∈ F.chart.source, F.chart x = boundaryMobius P.base (X.inverse x)) ∧
      (∀ x ∈ flatArc F.sourceR, P.tau.symm x ≠ -P.base) :=  by 
  have pole_denominator (a z : E2) : (-complexCoordinate a) - complexCoordinate z = 0 ↔ z = -a := by
    constructor
    · intro h
      ext i
      fin_cases i
      · have hr := congrArg Complex.re h
        dsimp [complexCoordinate] at hr
        simp at hr
        change z 0 = -a 0
        linarith
      · have hi := congrArg Complex.im h
        dsimp [complexCoordinate] at hi
        simp at hi
        change z 1 = -a 1
        linarith
    · intro h
      subst z
      dsimp [complexCoordinate]
      simp
      ring
  have mobius_base (a : E2) : boundaryMobius a a = 0 := by
    change realCoordinate (Complex.I * ((-complexCoordinate a) + complexCoordinate a) /
      ((-complexCoordinate a) - complexCoordinate a)) = 0
    rw [neg_add_cancel, mul_zero, zero_div]
    change (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(0 : ℂ).re, (0 : ℂ).im] = 0
    ext i
    fin_cases i <;> rfl
  have complex_smooth : ContDiff ℝ ∞ complexCoordinate := by
    unfold complexCoordinate
    apply ContDiff.add
    · exact Complex.ofRealCLM.contDiff.comp (by fun_prop)
    · apply contDiff_const.mul
      exact Complex.ofRealCLM.contDiff.comp (by fun_prop)
  have real_smooth : ContDiff ℝ ∞ realCoordinate := by
    unfold realCoordinate
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.contDiff.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.contDiff
    · exact Complex.imCLM.contDiff
  have mobius_smooth (a : E2) : ContDiffOn ℝ ∞ (boundaryMobius a) {z | z ≠ -a} := by
    have hc : ContDiff ℝ ∞ complexCoordinate := by
      unfold complexCoordinate
      apply ContDiff.add
      · exact Complex.ofRealCLM.contDiff.comp (by fun_prop)
      · apply contDiff_const.mul
        exact Complex.ofRealCLM.contDiff.comp (by fun_prop)
    have hr : ContDiff ℝ ∞ realCoordinate := by
      unfold realCoordinate
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.contDiff.comp
      apply contDiff_pi.mpr
      intro i
      fin_cases i
      · exact Complex.reCLM.contDiff
      · exact Complex.imCLM.contDiff
    intro z hz
    have hd : (-complexCoordinate a) - complexCoordinate z ≠ 0 := by
      intro h
      apply hz
      ext i
      fin_cases i
      · have he := congrArg Complex.re h
        dsimp [complexCoordinate] at he
        simp at he
        change z 0 = -a 0
        linarith
      · have he := congrArg Complex.im h
        dsimp [complexCoordinate] at he
        simp at he
        change z 1 = -a 1
        linarith
    change ContDiffWithinAt ℝ ∞
      (fun y => realCoordinate (Complex.I * ((-complexCoordinate a) + complexCoordinate y) /
        ((-complexCoordinate a) - complexCoordinate y))) _ z
    apply ContDiffAt.contDiffWithinAt
    apply hr.contDiffAt.comp z
    simp only [div_eq_mul_inv]
    exact (contDiffAt_const.mul (contDiffAt_const.add hc.contDiffAt)).mul
      ((contDiffAt_const.sub hc.contDiffAt).inv hd)
  have mobius_boundary (a z : E2) (ha : ‖a‖ = 1) (hz : ‖z‖ = 1) (hza : z ≠ -a) :
      (boundaryMobius a z) 1 = 0 := by
    have hd : (-complexCoordinate a) - complexCoordinate z ≠ 0 := by
      intro h
      apply hza
      ext i
      fin_cases i
      · have he := congrArg Complex.re h
        dsimp [complexCoordinate] at he
        simp at he
        change z 0 = -a 0
        linarith
      · have he := congrArg Complex.im h
        dsimp [complexCoordinate] at he
        simp at he
        change z 1 = -a 1
        linarith
    change (Complex.I * ((-complexCoordinate a) + complexCoordinate z) /
      ((-complexCoordinate a) - complexCoordinate z)).im = 0
    rw [Complex.div_im]
    have hnorm : Complex.normSq ((-complexCoordinate a) - complexCoordinate z) ≠ 0 :=
      (Complex.normSq_pos.mpr hd).ne'
    field_simp [hnorm]
    have ha2 := EuclideanSpace.norm_sq_eq a
    have hz2 := EuclideanSpace.norm_sq_eq z
    simp only [ha, hz, one_pow, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at ha2 hz2
    dsimp only [complexCoordinate]
    simp only [Complex.neg_re, Complex.neg_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith
  have mobius_interior (a z : E2) (ha : ‖a‖ = 1) (hz : ‖z‖ < 1) (hza : z ≠ -a) :
      0 < (boundaryMobius a z) 1 := by
    have hd : (-complexCoordinate a) - complexCoordinate z ≠ 0 := by
      intro h
      apply hza
      ext i
      fin_cases i
      · have he := congrArg Complex.re h
        dsimp [complexCoordinate] at he
        simp at he
        change z 0 = -a 0
        linarith
      · have he := congrArg Complex.im h
        dsimp [complexCoordinate] at he
        simp at he
        change z 1 = -a 1
        linarith
    change 0 < (Complex.I * ((-complexCoordinate a) + complexCoordinate z) /
      ((-complexCoordinate a) - complexCoordinate z)).im
    rw [Complex.div_im]
    have hnorm : Complex.normSq ((-complexCoordinate a) - complexCoordinate z) ≠ 0 :=
      (Complex.normSq_pos.mpr hd).ne'
    rw [← sub_div, div_pos_iff]
    left
    refine ⟨?_, Complex.normSq_pos.mpr hd⟩
    have ha2 := EuclideanSpace.norm_sq_eq a
    have hz2 := EuclideanSpace.norm_sq_eq z
    simp only [ha, one_pow, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at ha2 hz2
    dsimp only [complexCoordinate]
    simp only [Complex.neg_re, Complex.neg_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [norm_nonneg z]
  have safe_radius :
      ∃ r : ℝ, 0 < r ∧ r < Ω.localR ∧
        closedDisc r ⊆ X.inverse_neighborhood ∧
        (∀ x ∈ closedDisc r, X.inverse x ≠ -P.base) ∧
        (∀ x ∈ closedHalfDisc r, P.tau.symm x ≠ -P.base) := by
    have hzero : (0 : E2) ∈ closure Ω.domain := frontier_subset_closure Ω.base_boundary
    have hbase : X.inverse 0 = P.base := (X.inverse_agrees 0 hzero).trans P.inverse_base
    have hnorm : ‖P.base‖ = 1 := by
      have hh := P.base_on_circle
      rw [Metric.mem_sphere, dist_zero_right] at hh
      exact hh
    have hne : P.base ≠ -P.base := by
      intro hh
      have hz : P.base = 0 := by
        ext i
        have hi := congrArg (fun x : E2 => x i) hh
        change P.base i = -P.base i at hi
        change P.base i = 0
        linarith
      rw [hz, norm_zero] at hnorm
      norm_num at hnorm
    have hcontinuous : ContinuousAt X.inverse 0 :=
      (X.inverse_C1 0 (X.inverse_contains hzero)).contDiffAt
        (X.inverse_open.mem_nhds (X.inverse_contains hzero)) |>.continuousAt
    have hpole := hcontinuous.eventually_ne (show X.inverse 0 ≠ -P.base by rw [hbase]; exact hne)
    obtain ⟨e, he, hball⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem hpole (X.inverse_open.mem_nhds (X.inverse_contains hzero)))
    refine ⟨min e Ω.localR / 2, div_pos (lt_min he Ω.localR_pos) (by norm_num), ?_, ?_, ?_, ?_⟩
    · have := min_le_right e Ω.localR
      linarith [Ω.localR_pos]
    · intro x hx
      exact (hball ((Metric.closedBall_subset_ball (by linarith [min_le_left e Ω.localR, he])) hx)).2
    · intro x hx
      exact (hball ((Metric.closedBall_subset_ball (by linarith [min_le_left e Ω.localR, he])) hx)).1
    · intro x hx
      have hcl : x ∈ closure Ω.domain := Ω.contains_closed_half_disc
        ⟨Metric.closedBall_subset_closedBall (by linarith [min_le_right e Ω.localR, Ω.localR_pos]) hx.1, hx.2⟩
      rw [← X.inverse_agrees x hcl]
      exact (hball ((Metric.closedBall_subset_ball (by linarith [min_le_left e Ω.localR, he])) hx.1)).1
  obtain ⟨r, hr, hr_local, hr_neighborhood, hr_pole, hr_tau_pole⟩ := safe_radius
  have hr_inside : r < N.R / 2 := hr_local.trans Ω.localR_inside
  have map_regular : ∀ x ∈ closedDisc r,
      ContDiffAt ℝ 1 (fun y => boundaryMobius P.base (X.inverse y)) x := by
    intro x hx
    have hc := (X.inverse_C1 x (hr_neighborhood hx)).contDiffAt
      (X.inverse_open.mem_nhds (hr_neighborhood hx))
    have hm : ContDiffAt ℝ ∞ (boundaryMobius P.base) (X.inverse x) :=
      (mobius_smooth P.base (X.inverse x) (hr_pole x hx)).contDiffAt
        (isOpen_compl_singleton.mem_nhds (hr_pole x hx))
    exact (hm.of_le (by simp)).comp x hc
  have actual_inverse_agrees : ∀ x ∈ closedHalfDisc r,
      X.inverse x = P.tau.symm x := by
    intro x hx
    apply X.inverse_agrees
    apply Ω.contains_closed_half_disc
    exact ⟨Metric.closedBall_subset_closedBall hr_local.le hx.1, hx.2⟩
  have map_base : boundaryMobius P.base (X.inverse 0) = 0 := by
    rw [X.inverse_agrees 0 (frontier_subset_closure Ω.base_boundary), P.inverse_base]
    exact mobius_base P.base
  have base_norm : ‖P.base‖ = 1 := by
    have h := P.base_on_circle
    rwa [Metric.mem_sphere, dist_zero_right] at h
  have map_boundary : ∀ x ∈ closedHalfDisc r, x 1 = 0 →
      (boundaryMobius P.base (X.inverse x)) 1 = 0 := by
    intro x hx hxzero
    have hflat : x ∈ flatArc Ω.localR :=
      ⟨Metric.closedBall_subset_ball hr_local hx.1, hxzero⟩
    have hfront : x ∈ frontier Ω.domain := by
      rw [← Ω.flat_subarc] at hflat
      exact hflat.1
    have hunit : P.tau.symm x ∈ Metric.sphere (0 : E2) 1 := by
      rw [← P.inverse_boundary_image]
      exact ⟨x, hfront, rfl⟩
    rw [actual_inverse_agrees x hx]
    apply mobius_boundary P.base (P.tau.symm x) base_norm
    · rwa [Metric.mem_sphere, dist_zero_right] at hunit
    · exact hr_tau_pole x hx
  have map_interior : ∀ x ∈ closedHalfDisc r, 0 < x 1 →
      0 < (boundaryMobius P.base (X.inverse x)) 1 := by
    intro x hx hxpos
    have hhalf : x ∈ halfDisc Ω.localR :=
      ⟨Metric.closedBall_subset_ball hr_local hx.1, hxpos⟩
    have hdom : x ∈ Ω.domain := by
      rw [← Ω.inward_side] at hhalf
      exact hhalf.1
    have hunit : P.tau.symm x ∈ disc 1 := by
      rw [← P.inverse_interior_image]
      exact ⟨x, hdom, rfl⟩
    rw [actual_inverse_agrees x hx]
    apply mobius_interior P.base (P.tau.symm x) base_norm
    · change dist (P.tau.symm x) 0 < 1 at hunit
      rwa [dist_zero_right] at hunit
    · exact hr_tau_pole x hx
  have map_boundary_iff : ∀ x ∈ closedHalfDisc r,
      (boundaryMobius P.base (X.inverse x)) 1 = 0 ↔ x 1 = 0 := by
    intro x hx
    constructor
    · intro he
      by_contra hn
      have hp := map_interior x hx (lt_of_le_of_ne hx.2 (Ne.symm hn))
      rw [he] at hp
      exact (lt_irrefl _ hp)
    · exact map_boundary x hx
  have inverse_metric_algebra (A T : Mat2) (lam : ℝ) (hT : Matrix.det T ≠ 0)
      (h : T.transpose * A * T = lam • (1 : Mat2)) :
      A = lam • (T⁻¹.transpose * T⁻¹) := by
    have hu : IsUnit (Matrix.det T) := isUnit_iff_ne_zero.mpr hT
    have hut : IsUnit (Matrix.det T.transpose) := by simpa using hu
    have he := congrArg (fun M : Mat2 => T.transpose⁻¹ * M * T⁻¹) h
    rw [Matrix.mul_assoc (Matrix.transpose T) A T, Matrix.nonsing_inv_mul_cancel_left, Matrix.mul_nonsing_inv_cancel_right] at he
    · rw [← Matrix.transpose_nonsing_inv] at he
      simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] using he
    · exact hu
    · exact hut
  have actual_metric_inverse : ∀ x ∈ closedHalfDisc r,
      inverseMetric N.normalizedA x = P.lambda (P.tau.symm x) •
        ((jacobianWithin P.tau (closedDisc 1) (P.tau.symm x))⁻¹.transpose *
          (jacobianWithin P.tau (closedDisc 1) (P.tau.symm x))⁻¹) := by
    intro x hx
    have htarget : x ∈ P.tau.target := by
      rw [P.target_eq]
      apply Ω.contains_closed_half_disc
      exact ⟨Metric.closedBall_subset_closedBall hr_local.le hx.1, hx.2⟩
    have hsource : P.tau.symm x ∈ closedDisc 1 := by
      rw [← P.source_eq]
      exact P.tau.map_target htarget
    have hm := P.conformal (P.tau.symm x) hsource
    rw [P.tau.right_inv htarget] at hm
    exact inverse_metric_algebra _ _ _ (P.forward_det _ hsource) hm
  have inverse_mobius (a : E2) (ha : ‖a‖ = 1) :
      ∃ inv : E2 → E2,
        (∀ z, z ≠ -a → inv (boundaryMobius a z) = z) ∧
        (∀ w, 0 ≤ w 1 → boundaryMobius a (inv w) = w) ∧
        (∀ w, 0 ≤ w 1 → inv w ∈ closedDisc 1) ∧
        (∀ w, 0 < w 1 → inv w ∈ disc 1) ∧
        (∀ w, w 1 = 0 → inv w ∈ Metric.sphere (0 : E2) 1) ∧
        inv 0 = a ∧
        (∀ w, 0 ≤ w 1 → ContDiffAt ℝ ∞ inv w) ∧
        (∀ w, 0 ≤ w 1 → inv w ≠ -a) := by
    have cr (z : ℂ) : complexCoordinate (realCoordinate z) = z := by
      dsimp only [complexCoordinate, realCoordinate]
      change (z.re : ℂ) + Complex.I * (z.im : ℂ) = z
      rw [mul_comm]
      exact Complex.re_add_im z
    have rc (x : E2) : realCoordinate (complexCoordinate x) = x := by
      ext i
      fin_cases i <;> dsimp only [realCoordinate, complexCoordinate] <;>
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
          Complex.add_im, Complex.mul_im, one_mul, zero_add] <;> rfl
    have cnorm (x : E2) : ‖complexCoordinate x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
      dsimp only [complexCoordinate]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, one_mul, sub_zero, add_zero, zero_add, Fin.sum_univ_two]
      ring
    have an : complexCoordinate a ≠ 0 := by
      intro hh
      have hn := cnorm a
      rw [hh, norm_zero, ha] at hn
      norm_num at hn
    let inv (w : E2) : E2 := realCoordinate
      (complexCoordinate a * (Complex.I - complexCoordinate w) / (Complex.I + complexCoordinate w))
    have den (w : E2) (hw : 0 ≤ w 1) : Complex.I + complexCoordinate w ≠ 0 := by
      intro h
      have hh := congrArg Complex.im h
      dsimp only [complexCoordinate] at hh
      simp only [Complex.add_im, Complex.I_im, Complex.mul_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, add_zero, zero_add,
        Complex.zero_im] at hh
      linarith
    have inv_complex (w : E2) : complexCoordinate (inv w) =
        complexCoordinate a * (Complex.I - complexCoordinate w) / (Complex.I + complexCoordinate w) := cr _
    have inv_norm (w : E2) (hw : 0 ≤ w 1) :
        ‖inv w‖ ^ 2 = ‖Complex.I - complexCoordinate w‖ ^ 2 /
          ‖Complex.I + complexCoordinate w‖ ^ 2 := by
      rw [← cnorm, inv_complex, norm_div, norm_mul, div_pow, mul_pow, cnorm, ha, one_pow, one_mul]
    have diff_norm (w : E2) :
        ‖Complex.I + complexCoordinate w‖ ^ 2 - ‖Complex.I - complexCoordinate w‖ ^ 2 = 4 * w 1 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      dsimp only [complexCoordinate]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, sub_zero, add_zero, zero_add]
      ring
    refine ⟨inv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      have hd : (-complexCoordinate a) - complexCoordinate z ≠ 0 := by
        intro hh
        apply hz
        apply (Function.LeftInverse.injective rc)
        have hzneg : complexCoordinate (-a) = -complexCoordinate a := by
          dsimp only [complexCoordinate]
          simp only [PiLp.neg_apply, Complex.ofReal_neg]
          ring
        rw [hzneg]
        linear_combination -hh
      apply (Function.LeftInverse.injective rc)
      rw [inv_complex]
      change complexCoordinate a *
        (Complex.I - complexCoordinate (realCoordinate (Complex.I * ((-complexCoordinate a) + complexCoordinate z) / ((-complexCoordinate a) - complexCoordinate z)))) /
        (Complex.I + complexCoordinate (realCoordinate (Complex.I * ((-complexCoordinate a) + complexCoordinate z) / ((-complexCoordinate a) - complexCoordinate z)))) = _
      rw [cr]
      field_simp (disch := first | assumption | exact Complex.I_ne_zero | positivity | norm_num)
      <;> ring_nf
      <;> field_simp (disch := first | assumption | exact Complex.I_ne_zero | positivity | norm_num)
    · intro w hw
      apply (Function.LeftInverse.injective rc)
      change complexCoordinate (realCoordinate (Complex.I * ((-complexCoordinate a) + complexCoordinate (inv w)) / ((-complexCoordinate a) - complexCoordinate (inv w)))) = complexCoordinate w
      rw [cr, inv_complex]
      have hdw := den w hw
      field_simp (disch := first | assumption | exact Complex.I_ne_zero | positivity | norm_num)
      <;> ring_nf
      <;> field_simp (disch := first | assumption | exact Complex.I_ne_zero | positivity | norm_num)
    · intro w hw
      change dist (inv w) 0 ≤ 1
      rw [dist_zero_right]
      have hdpos : 0 < ‖Complex.I + complexCoordinate w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (den w hw))
      have hn : ‖inv w‖ ^ 2 ≤ 1 := by
        rw [inv_norm w hw, div_le_one hdpos]
        linarith [diff_norm w]
      nlinarith [norm_nonneg (inv w)]
    · intro w hw
      change dist (inv w) 0 < 1
      rw [dist_zero_right]
      have hdpos : 0 < ‖Complex.I + complexCoordinate w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (den w hw.le))
      have hn : ‖inv w‖ ^ 2 < 1 := by
        rw [inv_norm w hw.le, div_lt_one hdpos]
        linarith [diff_norm w]
      nlinarith [norm_nonneg (inv w)]
    · intro w hw
      rw [Metric.mem_sphere, dist_zero_right]
      have hdpos : 0 < ‖Complex.I + complexCoordinate w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (den w (by linarith)))
      have hn : ‖inv w‖ ^ 2 = 1 := by
        rw [inv_norm w (by linarith), div_eq_one_iff_eq hdpos.ne']
        linarith [diff_norm w]
      nlinarith [norm_nonneg (inv w)]
    · change realCoordinate (complexCoordinate a * (Complex.I - complexCoordinate 0) / (Complex.I + complexCoordinate 0)) = a
      have hc0 : complexCoordinate 0 = 0 := by
        dsimp only [complexCoordinate]
        change (0 : ℂ) + Complex.I * 0 = 0
        ring
      rw [hc0, sub_zero, add_zero, mul_div_cancel_right₀ _ Complex.I_ne_zero, rc]
    · intro w hw
      have hc : ContDiff ℝ ∞ complexCoordinate := by
        unfold complexCoordinate
        exact Complex.ofRealCLM.contDiff.comp (by fun_prop) |>.add
          (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (by fun_prop)))
      have hr : ContDiff ℝ ∞ realCoordinate := by
        unfold realCoordinate
        apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.contDiff.comp
        apply contDiff_pi.mpr
        intro i
        fin_cases i
        · exact Complex.reCLM.contDiff
        · exact Complex.imCLM.contDiff
      change ContDiffAt ℝ ∞ (fun y => realCoordinate (complexCoordinate a * (Complex.I - complexCoordinate y) / (Complex.I + complexCoordinate y))) w
      apply hr.contDiffAt.comp w
      simp only [div_eq_mul_inv]
      exact (contDiffAt_const.mul (contDiffAt_const.sub hc.contDiffAt)).mul
        ((contDiffAt_const.add hc.contDiffAt).inv (den w hw))
    · intro w hw hh
      have hc := congrArg complexCoordinate hh
      rw [inv_complex] at hc
      have hneg : complexCoordinate (-a) = -complexCoordinate a := by
        dsimp only [complexCoordinate]
        simp only [PiLp.neg_apply, Complex.ofReal_neg]
        ring
      rw [hneg] at hc
      have he : Complex.I * 2 = 0 := by
        have hdw := den w hw
        field_simp (disch := first | assumption | exact Complex.I_ne_zero | positivity | norm_num) at hc
        linear_combination hc
      have hn : Complex.I * 2 ≠ 0 := mul_ne_zero Complex.I_ne_zero (by norm_num)
      exact hn he
  have unique_half (r : ℝ) (hr : 0 < r) : UniqueDiffOn ℝ (closedHalfDisc r) := by
    have hlin : IsLinearMap ℝ (fun x : E2 => x 1) := by
      constructor
      · intro x y; rfl
      · intro c x; rfl
    have hc : Convex ℝ (closedHalfDisc r) := (convex_closedBall (0 : E2) r).inter (convex_halfSpace_ge hlin 0)
    apply uniqueDiffOn_convex hc
    have ho : IsOpen (halfDisc r) := Metric.isOpen_ball.inter (isOpen_lt continuous_const (show Continuous (fun x : E2 => x 1) by fun_prop))
    have hsub : halfDisc r ⊆ closedHalfDisc r := fun x hx => ⟨Metric.ball_subset_closedBall hx.1, hx.2.le⟩
    let p : E2 := (r / 2) • coordinateVector 2 1
    have hp1 : p 1 = r / 2 := by
      dsimp only [p, coordinateVector]
      simp
    have hp : ‖p‖ = r / 2 := by
      dsimp only [p, coordinateVector]
      rw [norm_smul, EuclideanSpace.norm_single]
      simp [abs_of_pos hr]
    refine ⟨p, interior_maximal hsub ho ?_⟩
    constructor
    · change dist p 0 < r
      rw [dist_zero_right, hp]
      linarith
    · rw [hp1]
      exact half_pos hr
  have jacobian_facts :
      (∀ (f g : E2 → E2) (x : E2), DifferentiableAt ℝ f x → DifferentiableAt ℝ g (f x) →
        jacobian (fun y => g (f y)) x = jacobian g (f x) * jacobian f x) ∧
      (∀ (a z : E2), ‖a‖ = 1 → z ≠ -a → ∃ c : ℂ,
        c ≠ 0 ∧ jacobian (boundaryMobius a) z = !![c.re, -c.im; c.im, c.re]) := by
    have decomp (p : E2) : p = ∑ j : Fin 2, p j • coordinateVector 2 j := by
      ext i
      fin_cases i <;> simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply]
      all_goals dsimp only [coordinateVector]
      all_goals norm_num
    constructor
    · intro f g x hf hg
      ext i j
      change (fderiv ℝ (fun y => g (f y)) x (coordinateVector 2 j)) i =
        ∑ k : Fin 2, (fderiv ℝ g (f x) (coordinateVector 2 k)) i * (fderiv ℝ f x (coordinateVector 2 j)) k
      rw [fderiv_fun_comp x hg hf]
      change (fderiv ℝ g (f x) (fderiv ℝ f x (coordinateVector 2 j))) i = _
      nth_rw 1 [decomp (fderiv ℝ f x (coordinateVector 2 j))]
      rw [map_sum]
      simp only [Fin.sum_univ_two, PiLp.add_apply, map_smul, PiLp.smul_apply, smul_eq_mul]
      ring
    · intro a z ha hz
      let e : E2 ≃L[ℝ] ℂ := ((EuclideanSpace.equiv (Fin 2) ℝ).trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).trans Complex.equivRealProdCLM.symm
      have he (x : E2) : e x = complexCoordinate x := by
        apply Complex.ext <;> dsimp only [complexCoordinate]
        all_goals simp [e]
      have hei (w : ℂ) : e.symm w = realCoordinate w := by
        ext i
        fin_cases i <;> rfl
      have hd : (-e a) - e z ≠ 0 := by
        intro h
        have hz' : e z = e (-a) := by rw [map_neg]; linear_combination -h
        exact hz (e.injective hz')
      have ha0 : e a ≠ 0 := by
        intro h
        have : a = 0 := e.injective (by rw [h, map_zero])
        rw [this, norm_zero] at ha
        norm_num at ha
      let C : ℂ := (Complex.I * 1 * ((-e a) - e z) - (Complex.I * ((-e a) + e z)) * (-1)) /
        ((-e a) - e z) ^ 2
      have hC : C ≠ 0 := by
        dsimp only [C]
        apply div_ne_zero _ (pow_ne_zero 2 hd)
        have hh : Complex.I * 1 * ((-e a) - e z) - (Complex.I * ((-e a) + e z)) * (-1) = -2 * Complex.I * e a := by ring
        rw [hh]
        exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) ha0
      have hder := (((hasDerivAt_id (e z)).const_add (-e a)).const_mul Complex.I).div
          ((hasDerivAt_id (e z)).const_sub (-e a)) hd
      have hdreal := hder.hasFDerivAt.restrictScalars ℝ
      have hf := e.symm.hasFDerivAt.comp z (hdreal.comp z e.hasFDerivAt)
      have hfun : (fun x : E2 => e.symm (Complex.I * ((-e a) + e x) / ((-e a) - e x))) = boundaryMobius a := by
        funext x
        rw [hei, he a, he x]
        rfl
      change HasFDerivAt (fun x : E2 => e.symm (Complex.I * ((-e a) + e x) / ((-e a) - e x))) _ z at hf
      rw [hfun] at hf
      refine ⟨C, hC, ?_⟩
      ext i j
      change (fderiv ℝ (boundaryMobius a) z (coordinateVector 2 j)) i = _
      rw [hf.fderiv]
      fin_cases i <;> fin_cases j
      all_goals
        change (e.symm (e (coordinateVector 2 _) * C)) _ = _
        rw [hei, he]
        dsimp only [realCoordinate, complexCoordinate, coordinateVector]
        norm_num [Complex.mul_re, Complex.mul_im]
  have holder_facts (S : Set E2) (hs : IsCompact S) (α : ℝ≥0) (hα : 0 < α) :
      (∀ (f : E2 → ℝ) (C : ℝ≥0), (∀ x ∈ S, ∀ y ∈ S,
        dist (f x) (f y) ≤ C * dist x y ^ (α : ℝ)) → HolderOnWith C α f S) ∧
      (∀ (f g : E2 → ℝ), (∃ C, HolderOnWith C α f S) →
        (∃ C, HolderOnWith C α g S) → ∃ C, HolderOnWith C α (fun x => f x + g x) S) ∧
      (∀ (f g : E2 → ℝ), (∃ C, HolderOnWith C α f S) →
        (∃ C, HolderOnWith C α g S) → ∃ C, HolderOnWith C α (fun x => f x * g x) S) := by
    have ofdist (f : E2 → ℝ) (C : ℝ≥0) (h : ∀ x ∈ S, ∀ y ∈ S,
        dist (f x) (f y) ≤ C * dist x y ^ (α : ℝ)) : HolderOnWith C α f S := by
      intro x hx y hy
      rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
        ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
      exact ENNReal.ofReal_le_ofReal (h x hx y hy)
    refine ⟨ofdist, ?_, ?_⟩
    · intro f g hf hg
      obtain ⟨Cf, hf⟩ := hf
      obtain ⟨Cg, hg⟩ := hg
      refine ⟨Cf + Cg, ofdist _ _ ?_⟩
      intro x hx y hy
      have hsum := dist_add_add_le (f x) (g x) (f y) (g y)
      have hff := hf.dist_le hx hy
      have hgg := hg.dist_le hx hy
      change dist (f x + g x) (f y + g y) ≤ ((Cf : ℝ) + Cg) * dist x y ^ (α : ℝ)
      linarith
    · intro f g hf hg
      obtain ⟨Cf, hf⟩ := hf
      obtain ⟨Cg, hg⟩ := hg
      obtain ⟨Bf, hBf⟩ := hs.exists_bound_of_continuousOn (hf.continuousOn (by positivity))
      obtain ⟨Bg, hBg⟩ := hs.exists_bound_of_continuousOn (hg.continuousOn (by positivity))
      let bf : ℝ≥0 := ⟨max Bf 0, le_max_right _ _⟩
      let bg : ℝ≥0 := ⟨max Bg 0, le_max_right _ _⟩
      refine ⟨bf * Cg + bg * Cf, ofdist _ _ ?_⟩
      intro x hx y hy
      have h1 : |f x| ≤ (bf : ℝ) := by dsimp [bf]; exact (hBf x hx).trans (le_max_left _ _)
      have h2 : |g y| ≤ (bg : ℝ) := by dsimp [bg]; exact (hBg y hy).trans (le_max_left _ _)
      have hff := hf.dist_le hx hy
      have hgg := hg.dist_le hx hy
      have he : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
      rw [Real.dist_eq, he]
      calc
        |f x * (g x - g y) + g y * (f x - f y)| ≤ |f x * (g x - g y)| + |g y * (f x - f y)| := abs_add_le _ _
        _ = |f x| * dist (g x) (g y) + |g y| * dist (f x) (f y) := by rw [abs_mul, abs_mul, Real.dist_eq, Real.dist_eq]
        _ ≤ (bf : ℝ) * ((Cg : ℝ) * dist x y ^ (α : ℝ)) + (bg : ℝ) * ((Cf : ℝ) * dist x y ^ (α : ℝ)) := add_le_add
          (mul_le_mul h1 hgg dist_nonneg bf.coe_nonneg) (mul_le_mul h2 hff dist_nonneg bg.coe_nonneg)
        _ = ↑(bf * Cg + bg * Cf) * dist x y ^ (α : ℝ) := by push_cast; ring
  obtain ⟨jac_comp, mobius_jac⟩ := jacobian_facts
  obtain ⟨invM, hMleft, hMright, hMclosed, hMopen, hMflat, hMzero, hMsmooth, hMnopole⟩ :=
    inverse_mobius P.base base_norm
  let f (x : E2) : E2 := boundaryMobius P.base (X.inverse x)
  let h (z : E2) : E2 := X.forward (invM z)
  have hzero : h 0 = 0 := by
    change X.forward (invM 0) = 0
    rw [hMzero, X.forward_agrees P.base (Metric.sphere_subset_closedBall P.base_on_circle), P.base_image]
  have hclosure (z : E2) (hz : 0 ≤ z 1) : h z ∈ closure Ω.domain := by
    change X.forward (invM z) ∈ _
    rw [X.forward_agrees _ (hMclosed z hz), ← P.target_eq]
    exact P.tau.map_source (by rw [P.source_eq]; exact hMclosed z hz)
  have hsmooth (z : E2) (hz : 0 ≤ z 1) : ContDiffAt ℝ 1 h z := by
    have hf := (X.forward_C1 _ (X.forward_contains (hMclosed z hz))).contDiffAt
      (X.forward_open.mem_nhds (X.forward_contains (hMclosed z hz)))
    exact hf.comp z ((hMsmooth z hz).of_le (by simp))
  have fpos (x : E2) (hx : x ∈ closedHalfDisc r) : 0 ≤ (f x) 1 := by
    rcases eq_or_lt_of_le hx.2 with he | hp
    · exact le_of_eq (map_boundary x hx he.symm).symm
    · exact (map_interior x hx hp).le
  have hfleft (x : E2) (hx : x ∈ closedHalfDisc r) : h (f x) = x := by
    change X.forward (invM (boundaryMobius P.base (X.inverse x))) = x
    rw [actual_inverse_agrees x hx, hMleft _ (hr_tau_pole x hx)]
    have ht : x ∈ P.tau.target := by
      rw [P.target_eq]
      exact Ω.contains_closed_half_disc ⟨Metric.closedBall_subset_closedBall hr_local.le hx.1, hx.2⟩
    rw [X.forward_agrees _ (by rw [← P.source_eq]; exact P.tau.map_target ht), P.tau.right_inv ht]
  have hfright (z : E2) (hz : 0 ≤ z 1) : f (h z) = z := by
    change boundaryMobius P.base (X.inverse (h z)) = z
    rw [X.inverse_agrees _ (hclosure z hz)]
    change boundaryMobius P.base (P.tau.symm (X.forward (invM z))) = z
    rw [X.forward_agrees _ (hMclosed z hz), P.tau.left_inv (by rw [P.source_eq]; exact hMclosed z hz)]
    exact hMright z hz
  have hsmall : ∃ t : ℝ, 0 < t ∧ ∀ z ∈ closedHalfDisc t, h z ∈ disc r := by
    have hn := (hsmooth 0 (by simp)).continuousAt.preimage_mem_nhds
      (show disc r ∈ nhds (h 0) by rw [hzero]; exact Metric.ball_mem_nhds _ hr)
    obtain ⟨e, he, hemap⟩ := Metric.mem_nhds_iff.mp hn
    refine ⟨e / 2, half_pos he, ?_⟩
    intro z hz
    exact hemap (Metric.closedBall_subset_ball (by linarith) hz.1)
  obtain ⟨t, ht, htmap⟩ := hsmall
  have hhalf (z : E2) (hz : z ∈ closedHalfDisc t) : h z ∈ closedHalfDisc r :=
    ⟨Metric.ball_subset_closedBall (htmap z hz), (Ω.closure_inside (hclosure z hz.2)).2⟩
  have hinner (z : E2) (hz : z ∈ halfDisc t) : h z ∈ halfDisc r := by
    have hcl : z ∈ closedHalfDisc t := ⟨Metric.ball_subset_closedBall hz.1, hz.2.le⟩
    have hdom : h z ∈ Ω.domain := by
      change X.forward (invM z) ∈ _
      rw [X.forward_agrees _ (hMclosed z hz.2.le), ← P.interior_image]
      exact ⟨invM z, hMopen z hz.2, rfl⟩
    have hlocal : h z ∈ disc Ω.localR := Metric.ball_subset_ball hr_local.le (htmap z hcl)
    have hm : h z ∈ halfDisc Ω.localR := by rw [← Ω.inward_side]; exact ⟨hdom, hlocal⟩
    exact ⟨htmap z hcl, hm.2⟩
  have hflat (z : E2) (hz : z ∈ flatArc t) : h z ∈ flatArc r := by
    have hcl : z ∈ closedHalfDisc t := ⟨Metric.ball_subset_closedBall hz.1, le_of_eq hz.2.symm⟩
    have hfront : h z ∈ frontier Ω.domain := by
      change X.forward (invM z) ∈ _
      rw [X.forward_agrees _ (hMclosed z hcl.2), ← P.boundary_image]
      exact ⟨invM z, hMflat z hz.2, rfl⟩
    have hlocal : h z ∈ disc Ω.localR := Metric.ball_subset_ball hr_local.le (htmap z hcl)
    have hm : h z ∈ flatArc Ω.localR := by rw [← Ω.flat_subarc]; exact ⟨hfront, hlocal⟩
    exact ⟨htmap z hcl, hm.2⟩
  let chart : PartialHomeomorph E2 E2 := {
    toFun := f
    invFun := h
    source := closedHalfDisc r
    target := f '' closedHalfDisc r
    map_source' := fun x hx => ⟨x, hx, rfl⟩
    map_target' := by
      rintro z ⟨x, hx, rfl⟩
      rw [hfleft x hx]
      exact hx
    left_inv' := hfleft
    right_inv' := by
      rintro z ⟨x, hx, rfl⟩
      rw [hfleft x hx]
    continuousOn_toFun := fun x hx => (map_regular x hx.1).continuousAt.continuousWithinAt
    continuousOn_invFun := by
      rintro z ⟨x, hx, rfl⟩
      exact (hsmooth (f x) (fpos x hx)).continuousAt.continuousWithinAt }
  have htarget_contains : closedHalfDisc t ⊆ chart.target := by
    intro z hz
    exact ⟨h z, hhalf z hz, hfright z hz.2⟩
  have hsource_compact : IsCompact (closedHalfDisc r) := by
    change IsCompact (Metric.closedBall (0 : E2) r ∩ {x : E2 | 0 ≤ x 1})
    exact (isCompact_closedBall (0 : E2) r).inter_right (isClosed_le continuous_const (show Continuous (fun x : E2 => x 1) by fun_prop))
  have hflip : ∃ C : ℝ≥0, LipschitzOnWith C f (closedHalfDisc r) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hsource_compact
    intro x hx
    obtain ⟨C, U, hU, hLip⟩ := (map_regular x hx.1).exists_lipschitzOnWith
    exact ⟨C, U, mem_nhdsWithin_of_mem_nhds hU, hLip⟩
  have hhlip : ∃ C : ℝ≥0, LipschitzOnWith C h chart.target := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (hsource_compact.image_of_continuousOn chart.continuousOn)
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨C, U, hU, hLip⟩ := (hsmooth (f x) (fpos x hx)).exists_lipschitzOnWith
    exact ⟨C, U, mem_nhdsWithin_of_mem_nhds hU, hLip⟩
  have hbilip : ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      ∀ x ∈ closedHalfDisc r, ∀ y ∈ closedHalfDisc r,
        lo * dist x y ≤ dist (chart x) (chart y) ∧ dist (chart x) (chart y) ≤ hi * dist x y := by
    obtain ⟨Cf, hfLip⟩ := hflip
    obtain ⟨Ch, hhLip⟩ := hhlip
    refine ⟨((Ch : ℝ) + 1)⁻¹, (Cf : ℝ) + 1, inv_pos.mpr (by positivity), by positivity, ?_⟩
    intro x hx y hy
    have hup := hfLip.dist_le_mul x hx y hy
    have hlo := hhLip.dist_le_mul (f x) (chart.map_source hx) (f y) (chart.map_source hy)
    rw [hfleft x hx, hfleft y hy] at hlo
    constructor
    · change ((Ch : ℝ) + 1)⁻¹ * dist x y ≤ dist (f x) (f y)
      rw [← div_eq_inv_mul, div_le_iff₀ (by positivity)]
      nlinarith [show 0 ≤ dist (f x) (f y) from dist_nonneg]
    · change dist (f x) (f y) ≤ ((Cf : ℝ) + 1) * dist x y
      nlinarith [show 0 ≤ dist x y from dist_nonneg]
  have jacobian_id_from_eqOn (u : E2 → E2) (R : ℝ) (hR : 0 < R)
      (heq : ∀ x ∈ closedHalfDisc R, u x = x) (x : E2)
      (hx : x ∈ closedHalfDisc R) (hd : DifferentiableAt ℝ u x) : jacobian u x = 1 := by
    have hu := (unique_half R hR) x hx
    have hid : HasFDerivWithinAt (id : E2 → E2) (fderiv ℝ u x) (closedHalfDisc R) x :=
      hd.hasFDerivAt.hasFDerivWithinAt.congr' (fun y hy => (heq y hy).symm) hx
    have hder : fderiv ℝ u x = ContinuousLinearMap.id ℝ E2 :=
      hu.eq hid (hasFDerivWithinAt_id x (closedHalfDisc R))
    ext i j
    change (fderiv ℝ u x (coordinateVector 2 j)) i = (1 : Mat2) i j
    rw [hder]
    fin_cases i <;> fin_cases j <;> norm_num [coordinateVector]
  have invM_det (z : E2) (hz : 0 ≤ z 1) : Matrix.det (jacobian invM z) ≠ 0 := by
    have hp := hMnopole z hz
    have hc := (mobius_smooth P.base (invM z) hp).contDiffAt
      (isOpen_compl_singleton.mem_nhds hp)
    have hi := (hMsmooth z hz).differentiableAt (by simp)
    have hd := hc.differentiableAt (by simp)
    have hh := jacobian_id_from_eqOn (fun w => boundaryMobius P.base (invM w))
      (‖z‖ + 1) (by positivity) (fun w hw => hMright w hw.2) z
      (by constructor; change dist z 0 ≤ ‖z‖ + 1; rw [dist_zero_right]; linarith; exact hz)
      (hd.comp z hi)
    rw [jac_comp invM (boundaryMobius P.base) z hi hd] at hh
    have hdet := congrArg Matrix.det hh
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    intro hn
    rw [hn, mul_zero] at hdet
    norm_num at hdet
  have fdet (x : E2) (hx : x ∈ closedHalfDisc r) : Matrix.det (jacobian f x) ≠ 0 := by
    have hp := hr_pole x hx.1
    have hm := (mobius_smooth P.base (X.inverse x) hp).contDiffAt
      (isOpen_compl_singleton.mem_nhds hp)
    have hi := (X.inverse_C1 x (hr_neighborhood hx.1)).contDiffAt
      (X.inverse_open.mem_nhds (hr_neighborhood hx.1))
    change Matrix.det (jacobian (fun y => boundaryMobius P.base (X.inverse y)) x) ≠ 0
    rw [jac_comp X.inverse (boundaryMobius P.base) x (hi.differentiableAt (by norm_num))
      (hm.differentiableAt (by simp)), Matrix.det_mul]
    apply mul_ne_zero _ (X.inverse_det x (hr_neighborhood hx.1))
    obtain ⟨c, hc, he⟩ := mobius_jac P.base (X.inverse x) base_norm hp
    rw [he, Matrix.det_fin_two]
    change c.re * c.re - (-c.im) * c.im ≠ 0
    have hp := Complex.normSq_pos.mpr hc
    rw [Complex.normSq_apply] at hp
    nlinarith
  have hdet (z : E2) (hz : 0 ≤ z 1) : Matrix.det (jacobian h z) ≠ 0 := by
    have hi := (hMsmooth z hz).differentiableAt (by simp)
    have hf := (X.forward_C1 _ (X.forward_contains (hMclosed z hz))).contDiffAt
      (X.forward_open.mem_nhds (X.forward_contains (hMclosed z hz)))
    change Matrix.det (jacobian (fun w => X.forward (invM w)) z) ≠ 0
    rw [jac_comp invM X.forward z hi (hf.differentiableAt (by norm_num)), Matrix.det_mul]
    exact mul_ne_zero (X.forward_det _ (X.forward_contains (hMclosed z hz))) (invM_det z hz)
  have jets_inverse (x : E2) (hx : x ∈ closedHalfDisc r) :
      jacobian X.inverse x = (jacobianWithin P.tau (closedDisc 1) (P.tau.symm x))⁻¹ := by
    have hcl : x ∈ closure Ω.domain := Ω.contains_closed_half_disc
      ⟨Metric.closedBall_subset_closedBall hr_local.le hx.1, hx.2⟩
    have ht : x ∈ P.tau.target := by rw [P.target_eq]; exact hcl
    have hs : P.tau.symm x ∈ closedDisc 1 := by rw [← P.source_eq]; exact P.tau.map_target ht
    have hi := (X.inverse_C1 x (hr_neighborhood hx.1)).contDiffAt
      (X.inverse_open.mem_nhds (hr_neighborhood hx.1))
    have hf := (X.forward_C1 (X.inverse x) (by rw [actual_inverse_agrees x hx]; exact X.forward_contains hs)).contDiffAt
      (X.forward_open.mem_nhds (by rw [actual_inverse_agrees x hx]; exact X.forward_contains hs))
    have heq : ∀ y ∈ closedHalfDisc r, X.forward (X.inverse y) = y := by
      intro y hy
      have hyt : y ∈ P.tau.target := by
        rw [P.target_eq]
        exact Ω.contains_closed_half_disc ⟨Metric.closedBall_subset_closedBall hr_local.le hy.1, hy.2⟩
      rw [actual_inverse_agrees y hy, X.forward_agrees _ (by rw [← P.source_eq]; exact P.tau.map_target hyt), P.tau.right_inv hyt]
    have hm := jacobian_id_from_eqOn (fun y => X.forward (X.inverse y)) r hr heq x hx
      ((hf.differentiableAt (by norm_num)).comp x (hi.differentiableAt (by norm_num)))
    rw [jac_comp X.inverse X.forward x (hi.differentiableAt (by norm_num)) (hf.differentiableAt (by norm_num)),
      actual_inverse_agrees x hx, X.forward_jet _ hs] at hm
    have he := congrArg (fun M : Mat2 => (jacobianWithin P.tau (closedDisc 1) (P.tau.symm x))⁻¹ * M) hm
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (P.forward_det _ hs)), Matrix.one_mul, Matrix.mul_one] at he
    exact he
  have fmetric (x : E2) (hx : x ∈ closedHalfDisc r) : ∃ lam : ℝ,
      0 < lam ∧ (N.normalizedA x)⁻¹ = lam • ((jacobian f x).transpose * jacobian f x) := by
    have hp := hr_pole x hx.1
    have hm := (mobius_smooth P.base (X.inverse x) hp).contDiffAt
      (isOpen_compl_singleton.mem_nhds hp)
    have hi := (X.inverse_C1 x (hr_neighborhood hx.1)).contDiffAt
      (X.inverse_open.mem_nhds (hr_neighborhood hx.1))
    obtain ⟨c, hc, hj⟩ := mobius_jac P.base (X.inverse x) base_norm hp
    have hjf : jacobian f x = !![c.re, -c.im; c.im, c.re] * jacobian X.inverse x := by
      rw [jac_comp X.inverse (boundaryMobius P.base) x (hi.differentiableAt (by norm_num)) (hm.differentiableAt (by simp)), hj]
    have hgram : (!![c.re, -c.im; c.im, c.re] : Mat2).transpose * !![c.re, -c.im; c.im, c.re] = Complex.normSq c • (1 : Mat2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.normSq_apply] <;> ring
    have hz : P.tau.symm x ∈ closedDisc 1 := by
      rw [← P.source_eq]
      apply P.tau.map_target
      rw [P.target_eq]
      exact Ω.contains_closed_half_disc ⟨Metric.closedBall_subset_closedBall hr_local.le hx.1, hx.2⟩
    refine ⟨P.lambda (P.tau.symm x) / Complex.normSq c,
      div_pos (P.lambda_pos _ hz) (Complex.normSq_pos.mpr hc), ?_⟩
    change inverseMetric N.normalizedA x = _
    rw [actual_metric_inverse x hx, ← jets_inverse x hx, hjf, Matrix.transpose_mul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (!![c.re, -c.im; c.im, c.re] : Mat2).transpose, hgram]
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_smul]
    rw [div_mul_cancel₀ _ (Complex.normSq_pos.mpr hc).ne']
  have compact_lipschitz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (S : Set E2) (hS : IsCompact S) (u : E2 → V)
      (hu : ∀ x ∈ S, ContDiffAt ℝ 1 u x) : ∃ C : ℝ≥0, LipschitzOnWith C u S := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS
    intro x hx
    obtain ⟨C, U, hU, hLip⟩ := (hu x hx).exists_lipschitzOnWith
    exact ⟨C, U, mem_nhdsWithin_of_mem_nhds hU, hLip⟩
  have half_compact (q : ℝ) : IsCompact (closedHalfDisc q) := by
    change IsCompact (Metric.closedBall (0 : E2) q ∩ {x : E2 | 0 ≤ x 1})
    exact (isCompact_closedBall (0 : E2) q).inter_right
      (isClosed_le continuous_const (show Continuous (fun x : E2 => x 1) by fun_prop))
  have smooth_jac (u : E2 → E2) (x : E2) (hu : ContDiffAt ℝ ∞ u x) (i j : Fin 2) :
      ContDiffAt ℝ 1 (fun y => jacobian u y i j) x := by
    have hd : ContDiffAt ℝ 1 (fun y => fderiv ℝ u y (coordinateVector 2 j)) x :=
      (hu.fderiv_right (by simp)).clm_apply contDiffAt_const
    exact (show ContDiff ℝ 1 (fun p : E2 => p i) by fun_prop).contDiffAt.comp x hd
  have lip_holder (q : ℝ) (hq : 0 < q) (u : E2 → ℝ)
      (hL : ∃ C, LipschitzOnWith C u (closedHalfDisc q)) :
      ∃ C, HolderOnWith C G.alpha u (closedHalfDisc q) := by
    obtain ⟨C, hC⟩ := hL
    let diam : ℝ≥0 := ⟨2 * q, by positivity⟩
    have hdiam : ∀ x ∈ closedHalfDisc q, ∀ y ∈ closedHalfDisc q, edist x y ≤ (diam : ℝ≥0∞) := by
      intro x hx y hy
      rw [edist_dist, ENNReal.ofReal_le_coe]
      change dist x y ≤ 2 * q
      have hx' : dist x 0 ≤ q := hx.1
      have hy' : dist y 0 ≤ q := hy.1
      have htri := dist_triangle_right x y (0 : E2)
      linarith
    exact ⟨_, HolderOnWith.of_le hdiam hC.holderOnWith G.alpha_lt_one.le⟩
  have inv_coeff_holder (i j : Fin 2) : ∃ C,
      HolderOnWith C G.alpha (fun x => jacobian X.inverse x i j) (closedHalfDisc r) := by
    obtain ⟨C, hC⟩ := P.inverse_holder i j
    refine ⟨C, ?_⟩
    intro x hx y hy
    have hxc := Ω.contains_closed_half_disc ⟨Metric.closedBall_subset_closedBall hr_local.le hx.1, hx.2⟩
    have hyc := Ω.contains_closed_half_disc ⟨Metric.closedBall_subset_closedBall hr_local.le hy.1, hy.2⟩
    change edist (jacobian X.inverse x i j) (jacobian X.inverse y i j) ≤ _
    rw [X.inverse_jet x hxc, X.inverse_jet y hyc]
    exact hC x hxc y hyc
  have mobius_coeff_holder (i j : Fin 2) : ∃ C,
      HolderOnWith C G.alpha (fun x => jacobian (boundaryMobius P.base) (X.inverse x) i j) (closedHalfDisc r) := by
    apply lip_holder r hr
    apply compact_lipschitz _ hsource_compact
    intro x hx
    have hp := hr_pole x hx.1
    have hm := (mobius_smooth P.base (X.inverse x) hp).contDiffAt
      (isOpen_compl_singleton.mem_nhds hp)
    have hi := (X.inverse_C1 x (hr_neighborhood hx.1)).contDiffAt
      (X.inverse_open.mem_nhds (hr_neighborhood hx.1))
    exact (smooth_jac _ _ hm i j).comp x hi
  have fjac (x : E2) (hx : x ∈ closedHalfDisc r) :
      jacobian f x = jacobian (boundaryMobius P.base) (X.inverse x) * jacobian X.inverse x := by
    have hp := hr_pole x hx.1
    have hm := (mobius_smooth P.base (X.inverse x) hp).contDiffAt
      (isOpen_compl_singleton.mem_nhds hp)
    have hi := (X.inverse_C1 x (hr_neighborhood hx.1)).contDiffAt
      (X.inverse_open.mem_nhds (hr_neighborhood hx.1))
    exact jac_comp _ _ _ (hi.differentiableAt (by norm_num)) (hm.differentiableAt (by simp))
  have fholder (i j : Fin 2) : ∃ C, HolderOnWith C G.alpha
      (fun x => jacobian f x i j) (closedHalfDisc r) := by
    obtain ⟨hofdist, hadd, hmul⟩ := holder_facts (closedHalfDisc r) hsource_compact G.alpha G.alpha_pos
    have h0 := hmul (fun x => jacobian (boundaryMobius P.base) (X.inverse x) i 0)
      (fun x => jacobian X.inverse x 0 j) (mobius_coeff_holder i 0) (inv_coeff_holder 0 j)
    have h1 := hmul (fun x => jacobian (boundaryMobius P.base) (X.inverse x) i 1)
      (fun x => jacobian X.inverse x 1 j) (mobius_coeff_holder i 1) (inv_coeff_holder 1 j)
    obtain ⟨C, hC⟩ := hadd _ _ h0 h1
    refine ⟨C, ?_⟩
    intro x hx y hy
    change edist (jacobian f x i j) (jacobian f y i j) ≤ _
    rw [fjac x hx, fjac y hy]
    simpa only [Matrix.mul_apply, Fin.sum_univ_two] using hC x hx y hy
  have invMlip : ∃ C : ℝ≥0, LipschitzOnWith C invM (closedHalfDisc t) :=
    compact_lipschitz _ (half_compact t) invM (fun x hx => (hMsmooth x hx.2).of_le (by simp))
  have forward_coeff_holder (i j : Fin 2) : ∃ C,
      HolderOnWith C G.alpha (fun z => jacobian X.forward (invM z) i j) (closedHalfDisc t) := by
    obtain ⟨C, hC⟩ := P.forward_holder i j
    obtain ⟨L, hL⟩ := invMlip
    have hcomp := hC.comp hL.holderOnWith (show MapsTo invM (closedHalfDisc t) (closedDisc 1) from fun z hz => hMclosed z hz.2)
    rw [mul_one] at hcomp
    refine ⟨C * L ^ (G.alpha : ℝ), ?_⟩
    intro x hx y hy
    change edist (jacobian X.forward (invM x) i j) (jacobian X.forward (invM y) i j) ≤ _
    rw [X.forward_jet _ (hMclosed x hx.2), X.forward_jet _ (hMclosed y hy.2)]
    exact hcomp x hx y hy
  have invM_coeff_holder (i j : Fin 2) : ∃ C,
      HolderOnWith C G.alpha (fun z => jacobian invM z i j) (closedHalfDisc t) := by
    apply lip_holder t ht
    exact compact_lipschitz _ (half_compact t) _ (fun z hz => smooth_jac invM z (hMsmooth z hz.2) i j)
  have hjac (z : E2) (hz : 0 ≤ z 1) :
      jacobian h z = jacobian X.forward (invM z) * jacobian invM z := by
    have hi := (hMsmooth z hz).differentiableAt (by simp)
    have hf := (X.forward_C1 _ (X.forward_contains (hMclosed z hz))).contDiffAt
      (X.forward_open.mem_nhds (X.forward_contains (hMclosed z hz)))
    exact jac_comp _ _ _ hi (hf.differentiableAt (by norm_num))
  have hholder (i j : Fin 2) : ∃ C, HolderOnWith C G.alpha
      (fun z => jacobian h z i j) (closedHalfDisc t) := by
    obtain ⟨hofdist, hadd, hmul⟩ := holder_facts (closedHalfDisc t) (half_compact t) G.alpha G.alpha_pos
    have h0 := hmul (fun z => jacobian X.forward (invM z) i 0)
      (fun z => jacobian invM z 0 j) (forward_coeff_holder i 0) (invM_coeff_holder 0 j)
    have h1 := hmul (fun z => jacobian X.forward (invM z) i 1)
      (fun z => jacobian invM z 1 j) (forward_coeff_holder i 1) (invM_coeff_holder 1 j)
    obtain ⟨C, hC⟩ := hadd _ _ h0 h1
    refine ⟨C, ?_⟩
    intro x hx y hy
    change edist (jacobian h x i j) (jacobian h y i j) ≤ _
    rw [hjac x hx.2, hjac y hy.2]
    simpa only [Matrix.mul_apply, Fin.sum_univ_two] using hC x hx y hy
  have chart_construction : ∃ F : BoundaryIsothermalPatch N,
      F.sourceR ≤ r ∧
      (∀ x ∈ closedHalfDisc F.sourceR, F.chart x = boundaryMobius P.base (P.tau.symm x)) ∧
      (∀ x ∈ F.chart.source, F.chart x = boundaryMobius P.base (X.inverse x)) := by
    let F : BoundaryIsothermalPatch N := {
      sourceR := r
      sourceR_pos := hr
      sourceR_inside := hr_inside
      targetR := t
      targetR_pos := ht
      chart := chart
      source_contains := Subset.rfl
      target_contains := htarget_contains
      base := map_base
      forward_C1 := fun x hx => (map_regular x hx.1).contDiffWithinAt
      inverse_C1 := by
        rintro z ⟨x, hx, rfl⟩
        exact (hsmooth (f x) (fpos x hx)).contDiffWithinAt
      forward_det := fdet
      inverse_det := by
        rintro z ⟨x, hx, rfl⟩
        exact hdet (f x) (fpos x hx)
      alpha := G.alpha
      alpha_pos := G.alpha_pos
      alpha_lt_one := G.alpha_lt_one
      forward_holder := fholder
      inverse_holder := hholder
      forward_boundary := map_boundary_iff
      forward_interior := fun x hx => map_interior x ⟨Metric.ball_subset_closedBall hx.1, hx.2.le⟩ hx.2
      inverse_half_disc := hhalf
      inverse_interior := hinner
      inverse_flat := hflat
      biLipschitz := hbilip
      conformalInverseMetric := fmetric }
    refine ⟨F, le_rfl, ?_, ?_⟩
    · intro x hx
      change boundaryMobius P.base (X.inverse x) = boundaryMobius P.base (P.tau.symm x)
      rw [actual_inverse_agrees x hx]
    · intro x hx
      rfl
  obtain ⟨F, hFr, hFactual, hFextension⟩ := chart_construction
  refine ⟨F, hFr.trans_lt hr_local, hFactual, hFextension, ?_⟩
  intro x hx
  apply hr_tau_pole x
  exact ⟨Metric.closedBall_subset_closedBall hFr (Metric.ball_subset_closedBall hx.1),
    le_of_eq hx.2.symm⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
