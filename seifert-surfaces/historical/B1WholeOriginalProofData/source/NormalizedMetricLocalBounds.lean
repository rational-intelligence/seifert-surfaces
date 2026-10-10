import IsothermalPDEData
import NormalizedMetricAlgebra

noncomputable section
set_option autoImplicit false
open Set Topology Function MeasureTheory
open scoped NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.MetricNormalization
open SeifertSurfaces.AppendixACoordinates
open IsothermalPDELower

/-- Local control of the existing normalized inverse on the supplied full ball. -/
theorem normalizedInverse_local_bounds
    (R : ℝ) (A : E2 → Mat2) (G : InverseMetricData R A)
    (M : E2 → Mat2) (y : E2) (r : ℝ) (hr : 0 < r)
    (symmetric : SymmetricOn M (Metric.ball y r))
    (elliptic : UniformEllipticOn M (Metric.ball y r))
    (holder : ∀ i j, ∃ C : ℝ≥0,
      HolderOnWith C G.alpha (fun x => M x i j) (Metric.ball y r)) :
    ∃ lam K : ℝ, ∃ HN : ℝ≥0,
      0 < lam ∧ 0 < K ∧
      (∀ x ∈ Metric.ball y r, ∀ v : E2,
        lam * ‖v‖ ^ 2 ≤ inner ℝ (matrixAction (normalizedInverse M x) v) v ∧
        ‖matrixAction (normalizedInverse M x) v‖ ≤ K * ‖v‖) ∧
      (∀ i j, HolderOnWith HN G.alpha (fun x => normalizedInverse M x i j)
        (Metric.ball y r)) := by
  set_option maxHeartbeats 2000000 in
  exact (by
    classical
    let S := Metric.ball y r
    let d (x : E2) := Matrix.det (M x)
    let s (x : E2) := Real.sqrt (d x)
    let N (x : E2) : Mat2 := s x • (M x)⁻¹
    obtain ⟨ell, C, hell, hC, hb⟩ := elliptic
    have quad (x : E2) (hx : x ∈ S) (p : E2) :
        inner ℝ p (matrixAction (M x) p) =
        M x 0 0 * p 0 ^ 2 + 2 * M x 0 1 * p 0 * p 1 + M x 1 1 * p 1 ^ 2 := by
      simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
      dsimp only [matrixAction]
      simp only [Fin.sum_univ_two, starRingEnd_apply, star_trivial]
      change (M x 0 0 * p 0 + M x 0 1 * p 1) * p 0 +
        (M x 1 0 * p 0 + M x 1 1 * p 1) * p 1 = _
      rw [← symmetric x hx 0 1]
      ring
    have bound (x : E2) (hx : x ∈ S) (u v : ℝ) :
        ell * (u ^ 2 + v ^ 2) ≤ M x 0 0 * u ^ 2 + 2 * M x 0 1 * u * v + M x 1 1 * v ^ 2 ∧
        M x 0 0 * u ^ 2 + 2 * M x 0 1 * u * v + M x 1 1 * v ^ 2 ≤ C * (u ^ 2 + v ^ 2) := by
      let p : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![u,v]
      have hn : ‖p‖ ^ 2 = u ^ 2 + v ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp only [Fin.sum_univ_two]
        rfl
      have hh := hb x hx p
      rw [quad x hx, hn] at hh
      exact hh
    have hdiag (x : E2) (hx : x ∈ S) : ell ≤ M x 0 0 ∧ M x 0 0 ≤ C ∧ ell ≤ M x 1 1 ∧ M x 1 1 ≤ C := by
      have h0 := bound x hx 1 0
      have h1 := bound x hx 0 1
      norm_num at h0 h1
      exact ⟨h0.1,h0.2,h1.1,h1.2⟩
    have hdet (x : E2) (hx : x ∈ S) : d x = M x 0 0 * M x 1 1 - (M x 0 1) ^ 2 := by
      dsimp only [d]
      rw [Matrix.det_fin_two, ← symmetric x hx 0 1]
      ring
    have hdb (x : E2) (hx : x ∈ S) : ell ^ 2 ≤ d x ∧ d x ≤ C ^ 2 := by
      obtain ⟨ha,haC,hc,hcC⟩ := hdiag x hx
      have hap : 0 < M x 0 0 := hell.trans_le ha
      have hp := (bound x hx (-M x 0 1) (M x 0 0)).1
      have he : M x 0 0 * (d x - ell * M x 0 0) ≥ 0 := by
        rw [hdet x hx]
        nlinarith [mul_nonneg hell.le (sq_nonneg (M x 0 1))]
      have hlow : ell * M x 0 0 ≤ d x := by
        have hh := (mul_nonneg_iff_of_pos_left hap).mp he
        linarith
      constructor
      · nlinarith [mul_nonneg hell.le (sub_nonneg.mpr ha)]
      · rw [hdet x hx]
        nlinarith [mul_le_mul haC hcC (hell.trans_le hc).le hC.le, sq_nonneg (M x 0 1)]
    have hpd (x : E2) (hx : x ∈ S) : 0 < d x :=
      (sq_pos_of_pos hell).trans_le (hdb x hx).1
    have hspos (x : E2) (hx : x ∈ S) : 0 < s x := Real.sqrt_pos.mpr (hpd x hx)
    have hs2 (x : E2) (hx : x ∈ S) : s x ^ 2 = d x := Real.sq_sqrt (hpd x hx).le
    have hinv (x : E2) (hx : x ∈ S) :
        N x = (s x)⁻¹ • !![M x 1 1, -M x 0 1; -M x 1 0, M x 0 0] := by
      dsimp only [N]
      rw [Matrix.inv_def, Matrix.adjugate_fin_two, smul_smul]
      congr 1
      rw [Ring.inverse_eq_inv]
      symm
      apply inv_eq_of_mul_eq_one_right
      change s x * (s x * (d x)⁻¹) = 1
      rw [← mul_assoc, ← pow_two, hs2 x hx]
      exact mul_inv_cancel₀ (hpd x hx).ne'
    have hsb (x : E2) (hx : x ∈ S) : ell ≤ s x ∧ s x ≤ C := by
      have hd := hdb x hx
      have he := hs2 x hx
      have hsp := (hspos x hx).le
      constructor <;> nlinarith
    let rotate (p : E2) : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-p 1,p 0]
    have hnorm (p : E2) : ‖rotate p‖ ^ 2 = ‖p‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      simp only [Fin.sum_univ_two]
      change (-p 1) ^ 2 + (p 0) ^ 2 = (p 0) ^ 2 + (p 1) ^ 2
      ring
    have hquad (x : E2) (hx : x ∈ S) (p : E2) :
        inner ℝ p (matrixAction (N x) p) = (s x)⁻¹ * inner ℝ (rotate p) (matrixAction (M x) (rotate p)) := by
      rw [hinv x hx]
      simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
      dsimp only [matrixAction]
      simp only [Fin.sum_univ_two, starRingEnd_apply, star_trivial]
      change (((s x)⁻¹ * M x 1 1) * p 0 + ((s x)⁻¹ * -M x 0 1) * p 1) * p 0 +
        (((s x)⁻¹ * -M x 1 0) * p 0 + ((s x)⁻¹ * M x 0 0) * p 1) * p 1 =
        (s x)⁻¹ * ((M x 0 0 * -p 1 + M x 0 1 * p 0) * -p 1 +
          (M x 1 0 * -p 1 + M x 1 1 * p 0) * p 0)
      rw [← symmetric x hx 0 1]
      ring
    have hcoercive (x : E2) (hx : x ∈ S) (p : E2) :
        ell / C * ‖p‖ ^ 2 ≤ inner ℝ (matrixAction (N x) p) p := by
      rw [real_inner_comm, hquad x hx]
      have h := (hb x hx (rotate p)).1
      rw [hnorm] at h
      have hi : C⁻¹ ≤ (s x)⁻¹ := (inv_le_inv₀ hC (hspos x hx)).mpr (hsb x hx).2
      calc
        ell / C * ‖p‖ ^ 2 = C⁻¹ * (ell * ‖p‖ ^ 2) := by ring
        _ ≤ (s x)⁻¹ * (ell * ‖p‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hi (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (hspos x hx).le)
    have bounded_holder (f : E2 → ℝ) (K : ℝ≥0) (hf : HolderOnWith K G.alpha f S) :
        ∃ B : ℝ, ∀ x ∈ S, ‖f x‖ ≤ B := by
      refine ⟨‖f y‖ + (K : ℝ) * r ^ (G.alpha : ℝ), ?_⟩
      intro x hx
      have hy : y ∈ S := Metric.mem_ball_self hr
      have hdist : dist x y ≤ r := le_of_lt hx
      have hh := hf.dist_le hx hy
      calc
        ‖f x‖ ≤ dist (f x) (f y) + ‖f y‖ := by
          rw [dist_eq_norm]
          calc
            ‖f x‖ = ‖(f x - f y) + f y‖ := by congr 1; ring
            _ ≤ _ := norm_add_le _ _
        _ ≤ (K : ℝ) * r ^ (G.alpha : ℝ) + ‖f y‖ := add_le_add
          (hh.trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow dist_nonneg hdist G.alpha.coe_nonneg) K.coe_nonneg)) le_rfl
        _ = _ := add_comm _ _
    have ofdist (f : E2 → ℝ) (K : ℝ≥0) (h : ∀ x ∈ S, ∀ z ∈ S,
        dist (f x) (f z) ≤ K * dist x z ^ (G.alpha : ℝ)) : HolderOnWith K G.alpha f S := by
      intro x hx z hz
      rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg G.alpha.coe_nonneg,
        ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
      exact ENNReal.ofReal_le_ofReal (h x hx z hz)
    have hneg (f : E2 → ℝ) (hf : ∃ K, HolderOnWith K G.alpha f S) :
        ∃ K, HolderOnWith K G.alpha (fun x => -f x) S := by
      obtain ⟨K,hK⟩ := hf
      refine ⟨K,ofdist _ K ?_⟩
      intro x hx z hz
      rw [dist_neg_neg]
      exact hK.dist_le hx hz
    have hadd (f g : E2 → ℝ) (hf : ∃ K, HolderOnWith K G.alpha f S)
        (hg : ∃ K, HolderOnWith K G.alpha g S) :
        ∃ K, HolderOnWith K G.alpha (fun x => f x + g x) S := by
      obtain ⟨K,hK⟩ := hf
      obtain ⟨L,hL⟩ := hg
      refine ⟨K+L,ofdist _ _ ?_⟩
      intro x hx z hz
      have h1 := hK.dist_le hx hz
      have h2 := hL.dist_le hx hz
      have h3 := dist_add_add_le (f x) (g x) (f z) (g z)
      change _ ≤ ((K : ℝ)+(L : ℝ))*_
      linarith
    have hmul (f g : E2 → ℝ) (hf : ∃ K, HolderOnWith K G.alpha f S)
        (hg : ∃ K, HolderOnWith K G.alpha g S) :
        ∃ K, HolderOnWith K G.alpha (fun x => f x * g x) S := by
      obtain ⟨K,hK⟩ := hf
      obtain ⟨L,hL⟩ := hg
      obtain ⟨Bf,hBf⟩ := bounded_holder f K hK
      obtain ⟨Bg,hBg⟩ := bounded_holder g L hL
      let bf : ℝ≥0 := ⟨max Bf 0,le_max_right _ _⟩
      let bg : ℝ≥0 := ⟨max Bg 0,le_max_right _ _⟩
      refine ⟨bf*L+bg*K,ofdist _ _ ?_⟩
      intro x hx z hz
      have h1 : |f x| ≤ (bf : ℝ) := (hBf x hx).trans (le_max_left _ _)
      have h2 : |g z| ≤ (bg : ℝ) := (hBg z hz).trans (le_max_left _ _)
      have he : f x*g x-f z*g z = f x*(g x-g z)+g z*(f x-f z) := by ring
      rw [Real.dist_eq,he]
      calc
        _ ≤ |f x*(g x-g z)| + |g z*(f x-f z)| := abs_add_le _ _
        _ = |f x| * dist (g x) (g z)+|g z| * dist (f x) (f z) := by rw [abs_mul,abs_mul,Real.dist_eq,Real.dist_eq]
        _ ≤ (bf : ℝ)*((L : ℝ)*dist x z^(G.alpha : ℝ))+(bg : ℝ)*((K : ℝ)*dist x z^(G.alpha : ℝ)) :=
          add_le_add (mul_le_mul h1 (hL.dist_le hx hz) dist_nonneg bf.coe_nonneg)
            (mul_le_mul h2 (hK.dist_le hx hz) dist_nonneg bg.coe_nonneg)
        _ = ↑(bf*L+bg*K)*dist x z^(G.alpha : ℝ) := by push_cast; ring
    have hentry (i j : Fin 2) : ∃ K, HolderOnWith K G.alpha (fun x => M x i j) S := by
      obtain ⟨K,hK⟩ := holder i j
      exact ⟨K,hK⟩
    have hdh : ∃ K, HolderOnWith K G.alpha d S := by
      obtain ⟨K,hK⟩ := hadd _ _ (hmul _ _ (hentry 0 0) (hentry 1 1))
        (hneg _ (hmul _ _ (hentry 0 1) (hentry 0 1)))
      refine ⟨K,ofdist d K ?_⟩
      intro x hx z hz
      simpa only [hdet x hx, hdet z hz,sub_eq_add_neg,pow_two] using hK.dist_le hx hz
    have hscalar : ContDiffOn ℝ 1 (fun t : ℝ => (Real.sqrt t)⁻¹) (Icc (ell^2) (C^2)) := by
      apply ContDiffOn.inv
      · exact contDiffOn_id.sqrt (fun t ht => (lt_of_lt_of_le (sq_pos_of_pos hell) ht.1).ne')
      · intro t ht
        exact (Real.sqrt_pos.mpr (lt_of_lt_of_le (sq_pos_of_pos hell) ht.1)).ne'
    obtain ⟨L,hL⟩ := hscalar.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
    obtain ⟨K,hK⟩ := hdh
    have hsh : ∃ K, HolderOnWith K G.alpha (fun x => (s x)⁻¹) S := by
      refine ⟨L*K,?_⟩
      have hh := hL.holderOnWith.comp hK (fun x hx => hdb x hx)
      simpa only [NNReal.coe_one,NNReal.rpow_one,one_mul,Function.comp_def,s] using hh
    have hNh : ∀ i j, ∃ K, HolderOnWith K G.alpha (fun x => N x i j) S := by
      intro i j
      have h00 := hmul _ _ hsh (hentry 1 1)
      have h01 := hmul _ _ hsh (hneg _ (hentry 0 1))
      have h10 := hmul _ _ hsh (hneg _ (hentry 1 0))
      have h11 := hmul _ _ hsh (hentry 0 0)
      fin_cases i <;> fin_cases j
      all_goals
        first
        | obtain ⟨K,hK⟩ := h00
          refine ⟨K,ofdist _ K ?_⟩
          intro x hx z hz
          change dist (N x 0 0) (N z 0 0) ≤ _
          rw [hinv x hx,hinv z hz]
          exact hK.dist_le hx hz
        | obtain ⟨K,hK⟩ := h01
          refine ⟨K,ofdist _ K ?_⟩
          intro x hx z hz
          change dist (N x 0 1) (N z 0 1) ≤ _
          rw [hinv x hx,hinv z hz]
          exact hK.dist_le hx hz
        | obtain ⟨K,hK⟩ := h10
          refine ⟨K,ofdist _ K ?_⟩
          intro x hx z hz
          change dist (N x 1 0) (N z 1 0) ≤ _
          rw [hinv x hx,hinv z hz]
          exact hK.dist_le hx hz
        | obtain ⟨K,hK⟩ := h11
          refine ⟨K,ofdist _ K ?_⟩
          intro x hx z hz
          change dist (N x 1 1) (N z 1 1) ≤ _
          rw [hinv x hx,hinv z hz]
          exact hK.dist_le hx hz
    choose HH hHH using hNh
    let HN : ℝ≥0 := ∑ i : Fin 2, ∑ j : Fin 2, HH i j
    have hHN (i j : Fin 2) : HolderOnWith HN G.alpha (fun x => N x i j) S := by
      have hh : HH i j ≤ HN :=
        (Finset.single_le_sum (f := fun k : Fin 2 => HH i k)
          (fun k _ => by positivity) (Finset.mem_univ j)).trans
          (Finset.single_le_sum (f := fun k : Fin 2 => ∑ l : Fin 2, HH k l)
            (fun k _ => by positivity) (Finset.mem_univ i))
      intro x hx z hz
      exact ((hHH i j).edist_le hx hz).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hh) (by positivity))
    have hNb (i j : Fin 2) : ∃ B : ℝ, ∀ x ∈ S, ‖N x i j‖ ≤ B :=
      bounded_holder _ HN (hHN i j)
    choose BB hBB using hNb
    let B : ℝ := ∑ i : Fin 2, ∑ j : Fin 2, max (BB i j) 0
    have hB : 0 ≤ B := by dsimp only [B]; positivity
    have hBe (x : E2) (hx : x ∈ S) (i j : Fin 2) : ‖N x i j‖ ≤ B := by
      exact ((hBB i j x hx).trans (le_max_left _ _)).trans
        ((Finset.single_le_sum (fun k _ => le_max_right (BB i k) 0) (Finset.mem_univ j)).trans
          (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => le_max_right (BB k l) 0))
            (Finset.mem_univ i)))
    have hoperator (x : E2) (hx : x ∈ S) (p : E2) :
        ‖matrixAction (N x) p‖ ≤ (4 * B + 1) * ‖p‖ := by
      let q := matrixAction (N x) p
      have he (i : Fin 2) : q i = N x i 0 * p 0 + N x i 1 * p 1 := by
        dsimp only [q, matrixAction]
        simp only [Fin.sum_univ_two]
        rfl
      have hc (i : Fin 2) : |q i| ≤ 2 * B * ‖p‖ := by
        rw [he]
        calc
          |N x i 0 * p 0 + N x i 1 * p 1| ≤
              |N x i 0 * p 0| + |N x i 1 * p 1| := abs_add_le _ _
          _ = |N x i 0| * |p 0| + |N x i 1| * |p 1| := by rw [abs_mul, abs_mul]
          _ ≤ B * ‖p‖ + B * ‖p‖ := add_le_add
            (mul_le_mul (hBe x hx i 0) (PiLp.norm_apply_le (p := 2) p 0) (abs_nonneg _) hB)
            (mul_le_mul (hBe x hx i 1) (PiLp.norm_apply_le (p := 2) p 1) (abs_nonneg _) hB)
          _ = 2 * B * ‖p‖ := by ring
      have hq : ‖q‖ ^ 2 = (q 0) ^ 2 + (q 1) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp only [Fin.sum_univ_two]
      have h0 := hc 0
      have h1 := hc 1
      have h00 : (q 0) ^ 2 ≤ (2 * B * ‖p‖) ^ 2 := by
        nlinarith [sq_abs (q 0), abs_nonneg (q 0), mul_nonneg hB (norm_nonneg p)]
      have h11 : (q 1) ^ 2 ≤ (2 * B * ‖p‖) ^ 2 := by
        nlinarith [sq_abs (q 1), abs_nonneg (q 1), mul_nonneg hB (norm_nonneg p)]
      have hbq : ‖q‖ ≤ 4 * B * ‖p‖ := by
        nlinarith [sq_nonneg (B * ‖p‖), norm_nonneg q, mul_nonneg hB (norm_nonneg p)]
      exact hbq.trans (by nlinarith [norm_nonneg p])
    refine ⟨ell / C, 4 * B + 1, HN, div_pos hell hC, by positivity, ?_, ?_⟩
    · intro x hx v
      exact ⟨hcoercive x hx v, hoperator x hx v⟩
    · intro i j
      exact hHN i j
  )

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.MetricNormalization
