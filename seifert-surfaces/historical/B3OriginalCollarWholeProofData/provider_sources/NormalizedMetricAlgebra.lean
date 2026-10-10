import B1MetricVariationalInterfaces

noncomputable section
open Set Topology Function MeasureTheory
open scoped NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.MetricNormalization
open SeifertSurfaces.AppendixACoordinates

theorem positive_det_of_symmetric_uniform_elliptic
    (M : E2 → Mat2)
    (symmetric : SymmetricOn M univ)
    (elliptic : UniformEllipticOn M univ) :
    ∀ y : E2, 0 < Matrix.det (M y) := by { intro y; obtain ⟨ell, C, hell, hC, hbound⟩ := elliptic; apply Matrix.PosDef.det_pos; apply Matrix.PosDef.of_dotProduct_mulVec_pos; · { ext i j; simpa only [Matrix.conjTranspose_apply, star_trivial] using (symmetric y (mem_univ y) j i) }; · { intro x hx; let p : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm x; have hp : p ≠ 0 := by { intro h; apply hx; have := congrArg (EuclideanSpace.equiv (Fin 2) ℝ) h; simpa only [p, ContinuousLinearEquiv.apply_symm_apply, map_zero] using this }; have hpos : 0 < inner ℝ p (matrixAction (M y) p) := (mul_pos hell (sq_pos_of_pos (norm_pos_iff.mpr hp))).trans_le (hbound y (mem_univ y) p).1; change 0 < ∑ i : Fin 2, (∑ j : Fin 2, M y i j * x j) * x i at hpos; simpa only [Matrix.mulVec, dotProduct, star_trivial, mul_comm] using hpos } }

theorem normalized_inverse_metric
    (R : ℝ) (A : E2 → Mat2) (G : InverseMetricData R A)
    (M : E2 → Mat2)
    (symmetric : SymmetricOn M univ)
    (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (positive_det : ∀ y : E2, 0 < Matrix.det (M y)) :
    let N : E2 → Mat2 := fun y => Real.sqrt (Matrix.det (M y)) • (M y)⁻¹
    (∀ y : E2, Matrix.det (N y) = 1) ∧
    SymmetricOn N univ ∧
    UniformEllipticOn N univ ∧
    (∀ y : E2, ∀ p : E2, p ≠ 0 → 0 < inner ℝ p (matrixAction (N y) p)) ∧
    (∀ y : E2, ∀ r : ℝ, 0 < r → ∀ i j, ∃ C : ℝ≥0,
      HolderOnWith C G.alpha (fun x => N x i j) (Metric.closedBall y r)) := by
  classical
  dsimp only
  let d (x : E2) := Matrix.det (M x)
  let s (x : E2) := Real.sqrt (d x)
  let N (x : E2) : Mat2 := s x • (M x)⁻¹
  have hspos (x : E2) : 0 < s x := Real.sqrt_pos.mpr (positive_det x)
  have hs2 (x : E2) : s x ^ 2 = d x := Real.sq_sqrt (positive_det x).le
  have hinv (x : E2) : N x = (s x)⁻¹ • !![M x 1 1, -M x 0 1; -M x 1 0, M x 0 0] := by
    dsimp only [N]
    rw [Matrix.inv_def, Matrix.adjugate_fin_two, smul_smul]
    congr 1
    rw [Ring.inverse_eq_inv]
    symm
    apply inv_eq_of_mul_eq_one_right
    change s x * (s x * (d x)⁻¹) = 1
    rw [← mul_assoc, ← pow_two, hs2]
    exact mul_inv_cancel₀ (positive_det x).ne'
  obtain ⟨ell, C, hell, hC, hb⟩ := elliptic
  have quad (x : E2) (p : E2) :
      inner ℝ p (matrixAction (M x) p) =
      M x 0 0 * p 0 ^ 2 + 2 * M x 0 1 * p 0 * p 1 + M x 1 1 * p 1 ^ 2 := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
    dsimp only [matrixAction]
    simp only [Fin.sum_univ_two, starRingEnd_apply, star_trivial]
    change (M x 0 0 * p 0 + M x 0 1 * p 1) * p 0 +
      (M x 1 0 * p 0 + M x 1 1 * p 1) * p 1 = _
    rw [← symmetric x (mem_univ x) 0 1]
    ring
  have bound (x : E2) (u v : ℝ) :
      ell * (u ^ 2 + v ^ 2) ≤ M x 0 0 * u ^ 2 + 2 * M x 0 1 * u * v + M x 1 1 * v ^ 2 ∧
      M x 0 0 * u ^ 2 + 2 * M x 0 1 * u * v + M x 1 1 * v ^ 2 ≤ C * (u ^ 2 + v ^ 2) := by
    let p : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![u,v]
    have hn : ‖p‖ ^ 2 = u ^ 2 + v ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [Fin.sum_univ_two]
      rfl
    have hh := hb x (mem_univ x) p
    rw [quad, hn] at hh
    exact hh
  have hdiag (x : E2) : ell ≤ M x 0 0 ∧ M x 0 0 ≤ C ∧ ell ≤ M x 1 1 ∧ M x 1 1 ≤ C := by
    have h0 := bound x 1 0
    have h1 := bound x 0 1
    norm_num at h0 h1
    exact ⟨h0.1,h0.2,h1.1,h1.2⟩
  have hdet (x : E2) : d x = M x 0 0 * M x 1 1 - (M x 0 1) ^ 2 := by
    dsimp only [d]
    rw [Matrix.det_fin_two, ← symmetric x (mem_univ x) 0 1]
    ring
  have hdb (x : E2) : ell ^ 2 ≤ d x ∧ d x ≤ C ^ 2 := by
    obtain ⟨ha,haC,hc,hcC⟩ := hdiag x
    have hap : 0 < M x 0 0 := hell.trans_le ha
    have hp := (bound x (-M x 0 1) (M x 0 0)).1
    have he : M x 0 0 * (d x - ell * M x 0 0) ≥ 0 := by
      rw [hdet]
      nlinarith [mul_nonneg hell.le (sq_nonneg (M x 0 1))]
    have hlow : ell * M x 0 0 ≤ d x := by
      have hh := (mul_nonneg_iff_of_pos_left hap).mp he
      linarith
    constructor
    · nlinarith [mul_nonneg hell.le (sub_nonneg.mpr ha)]
    · rw [hdet]
      nlinarith [mul_le_mul haC hcC (hell.trans_le hc).le hC.le, sq_nonneg (M x 0 1)]
  have hsb (x : E2) : ell ≤ s x ∧ s x ≤ C := by
    have hd := hdb x
    have he := hs2 x
    have hsp := (hspos x).le
    constructor <;> nlinarith
  let rotate (p : E2) : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-p 1,p 0]
  have hnorm (p : E2) : ‖rotate p‖ ^ 2 = ‖p‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
    change (-p 1) ^ 2 + (p 0) ^ 2 = (p 0) ^ 2 + (p 1) ^ 2
    ring
  have hquad (x : E2) (p : E2) :
      inner ℝ p (matrixAction (N x) p) = (s x)⁻¹ * inner ℝ (rotate p) (matrixAction (M x) (rotate p)) := by
    rw [hinv]
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
    dsimp only [matrixAction]
    simp only [Fin.sum_univ_two, starRingEnd_apply, star_trivial]
    change (((s x)⁻¹ * M x 1 1) * p 0 + ((s x)⁻¹ * -M x 0 1) * p 1) * p 0 +
      (((s x)⁻¹ * -M x 1 0) * p 0 + ((s x)⁻¹ * M x 0 0) * p 1) * p 1 =
      (s x)⁻¹ * ((M x 0 0 * -p 1 + M x 0 1 * p 0) * -p 1 +
        (M x 1 0 * -p 1 + M x 1 1 * p 0) * p 0)
    rw [← symmetric x (mem_univ x) 0 1]
    ring
  have hNell : UniformEllipticOn N univ := by
    refine ⟨ell / C,C / ell,div_pos hell hC,div_pos hC hell,?_⟩
    intro x hx p
    have h := hb x (mem_univ x) (rotate p)
    rw [hnorm] at h
    rw [hquad]
    have hi : C⁻¹ ≤ (s x)⁻¹ ∧ (s x)⁻¹ ≤ ell⁻¹ :=
      ⟨(inv_le_inv₀ hC (hspos x)).mpr (hsb x).2, (inv_le_inv₀ (hspos x) hell).mpr (hsb x).1⟩
    constructor
    · calc
        ell / C * ‖p‖ ^ 2 = C⁻¹ * (ell * ‖p‖ ^ 2) := by ring
        _ ≤ (s x)⁻¹ * (ell * ‖p‖ ^ 2) := mul_le_mul_of_nonneg_right hi.1 (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left h.1 (inv_nonneg.mpr (hspos x).le)
    · calc
        _ ≤ (s x)⁻¹ * (C * ‖p‖ ^ 2) := mul_le_mul_of_nonneg_left h.2 (inv_nonneg.mpr (hspos x).le)
        _ ≤ ell⁻¹ * (C * ‖p‖ ^ 2) := mul_le_mul_of_nonneg_right hi.2 (by positivity)
        _ = C / ell * ‖p‖ ^ 2 := by ring
  refine ⟨?_,?_,hNell,?_,?_⟩
  · intro x
    change Matrix.det (s x • (M x)⁻¹) = 1
    rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    change s x ^ 2 * (d x)⁻¹ = 1
    rw [hs2,mul_inv_cancel₀ (positive_det x).ne']
  · intro x hx i j
    change N x i j = N x j i
    rw [hinv]
    have h01 := symmetric x (mem_univ x) 0 1
    fin_cases i <;> fin_cases j <;> simp [h01]
  · intro x p hp
    obtain ⟨l,c,hl,hc,h⟩ := hNell
    exact (mul_pos hl (sq_pos_of_pos (norm_pos_iff.mpr hp))).trans_le (h x (mem_univ x) p).1
  · intro y r hr
    let S := Metric.closedBall y r
    have hcompact : IsCompact S := isCompact_closedBall y r
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
      obtain ⟨Bf,hBf⟩ := hcompact.exists_bound_of_continuousOn (hK.continuousOn G.alpha_pos)
      obtain ⟨Bg,hBg⟩ := hcompact.exists_bound_of_continuousOn (hL.continuousOn G.alpha_pos)
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
      exact ⟨K,hK.holderOnWith S⟩
    have hdh : ∃ K, HolderOnWith K G.alpha d S := by
      obtain ⟨K,hK⟩ := hadd _ _ (hmul _ _ (hentry 0 0) (hentry 1 1))
        (hneg _ (hmul _ _ (hentry 0 1) (hentry 0 1)))
      refine ⟨K,ofdist d K ?_⟩
      intro x hx z hz
      simpa only [hdet,sub_eq_add_neg,pow_two] using hK.dist_le hx hz
    have hscalar : ContDiffOn ℝ 1 (fun t : ℝ => (Real.sqrt t)⁻¹) (Icc (ell^2) (C^2)) := by
      apply ContDiffOn.inv
      · exact contDiffOn_id.sqrt (fun t ht => (lt_of_lt_of_le (sq_pos_of_pos hell) ht.1).ne')
      · intro t ht
        exact (Real.sqrt_pos.mpr (lt_of_lt_of_le (sq_pos_of_pos hell) ht.1)).ne'
    obtain ⟨L,hL⟩ := hscalar.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
    obtain ⟨K,hK⟩ := hdh
    have hsh : ∃ K, HolderOnWith K G.alpha (fun x => (s x)⁻¹) S := by
      refine ⟨L*K,?_⟩
      have hh := hL.holderOnWith.comp hK (fun x hx => hdb x)
      simpa only [NNReal.coe_one,NNReal.rpow_one,one_mul,Function.comp_def,s] using hh
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
        rw [hinv,hinv]
        exact hK.dist_le hx hz
      | obtain ⟨K,hK⟩ := h01
        refine ⟨K,ofdist _ K ?_⟩
        intro x hx z hz
        change dist (N x 0 1) (N z 0 1) ≤ _
        rw [hinv,hinv]
        exact hK.dist_le hx hz
      | obtain ⟨K,hK⟩ := h10
        refine ⟨K,ofdist _ K ?_⟩
        intro x hx z hz
        change dist (N x 1 0) (N z 1 0) ≤ _
        rw [hinv,hinv]
        exact hK.dist_le hx hz
      | obtain ⟨K,hK⟩ := h11
        refine ⟨K,ofdist _ K ?_⟩
        intro x hx z hz
        change dist (N x 1 1) (N z 1 1) ≤ _
        rw [hinv,hinv]
        exact hK.dist_le hx hz

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.MetricNormalization
