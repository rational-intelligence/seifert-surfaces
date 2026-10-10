import HopfAdapters.ClosedBallGeometry

noncomputable section
open Set Metric Function
open scoped Topology BigOperators ContDiff
open scoped Matrix

namespace SeifertSurfaces.AppendixACoordinates.HopfAdapters

theorem extended_gram_continuous (V : Set E3) (g : CoordinateMetric V)
    (K : Set E2) (Φ : E2 → E3) (F : E2 → E2 →L[ℝ] E3)
    (hΦ : ContinuousOn Φ K) (hF : ContinuousOn F K) (hgraph : MapsTo Φ K V) :
    ContinuousOn (extendedGram g.tensor Φ F) K := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  unfold extendedGram coordinateInner
  apply continuousOn_finsetSum
  intro a ha
  apply continuousOn_finsetSum
  intro b hb
  exact (((g.smooth a b).continuousOn.comp hΦ hgraph).mul
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) a).comp_continuousOn (hF.clm_apply continuousOn_const))).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) b).comp_continuousOn (hF.clm_apply continuousOn_const))

theorem extended_gram_posDef (V : Set E3) (g : CoordinateMetric V)
    (K : Set E2) (Φ : E2 → E3) (F : E2 → E2 →L[ℝ] E3)
    (hgraph : MapsTo Φ K V) (hF : ∀ x ∈ K, Injective (F x)) :
    ∀ x ∈ K, (extendedGram g.tensor Φ F x).PosDef := by
  intro x hx
  have hsym : ∀ u v : E3, coordinateInner g.tensor (Φ x) u v =
      coordinateInner g.tensor (Φ x) v u := by
    intro u v
    unfold coordinateInner
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [g.symmetric (Φ x) (hgraph hx) b a]
    ring
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simpa only [Matrix.conjTranspose_apply, star_trivial, extendedGram] using
      hsym (F x (coordinateVector 2 j)) (F x (coordinateVector 2 i))
  · intro ξ hξ
    let v : E2 := ∑ i : Fin 2, ξ i • coordinateVector 2 i
    have hv : v ≠ 0 := by
      intro h
      apply hξ
      funext i
      have hi := congrArg (fun z : E2 => z i) h
      fin_cases i <;>
        simpa [v, coordinateVector, EuclideanSpace.single, PiLp.single_apply] using hi
    have hFv : F x v ≠ 0 := by
      intro h
      exact hv ((hF x hx) (by simpa using h))
    have hpositive := g.positive (Φ x) (hgraph hx) (F x v) hFv
    have hquadratic : coordinateInner g.tensor (Φ x) (F x v) (F x v) =
        star ξ ⬝ᵥ (extendedGram g.tensor Φ F x *ᵥ ξ) := by
      simp [v, map_add, map_smul, coordinateInner, extendedGram,
        dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
        Fin.sum_univ_succ, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rwa [hquadratic] at hpositive

theorem inverse_gram_continuous_posDef (V : Set E3) (g : CoordinateMetric V)
    (K : Set E2) (Φ : E2 → E3) (F : E2 → E2 →L[ℝ] E3)
    (hΦ : ContinuousOn Φ K) (hF : ContinuousOn F K) (hgraph : MapsTo Φ K V)
    (hinj : ∀ x ∈ K, Injective (F x)) :
    ContinuousOn (inverseGram g.tensor Φ F) K ∧
      ∀ x ∈ K, (inverseGram g.tensor Φ F x).PosDef := by
  have hG := extended_gram_continuous V g K Φ F hΦ hF hgraph
  have hpos := extended_gram_posDef V g K Φ F hgraph hinj
  constructor
  · intro x hx
    exact (continuousAt_matrix_inv (extendedGram g.tensor Φ F x)
      (by rw [Ring.inverse_eq_inv']; exact
        continuousAt_inv₀ (ne_of_gt (hpos x hx).det_pos))).comp_continuousWithinAt (hG x hx)
  · intro x hx
    exact (hpos x hx).inv

theorem inverse_gram_eq_induced (U : Set E2) (g : MetricTensor) (p : E3)
    (L : E2 →L[ℝ] E3) (normal : E3) (w : E2 → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w U) (c : E2) (R : ℝ)
    (hK : closedBall c R ⊆ U) (x : E2) (hx : x ∈ ball c R) :
    inverseGram g (graphMap p L normal w)
      (boundaryGraphLinearization (closedBall c R) L normal w) x =
        (inducedMetric g (graphMap p L normal w) x)⁻¹ := by
  unfold inverseGram
  congr 1
  ext i j
  unfold extendedGram inducedMetric graphTangent
  rw [boundary_graph_linearization_eq_fderiv U p L normal w hwC1 c R hK x hx]

theorem inverse_gram_symmetric (V : Set E3) (g : CoordinateMetric V)
    (K : Set E2) (Φ : E2 → E3) (F : E2 → E2 →L[ℝ] E3)
    (hgraph : MapsTo Φ K V) (hinj : ∀ x ∈ K, Injective (F x)) :
    ∀ x ∈ K, ∀ i j, inverseGram g.tensor Φ F x i j =
      inverseGram g.tensor Φ F x j i := by
  intro x hx i j
  have h := ((extended_gram_posDef V g K Φ F hgraph hinj x hx).inv).isHermitian
  simpa only [Matrix.conjTranspose_apply, star_trivial, inverseGram] using (h.apply j i)

theorem compact_uniform_coefficient_bounds (K : Set E2) (hK : IsCompact K)
    (a : E2 → Matrix (Fin 2) (Fin 2) ℝ) (b : E2 → E2)
    (ha : ContinuousOn a K) (hb : ContinuousOn b K)
    (hpositive : ∀ x ∈ K, (a x).PosDef) :
    Nonempty (CoefficientBounds K a b) := by
  let q : E2 → E2 → ℝ := fun x v => ∑ i, ∑ j, a x i j * v i * v j
  have hq : ContinuousOn (fun z : E2 × E2 => q z.1 z.2)
      (K ×ˢ sphere (0 : E2) 1) := by
    apply continuousOn_finsetSum
    intro i hi
    apply continuousOn_finsetSum
    intro j hj
    have hai : ContinuousOn (fun z : E2 × E2 => a z.1 i j)
        (K ×ˢ sphere (0 : E2) 1) :=
      (continuousOn_pi.mp (continuousOn_pi.mp ha i) j).comp continuousOn_fst
        (fun z hz => hz.1)
    exact (hai.mul ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i).comp continuous_snd).continuousOn).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) j).comp continuous_snd).continuousOn
  have hqpos : ∀ z ∈ K ×ˢ sphere (0 : E2) 1, 0 < q z.1 z.2 := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hvne : v ≠ 0 := by
      intro heq
      simp [heq] at hv
    have hcoordinates : (fun i => v i) ≠ 0 := by
      intro heq
      apply hvne
      exact PiLp.ext (fun i => congrFun heq i)
    have h := (hpositive x hx).dotProduct_mulVec_pos hcoordinates
    convert h using 1
    simp only [q, dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Fin.sum_univ_two]
    ring
  obtain ⟨θ, hθ, hθq⟩ := (hK.prod (isCompact_sphere (0 : E2) 1)).exists_forall_le' hq hqpos
  have hsmul : ∀ x v t, q x (t • v) = t ^ 2 * q x v := by
    intro x v t
    simp only [q, PiLp.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    ring
  have helliptic : ∀ x ∈ K, ∀ ξ : Fin 2 → ℝ,
      θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j := by
    intro x hx ξ
    let v : E2 := WithLp.toLp 2 ξ
    by_cases hv : v = 0
    · have hξ : ξ = 0 := WithLp.toLp_injective 2 hv
      simp [hξ]
    · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      let u : E2 := ‖v‖⁻¹ • v
      have hu : u ∈ sphere (0 : E2) 1 := by
        rw [mem_sphere, dist_zero_right]
        simp [u, norm_smul, hn]
      have h := mul_le_mul_of_nonneg_left (hθq (x, u) ⟨hx, hu⟩) (sq_nonneg ‖v‖)
      have hcancel : ‖v‖ ^ 2 * q x u = q x v := by
        rw [hsmul]
        field_simp
      rw [hcancel, mul_comm (‖v‖ ^ 2)] at h
      simpa only [EuclideanSpace.real_norm_sq_eq, v, WithLp.ofLp_toLp, q] using h
  have hentry : ∀ i j, ∃ M : ℝ, ∀ x ∈ K, |a x i j| ≤ M := by
    intro i j
    obtain ⟨M, hM⟩ := hK.bddAbove_image
      (continuousOn_pi.mp (continuousOn_pi.mp ha i) j).abs
    exact ⟨M, fun x hx => hM ⟨x, hx, rfl⟩⟩
  obtain ⟨A00, hA00⟩ := hentry 0 0
  obtain ⟨A01, hA01⟩ := hentry 0 1
  obtain ⟨A10, hA10⟩ := hentry 1 0
  obtain ⟨A11, hA11⟩ := hentry 1 1
  let A := max A00 (max A01 (max A10 A11))
  have hA : ∀ x ∈ K, ∀ i j, |a x i j| ≤ A := by
    intro x hx i j
    fin_cases i <;> fin_cases j
    · exact (hA00 x hx).trans (le_max_left _ _)
    · exact (hA01 x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hA10 x hx).trans ((le_max_left _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))
    · exact (hA11 x hx).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))
  have hBnorm : ContinuousOn (fun x => ‖b x‖) K := hb.norm
  obtain ⟨B, hB⟩ := (hK.bddAbove_image hBnorm)
  refine ⟨⟨θ, max A 0, max B 0, hθ, le_max_right _ _, le_max_right _ _, helliptic, ?_, ?_⟩⟩
  · intro x hx i j
    exact (hA x hx i j).trans (le_max_left _ _)
  · intro x hx i
    have hi : |b x i| ≤ ‖b x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (b x) i
    exact hi.trans ((hB ⟨x, hx, rfl⟩).trans (le_max_left _ _))

theorem christoffel_continuous (V : Set E3) (hV : IsOpen V) (g : CoordinateMetric V)
    (a b k : Fin 3) : ContinuousOn (fun y => christoffel g.tensor y a b k) V := by
  have hmetric : ContinuousOn g.tensor V := by
    exact continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => (g.smooth i j).continuousOn
  have hpos : ∀ y ∈ V, (g.tensor y).PosDef := by
    intro y hy
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      simpa only [Matrix.conjTranspose_apply, star_trivial] using g.symmetric y hy j i
    · intro ξ hξ
      let v : E3 := WithLp.toLp 2 ξ
      have hv : v ≠ 0 := by
        intro h
        apply hξ
        exact WithLp.toLp_injective 2 h
      have h := g.positive y hy v hv
      convert h using 1
      simp only [coordinateInner, dotProduct, Matrix.mulVec, Pi.star_apply,
        star_trivial, v, Fin.sum_univ_succ]
      ring
  have hinv : ContinuousOn (fun y => (g.tensor y)⁻¹) V := by
    intro y hy
    exact (continuousAt_matrix_inv (g.tensor y)
      (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ (ne_of_gt (hpos y hy).det_pos)))
        |>.comp_continuousWithinAt (hmetric y hy)
  have hpartial : ∀ i j l, ContinuousOn (fun y => partial3 (fun z => g.tensor z i j) y l) V := by
    intro i j l
    exact ((g.smooth i j).continuousOn_fderiv_of_isOpen hV (by simp)).clm_apply continuousOn_const
  unfold christoffel
  apply ContinuousOn.const_mul
  apply continuousOn_finsetSum
  intro l hl
  exact (continuousOn_pi.mp (continuousOn_pi.mp hinv k) l).mul
    (((hpartial l b a).add (hpartial l a b)).sub (hpartial a b l))

theorem traced_christoffel_continuous (V : Set E3) (hV : IsOpen V)
    (g : CoordinateMetric V) (K : Set E2) (Φ : E2 → E3)
    (F : E2 → E2 →L[ℝ] E3) (a : E2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hΦ : ContinuousOn Φ K) (hF : ContinuousOn F K) (ha : ContinuousOn a K)
    (hgraph : MapsTo Φ K V) :
    ContinuousOn (tracedChristoffel g.tensor Φ F a) K := by
  have hΓ : ∀ k l m, ContinuousOn (fun x => christoffel g.tensor (Φ x) k l m) K := by
    intro k l m
    exact (christoffel_continuous V hV g k l m).comp hΦ hgraph
  have hcomponent : ∀ i k, ContinuousOn (fun x => F x (coordinateVector 2 i) k) K := by
    intro i k
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).comp_continuousOn
      (hF.clm_apply continuousOn_const)
  unfold tracedChristoffel christoffelVector
  apply continuousOn_finsetSum
  intro i hi
  apply continuousOn_finsetSum
  intro j hj
  have hcoeff : ContinuousOn (fun x => a x i j) K :=
    continuousOn_pi.mp (continuousOn_pi.mp ha i) j
  apply hcoeff.smul
  apply continuousOn_finsetSum
  intro k hk
  have hscalar : ContinuousOn (fun x => ∑ l, ∑ m,
      christoffel g.tensor (Φ x) l m k * F x (coordinateVector 2 i) l *
        F x (coordinateVector 2 j) m) K := by
    apply continuousOn_finsetSum
    intro l hl
    apply continuousOn_finsetSum
    intro m hm
    exact ((hΓ l m k).mul (hcomponent i l)).mul (hcomponent j m)
  exact hscalar.smul (continuousOn_const (c := coordinateVector 3 k))

theorem graph_drift_continuous (K : Set E2) (P : E3 →L[ℝ] E2) (C : E2 → E3)
    (hC : ContinuousOn C K) : ContinuousOn (graphDrift P C) K := by
  exact P.continuous.comp_continuousOn hC

theorem exists_graph_coefficient_bounds (V : Set E3) (hV : IsOpen V)
    (g : CoordinateMetric V) (U : Set E2) (p normal : E3) (hp : p ∈ V)
    (hnormal : normal ≠ 0) (L : E2 →L[ℝ] E3) (hL : Injective L)
    (horth : ∀ v : E2, coordinateInner g.tensor p (L v) normal = 0)
    (P : GraphProjection L normal) (w : E2 → ℝ) (hwC1 : ContDiffOn ℝ 1 w U)
    (hgraph : MapsTo (graphMap p L normal w) U V)
    (c : E2) (R : ℝ) (hR : 0 < R) (hK : closedBall c R ⊆ U) :
    let Φ := graphMap p L normal w
    let F := boundaryGraphLinearization (closedBall c R) L normal w
    let a := inverseGram g.tensor Φ F
    let b := graphDrift P.map (tracedChristoffel g.tensor Φ F a)
    ContinuousOn a (closedBall c R) ∧ ContinuousOn b (closedBall c R) ∧
      (∀ x ∈ closedBall c R, (a x).PosDef) ∧
      (∀ x ∈ closedBall c R, ∀ i j, a x i j = a x j i) ∧
      Nonempty (CoefficientBounds (closedBall c R) a b) := by
  let Φ := graphMap p L normal w
  let F := boundaryGraphLinearization (closedBall c R) L normal w
  have hΦ : ContinuousOn Φ (closedBall c R) := by
    exact (continuousOn_const.add L.continuous.continuousOn).add
      ((hwC1.mono hK).continuousOn.smul continuousOn_const)
  have hF := boundary_graph_linearization_continuous U L normal w hwC1 c R hR hK
  have hmaps : MapsTo Φ (closedBall c R) V := hgraph.mono_left hK
  have hinj : ∀ x ∈ closedBall c R, Injective (F x) := by
    intro x hx
    exact boundary_graph_linearization_injective V g p normal hp hnormal L hL horth _ w x
  have hA := inverse_gram_continuous_posDef V g _ Φ F hΦ hF hmaps hinj
  have hC := traced_christoffel_continuous V hV g _ Φ F _ hΦ hF hA.1 hmaps
  have hB := graph_drift_continuous _ P.map _ hC
  exact ⟨hA.1, hB, hA.2, inverse_gram_symmetric V g _ Φ F hmaps hinj,
    compact_uniform_coefficient_bounds _ (isCompact_closedBall c R) _ _ hA.1 hB hA.2⟩

end SeifertSurfaces.AppendixACoordinates.HopfAdapters
