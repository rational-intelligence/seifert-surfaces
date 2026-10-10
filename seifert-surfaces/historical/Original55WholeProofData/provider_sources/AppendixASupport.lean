import Mathlib

/-!
Concrete support statements for Appendix A of `seifert-surfaces.txt`, pp. 23--28.
These are component lemmas, not replacements for A.2--A.7.
In particular, no regularity conclusion is packaged as an input assumption.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Topology BigOperators Manifold ContDiff

namespace SeifertSurfaces.AppendixA

abbrev PlaneSpace := EuclideanSpace ℝ (Fin 2)
abbrev AmbientSpace := EuclideanSpace ℝ (Fin 3)

section FirstVariation

variable {ι Ω : Type*} [MeasurableSpace Ω]

/-- The right-hand side of (28), once the piece measures and tangential divergences
have actually been constructed. This definition does not construct those geometric data. -/
def pieceFirstVariation (pieces : Finset ι) (μ : ι → Measure Ω)
    (divergence : ι → Ω → ℝ) : ℝ :=
  ∑ i ∈ pieces, ∫ x, divergence i x ∂μ i

/-- A.2: Fermat's theorem is the calculus step after the geometric area variation formula. -/
theorem firstVariation_eq_zero_of_area_minimum
    (pieces : Finset ι) (μ : ι → Measure Ω) (divergence : ι → Ω → ℝ)
    (areaAlongFlow : ℝ → ℝ)
    (hmin : IsLocalMin areaAlongFlow 0)
    (hvariation : HasDerivAt areaAlongFlow (pieceFirstVariation pieces μ divergence) 0) :
    pieceFirstVariation pieces μ divergence = 0 := by
  exact hmin.hasDerivAt_eq_zero hvariation

/-- A.2: finite addition of the separate piecewise area derivatives. -/
theorem firstVariation_eq_zero_of_piece_derivatives
    (pieces : Finset ι) (μ : ι → Measure Ω) (divergence : ι → Ω → ℝ)
    (pieceAreaAlongFlow : ι → ℝ → ℝ)
    (hmin : IsLocalMin (fun t => ∑ i ∈ pieces, pieceAreaAlongFlow i t) 0)
    (hvariation : ∀ i ∈ pieces,
      HasDerivAt (pieceAreaAlongFlow i) (∫ x, divergence i x ∂μ i) 0) :
    pieceFirstVariation pieces μ divergence = 0 := by
  exact hmin.hasDerivAt_eq_zero (HasDerivAt.fun_sum hvariation)

end FirstVariation

section Conormals

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A.2(ii), with the source's outward-conormal sign convention. -/
def OppositeConormals (η₁ η₂ : E) : Prop := η₁ + η₂ = 0

/-- The last pointwise step of A.2(ii). -/
theorem oppositeConormals_of_pairings_vanish (η₁ η₂ : E)
    (h : ∀ v : E, inner ℝ (η₁ + η₂) v = 0) :
    OppositeConormals η₁ η₂ := by
  exact inner_self_eq_zero.mp (h (η₁ + η₂))

/-- Rewriting the orientation convention used at the beginning of A.3. -/
theorem oppositeConormals_iff_eq_neg (η₁ η₂ : E) :
    OppositeConormals η₁ η₂ ↔ η₂ = -η₁ := by
  dsimp [OppositeConormals]
  exact add_eq_zero_iff_eq_neg'

/-- A.3: a shared edge tangent and opposite conormals span the same tangent plane. -/
theorem tangent_spans_eq_of_oppositeConormals (τ η₁ η₂ : E)
    (h : OppositeConormals η₁ η₂) :
    Submodule.span ℝ ({τ, η₁} : Set E) = Submodule.span ℝ ({τ, η₂} : Set E) := by
  rw [(oppositeConormals_iff_eq_neg η₁ η₂).mp h]
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact Submodule.subset_span (by simp)
    · have heq : x = η₁ := Set.mem_singleton_iff.mp hx
      rw [heq]
      change η₁ ∈ Submodule.span ℝ ({τ, -η₁} : Set E)
      rw [← Submodule.neg_mem_iff]
      exact Submodule.subset_span (by simp)
  · intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact Submodule.subset_span (by simp)
    · rw [Set.mem_singleton_iff.mp hx]
      exact (Submodule.span ℝ ({τ, η₁} : Set E)).neg_mem
        (Submodule.subset_span (by simp))

/-- A.3: orthogonal nonzero edge tangent and unit conormal really span a plane. -/
theorem tangent_conormal_span_finrank (τ η : E)
    (hτ : τ ≠ 0) (hη : ‖η‖ = 1) (horth : inner ℝ τ η = 0) :
    Module.finrank ℝ (Submodule.span ℝ ({τ, η} : Set E)) = 2 := by
  have hη₀ : η ≠ 0 := by
    intro heq
    simp [heq] at hη
  have hlin : LinearIndependent ℝ (![τ, η] : Fin 2 → E) := by
    apply linearIndependent_of_ne_zero_of_inner_eq_zero
    · intro i
      fin_cases i <;> simp [hτ, hη₀]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [real_inner_comm]
  have hrange : Set.range (![τ, η] : Fin 2 → E) = ({τ, η} : Set E) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [← hrange]
  exact finrank_span_eq_card hlin

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A.3: the interface terms cancel. Integrals are over one common interface measure. -/
theorem interface_pairing_integrals_cancel (μ : Measure Ω)
    (η₁ η₂ X : Ω → E) (hη : ∀ x, OppositeConormals (η₁ x) (η₂ x)) :
    (∫ x, inner ℝ (η₁ x) (X x) ∂μ) +
      (∫ x, inner ℝ (η₂ x) (X x) ∂μ) = 0 := by
  have hneg : η₂ = fun x => -η₁ x := funext fun x =>
    (oppositeConormals_iff_eq_neg _ _).mp (hη x)
  rw [hneg]
  simp only [inner_neg_left, integral_neg, add_neg_cancel]

/-- The same cancellation for a scalar test function in the weak formulation in A.3. -/
theorem interface_flux_integrals_cancel (μ : Measure Ω)
    (flux ν₁ ν₂ : Ω → E) (φ : Ω → ℝ)
    (hν : ∀ x, OppositeConormals (ν₁ x) (ν₂ x)) :
    (∫ x, inner ℝ (flux x) (ν₁ x) * φ x ∂μ) +
      (∫ x, inner ℝ (flux x) (ν₂ x) * φ x ∂μ) = 0 := by
  have hneg : ν₂ = fun x => -ν₁ x := funext fun x =>
    (oppositeConormals_iff_eq_neg _ _).mp (hν x)
  rw [hneg]
  simp only [inner_neg_right, neg_mul, integral_neg, add_neg_cancel]

end Conormals

/-- A.2(ii): the localization/fundamental-lemma step on an arc parametrized by a real interval.
The vector test is a smooth scalar test times an arbitrary constant ambient vector. Extension
of these arc tests to ambient smooth fields is a separate geometric obligation. -/
theorem oppositeConormals_on_interval_of_integral_tests
    (a b : ℝ) (η₁ η₂ : ℝ → AmbientSpace)
    (hη₁ : ContinuousOn η₁ (Ioo a b)) (hη₂ : ContinuousOn η₂ (Ioo a b))
    (htests : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → ∀ v : AmbientSpace,
        ∫ t in Ioo a b, φ t * inner ℝ (η₁ t + η₂ t) v = 0) :
    ∀ t ∈ Ioo a b, OppositeConormals (η₁ t) (η₂ t) := by
  intro t ht
  apply oppositeConormals_of_pairings_vanish
  intro v
  have hc : ContinuousOn (fun t => inner ℝ (η₁ t + η₂ t) v) (Ioo a b) :=
    (hη₁.add hη₂).inner continuousOn_const
  have hzero : ∀ᵐ t, t ∈ Ioo a b → inner ℝ (η₁ t + η₂ t) v = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hc.locallyIntegrableOn measurableSet_Ioo)
    intro φ hφ hsφ hsupport
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Ioo a b) (f := fun t => φ t • inner ℝ (η₁ t + η₂ t) v)]
    · exact htests φ hφ hsφ hsupport v
    · intro x hx
      have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hmem => hx (hsupport hmem))
      simp [hφx]
  have hae : (fun t => inner ℝ (η₁ t + η₂ t) v) =ᵐ[volume.restrict (Ioo a b)] 0 :=
    (ae_restrict_iff' measurableSet_Ioo).mpr hzero
  exact Measure.eqOn_open_of_ae_eq hae isOpen_Ioo hc continuousOn_const ht

section BoundaryLinearAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `dr` is nonzero on the tangent plane, the literal conclusion of A.4. -/
def IsTransverseToLevel (T : Submodule ℝ E) (dr : E →L[ℝ] ℝ) : Prop :=
  ∃ v : T, dr v ≠ 0

theorem isTransverseToLevel_iff_restriction_ne_zero
    (T : Submodule ℝ E) (dr : E →L[ℝ] ℝ) :
    IsTransverseToLevel T dr ↔ dr.comp T.subtypeL ≠ 0 := by
  change (∃ v : T, dr v ≠ 0) ↔ _
  constructor
  · rintro ⟨v, hv⟩ heq
    have h := congrArg (fun f : T →L[ℝ] ℝ => f v) heq
    exact hv h
  · intro h
    by_contra hn
    push Not at hn
    apply h
    ext v
    exact hn v

theorem isTransverseToLevel_iff_not_le_kernel
    (T : Submodule ℝ E) (dr : E →L[ℝ] ℝ) :
    IsTransverseToLevel T dr ↔ ¬T ≤ LinearMap.ker dr.toLinearMap := by
  change (∃ v : T, dr v ≠ 0) ↔ _
  constructor
  · rintro ⟨v, hv⟩ hle
    exact hv (hle v.property)
  · intro h
    by_contra hn
    push Not at hn
    apply h
    intro v hv
    exact hn ⟨v, hv⟩

/-- A.4: the negative outward Hopf derivative supplies the required nonzero vector. -/
theorem isTransverseToLevel_of_negative_outward_derivative
    (T : Submodule ℝ E) (dr : E →L[ℝ] ℝ) (ν : T) (hν : dr ν < 0) :
    IsTransverseToLevel T dr := by
  exact ⟨ν, ne_of_lt hν⟩

/-- One direction needs no dimension assumption. -/
theorem tangent_ne_level_plane_of_transverse
    (T : Submodule ℝ E) (dr : E →L[ℝ] ℝ)
    (h : IsTransverseToLevel T dr) :
    T ≠ LinearMap.ker dr.toLinearMap := by
  intro heq
  exact (isTransverseToLevel_iff_not_le_kernel T dr).mp h (le_of_eq heq)

/-- A.4/A.7: the converse needs both subspaces to be planes in dimension three. -/
theorem plane_transverse_iff_ne_boundary_plane
    (T : Submodule ℝ AmbientSpace) (dr : AmbientSpace →L[ℝ] ℝ)
    (hT : Module.finrank ℝ T = 2) (hdr : dr ≠ 0) :
    IsTransverseToLevel T dr ↔ T ≠ LinearMap.ker dr.toLinearMap := by
  constructor
  · exact tangent_ne_level_plane_of_transverse T dr
  · intro hne
    rw [isTransverseToLevel_iff_not_le_kernel]
    intro hle
    have hdr' : dr.toLinearMap ≠ 0 := by
      intro hzero
      apply hdr
      ext x
      exact LinearMap.congr_fun hzero x
    have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hdr'
    have hker : Module.finrank ℝ (LinearMap.ker dr.toLinearMap) = 2 := by
      simp [AmbientSpace] at hdim
      omega
    exact hne (Submodule.eq_of_le_of_finrank_eq hle (hT.trans hker.symm))

/-- A.7: distinct two-dimensional planes in three-space have full tangent sum. -/
theorem distinct_planes_span_ambient
    (T B : Submodule ℝ AmbientSpace)
    (hT : Module.finrank ℝ T = 2) (hB : Module.finrank ℝ B = 2) (hne : T ≠ B) :
    T ⊔ B = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have hle : Module.finrank ℝ ↥(T ⊔ B) ≤ 3 := by
    simpa [AmbientSpace] using (T ⊔ B).finrank_le
  have hTle : 2 ≤ Module.finrank ℝ ↥(T ⊔ B) := by
    simpa [hT] using Submodule.finrank_mono (show T ≤ T ⊔ B from le_sup_left)
  have hneq : Module.finrank ℝ ↥(T ⊔ B) ≠ 2 := by
    intro heq
    have hTsup : T = T ⊔ B := Submodule.eq_of_le_of_finrank_eq le_sup_left (hT.trans heq.symm)
    have hBle : B ≤ T := hTsup ▸ le_sup_right
    exact hne (Submodule.eq_of_le_of_finrank_eq hBle (hB.trans hT.symm)).symm
  have hdim : Module.finrank ℝ ↥(T ⊔ B) = 3 := by omega
  simpa [AmbientSpace] using hdim

/-- A.7: the intersection along the boundary has the expected one-dimensional tangent. -/
theorem distinct_planes_intersection_finrank
    (T B : Submodule ℝ AmbientSpace)
    (hT : Module.finrank ℝ T = 2) (hB : Module.finrank ℝ B = 2) (hne : T ≠ B) :
    Module.finrank ℝ ↥(T ⊓ B) = 1 := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq T B
  rw [distinct_planes_span_ambient T B hT hB hne, finrank_top, hT, hB] at hdim
  simp only [AmbientSpace, finrank_euclideanSpace_fin] at hdim
  exact Nat.add_left_cancel hdim

end BoundaryLinearAlgebra

section GraphFirstOrder

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A.4: a graph whose height vanishes to first order has the prescribed tangent inclusion.
The within-set form also applies at the boundary of a closed region. -/
theorem graph_hasFDerivWithinAt_of_height_flat
    (U : Set D) (p n : E) (L : D →L[ℝ] E) (w : D → ℝ)
    (hw : HasFDerivWithinAt w (0 : D →L[ℝ] ℝ) U 0) :
    HasFDerivWithinAt (fun x => p + L x + w x • n) L U 0 := by
  convert ((L.hasFDerivWithinAt.const_add p).add (hw.smul_const n)) using 1
  simp

/-- A.4: the chain rule identifies the Hopf derivative with the restricted ambient `dr`. -/
theorem defining_function_graph_hasFDerivWithinAt
    (U : Set D) (p n : E) (L : D →L[ℝ] E) (w : D → ℝ) (r : E → ℝ)
    (hw₀ : w 0 = 0) (hw : HasFDerivWithinAt w (0 : D →L[ℝ] ℝ) U 0)
    (dr : E →L[ℝ] ℝ) (hr : HasFDerivAt r dr p) :
    HasFDerivWithinAt (fun x => r (p + L x + w x • n)) (dr.comp L) U 0 := by
  have hg := graph_hasFDerivWithinAt_of_height_flat U p n L w hw
  have hr' : HasFDerivAt r dr (p + L 0 + w 0 • n) := by simpa [hw₀] using hr
  exact hr'.comp_hasFDerivWithinAt 0 hg

/-- A.5, p. 26: a one-sided curve staying in `{r ≥ 0}` has a nonnegative inward
derivative of `r`. This is the analytic step behind containment of tangent rays
in the closed half-plane `{dr ≥ 0}`. -/
theorem boundary_differential_nonnegative_along_curve
    (r : E → ℝ) (p v : E) (c : ℝ → E) (dr : E →L[ℝ] ℝ)
    (hc₀ : c 0 = p) (hc : HasDerivAt c v 0) (hr : HasFDerivAt r dr p)
    (hr₀ : r p = 0)
    (hside : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ r (c t)) :
    0 ≤ dr v := by
  have hr' : HasFDerivAt r dr (c 0) := hc₀.symm ▸ hr
  have hderiv : HasDerivAt (fun t => r (c t)) (dr v) 0 := hr'.comp_hasDerivAt 0 hc
  apply ge_of_tendsto hderiv.tendsto_slope_zero_right
  filter_upwards [hside, self_mem_nhdsWithin] with t ht hpos
  simp only [zero_add, hc₀, hr₀, sub_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr hpos.le) ht

end GraphFirstOrder

/-- A.5, equation (29): a first prefix of angle at least `a` either stays below `2a`,
or the last sector alone has angle strictly larger than `a`. -/
theorem exists_large_sector_or_initial_sector_union
    (a : ℝ) (ha : 0 < a) (angles : List ℝ)
    (hangles : ∀ θ ∈ angles, 0 < θ ∧ θ < 2 * a) (htotal : a ≤ angles.sum) :
    (∃ k ≤ angles.length, a ≤ (angles.take k).sum ∧ (angles.take k).sum < 2 * a) ∨
      (∃ θ ∈ angles, a < θ ∧ θ < 2 * a) := by
  have hprefix : ∀ (xs : List ℝ) (s : ℝ), s < a →
      (∀ θ ∈ xs, 0 < θ ∧ θ < 2 * a) → a ≤ s + xs.sum →
      (∃ k ≤ xs.length, a ≤ s + (xs.take k).sum ∧ s + (xs.take k).sum < 2 * a) ∨
        (∃ θ ∈ xs, a < θ ∧ θ < 2 * a) := by
    intro xs
    induction xs with
    | nil =>
        intro s hs _ htotal
        simp only [List.sum_nil, add_zero] at htotal
        exact (not_le_of_gt hs htotal).elim
    | cons θ xs ih =>
        intro s hs hang htotal
        have hθ := hang θ (by simp)
        by_cases hcross : a ≤ s + θ
        · by_cases hsmall : s + θ < 2 * a
          · exact Or.inl ⟨1, by simp, by simpa using hcross, by simpa using hsmall⟩
          · exact Or.inr ⟨θ, by simp, by linarith, hθ.2⟩
        · have htail : a ≤ (s + θ) + xs.sum := by
            simpa only [List.sum_cons, add_assoc] using htotal
          rcases ih (s + θ) (lt_of_not_ge hcross)
              (fun z hz => hang z (by simp [hz])) htail with ⟨k, hk, hka, hk₂⟩ | ⟨z, hz, hza, hz₂⟩
          · exact Or.inl ⟨k + 1, by simp only [List.length_cons]; omega,
              by simpa only [List.take_succ_cons, List.sum_cons, add_assoc] using hka,
              by simpa only [List.take_succ_cons, List.sum_cons, add_assoc] using hk₂⟩
          · exact Or.inr ⟨z, by simp [hz], hza, hz₂⟩
  simpa only [zero_add] using hprefix angles 0 ha hangles (by simpa using htotal)

/-- A.5: the angular congruence together with the half-plane bound forces total angle `π`. -/
theorem boundary_total_angle_eq_pi
    (Θ : ℝ) (hΘ₀ : 0 ≤ Θ) (hΘπ : Θ ≤ Real.pi)
    (hcongr : ∃ k : ℤ, Θ = Real.pi + 2 * Real.pi * (k : ℝ)) :
    Θ = Real.pi := by
  obtain ⟨k, hk⟩ := hcongr
  have hk0 : (k : ℝ) ≤ 0 := by nlinarith [Real.pi_pos]
  have hk1 : (-1 : ℝ) < (k : ℝ) := by nlinarith [Real.pi_pos]
  have hk' : k = 0 := by
    have hki0 : k ≤ 0 := by exact_mod_cast hk0
    have hki1 : (-1 : ℤ) < k := by exact_mod_cast hk1
    omega
  simp [hk'] at hk
  exact hk

section SlidingBoundaryCompactness

/-- A.6: replacement by a fixed-boundary minimizer preserves convergence to the area infimum. -/
theorem replacement_areas_tendsto_infimum
    (A : ℝ) (original replacement : ℕ → ℝ)
    (horiginal : Tendsto original atTop (𝓝 A))
    (hlower : ∀ n, A ≤ replacement n) (hupper : ∀ n, replacement n ≤ original n) :
    Tendsto replacement atTop (𝓝 A) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds horiginal hlower hupper

/-- A.6: a sequence in a finite union has a subsequence contained in one member.
No disjointness or closedness is needed for this initial pigeonhole step. -/
theorem finite_cover_has_single_block_subsequence
    {X ι : Type*} [Fintype ι] (blocks : ι → Set X) (surfaces : ℕ → X)
    (hcover : ∀ n, ∃ i, surfaces n ∈ blocks i) :
    ∃ i, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ n, surfaces (ψ n) ∈ blocks i := by
  have hfreq : ∃ᶠ n in atTop, ∃ i, surfaces n ∈ blocks i :=
    (Eventually.of_forall hcover).frequently
  obtain ⟨i, hi⟩ := Filter.frequently_exists.mp hfreq
  obtain ⟨ψ, hψ, hmem⟩ := Filter.extraction_of_frequently_atTop hi
  exact ⟨i, ψ, hψ, hmem⟩

/-- A.6: compactness, a closed isotopy block, and continuity of area produce a limit
in the same block with the limiting area. Here `X` is an actual topological space, and
`area` is an actual continuous real function. The geometric area/topology bridge is
an explicit separate obligation, rather than an assumed regularity record. -/
theorem compact_closed_block_attains_limiting_area
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (C N : Set X) (hC : IsCompact C) (hN : IsClosed N)
    (area : X → ℝ) (harea : ContinuousOn area C) (surfaces : ℕ → X)
    (hmem : ∀ n, surfaces n ∈ C ∩ N) (A : ℝ)
    (hlimit : Tendsto (fun n => area (surfaces n)) atTop (𝓝 A)) :
    ∃ surface ∈ C ∩ N, area surface = A := by
  obtain ⟨x, hx, ψ, hψ, hlim⟩ := (hC.inter_right hN).tendsto_subseq hmem
  have hlim' : Tendsto (surfaces ∘ ψ) atTop (𝓝 x) := hlim
  have hlima : Tendsto (fun n => area (surfaces (ψ n))) atTop (𝓝 (area x)) :=
    (harea x hx.1).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hlim', Eventually.of_forall (fun n => (hmem (ψ n)).1)⟩)
  have hlimA := hlimit.comp hψ.tendsto_atTop
  exact ⟨x, hx, tendsto_nhds_unique hlima hlimA⟩

end SlidingBoundaryCompactness

section ProperEmbedding

variable {HS HM S M : Type*} [TopologicalSpace HS] [TopologicalSpace HM]
  [TopologicalSpace S] [TopologicalSpace M] [ChartedSpace HS S] [ChartedSpace HM M]
  (IS : ModelWithCorners ℝ PlaneSpace HS) (IM : ModelWithCorners ℝ AmbientSpace HM)

/-- The smooth proper embedding appearing in A.5/A.6. This is conclusion data, not a
regularity assumption used to manufacture a proof of A.5/A.6. Compactness of the domain
must be supplied separately when invoking the surface results. -/
structure SmoothProperEmbedding [IsManifold IS ∞ S] [IsManifold IM ∞ M] where
  toFun : S → M
  smooth : ContMDiff IS IM ∞ toFun
  isEmbedding : Topology.IsEmbedding toFun
  differentialImmersion : ∀ x, IsDiffImmersionAt IS IM toFun x
  preimage_boundary : toFun ⁻¹' IM.boundary M = IS.boundary S

variable [IsManifold IS ∞ S] [IsManifold IM ∞ M]

/-- The embedded tangent plane is the actual range of the manifold differential. -/
def tangentImage (f : S → M) (x : S) : Submodule ℝ (TangentSpace IM (f x)) :=
  LinearMap.range (mfderiv IS IM f x).toLinearMap

/-- A smooth differential embedding of a surface really has a two-dimensional tangent image. -/
theorem smooth_proper_embedding_tangent_finrank
    (f : SmoothProperEmbedding IS IM (S := S) (M := M)) (x : S) :
    Module.finrank ℝ (tangentImage IS IM f.toFun x) = 2 := by
  rw [tangentImage, LinearMap.finrank_range_of_inj (f.differentialImmersion x).mfderiv_injective]
  change Module.finrank ℝ PlaneSpace = 2
  simp [PlaneSpace]

/-- Properness identifies the ambient-boundary intersection with the embedded source boundary. -/
theorem proper_embedding_boundary_intersection (f : SmoothProperEmbedding IS IM (S := S) (M := M)) :
    Set.range f.toFun ∩ IM.boundary M = f.toFun '' IS.boundary S := by
  ext y
  constructor
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, ?_, rfl⟩
    rw [← f.preimage_boundary]
    exact hx
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    rw [← f.preimage_boundary] at hx
    exact hx

end ProperEmbedding

end SeifertSurfaces.AppendixA
