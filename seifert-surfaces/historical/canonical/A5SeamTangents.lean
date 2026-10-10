import A5RelativeC1Inverse
import A5NativeProjectionFiber

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- Exact image equality determines a continuous sector-coordinate lift
through an embedded piece. Continuity of the supplied lift is an output. -/
theorem continuous_coordinate_lift_of_embedded_image
    {V P N : Type*} [TopologicalSpace V] [TopologicalSpace P] [TopologicalSpace N]
    (c : PartialHomeomorph P (Euc 2)) (f : P → N) (hf : IsEmbedding f)
    (T : Set V) (γ : V → N) (q : V → Euc 2)
    (hγ : ContinuousOn γ T) (hmaps : MapsTo q T c.target)
    (heq : ∀ t ∈ T, f (c.symm (q t)) = γ t) : ContinuousOn q T := by
  let e := hf.toHomeomorph
  let γT : T → range f := fun t => ⟨γ t, ⟨c.symm (q t), heq t t.property⟩⟩
  have hγT : Continuous γT :=
    (hγ.comp_continuous continuous_subtype_val (fun t => t.property)).subtype_mk _
  let p : T → P := e.symm ∘ γT
  have hp : Continuous p := e.symm.continuous.comp hγT
  have hpq (t : T) : p t = c.symm (q t) := by
    apply e.injective
    exact (e.apply_symm_apply (γT t)).trans (Subtype.ext (heq t t.property).symm)
  have hpc : MapsTo p univ c.source := by
    intro t _
    rw [hpq]
    exact c.map_target (hmaps t.property)
  have hcont : Continuous (c ∘ p) :=
    c.continuousOn.comp_continuous hp (fun t => hpc (mem_univ t))
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hcont.congr
  intro t
  change c (p t) = q t
  rw [hpq, c.right_inv (hmaps t.property)]

/-- Differentiating a continuous lift through a relative immersion places
the actual curve velocity in the actual within-tangent range. -/
theorem relative_curve_lift_hasDerivWithinAt
    (S : Set (Euc 2)) (T : Set ℝ) (t : ℝ) (ht : t ∈ T)
    (hT : UniqueDiffWithinAt ℝ T t)
    (G : Euc 2 → Euc 3) (γ : ℝ → Euc 3) (q : ℝ → Euc 2)
    (D : Euc 2 →L[ℝ] Euc 3) (v : Euc 3)
    (hG : HasFDerivWithinAt G D S (q t)) (hD : Function.Injective D)
    (hγ : HasDerivWithinAt γ v T t) (hq : ContinuousWithinAt q T t)
    (hmaps : MapsTo q T S) (heq : ∀ z ∈ T, G (q z) = γ z) :
    ∃ w : Euc 2, HasDerivWithinAt q w T t ∧ D w = v := by
  obtain ⟨L, hL⟩ := D.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hD)
  let Lc : Euc 3 →L[ℝ] Euc 2 := L.toContinuousLinearMap
  have hinv : Function.LeftInverse Lc D := fun w =>
    congrArg (fun A : Euc 2 →ₗ[ℝ] Euc 2 => A w) hL
  have hqd := HasFDerivWithinAt.of_comp_of_leftInverse
    (hq.tendsto_nhdsWithin hmaps) hG hγ.hasFDerivWithinAt
    (Set.EqOn.eventuallyEq_nhdsWithin heq) hinv ht
  have hd := (hG.comp t hqd hmaps).fderivWithin hT
  have he : fderivWithin ℝ (G ∘ q) T t = fderivWithin ℝ γ T t :=
    fderivWithin_congr' heq ht
  have hv := congrArg (fun A : ℝ →L[ℝ] Euc 3 => A 1) (hd.symm.trans (he.trans (hγ.hasFDerivWithinAt.fderivWithin hT)))
  exact ⟨Lc v, by simpa using hqd.hasDerivWithinAt, by simpa using hv⟩

/-- The actual curve velocity belongs to the relative tangent range. -/
theorem curve_derivative_mem_relative_tangent_range
    (S : Set (Euc 2)) (T : Set ℝ) (t : ℝ) (ht : t ∈ T)
    (hT : UniqueDiffWithinAt ℝ T t)
    (G : Euc 2 → Euc 3) (γ : ℝ → Euc 3) (q : ℝ → Euc 2)
    (D : Euc 2 →L[ℝ] Euc 3) (v : Euc 3)
    (hG : HasFDerivWithinAt G D S (q t)) (hD : Function.Injective D)
    (hγ : HasDerivWithinAt γ v T t) (hq : ContinuousWithinAt q T t)
    (hmaps : MapsTo q T S) (heq : ∀ z ∈ T, G (q z) = γ z) :
    v ∈ D.toLinearMap.range := by
  obtain ⟨w, _, hw⟩ := relative_curve_lift_hasDerivWithinAt S T t ht hT G γ q D v hG hD hγ hq hmaps heq
  exact ⟨w, hw⟩

/-- The common edge velocity and opposite unit conormals determine the same
two-dimensional tangent plane. Only the metric covector at that point is used. -/
theorem tangent_ranges_eq_of_opposite_conormals
    (D₁ D₂ : Euc 2 →L[ℝ] Euc 3)
    (hD₁ : Function.Injective D₁) (hD₂ : Function.Injective D₂)
    (v n₁ n₂ : Euc 3) (hv : v ≠ 0)
    (hv₁ : v ∈ D₁.toLinearMap.range) (hv₂ : v ∈ D₂.toLinearMap.range)
    (hn₁ : n₁ ∈ D₁.toLinearMap.range) (hn₂ : n₂ ∈ D₂.toLinearMap.range)
    (ℓ : Euc 3 →L[ℝ] ℝ) (hunit : ℓ n₁ = 1) (horth : ℓ v = 0)
    (hopp : n₁ + n₂ = 0) : D₁.toLinearMap.range = D₂.toLinearMap.range := by
  have hnzero : n₁ ≠ 0 := by
    intro he
    simp [he] at hunit
  have hli : LinearIndependent ℝ (![v, n₁] : Fin 2 → Euc 3) := by
    apply linearIndependent_fin2.mpr
    refine ⟨hnzero, ?_⟩
    intro a ha
    change a • n₁ = v at ha
    have he := congrArg ℓ ha
    simp only [map_smul, hunit, horth, smul_eq_mul, mul_one] at he
    subst a
    exact hv (by simpa using ha.symm)
  have hn₁₂ : n₁ ∈ D₂.toLinearMap.range := by
    have he : n₁ = -n₂ := eq_neg_of_add_eq_zero_left hopp
    rw [he]
    exact D₂.toLinearMap.range.neg_mem hn₂
  have hspan : Module.finrank ℝ (Submodule.span ℝ ({v, n₁} : Set (Euc 3))) = 2 := by
    have hr : range (![v, n₁] : Fin 2 → Euc 3) = {v, n₁} := by ext z; simp [or_comm]
    rw [← hr]
    exact finrank_span_eq_card hli
  have range_eq (D : Euc 2 →L[ℝ] Euc 3) (hD : Function.Injective D)
      (hvD : v ∈ D.toLinearMap.range) (hnD : n₁ ∈ D.toLinearMap.range) :
      Submodule.span ℝ ({v, n₁} : Set (Euc 3)) = D.toLinearMap.range := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨hvD, hnD⟩)
    · rw [hspan, LinearMap.finrank_range_of_inj hD]
      norm_num [Euc]
  exact (range_eq D₁ hD₁ hv₁ hn₁).symm.trans (range_eq D₂ hD₂ hv₂ hn₁₂)

/-- Native whole-piece image equality supplies continuity of every supplied
curve lift, including lifts into a closed radial edge or a corner. -/
theorem native_piece_curve_coordinates_continuous
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (U : Set ℝ) (γ : ℝ → ThreeSphere) (q : ℝ → Euc 2)
    (hγ : ContinuousOn γ U)
    (hq : MapsTo q U ((F.domain i).chart j).map.target)
    (heq : ∀ t ∈ U, E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q t)) = γ t) :
    ContinuousOn q U := by
  exact continuous_coordinate_lift_of_embedded_image ((F.domain i).chart j).map
    (E.toSphere ∘ F.map ∘ F.parametrization i)
    (IsEmbedding.subtypeVal.comp (F.piece_topological_embedding i)) U γ q hγ hq heq

/-- The actual native C1 chart and image equality place the actual smooth
edge velocity in its tangent range in every ambient chart containing the
point. No regularity premise on the supplied coordinate lift occurs. -/
theorem native_curve_velocity_mem_piece_tangent
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (U : Set ℝ) (hU : IsOpen U) (γ : ℝ → ThreeSphere) (q : ℝ → Euc 2)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 3) 1 γ U)
    (hq : MapsTo q U ((F.domain i).chart j).map.target)
    (heq : ∀ t ∈ U, E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q t)) = γ t)
    (t : ℝ) (ht : t ∈ U) (c : SeifertSurfaces.OriginalEndpoints.SmoothAmbientChart ThreeSphere)
    (hc : γ t ∈ c.chart.source) :
    deriv (c.chart ∘ γ) t ∈ (fderivWithin ℝ
      (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      ((F.domain i).chart j).map.target (q t)).toLinearMap.range := by
  have hqcont := native_piece_curve_coordinates_continuous E F i j U γ q hγ.continuousOn hq heq
  obtain ⟨hG, hrank⟩ := native_piece_chart_C1_rank_at E F i j (q t) (hq ht) c
    (by rw [heq t ht]; exact hc)
  have hcoord : ContDiffAt ℝ 1 (c.chart ∘ γ) t :=
    (((c.smooth _ hc).contMDiffAt (c.chart.open_source.mem_nhds hc)).of_le (by simp)
      |>.comp t ((hγ t ht).contMDiffAt (hU.mem_nhds ht))).contDiffAt
  exact curve_derivative_mem_relative_tangent_range _ U t ht (hU.uniqueDiffOn t ht)
    _ _ q _ _ (hG.differentiableWithinAt (by norm_num)).hasFDerivWithinAt hrank
    ((hcoord.differentiableAt (by norm_num)).hasDerivAt.hasDerivWithinAt)
    (hqcont t ht) hq (fun z hz => congrArg c.chart (heq z hz))

/-- The actual native C1 chart and image equality place the actual smooth
edge velocity in its tangent range in every ambient chart containing the
point. No regularity premise on the supplied coordinate lift occurs. -/
theorem native_curve_coordinates_hasDerivAt
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (U : Set ℝ) (hU : IsOpen U) (γ : ℝ → ThreeSphere) (q : ℝ → Euc 2)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 3) 1 γ U)
    (hq : MapsTo q U ((F.domain i).chart j).map.target)
    (heq : ∀ t ∈ U, E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q t)) = γ t)
    (t : ℝ) (ht : t ∈ U) (c : SeifertSurfaces.OriginalEndpoints.SmoothAmbientChart ThreeSphere)
    (hc : γ t ∈ c.chart.source) :
    ∃ w : Euc 2, HasDerivAt q w t ∧
      (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target (q t)) w = deriv (c.chart ∘ γ) t := by
  have hqcont := native_piece_curve_coordinates_continuous E F i j U γ q hγ.continuousOn hq heq
  obtain ⟨hG, hrank⟩ := native_piece_chart_C1_rank_at E F i j (q t) (hq ht) c
    (by rw [heq t ht]; exact hc)
  have hcoord : ContDiffAt ℝ 1 (c.chart ∘ γ) t :=
    (((c.smooth _ hc).contMDiffAt (c.chart.open_source.mem_nhds hc)).of_le (by simp)
      |>.comp t ((hγ t ht).contMDiffAt (hU.mem_nhds ht))).contDiffAt
  obtain ⟨w, hw, he⟩ := relative_curve_lift_hasDerivWithinAt _ U t ht (hU.uniqueDiffOn t ht)
    _ _ q _ _ (hG.differentiableWithinAt (by norm_num)).hasFDerivWithinAt hrank
    ((hcoord.differentiableAt (by norm_num)).hasDerivAt.hasDerivWithinAt)
    (hqcont t ht) hq (fun z hz => congrArg c.chart (heq z hz))

  exact ⟨w, hw.hasDerivAt (hU.mem_nhds ht), he⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
