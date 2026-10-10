import A5ConormalEuclideanAdapter
import A5NativeSeamSector
import A5TwoSectorProjection

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- The native two-piece conormal data imply local injectivity across the
seam of any projection transverse to the two actual piece derivatives.
The coordinate lifts need no supplied continuity or differentiability. -/
theorem native_two_sector_projection_collisions
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin 2 → Fin F.pieceCount) (j : ∀ k, Fin (F.domain (i k)).count)
    (U : Set ℝ) (hU : IsOpen U) (h0 : 0 ∈ U)
    (γ : ℝ → ThreeSphere) (q : Fin 2 → ℝ → Euc 2) (n : Fin 2 → Euc 2)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 3) 1 γ U)
    (hreg : mfderiv 𝓘(ℝ) (𝓡 3) γ 0 1 ≠ 0)
    (hq : ∀ k, MapsTo (q k) U (((F.domain (i k)).chart (j k)).map.target ∩
      frontier ((F.domain (i k)).chart (j k)).map.target))
    (heq : ∀ k t, t ∈ U → E.toSphere
      (sectorCoordinateMap (F.map ∘ F.parametrization (i k)) (j k) (q k t)) = γ t)
    (hinward : ∀ k, ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ Ioo (0 : ℝ) ε,
      q k 0 - b • n k ∈ ((F.domain (i k)).chart (j k)).map.target)
    (c : SmoothAmbientChart ThreeSphere) (hc : γ 0 ∈ c.chart.source)
    (inner : TangentSpace (𝓡 3) (γ 0) →L[ℝ]
      TangentSpace (𝓡 3) (γ 0) →L[ℝ] ℝ)
    (P : Euc 3 →L[ℝ] Euc 2) :
    let G := fun k => E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization (i k)) (j k)
    let N : Fin 2 → TangentSpace (𝓡 3) (γ 0) := fun k => (heq k 0 h0) ▸ mfderivWithin 𝓘(ℝ, Euc 2) (𝓡 3)
      (G k) ((F.domain (i k)).chart (j k)).map.target (q k 0) (n k)
    (∀ k, inner (N k) (N k) = 1) →
    (∀ k, inner (N k) (mfderiv 𝓘(ℝ) (𝓡 3) γ 0 1) = 0) →
    N 0 + N 1 = 0 →
    (∀ k, Function.Bijective (P.comp (fderivWithin ℝ (c.chart ∘ G k)
      ((F.domain (i k)).chart (j k)).map.target (q k 0)))) →
    ∃ r : Fin 2 → ℝ, (∀ k, 0 < r k) ∧
      ∀ y₀ ∈ Metric.ball (q 0 0) (r 0) ∩ ((F.domain (i 0)).chart (j 0)).map.target,
      ∀ y₁ ∈ Metric.ball (q 1 0) (r 1) ∩ ((F.domain (i 1)).chart (j 1)).map.target,
        P (c.chart (G 0 y₀)) = P (c.chart (G 1 y₁)) → c.chart (G 0 y₀) = c.chart (G 1 y₁) := by
  dsimp only
  intro hunit horth hbalance hP
  let A := fun k => ((F.domain (i k)).chart (j k)).model
  let G := fun k => E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization (i k)) (j k)
  let H := fun k => c.chart ∘ G k
  let D := fun k => fderivWithin ℝ (H k) ((F.domain (i k)).chart (j k)).map.target (q k 0)
  let N : Fin 2 → TangentSpace (𝓡 3) (γ 0) := fun k => (heq k 0 h0) ▸ mfderivWithin 𝓘(ℝ, Euc 2) (𝓡 3)
    (G k) ((F.domain (i k)).chart (j k)).map.target (q k 0) (n k)
  obtain ⟨C, hC⟩ := ambient_chart_tangent_equivalence c (γ 0) hc
  have hN (k : Fin 2) : D k (n k) = C (N k) := by
    rw [hC]
    apply ambient_chart_within_derivative_transport
    · rw [((F.domain (i k)).chart (j k)).target_eq]
      exact (A k).uniqueDiffOn_domain _ (by
        simpa only [A, ← ((F.domain (i k)).chart (j k)).target_eq] using (hq k h0).1)
    · exact ((native_piece_sphere_C1_rank E F (i k) (j k)).1 _ (hq k h0).1).mdifferentiableWithinAt (by norm_num)
    · exact hc
  have hga := (hγ 0 h0).contMDiffAt (hU.mem_nhds h0)
  have hvelocity : deriv (c.chart ∘ γ) 0 = C (mfderiv 𝓘(ℝ) (𝓡 3) γ 0 1) := by
    rw [hC]
    exact ambient_chart_curve_derivative_transport γ 0 (hga.mdifferentiableAt (by norm_num)) c hc
  have hvelocity_ne : deriv (c.chart ∘ γ) 0 ≠ 0 := by
    rw [hvelocity]
    simpa only [C.map_zero] using C.injective.ne hreg
  choose v hv hvD using fun k => native_curve_coordinates_hasDerivAt E F (i k) (j k)
    U hU γ (q k) hγ (fun _ ht => (hq k ht).1) (heq k) 0 h0 c hc
  have hvne (k : Fin 2) : v k ≠ 0 := by
    intro he
    have hz := hvD k
    rw [he, map_zero] at hz
    exact hvelocity_ne hz.symm
  have hframe (k : Fin 2) : LinearIndependent ℝ (![v k, n k] : Fin 2 → Euc 2) := by
    let L : Euc 3 →L[ℝ] ℝ := (inner (N k)).comp C.symm.toContinuousLinearMap
    apply conormal_coordinate_frame (D k) (v k) (n k) (hvne k) L
    · rw [hN]
      simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        C.symm_apply_apply] using hunit k
    · change L ((fderivWithin ℝ (H k) _ (q k 0)) (v k)) = 0
      rw [hvD, hvelocity]
      simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        C.symm_apply_apply] using horth k
  have hbal : D 0 (n 0) + D 1 (n 1) = 0 := by
    rw [hN, hN, ← C.map_add, hbalance, C.map_zero]
  have hG (k : Fin 2) : ContDiffWithinAt ℝ 1 (H k) (A k).domain (q k 0) := by
    have hg := (native_piece_chart_C1_rank_at E F (i k) (j k) (q k 0)
      (hq k h0).1 c (by rw [heq k 0 h0]; exact hc)).1
    simpa only [A, ← ((F.domain (i k)).chart (j k)).target_eq] using hg
  have hPi (k : Fin 2) : Function.Bijective
      (P.comp (fderivWithin ℝ (H k) (A k).domain (q k 0))) := by
    simpa only [A, ← ((F.domain (i k)).chart (j k)).target_eq] using hP k
  have hcoord : ContDiffAt ℝ 1 (c.chart ∘ γ) 0 :=
    (((c.smooth _ hc).contMDiffAt (c.chart.open_source.mem_nhds hc)).of_le (by simp)
      |>.comp 0 hga).contDiffAt
  have hPcurve : ContDiffAt ℝ 1 (P ∘ c.chart ∘ γ) 0 :=
    P.contDiff.contDiffAt.comp 0 hcoord
  have hPv : deriv (P ∘ c.chart ∘ γ) 0 = P (D 0 (v 0)) := by
    rw [hvD]
    exact (P.hasFDerivAt.comp_hasDerivAt 0
      (hcoord.differentiableAt (by norm_num)).hasDerivAt).deriv
  have hPvne : deriv (P ∘ c.chart ∘ γ) 0 ≠ 0 := by
    rw [hPv]
    exact (hP 0).1.ne (hvne 0) |>.trans_eq (map_zero _)
  rw [((F.domain (i 0)).chart (j 0)).target_eq, ((F.domain (i 1)).chart (j 1)).target_eq]
  apply two_sector_projection_collisions_are_same_point A H q v n (c.chart ∘ γ) hv (P := P)
  · intro k
    filter_upwards [hU.mem_nhds h0] with t ht
    simpa only [A, ← ((F.domain (i k)).chart (j k)).target_eq] using hq k ht
  · intro k
    filter_upwards [hU.mem_nhds h0] with t ht
    exact congrArg c.chart (heq k t ht)
  · intro k
    by_cases he : q k 0 = 0
    · exact Or.inr (native_regular_seam_through_sector_origin E F (i k) (j k)
        U hU h0 γ (q k) hγ hreg (hq k) (heq k) he c hc).2
    · exact Or.inl he
  · exact hG
  · exact hframe
  · intro k
    simpa only [A, ← ((F.domain (i k)).chart (j k)).target_eq] using hinward k
  · simpa only [D, A, ← ((F.domain (i 0)).chart (j 0)).target_eq,
      ← ((F.domain (i 1)).chart (j 1)).target_eq] using hbal
  · exact hPi
  · exact hPcurve
  · exact hPvne

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
