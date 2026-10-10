import A5NativeTwoSectorProjection
import A5RegularProjectionInjectivity
import A5LocalSheetIsolation

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- The actual two native sheets and their opposite metric conormals make a
transverse projection a local homeomorphism at the ordinary interior seam.
All coordinate regularity, small-sheet isolation and openness are derived. -/
theorem native_regular_seam_projection_local_homeomorph
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
    (P : Euc 3 →L[ℝ] Euc 2)
    (x : S) (hx : x ∈ (𝓡∂ 2).interior S)
    (hγx : γ 0 = E.toSphere (F.map x))
    (W : Set ThreeSphere) (hW : IsOpen W) (hxW : E.toSphere (F.map x) ∈ W)
    (hcover : ∀ z ∈ E.toSphere '' F.image ∩ W,
      ∃ k : Fin 2, z ∈ range (E.toSphere ∘ F.map ∘ F.parametrization (i k))) :
    let G := fun k => E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization (i k)) (j k)
    let N : Fin 2 → TangentSpace (𝓡 3) (γ 0) := fun k => (heq k 0 h0) ▸ mfderivWithin 𝓘(ℝ, Euc 2) (𝓡 3)
      (G k) ((F.domain (i k)).chart (j k)).map.target (q k 0) (n k)
    (∀ k, inner (N k) (N k) = 1) →
    (∀ k, inner (N k) (mfderiv 𝓘(ℝ) (𝓡 3) γ 0 1) = 0) →
    N 0 + N 1 = 0 →
    (∀ k, Function.Bijective (P.comp (fderivWithin ℝ (c.chart ∘ G k)
      ((F.domain (i k)).chart (j k)).map.target (q k 0)))) →
    IsLocalHomeomorphOn (P ∘ c.chart ∘ E.toSphere ∘ F.map) {x} := by
  dsimp only
  intro hunit horth hbalance hP
  let G := fun k => E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization (i k)) (j k)
  let H := fun k => c.chart ∘ G k
  let f := E.toSphere ∘ F.map
  let g := fun k => E.toSphere ∘ F.map ∘ F.parametrization (i k)
  have hg (k : Fin 2) : IsEmbedding (g k) :=
    IsEmbedding.subtypeVal.comp (F.piece_topological_embedding (i k))
  have hregular (k : Fin 2) : q k 0 ≠ 0 ∨ ((F.domain (i k)).chart (j k)).model.angle = Real.pi := by
    by_cases he : q k 0 = 0
    · exact Or.inr (native_regular_seam_through_sector_origin E F (i k) (j k)
        U hU h0 γ (q k) hγ hreg (hq k) (heq k) he c hc).2
    · exact Or.inl he
  obtain ⟨r, hr, hcross⟩ := native_two_sector_projection_collisions E F i j U hU h0
    γ q n hγ hreg hq heq hinward c hc inner P hunit horth hbalance hP
  have hself (k : Fin 2) : ∃ s : ℝ, 0 < s ∧
      InjOn (P ∘ H k) (Metric.ball (q k 0) s ∩ ((F.domain (i k)).chart (j k)).map.target) := by
    have hd := (native_piece_chart_C1_rank_at E F (i k) (j k) (q k 0)
      (hq k h0).1 c (by rw [heq k 0 h0]; exact hc)).1
    rw [((F.domain (i k)).chart (j k)).target_eq] at hd ⊢
    apply regular_sector_projection_injective_near _ _ _
      (by simpa only [← ((F.domain (i k)).chart (j k)).target_eq] using (hq k h0).1)
      (hregular k) hd P
    simpa only [← ((F.domain (i k)).chart (j k)).target_eq] using hP k
  choose s hs hself using hself
  let Q := fun k => ((F.domain (i k)).chart (j k)).map.source ∩
    ((F.domain (i k)).chart (j k)).map ⁻¹' Metric.ball (q k 0) (min (r k) (s k)) ∩
    (g k) ⁻¹' c.chart.source
  have hQ (k : Fin 2) : IsOpen (Q k) :=
    (((F.domain (i k)).chart (j k)).map.continuousOn.isOpen_inter_preimage
      ((F.domain (i k)).chart (j k)).source_open Metric.isOpen_ball).inter
        (c.chart.open_source.preimage (hg k).continuous)
  let a := fun k => ((F.domain (i k)).chart (j k)).map.symm (q k 0)
  have hag (k : Fin 2) : g k (a k) = f x := (heq k 0 h0).trans hγx
  have haQ (k : Fin 2) : a k ∈ Q k := by
    refine ⟨⟨((F.domain (i k)).chart (j k)).map.map_target (hq k h0).1, ?_⟩, ?_⟩
    · change ((F.domain (i k)).chart (j k)).map (a k) ∈ Metric.ball (q k 0) (min (r k) (s k))
      rw [((F.domain (i k)).chart (j k)).map.right_inv (hq k h0).1]
      exact Metric.mem_ball_self (lt_min (hr k) (hs k))
    · change g k (a k) ∈ c.chart.source
      rw [hag]
      change E.toSphere (F.map x) ∈ c.chart.source
      exact hγx ▸ hc
  have hpoint (k : Fin 2) (y : (F.domain (i k)).carrier) (hy : y ∈ Q k) :
      G k (((F.domain (i k)).chart (j k)).map y) = g k y := by
    dsimp [G, g, sectorCoordinateMap]
    rw [((F.domain (i k)).chart (j k)).map.left_inv hy.1.1]
  have hyball (k : Fin 2) (y : (F.domain (i k)).carrier) (hy : y ∈ Q k) :
      ((F.domain (i k)).chart (j k)).map y ∈
        Metric.ball (q k 0) (r k) ∩ ((F.domain (i k)).chart (j k)).map.target :=
    ⟨Metric.ball_subset_ball (min_le_left _ _) hy.1.2,
      ((F.domain (i k)).chart (j k)).map.map_source hy.1.1⟩
  have hcoll : ∀ k l y, y ∈ Q k → ∀ z, z ∈ Q l →
      (P ∘ c.chart) (g k y) = (P ∘ c.chart) (g l z) → g k y = g l z := by
    intro k l y hy z hz he
    apply c.chart.injOn hy.2 hz.2
    by_cases hkl : k = l
    · subst l
      have hecoord : (P ∘ H k) (((F.domain (i k)).chart (j k)).map y) =
          (P ∘ H k) (((F.domain (i k)).chart (j k)).map z) := by
        change P (c.chart (G k _)) = P (c.chart (G k _))
        rw [hpoint k y hy, hpoint k z hz]
        exact he
      have hyself : ((F.domain (i k)).chart (j k)).map y ∈
          Metric.ball (q k 0) (s k) ∩ ((F.domain (i k)).chart (j k)).map.target :=
        ⟨Metric.ball_subset_ball (min_le_right _ _) hy.1.2, (hyball k y hy).2⟩
      have hzself : ((F.domain (i k)).chart (j k)).map z ∈
          Metric.ball (q k 0) (s k) ∩ ((F.domain (i k)).chart (j k)).map.target :=
        ⟨Metric.ball_subset_ball (min_le_right _ _) hz.1.2, (hyball k z hz).2⟩
      have heyz := ((F.domain (i k)).chart (j k)).map.injOn hy.1.1 hz.1.1
        (hself k hyself hzself hecoord)
      rw [heyz]
    · fin_cases k <;> fin_cases l
      · exact (hkl rfl).elim
      · have hec := hcross _ (hyball 0 y hy) _ (hyball 1 z hz)
        change P (c.chart (G 0 _)) = P (c.chart (G 1 _)) → c.chart (G 0 _) = c.chart (G 1 _) at hec
        rw [hpoint 0 y hy, hpoint 1 z hz] at hec
        exact hec he
      · have hec := hcross _ (hyball 0 z hz) _ (hyball 1 y hy)
        change P (c.chart (G 0 _)) = P (c.chart (G 1 _)) → c.chart (G 0 _) = c.chart (G 1 _) at hec
        rw [hpoint 0 z hz, hpoint 1 y hy] at hec
        exact (hec he.symm).symm
      · exact (hkl rfl).elim
  apply native_local_projection_of_sheet_collisions S f
    (IsEmbedding.subtypeVal.comp F.embedding) x hx (fun k : Fin 2 => (F.domain (i k)).carrier)
    g hg a hag Q hQ haQ (W ∩ c.chart.source) (hW.inter c.chart.open_source)
    ⟨hxW, (show E.toSphere (F.map x) ∈ c.chart.source from hγx ▸ hc)⟩ (π := P ∘ c.chart)
  · intro z hz
    have hzF : z ∈ E.toSphere '' F.image := by
      obtain ⟨y, hy⟩ := hz.1
      exact ⟨F.map y, ⟨y, rfl⟩, hy⟩
    obtain ⟨k, y, hy⟩ := hcover z ⟨hzF, hz.2.1⟩
    exact ⟨k, y, hy⟩
  · exact P.continuous.comp_continuousOn (c.chart.continuousOn.mono inter_subset_right)
  · exact hcoll

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
