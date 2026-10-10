import AreaSectorImmersionSupport
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option maxSynthPendingDepth 3
set_option autoImplicit false
open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory Bundle
namespace SeifertSurfaces.MetricFoundations.AreaCertificates
open Foundations AreaAnalysis
universe u v w
noncomputable section

/-- An exact countable union of compact Lipschitz curve images. The active
index set permits the empty coordinate set without inventing a point. -/
structure CountableLipschitzCurveCover (E : Set (Euc 2)) where
  active : Set ℕ
  curve : ℕ → C(Time, Euc 2)
  bound : ℕ → NNReal
  lipschitz : ∀ n ∈ active, LipschitzWith (bound n) (curve n)
  covers : (⋃ n ∈ active, Set.range (curve n)) = E

theorem lipschitz_time_curve_volume_zero (c : C(Time, Euc 2)) (K : NNReal)
    (hc : LipschitzWith K c) : volume (Set.range c) = 0 := by
  have hfinite : (μH[1] : Measure Time) univ ≠ ⊤ := by
    rw [← (isometry_subtype_coe (s := Icc (0 : ℝ) 1)).hausdorffMeasure_image
      (Or.inl (by norm_num)) univ]
    simp only [image_univ, Subtype.range_coe, hausdorffMeasure_real]
    exact (isCompact_Icc.measure_lt_top (μ := volume)).ne
  have htime : (μH[2] : Measure Time) univ = 0 := by
    exact (Measure.hausdorffMeasure_zero_or_top (by norm_num : (1 : ℝ) < 2) univ).resolve_right
      hfinite
  have hcurve : (μH[2] : Measure (Euc 2)) (Set.range c) = 0 := by
    have h := hc.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 2) univ
    simpa only [image_univ, htime, mul_zero, nonpos_iff_eq_zero] using h
  have hd : (Module.finrank ℝ (Euc 2) : ℝ) = 2 := by simp [Euc]
  have ha := Measure.absolutelyContinuous_isAddHaarMeasure
    (volume : Measure (Euc 2)) (μH[(Module.finrank ℝ (Euc 2) : ℝ)])
  rw [hd] at ha
  exact ha hcurve

theorem countable_lipschitz_curve_cover_measurable {E : Set (Euc 2)}
    (C : CountableLipschitzCurveCover E) : MeasurableSet E := by
  rw [← C.covers]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
    (isCompact_range (C.curve n).continuous).isClosed.measurableSet

theorem countable_lipschitz_curve_cover_volume_zero {E : Set (Euc 2)}
    (C : CountableLipschitzCurveCover E) : volume E = 0 := by
  rw [← C.covers]
  apply measure_iUnion_null
  intro n
  apply measure_iUnion_null
  intro hn
  exact lipschitz_time_curve_volume_zero (C.curve n) (C.bound n) (C.lipschitz n hn)

/-- Smoothness only on the actual relatively open parameter set, endpoints
included when that set contains them. No global smooth extension is assumed. -/
theorem smooth_time_coordinate_image_curve_cover (c : Time → Euc 2)
    (A : Set Time) (hA : IsOpen A)
    (hc : ContMDiffOn (𝓡∂ 1) 𝓘(ℝ, Euc 2) ∞ c A) :
    Nonempty (CountableLipschitzCurveCover (c '' A)) := by
  classical
  have hlocal (x : Time) (hx : x ∈ A) : ∃ U : Set Time, IsOpen U ∧ x ∈ U ∧
      ∃ γ : C(Time, Euc 2), ∃ K : NNReal, LipschitzWith K γ ∧
        c '' U ⊆ range γ ∧ range γ ⊆ c '' A := by
    let proj := Set.projIcc (0 : ℝ) 1 (by norm_num : (0 : ℝ) ≤ 1)
    let f := c ∘ proj
    have hc' : ContMDiffAt (𝓡∂ 1) 𝓘(ℝ, Euc 2) ∞ c x :=
      (hc x hx).contMDiffAt (hA.mem_nhds hx)
    have hf : ContDiffWithinAt ℝ 1 f (Icc (0 : ℝ) 1) x :=
      ((contMDiffWithinAt_comp_projIcc_iff (w := x)).mpr hc').contDiffWithinAt.of_le (by simp)
    obtain ⟨K, T, hT, hLip⟩ := hf.exists_lipschitzOnWith (convex_Icc (0 : ℝ) 1)
    have hxproj : proj x = x := by simp [proj]
    have hTA : T ∩ proj ⁻¹' A ∈ 𝓝[Icc (0 : ℝ) 1] (x : ℝ) :=
      Filter.inter_mem hT (mem_nhdsWithin_of_mem_nhds
        ((hA.preimage continuous_projIcc).mem_nhds (by
          change proj x ∈ A
          simpa only [hxproj] using hx)))
    obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhdsWithin_iff.mp hTA
    let l := max 0 ((x : ℝ) - ε / 2)
    let r := min 1 ((x : ℝ) + ε / 2)
    have hxl : l ≤ (x : ℝ) := max_le x.property.1 (by linarith)
    have hxr : (x : ℝ) ≤ r := le_min x.property.2 (by linarith)
    have hlr : l ≤ r := hxl.trans hxr
    have hI (z : ℝ) (hz : z ∈ Icc l r) : z ∈ T ∩ proj ⁻¹' A := by
      apply hεT
      refine ⟨?_, ⟨(le_max_left _ _).trans hz.1, hz.2.trans (min_le_left _ _)⟩⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      have hlo := (le_max_right 0 ((x : ℝ) - ε / 2)).trans hz.1
      have hhi := hz.2.trans (min_le_right 1 ((x : ℝ) + ε / 2))
      constructor <;> linarith
    have hline (t : Time) : AffineMap.lineMap l r (t : ℝ) ∈ Icc l r := by
      rw [← segment_eq_Icc hlr]
      exact lineMap_mem_segment ℝ l r t.property
    let g : Time → Euc 2 := f ∘ (fun t => AffineMap.lineMap l r (t : ℝ))
    have hg : LipschitzWith (K * nndist l r) g := by
      have hlineLip := (lipschitzWith_lineMap l r).comp
        (isometry_subtype_coe (s := Time)).lipschitz
      intro t s
      calc
        edist (g t) (g s) ≤ K * edist (AffineMap.lineMap l r (t : ℝ))
          (AffineMap.lineMap l r (s : ℝ)) := hLip (hI _ (hline t)).1 (hI _ (hline s)).1
        _ ≤ K * ((nndist l r : ENNReal) * edist t s) :=
          mul_right_mono (by simpa using hlineLip t s)
        _ = ((K * nndist l r : NNReal) : ENNReal) * edist t s := by simp [mul_assoc]
    let γ : C(Time, Euc 2) := ⟨g, hg.continuous⟩
    let U : Set Time := (fun t : Time => (t : ℝ)) ⁻¹' Metric.ball (x : ℝ) (ε / 2)
    refine ⟨U, Metric.isOpen_ball.preimage continuous_subtype_val,
      Metric.mem_ball_self (by linarith), γ, K * nndist l r, hg, ?_, ?_⟩
    · rintro z ⟨t, ht, rfl⟩
      have htI : (t : ℝ) ∈ Icc l r := by
        have hh := abs_lt.mp (show |(t : ℝ) - (x : ℝ)| < ε / 2 from ht)
        exact ⟨max_le t.property.1 (by linarith [hh.1]),
          le_min t.property.2 (by linarith [hh.2])⟩
      have him : (t : ℝ) ∈ AffineMap.lineMap l r '' Icc (0 : ℝ) 1 := by
        rw [← segment_eq_image_lineMap, segment_eq_Icc hlr]
        exact htI
      obtain ⟨s, hs, hst⟩ := him
      refine ⟨⟨s, hs⟩, ?_⟩
      change c (proj (AffineMap.lineMap l r s)) = c t
      rw [hst]
      congr 1
      exact Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) t.property
    · rintro z ⟨t, rfl⟩
      exact ⟨proj (AffineMap.lineMap l r (t : ℝ)), (hI _ (hline t)).2, rfl⟩
  by_cases hne : A.Nonempty
  · letI : Nonempty A := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    choose U hUo hxU γ K hLip hcover hsub using fun x : A => hlocal x x.property
    obtain ⟨idx, hidx⟩ := (HereditarilyLindelofSpace.isLindelof A).indexed_countable_subcover U hUo
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
    refine ⟨⟨univ, γ ∘ idx, K ∘ idx, fun n _ => hLip (idx n), ?_⟩⟩
    ext z
    constructor
    · intro hz
      obtain ⟨n, _, hn⟩ := mem_iUnion₂.mp hz
      exact hsub (idx n) hn
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hidx hx)
      exact mem_iUnion₂.mpr ⟨n, mem_univ n, hcover (idx n) ⟨x, hn, rfl⟩⟩
  · have he : A = ∅ := not_nonempty_iff_eq_empty.mp hne
    subst A
    refine ⟨⟨∅, fun _ => ContinuousMap.const Time 0, fun _ => 0,
      fun _ h => False.elim h, ?_⟩⟩
    simp

theorem smooth_circle_coordinate_image_curve_cover (c : Circle → Euc 2)
    (A : Set Circle) (hA : IsOpen A)
    (hc : ContMDiffOn (𝓡 1) 𝓘(ℝ, Euc 2) ∞ c A) :
    Nonempty (CountableLipschitzCurveCover (c '' A)) := by
  let q : Time → Circle := fun t => Circle.exp (-Real.pi + 2 * Real.pi * (t : ℝ))
  have hq : ContMDiff (𝓡∂ 1) (𝓡 1) ∞ q := by
    have hlin : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun t : ℝ => -Real.pi + 2 * Real.pi * t) :=
      (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => -Real.pi + 2 * Real.pi * t)).contMDiff
    exact contMDiff_circleExp.comp (hlin.comp contMDiff_subtypeVal_Icc)
  have hsurj : Function.Surjective q := by
    intro z
    let t := (Complex.arg (z : ℂ) + Real.pi) / (2 * Real.pi)
    have ht : t ∈ Icc (0 : ℝ) 1 := by
      constructor
      · apply div_nonneg _ (by positivity)
        linarith [Complex.neg_pi_lt_arg (z : ℂ)]
      · apply (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr
        linarith [Complex.arg_le_pi (z : ℂ)]
    refine ⟨⟨t, ht⟩, ?_⟩
    change Circle.exp (-Real.pi + 2 * Real.pi * t) = z
    have he : -Real.pi + 2 * Real.pi * t = Complex.arg (z : ℂ) := by
      dsimp [t]
      field_simp
      ring
    rw [he, Circle.exp_arg]
  have hAc : IsOpen (q ⁻¹' A) := hA.preimage hq.continuous
  have hcomp : ContMDiffOn (𝓡∂ 1) 𝓘(ℝ, Euc 2) ∞ (c ∘ q) (q ⁻¹' A) :=
    hc.comp hq.contMDiffOn (fun _ ht => ht)
  have heq : (c ∘ q) '' (q ⁻¹' A) = c '' A := by
    rw [image_comp, image_preimage_eq A hsurj]
  rw [← heq]
  exact smooth_time_coordinate_image_curve_cover _ _ hAc hcomp

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

def oppositeCurveParameterDomain {S R : CompactOrientedSurface.{u}}
    {K : Type w} [TopologicalSpace K]
    (G : GeometricPiecewiseSurface R M) (a : R ≃ₜ S) (σ : C(K, S))
    (A : Set K) (i : Fin G.pieceCount) (j : Fin (G.domain i).count) : Set K :=
  A ∩ σ ⁻¹' (a '' (G.parametrization i ''
    ((G.domain i).interior ∩ ((G.domain i).chart j).map.source)))

/-- Totalization through the actual opposite parametrization range; outside
that range its value is irrelevant to the fixed parameter domain. -/
def oppositeCurveCoordinates {S R : CompactOrientedSurface.{u}}
    {K : Type w} [TopologicalSpace K]
    (G : GeometricPiecewiseSurface R M) (a : R ≃ₜ S) (σ : C(K, S))
    (i : Fin G.pieceCount) (j : Fin (G.domain i).count) (t : K) : Euc 2 := by
  classical
  exact if ht : a.symm (σ t) ∈ Set.range (G.parametrization i) then
    ((G.domain i).chart j).map
      ((G.parametrization_embedding i).toHomeomorph.symm ⟨a.symm (σ t), ht⟩)
  else 0

theorem opposite_curve_parameter_domain_open {S R : CompactOrientedSurface.{u}}
    {K : Type w} [TopologicalSpace K]
    (G : GeometricPiecewiseSurface R M) (a : R ≃ₜ S) (σ : C(K, S))
    (A : Set K) (hA : IsOpen A) (i : Fin G.pieceCount) (j : Fin (G.domain i).count) :
    IsOpen (oppositeCurveParameterDomain G a σ A i j) := by
  exact hA.inter ((a.isOpenMap _
    (geometric_piece_chart_interior_image_open G i j)).preimage σ.continuous)

theorem opposite_curve_coordinate_image_exact {S R : CompactOrientedSurface.{u}}
    {K : Type w} [TopologicalSpace K]
    (G : GeometricPiecewiseSurface R M) (a : R ≃ₜ S) (σ : C(K, S))
    (A : Set K) (i : Fin G.pieceCount) (j : Fin (G.domain i).count) :
    oppositePieceCoordinates G a (σ '' A) i j =
      oppositeCurveCoordinates G a σ i j '' oppositeCurveParameterDomain G a σ A i j := by
  ext z
  constructor
  · rintro ⟨q, ⟨⟨hqi, hqt⟩, hqs⟩, rfl⟩
    obtain ⟨t, ht, he⟩ := hqt
    refine ⟨t, ⟨ht, ⟨G.parametrization i q, ⟨q, ⟨hqi, hqs⟩, rfl⟩, he.symm⟩⟩, ?_⟩
    have hr : a.symm (σ t) ∈ Set.range (G.parametrization i) := by
      rw [he, Homeomorph.symm_apply_apply]
      exact ⟨q, rfl⟩
    unfold oppositeCurveCoordinates
    rw [dite_eq_left hr]
    apply congrArg ((G.domain i).chart j).map
    apply (G.parametrization_embedding i).injective
    exact (congrArg Subtype.val
      ((G.parametrization_embedding i).toHomeomorph.apply_symm_apply ⟨_, hr⟩)).trans
      (by change a.symm (σ t) = G.parametrization i q
          rw [he, Homeomorph.symm_apply_apply])
  · rintro ⟨t, ⟨ht, r, ⟨q, hq, hqr⟩, hrt⟩, rfl⟩
    have he : a (G.parametrization i q) = σ t := by rw [hqr, hrt]
    have hr : a.symm (σ t) ∈ Set.range (G.parametrization i) := by
      rw [← he, Homeomorph.symm_apply_apply]
      exact ⟨q, rfl⟩
    have hinv : (G.parametrization_embedding i).toHomeomorph.symm ⟨_, hr⟩ = q := by
      apply (G.parametrization_embedding i).injective
      exact (congrArg Subtype.val
        ((G.parametrization_embedding i).toHomeomorph.apply_symm_apply ⟨_, hr⟩)).trans
        (by change a.symm (σ t) = G.parametrization i q
            rw [← he, Homeomorph.symm_apply_apply])
    refine ⟨q, ⟨⟨hq.1, ⟨t, ht, he.symm⟩⟩, hq.2⟩, ?_⟩
    simp only [oppositeCurveCoordinates, dite_eq_left hr, hinv]

/-- Exact local inverse expression for any continuous source curve. Only
the ambient composed curve is later used to establish smoothness. -/
theorem opposite_curve_local_immersion_inverse_identity
    {S R : CompactOrientedSurface.{u}} {K : Type w} [TopologicalSpace K]
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (hmap : ∀ x, G.map x = F.map (a x)) (σ : C(K, S))
    (A : Set K) (hA : IsOpen A) (i : Fin G.pieceCount) (j : Fin (G.domain i).count)
    (t₀ : K) (ht₀ : t₀ ∈ oppositeCurveParameterDomain G a σ A i j)
    (L : SectorPieceLocalInverse G i j (oppositeCurveCoordinates G a σ i j t₀)) :
    ∃ U : Set K, IsOpen U ∧ t₀ ∈ U ∧ U ⊆ oppositeCurveParameterDomain G a σ A i j ∧
      MapsTo (oppositeCurveCoordinates G a σ i j) U L.inverse.source ∧
      MapsTo (F.map ∘ σ) U
        (extChartAt (𝓡∂ 3) (F.map (σ t₀))).source ∧
      MapsTo (extChartAt (𝓡∂ 3) (F.map (σ t₀)) ∘ F.map ∘ σ) U L.inverse.target ∧
      (∀ t ∈ U, oppositeCurveCoordinates G a σ i j t =
        L.inverse.map (extChartAt (𝓡∂ 3) (F.map (σ t₀)) (F.map (σ t)))) := by
  let D := oppositeCurveParameterDomain G a σ A i j
  let c := oppositeCurveCoordinates G a σ i j
  have hex (t : K) (ht : t ∈ D) : ∃ q : G.domain i,
      q ∈ (G.domain i).interior ∩ ((G.domain i).chart j).map.source ∧
      G.parametrization i q = a.symm (σ t) ∧ c t = ((G.domain i).chart j).map q := by
    obtain ⟨_, r, ⟨q, hq, hqr⟩, hrt⟩ := ht
    have hp : G.parametrization i q = a.symm (σ t) := by
      rw [hqr, ← hrt, Homeomorph.symm_apply_apply]
    have hr : a.symm (σ t) ∈ range (G.parametrization i) := ⟨q, hp⟩
    refine ⟨q, hq, hp, ?_⟩
    change oppositeCurveCoordinates G a σ i j t = _
    unfold oppositeCurveCoordinates
    rw [dite_eq_left hr]
    apply congrArg ((G.domain i).chart j).map
    apply (G.parametrization_embedding i).injective
    exact (congrArg Subtype.val
      ((G.parametrization_embedding i).toHomeomorph.apply_symm_apply ⟨_, hr⟩)).trans hp.symm
  have hr (t : D) : a.symm (σ t) ∈ range (G.parametrization i) := by
    obtain ⟨q, _, hp, _⟩ := hex t t.property
    exact ⟨q, hp⟩
  let lift : D → range (G.parametrization i) := fun t => ⟨a.symm (σ t), hr t⟩
  have hlift : Continuous lift :=
    (a.symm.continuous.comp (σ.continuous.comp continuous_subtype_val)).subtype_mk _
  have hsource (t : D) : (G.parametrization_embedding i).toHomeomorph.symm (lift t) ∈
      ((G.domain i).chart j).map.source := by
    obtain ⟨q, hq, hp, _⟩ := hex t t.property
    have he : (G.parametrization_embedding i).toHomeomorph.symm (lift t) = q := by
      apply (G.parametrization_embedding i).injective
      exact (congrArg Subtype.val
        ((G.parametrization_embedding i).toHomeomorph.apply_symm_apply (lift t))).trans hp.symm
    exact he ▸ hq.2
  have hc : ContinuousOn c D := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := ((G.domain i).chart j).map.continuousOn.comp_continuous
      ((G.parametrization_embedding i).toHomeomorph.symm.continuous.comp hlift) hsource
    convert h using 1
    funext t
    exact dite_eq_left (hr t)
  have hpoint (t : K) (ht : t ∈ D) :
      sectorPieceSourcePoint G i j (c t) = a.symm (σ t) := by
    obtain ⟨q, hq, hp, he⟩ := hex t ht
    simp only [sectorPieceSourcePoint, he, ((G.domain i).chart j).map.left_inv hq.2]
    exact hp
  have hmatch (t : K) (ht : t ∈ D) :
      sectorCoordinateMap (G.map ∘ G.parametrization i) j (c t) = F.map (σ t) := by
    change G.map (sectorPieceSourcePoint G i j (c t)) = _
    rw [hpoint t ht, hmap, Homeomorph.apply_symm_apply]
  have hbase : G.map (sectorPieceSourcePoint G i j (c t₀)) = F.map (σ t₀) :=
    hmatch t₀ ht₀
  let U := D ∩ c ⁻¹' L.inverse.source
  have hU : IsOpen U := hc.isOpen_inter_preimage
    (opposite_curve_parameter_domain_open G a σ A hA i j) L.inverse.open_source
  have htU : t₀ ∈ U := ⟨ht₀, L.inverse.source_mem⟩
  have hcoord (t : K) (ht : t ∈ U) : sectorPieceAmbientCoordinates G i j (c t₀) (c t) =
      extChartAt (𝓡∂ 3) (F.map (σ t₀)) (F.map (σ t)) := by
    change extChartAt (𝓡∂ 3) (G.map (sectorPieceSourcePoint G i j (c t₀)))
      (sectorCoordinateMap (G.map ∘ G.parametrization i) j (c t)) = _
    rw [hbase, hmatch t ht.1]
  refine ⟨U, hU, htU, fun t ht => ht.1, fun t ht => ht.2, ?_, ?_, ?_⟩
  · intro t ht
    have h := (L.ambient_mem (L.inverse.source_subset ht.2)).1
    change sectorCoordinateMap (G.map ∘ G.parametrization i) j (c t) ∈
      (extChartAt (𝓡∂ 3) (G.map (sectorPieceSourcePoint G i j (c t₀)))).source at h
    rwa [hbase, hmatch t ht.1] at h
  · intro t ht
    change extChartAt (𝓡∂ 3) (F.map (σ t₀)) (F.map (σ t)) ∈ L.inverse.target
    rw [← hcoord t ht]
    exact L.inverse.mapsTo ht.2
  · intro t ht
    rw [← hcoord t ht]
    exact (L.inverse.left_inverse _ ht.2).symm

theorem opposite_ambient_smooth_arc_coordinates {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (hmap : ∀ x, G.map x = F.map (a x)) (σ : C(Time, S))
    (hσ : ContMDiff (𝓡∂ 1) (𝓡∂ 3) ∞ (F.map ∘ σ))
    (A : Set Time) (hA : IsOpen A) (i : Fin G.pieceCount) (j : Fin (G.domain i).count) :
    ContMDiffOn (𝓡∂ 1) 𝓘(ℝ, Euc 2) ∞ (oppositeCurveCoordinates G a σ i j)
      (oppositeCurveParameterDomain G a σ A i j) := by
  intro t ht
  have hcoord : oppositeCurveCoordinates G a σ i j t ∈
      interior ((G.domain i).chart j).map.target := by
    have him : oppositeCurveCoordinates G a σ i j t ∈
        oppositePieceCoordinates G a (σ '' A) i j := by
      rw [opposite_curve_coordinate_image_exact]
      exact ⟨t, ht, rfl⟩
    obtain ⟨q, ⟨⟨hqi, _⟩, hqs⟩, he⟩ := him
    rw [← he, ← sector_chart_piece_interior (G.domain i) j]
    exact ⟨q, ⟨hqi, hqs⟩, rfl⟩
  obtain ⟨L⟩ := sector_piece_local_immersion_inverse G i j _ hcoord
  obtain ⟨U, hU, htU, hUD, hsrc, hamb, htar, hid⟩ :=
    opposite_curve_local_immersion_inverse_identity F G a hmap σ A hA i j t ht L
  have hmap : ContMDiffAt 𝓘(ℝ, Euc 3) 𝓘(ℝ, Euc 2) ∞ L.inverse.map
      (extChartAt (𝓡∂ 3) (F.map (σ t)) (F.map (σ t))) :=
    (L.inverse.smooth.contDiffAt (L.inverse.open_target.mem_nhds (htar htU))).contMDiffAt
  have hcompose := hmap.comp t (contMDiffAt_extChartAt.comp t hσ.contMDiffAt)
  apply (hcompose.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hU.mem_nhds htU] with z hz
  exact hid z hz

theorem opposite_ambient_smooth_circle_coordinates {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (hmap : ∀ x, G.map x = F.map (a x)) (σ : C(Circle, S))
    (hσ : ContMDiff (𝓡 1) (𝓡∂ 3) ∞ (F.map ∘ σ))
    (A : Set Circle) (hA : IsOpen A) (i : Fin G.pieceCount) (j : Fin (G.domain i).count) :
    ContMDiffOn (𝓡 1) 𝓘(ℝ, Euc 2) ∞ (oppositeCurveCoordinates G a σ i j)
      (oppositeCurveParameterDomain G a σ A i j) := by
  intro t ht
  have hcoord : oppositeCurveCoordinates G a σ i j t ∈
      interior ((G.domain i).chart j).map.target := by
    have him : oppositeCurveCoordinates G a σ i j t ∈
        oppositePieceCoordinates G a (σ '' A) i j := by
      rw [opposite_curve_coordinate_image_exact]
      exact ⟨t, ht, rfl⟩
    obtain ⟨q, ⟨⟨hqi, _⟩, hqs⟩, he⟩ := him
    rw [← he, ← sector_chart_piece_interior (G.domain i) j]
    exact ⟨q, ⟨hqi, hqs⟩, rfl⟩
  obtain ⟨L⟩ := sector_piece_local_immersion_inverse G i j _ hcoord
  obtain ⟨U, hU, htU, hUD, hsrc, hamb, htar, hid⟩ :=
    opposite_curve_local_immersion_inverse_identity F G a hmap σ A hA i j t ht L
  have hmap : ContMDiffAt 𝓘(ℝ, Euc 3) 𝓘(ℝ, Euc 2) ∞ L.inverse.map
      (extChartAt (𝓡∂ 3) (F.map (σ t)) (F.map (σ t))) :=
    (L.inverse.smooth.contDiffAt (L.inverse.open_target.mem_nhds (htar htU))).contMDiffAt
  have hcompose := hmap.comp t (contMDiffAt_extChartAt.comp t hσ.contMDiffAt)
  apply (hcompose.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hU.mem_nhds htU] with z hz
  exact hid z hz

theorem opposite_ambient_smooth_arc_curve_cover {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (hmap : ∀ x, G.map x = F.map (a x)) (σ : C(Time, S))
    (hσ : ContMDiff (𝓡∂ 1) (𝓡∂ 3) ∞ (F.map ∘ σ))
    (A : Set Time) (hA : IsOpen A) (i : Fin G.pieceCount) (j : Fin (G.domain i).count) :
    Nonempty (CountableLipschitzCurveCover (oppositePieceCoordinates G a (σ '' A) i j)) := by
  rw [opposite_curve_coordinate_image_exact]
  exact smooth_time_coordinate_image_curve_cover _ _
    (opposite_curve_parameter_domain_open G a σ A hA i j)
    (opposite_ambient_smooth_arc_coordinates F G a hmap σ hσ A hA i j)

theorem opposite_ambient_smooth_circle_curve_cover {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (hmap : ∀ x, G.map x = F.map (a x)) (σ : C(Circle, S))
    (hσ : ContMDiff (𝓡 1) (𝓡∂ 3) ∞ (F.map ∘ σ))
    (A : Set Circle) (hA : IsOpen A) (i : Fin G.pieceCount) (j : Fin (G.domain i).count) :
    Nonempty (CountableLipschitzCurveCover (oppositePieceCoordinates G a (σ '' A) i j)) := by
  rw [opposite_curve_coordinate_image_exact]
  exact smooth_circle_coordinate_image_curve_cover _ _
    (opposite_curve_parameter_domain_open G a σ A hA i j)
    (opposite_ambient_smooth_circle_coordinates F G a hmap σ hσ A hA i j)

/-- Measurability of the actual set, obtained from its countable compact
curve-image cover, accompanies zero two-dimensional coordinate volume. -/
theorem opposite_ambient_smooth_arc_coordinate_nullity {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (hmap : ∀ x, G.map x = F.map (a x)) (σ : C(Time, S))
    (hσ : ContMDiff (𝓡∂ 1) (𝓡∂ 3) ∞ (F.map ∘ σ))
    (A : Set Time) (hA : IsOpen A) (i : Fin G.pieceCount) (j : Fin (G.domain i).count) :
    volume (oppositePieceCoordinates G a (σ '' A) i j) = 0 ∧
      MeasurableSet (oppositePieceCoordinates G a (σ '' A) i j) := by
  obtain ⟨C⟩ := opposite_ambient_smooth_arc_curve_cover F G a hmap σ hσ A hA i j
  exact ⟨countable_lipschitz_curve_cover_volume_zero C,
    countable_lipschitz_curve_cover_measurable C⟩

theorem opposite_ambient_smooth_circle_coordinate_nullity {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (hmap : ∀ x, G.map x = F.map (a x)) (σ : C(Circle, S))
    (hσ : ContMDiff (𝓡 1) (𝓡∂ 3) ∞ (F.map ∘ σ))
    (A : Set Circle) (hA : IsOpen A) (i : Fin G.pieceCount) (j : Fin (G.domain i).count) :
    volume (oppositePieceCoordinates G a (σ '' A) i j) = 0 ∧
      MeasurableSet (oppositePieceCoordinates G a (σ '' A) i j) := by
  obtain ⟨C⟩ := opposite_ambient_smooth_circle_curve_cover F G a hmap σ hσ A hA i j
  exact ⟨countable_lipschitz_curve_cover_volume_zero C,
    countable_lipschitz_curve_cover_measurable C⟩

/-- A separate topological measurability bridge for the full actual closed
opposite seam; it does not substitute NullMeasurableSet for MeasurableSet. -/
theorem opposite_closed_source_coordinates_measurable {S R : CompactOrientedSurface.{u}}
    (G : GeometricPiecewiseSurface R M) (a : R ≃ₜ S) (E : Set S) (hE : IsClosed E)
    (i : Fin G.pieceCount) (j : Fin (G.domain i).count) :
    MeasurableSet (oppositePieceCoordinates G a E i j) := by
  let c := ((G.domain i).chart j).map
  have hc : ContinuousOn (a ∘ G.parametrization i ∘ c.symm) (interior c.target) :=
    a.continuous.comp_continuousOn ((G.parametrization i).continuous.comp_continuousOn
      (c.symm.continuousOn.mono interior_subset))
  obtain ⟨B, hB, heB⟩ := continuousOn_iff_isClosed.mp hc E hE
  have heq : oppositePieceCoordinates G a E i j =
      (a ∘ G.parametrization i ∘ c.symm) ⁻¹' E ∩ interior c.target := by
    ext z
    constructor
    · rintro ⟨q, ⟨⟨hqi, hqE⟩, hqs⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa only [mem_preimage, Function.comp_apply, c, c.left_inv hqs] using hqE
      · rw [← sector_chart_piece_interior (G.domain i) j]
        exact ⟨q, ⟨hqi, hqs⟩, rfl⟩
    · rintro ⟨hzE, hzt⟩
      have hq := sector_chart_inverse_interior (G.domain i) j hzt
      exact ⟨c.symm z, ⟨⟨hq.1, hzE⟩, hq.2⟩, c.right_inv (interior_subset hzt)⟩
  rw [heq, heB]
  exact hB.measurableSet.inter isOpen_interior.measurableSet

end
end SeifertSurfaces.MetricFoundations.AreaCertificates
