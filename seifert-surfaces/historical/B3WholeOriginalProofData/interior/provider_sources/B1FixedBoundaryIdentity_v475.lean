import B1RelativeVariationMinimum_v475
import B1SectorCornerCover

noncomputable section
open Set Topology Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
private theorem native_geometric_identity_source_subdivision_v475 {S : CompactOrientedSurface.{v}}
    (F : GeometricPiecewiseSurface S E.Carrier) :
    Nonempty (GeometricSourceMap F F (id : S → S)) := by
  classical
  have hsectorCover (P : CompactSectorPiece.{v}) :
      ∃ n : ℕ, ∃ Q : Fin n → CompactCornerPiece.{v},
        ∃ j : Fin n → Fin P.count, ∃ p : (i : Fin n) → C(Q i, P),
          (∀ i, IsEmbedding (p i)) ∧
          (∀ i, MapsTo (p i) univ (P.chart (j i)).map.source) ∧
          (⋃ i, Set.range (p i)) = univ ∧
          (∀ i, ContMDiff CornerModel 𝓘(ℝ, Euc 2) ∞
            ((P.chart (j i)).map ∘ p i)) ∧
          (∀ i x, Function.Injective (mfderiv CornerModel 𝓘(ℝ, Euc 2)
            ((P.chart (j i)).map ∘ p i) x)) ∧
          (∀ i, MapsTo ((P.chart (j i)).map ∘ p i) (CornerModel.interior (Q i))
            (interior (P.chart (j i)).map.target)) := by
    -- Exact underlying-sector cover construction in requests/SectorCornerCover.lean.
    exact SeifertSurfaces.OriginalEndpoints.sector_corner_chart_cover_exists P
  choose n Q j p hemb hsub hcover hc1 hr hi using fun i => hsectorCover (F.domain i)
  let Index := Σ i : Fin F.pieceCount, Fin (n i)
  let e : Fin (Fintype.card Index) ≃ Index := (Fintype.equivFin Index).symm
  let domain (a : Fin (Fintype.card Index)) : CompactCornerPiece.{v} :=
    Q (e a).1 (e a).2
  let param (a : Fin (Fintype.card Index)) : C(domain a, S) :=
    (F.parametrization (e a).1).comp (p (e a).1 (e a).2)
  have hcomposition (i : Fin F.pieceCount) (k : Fin (n i)) :
      F.map ∘ F.parametrization i ∘ p i k =
        sectorCoordinateMap (F.map ∘ F.parametrization i) (j i k) ∘
          (((F.domain i).chart (j i k)).map ∘ p i k) := by
    funext q
    exact congrArg (fun z => F.map (F.parametrization i z))
      (((F.domain i).chart (j i k)).map.left_inv (hsub i k (mem_univ q))).symm
  have htarget (i : Fin F.pieceCount) (k : Fin (n i)) :
      MapsTo (((F.domain i).chart (j i k)).map ∘ p i k) univ
        ((F.domain i).chart (j i k)).map.target := by
    intro q hq
    exact ((F.domain i).chart (j i k)).map.map_source (hsub i k (mem_univ q))
  have hmapC1 (i : Fin F.pieceCount) (k : Fin (n i)) :
      ContMDiff CornerModel (𝓡∂ 3) 1 (F.map ∘ F.parametrization i ∘ p i k) := by
    rw [hcomposition]
    exact (F.piece_c1 i (j i k)).comp_contMDiff ((hc1 i k).of_le (by simp))
      (fun q => htarget i k (mem_univ q))
  have hmapRank (i : Fin F.pieceCount) (k : Fin (n i)) (q : Q i k) :
      Function.Injective (mfderiv CornerModel (𝓡∂ 3)
        (F.map ∘ F.parametrization i ∘ p i k) q) := by
    rw [hcomposition, ← mfderivWithin_univ]
    rw [mfderivWithin_comp q
      ((F.piece_c1 i (j i k)).mdifferentiableOn (by simp) _
        (htarget i k (mem_univ q)))
      ((hc1 i k).mdifferentiableAt (by simp)).mdifferentiableWithinAt
      (htarget i k) (uniqueMDiffWithinAt_univ CornerModel)]
    rw [mfderivWithin_univ]
    exact (F.piece_differential_injective i (j i k) _
      (htarget i k (mem_univ q))).comp (hr i k q)
  have hmapSmooth (i : Fin F.pieceCount) (k : Fin (n i)) :
      ContMDiffOn CornerModel (𝓡∂ 3) ∞ (F.map ∘ F.parametrization i ∘ p i k)
        (CornerModel.interior (Q i k)) := by
    rw [hcomposition]
    exact (F.piece_smooth_interior i (j i k)).comp (hc1 i k).contMDiffOn (hi i k)
  have hparamCover : (⋃ a, Set.range (param a)) = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ i, Set.range (F.parametrization i) := by rw [F.covers]; trivial
    rcases mem_iUnion.mp hx with ⟨i, q, rfl⟩
    have hq : q ∈ ⋃ k, Set.range (p i k) := by rw [hcover i]; trivial
    rcases mem_iUnion.mp hq with ⟨k, z, rfl⟩
    obtain ⟨a, ha⟩ := e.surjective ⟨i, k⟩
    refine mem_iUnion.mpr ⟨a, ?_⟩
    change (F.parametrization i) ((p i k) z) ∈ Set.range
      (fun q : Q (e a).1 (e a).2 =>
        (F.parametrization (e a).1) ((p (e a).1 (e a).2) q))
    rw [ha]
    exact ⟨z, rfl⟩
  refine ⟨{
    count := Fintype.card Index
    domain := domain
    parametrization := param
    embedding := fun a => (F.parametrization_embedding (e a).1).comp (hemb (e a).1 (e a).2)
    covers := hparamCover
    source_c1 := fun a => hmapC1 (e a).1 (e a).2
    source_injective := fun a => hmapRank (e a).1 (e a).2
    source_smooth_interior := fun a => hmapSmooth (e a).1 (e a).2
    target_c1 := fun a => hmapC1 (e a).1 (e a).2
    target_injective := fun a => hmapRank (e a).1 (e a).2
    target_smooth_interior := fun a => hmapSmooth (e a).1 (e a).2 }⟩

set_option backward.isDefEq.respectTransparency true in
private theorem native_geometric_static_cylinder_subdivision_v475 {S : CompactOrientedSurface.{v}}
    (F : GeometricPiecewiseSurface S E.Carrier) :
    Nonempty (GeometricTrack F (fun p : Time × S => F.map p.2)) := by
  classical
  have hmodelDiffeo : Nonempty (Diffeomorph (modelWithCornersEuclideanQuadrant 3)
      ((𝓡∂ 1).prod CornerModel) (EuclideanQuadrant 3)
      (ModelProd (EuclideanHalfSpace 1) (EuclideanQuadrant 2)) ∞) := by
    let split : Euc 3 → Euc 1 × Euc 2 := fun x => (!₂[x 0], !₂[x 1, x 2])
    let join : Euc 1 × Euc 2 → Euc 3 := fun p => !₂[p.1 0, p.2 0, p.2 1]
    have hsplit : ContDiff ℝ ∞ split := by
      have ha : ContDiff ℝ ∞ (fun x : Euc 3 => (!₂[x 0] : Euc 1)) := by
        apply (contDiff_piLp 2).mpr
        intro i
        fin_cases i
        exact contDiff_piLp_apply 2
      have hb : ContDiff ℝ ∞ (fun x : Euc 3 => (!₂[x 1, x 2] : Euc 2)) := by
        apply (contDiff_piLp 2).mpr
        intro i
        fin_cases i <;> exact contDiff_piLp_apply 2
      exact ha.prodMk hb
    have hjoin : ContDiff ℝ ∞ join := by
      apply (contDiff_piLp 2).mpr
      intro i
      fin_cases i
      · change ContDiff ℝ ∞ (fun p : Euc 1 × Euc 2 => p.1 0)
        exact (contDiff_piLp_apply 2).comp contDiff_fst
      · change ContDiff ℝ ∞ (fun p : Euc 1 × Euc 2 => p.2 0)
        exact (contDiff_piLp_apply 2).comp contDiff_snd
      · change ContDiff ℝ ∞ (fun p : Euc 1 × Euc 2 => p.2 1)
        exact (contDiff_piLp_apply 2).comp contDiff_snd
    let e : EuclideanQuadrant 3 ≃ₜ
        ModelProd (EuclideanHalfSpace 1) (EuclideanQuadrant 2) := {
      toFun := fun q => (⟨!₂[q.val 0], q.property 0⟩,
        ⟨!₂[q.val 1, q.val 2], by
          intro i
          fin_cases i
          · exact q.property 1
          · exact q.property 2⟩)
      invFun := fun p => ⟨!₂[p.1.val 0, p.2.val 0, p.2.val 1], by
        intro i; fin_cases i
        · exact p.1.property
        · exact p.2.property 0
        · exact p.2.property 1⟩
      left_inv := by intro q; apply Subtype.ext; ext i; fin_cases i <;> rfl
      right_inv := by
        intro p; apply Prod.ext
        · apply Subtype.ext; ext i; fin_cases i; rfl
        · apply Subtype.ext; ext i; fin_cases i <;> rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    have hs : ContMDiff (modelWithCornersEuclideanQuadrant 3)
        𝓘(ℝ, Euc 1 × Euc 2) ∞
        (split ∘ modelWithCornersEuclideanQuadrant 3) :=
      hsplit.contMDiff.comp (modelWithCornersEuclideanQuadrant 3).contMDiff
    have ht : ∀ q : EuclideanQuadrant 3,
        split (modelWithCornersEuclideanQuadrant 3 q) ∈ range ((𝓡∂ 1).prod CornerModel) := by
      intro q
      exact ⟨e q, rfl⟩
    have hforward : ContMDiff (modelWithCornersEuclideanQuadrant 3)
        ((𝓡∂ 1).prod CornerModel) ∞ e := by
      have h := ((𝓡∂ 1).prod CornerModel).contMDiffOn_symm.comp_contMDiff hs ht
      convert h using 1
      funext q
      change e q = ((𝓡∂ 1).prod CornerModel).symm
        (((𝓡∂ 1).prod CornerModel) (e q))
      exact (((𝓡∂ 1).prod CornerModel).left_inv (e q)).symm
    have hs' : ContMDiff ((𝓡∂ 1).prod CornerModel) 𝓘(ℝ, Euc 3) ∞
        (join ∘ ((𝓡∂ 1).prod CornerModel)) :=
      hjoin.contMDiff.comp ((𝓡∂ 1).prod CornerModel).contMDiff
    have ht' : ∀ p : ModelProd (EuclideanHalfSpace 1) (EuclideanQuadrant 2),
        join (((𝓡∂ 1).prod CornerModel) p) ∈ range (modelWithCornersEuclideanQuadrant 3) := by
      intro p
      exact ⟨e.symm p, rfl⟩
    have hbackward : ContMDiff ((𝓡∂ 1).prod CornerModel)
        (modelWithCornersEuclideanQuadrant 3) ∞ e.symm := by
      have h := (modelWithCornersEuclideanQuadrant 3).contMDiffOn_symm.comp_contMDiff hs' ht'
      convert h using 1
      funext p
      change e.symm p = (modelWithCornersEuclideanQuadrant 3).symm
        ((modelWithCornersEuclideanQuadrant 3) (e.symm p))
      exact ((modelWithCornersEuclideanQuadrant 3).left_inv (e.symm p)).symm
    exact ⟨{
      toEquiv := e.toEquiv
      contMDiff_toFun := hforward
      contMDiff_invFun := hbackward }⟩
  have hidentity : Nonempty (GeometricSourceMap F F (id : S → S)) := by
    -- Use the exact first anchor only after its body passes the clean proof gates.
    exact native_geometric_identity_source_subdivision_v475 F
  have hproductModel (P : CompactCornerPiece.{v}) :
      ∃ Q : CompactCornerPrism.{v},
        Nonempty (Diffeomorph (modelWithCornersEuclideanQuadrant 3)
          ((𝓡∂ 1).prod CornerModel) Q (Time × P) ∞) := by
    let e := hmodelDiffeo.some
    let H := ModelProd (EuclideanHalfSpace 1) (EuclideanQuadrant 2)
    let J := ((𝓡∂ 1).prod CornerModel)
    let I := modelWithCornersEuclideanQuadrant 3
    let he := e.toHomeomorph.toOpenPartialHomeomorph
    let cs : ChartedSpace (EuclideanQuadrant 3) (Time × P) := {
      atlas := (fun c : OpenPartialHomeomorph (Time × P) H => c.trans he.symm) ''
        atlas H (Time × P)
      chartAt := fun x => (chartAt H x).trans he.symm
      mem_chart_source := by intro x; simp [he, mfld_simps]
      chart_mem_atlas := by
        intro x
        exact ⟨chartAt H x, chart_mem_atlas H x, rfl⟩ }
    letI : ChartedSpace (EuclideanQuadrant 3) (Time × P) := cs
    have hs : IsManifold I ∞ (Time × P) := by
      apply isManifold_of_contDiffOn I ∞ (Time × P)
      intro c d hc hd
      obtain ⟨a, ha, rfl⟩ := hc
      obtain ⟨b, hb, rfl⟩ := hd
      have ht : ContMDiffOn J J ∞ (a.symm.trans b) (a.symm.trans b).source :=
        contMDiffOn_of_mem_contDiffGroupoid ((contDiffGroupoid ∞ J).compatible ha hb)
      have hu : ContMDiffOn I I ∞ ((a.trans he.symm).symm.trans (b.trans he.symm))
          ((a.trans he.symm).symm.trans (b.trans he.symm)).source := by
        have hm : MapsTo e ((a.trans he.symm).symm.trans (b.trans he.symm)).source
            (a.symm.trans b).source := by
          intro q hq
          simpa only [he, mfld_simps, Diffeomorph.coe_toHomeomorph] using hq
        have h := e.symm.contMDiff.comp_contMDiffOn
          (ht.comp e.contMDiff.contMDiffOn hm)
        simpa only [he, mfld_simps, Function.comp_def,
          Diffeomorph.coe_toHomeomorph, Diffeomorph.coe_toHomeomorph_symm] using h
      exact (I.contMDiff.comp_contMDiffOn
        (hu.comp (I.contMDiffOn_symm.mono inter_subset_right)
          (by intro x hx; exact hx.1))).contDiffOn
    letI : IsManifold I ∞ (Time × P) := hs
    let Q : CompactCornerPrism.{v} := {carrier := Time × P}
    have hf : ContMDiff I J ∞ (id : Q → Time × P) := by
      intro x
      apply contMDiffWithinAt_iff'.mpr
      refine ⟨continuousWithinAt_id, ?_⟩
      have h := J.contMDiff.comp e.contMDiff
      have hext : ∀ y ∈ (extChartAt I x).target,
          extChartAt J x (id ((extChartAt I x).symm y)) =
            J (e (I.symm y)) := by
        intro y hy
        change J ((chartAt H x) ((chartAt H x).symm (e (I.symm y)))) = J (e (I.symm y))
        have ht : e (I.symm y) ∈ (chartAt H x).target := by
          rw [extChartAt, OpenPartialHomeomorph.extend_target] at hy
          have ht := hy.1
          change I.symm y ∈ ((chartAt H x).trans he.symm).target at ht
          simpa only [he, mfld_simps, Diffeomorph.coe_toHomeomorph] using ht
        exact congrArg J ((chartAt H x).right_inv ht)
      have hc : ContDiffOn ℝ ∞ (J ∘ e ∘ I.symm) (range I) :=
        (h.comp_contMDiffOn I.contMDiffOn_symm).contDiffOn
      have hx : extChartAt I x x ∈ (extChartAt I x).target :=
        (extChartAt I x).map_source (mem_extChartAt_source x)
      have hsmall := hc.mono (extChartAt_target_subset_range x)
      apply ((hsmall _ hx).mono inter_subset_left).congr_of_mem
      · intro y hy
        exact hext y hy.1
      · refine ⟨hx, ?_⟩
        change (extChartAt I x).symm (extChartAt I x x) ∈ univ ∩ (extChartAt J x).source
        rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
        exact ⟨trivial, mem_extChartAt_source x⟩
    have hb : ContMDiff J I ∞ (id : Time × P → Q) := by
      intro x
      apply contMDiffWithinAt_iff'.mpr
      refine ⟨continuousWithinAt_id, ?_⟩
      have h := I.contMDiff.comp e.symm.contMDiff
      have hext : ∀ y ∈ (extChartAt J x).target,
          extChartAt I x (id ((extChartAt J x).symm y)) =
            I (e.symm (J.symm y)) := by
        intro y hy
        change I (e.symm ((chartAt H x) ((chartAt H x).symm (J.symm y)))) =
          I (e.symm (J.symm y))
        have ht : J.symm y ∈ (chartAt H x).target := by
          rw [extChartAt, OpenPartialHomeomorph.extend_target] at hy
          exact hy.1
        exact congrArg (I ∘ e.symm) ((chartAt H x).right_inv ht)
      have hc : ContDiffOn ℝ ∞ (I ∘ e.symm ∘ J.symm) (range J) :=
        (h.comp_contMDiffOn J.contMDiffOn_symm).contDiffOn
      have hx : extChartAt J x x ∈ (extChartAt J x).target :=
        (extChartAt J x).map_source (mem_extChartAt_source x)
      have hsmall := hc.mono (extChartAt_target_subset_range x)
      apply ((hsmall _ hx).mono inter_subset_left).congr_of_mem
      · intro y hy
        exact hext y hy.1
      · refine ⟨hx, ?_⟩
        change (extChartAt J x).symm (extChartAt J x x) ∈ univ ∩ (extChartAt I x).source
        rw [(extChartAt J x).left_inv (mem_extChartAt_source x)]
        exact ⟨trivial, mem_extChartAt_source x⟩
    exact ⟨Q, ⟨{
      toEquiv := Equiv.refl (Time × P)
      contMDiff_toFun := hf
      contMDiff_invFun := hb }⟩⟩
  let anchor := hidentity.some
  choose prism hdiffeo using fun i => hproductModel (anchor.domain i)
  let modelDiffeo (i : Fin anchor.count) := (hdiffeo i).some
  let param (i : Fin anchor.count) : C(prism i, Time × S) :=
    ⟨fun q => ((modelDiffeo i q).1, anchor.parametrization i (modelDiffeo i q).2),
      ((continuous_id.prodMap (anchor.parametrization i).continuous).comp
        (modelDiffeo i).continuous)⟩
  have hemb (i : Fin anchor.count) : IsEmbedding (param i) :=
    ((Homeomorph.refl Time).isEmbedding.prodMap (anchor.embedding i)).comp
      (modelDiffeo i).toHomeomorph.isEmbedding
  have hcover : (⋃ i, Set.range (param i)) = univ := by
    apply eq_univ_of_forall
    intro p
    have hp : p.2 ∈ ⋃ i, Set.range (anchor.parametrization i) := by rw [anchor.covers]; trivial
    rcases mem_iUnion.mp hp with ⟨i, q, hq⟩
    refine mem_iUnion.mpr ⟨i, (modelDiffeo i).symm (p.1, q), ?_⟩
    change ((modelDiffeo i ((modelDiffeo i).symm (p.1, q))).1,
      anchor.parametrization i (modelDiffeo i ((modelDiffeo i).symm (p.1, q))).2) = p
    rw [(modelDiffeo i).apply_symm_apply]
    exact Prod.ext rfl hq
  have hgraphC1 (i : Fin anchor.count) :
      ContMDiff (modelWithCornersEuclideanQuadrant 3) ((𝓡∂ 1).prod (𝓡∂ 3)) 1
        (fun q => ((param i q).1, F.map (param i q).2)) :=
    (contMDiff_id.prodMap (anchor.source_c1 i)).comp
      ((modelDiffeo i).contMDiff.of_le (by simp))
  have hgraphRank (i : Fin anchor.count) (q : prism i) :
      Function.Injective (mfderiv (modelWithCornersEuclideanQuadrant 3)
        ((𝓡∂ 1).prod (𝓡∂ 3))
        (fun q => ((param i q).1, F.map (param i q).2)) q) := by
    change Function.Injective (mfderiv (modelWithCornersEuclideanQuadrant 3)
      ((𝓡∂ 1).prod (𝓡∂ 3))
      (Prod.map (id : Time → Time) (F.map ∘ anchor.parametrization i) ∘ modelDiffeo i) q)
    rw [mfderiv_comp q
      ((contMDiff_id.prodMap (anchor.source_c1 i)).mdifferentiableAt (by simp))
      ((modelDiffeo i).contMDiff.mdifferentiableAt (by simp))]
    apply Function.Injective.comp _
      ((modelDiffeo i).mfderivToContinuousLinearEquiv (by simp) q).injective
    rw [mfderiv_prodMap mdifferentiableAt_id
      ((anchor.source_c1 i).mdifferentiableAt (by simp)), mfderiv_id]
    intro u w huw
    change (u.1, mfderiv CornerModel (𝓡∂ 3) (F.map ∘ anchor.parametrization i)
      ((modelDiffeo i q).2) u.2) =
      (w.1, mfderiv CornerModel (𝓡∂ 3) (F.map ∘ anchor.parametrization i)
        ((modelDiffeo i q).2) w.2) at huw
    apply Prod.ext
    · exact congrArg (fun p : TangentSpace (𝓡∂ 1) ((modelDiffeo i q).1) ×
        TangentSpace (𝓡∂ 3) (F.map (anchor.parametrization i (modelDiffeo i q).2)) =>
          p.1) huw
    · exact anchor.source_injective i _ (congrArg
        (fun p : TangentSpace (𝓡∂ 1) ((modelDiffeo i q).1) ×
          TangentSpace (𝓡∂ 3) (F.map (anchor.parametrization i (modelDiffeo i q).2)) =>
            p.2) huw)
  have hgraphSmooth (i : Fin anchor.count) :
      ContMDiffOn (modelWithCornersEuclideanQuadrant 3) ((𝓡∂ 1).prod (𝓡∂ 3)) ∞
        (fun q => ((param i q).1, F.map (param i q).2))
        ((modelWithCornersEuclideanQuadrant 3).interior (prism i)) := by
    have hs : ContMDiffOn ((𝓡∂ 1).prod CornerModel) ((𝓡∂ 1).prod (𝓡∂ 3)) ∞
        (Prod.map (id : Time → Time) (F.map ∘ anchor.parametrization i))
        (((𝓡∂ 1).prod CornerModel).interior (Time × anchor.domain i)) := by
      rw [ModelWithCorners.interior_prod]
      exact contMDiff_id.contMDiffOn.prodMap (anchor.source_smooth_interior i)
    apply hs.comp (modelDiffeo i).contMDiff.contMDiffOn
    intro q hq
    change q ∈ (modelDiffeo i) ⁻¹'
      (((𝓡∂ 1).prod CornerModel).interior (Time × anchor.domain i))
    rw [(modelDiffeo i).preimage_interior (by simp)]
    exact hq
  exact ⟨{
    count := anchor.count
    prism := prism
    parametrization := param
    embedding := hemb
    covers := hcover
    source_c1 := hgraphC1
    source_injective := hgraphRank
    source_smooth_interior := hgraphSmooth
    target_c1 := hgraphC1
    target_injective := hgraphRank
    target_smooth_interior := hgraphSmooth }⟩

theorem native_fixed_boundary_image_isotopic_refl_v475
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier) :
    FixedBoundaryImageIsotopic E F F := by
  classical
  obtain ⟨D⟩ := native_geometric_identity_source_subdivision_v475 F
  obtain ⟨H⟩ := native_geometric_static_cylinder_subdivision_v475 F
  let e : GeometricSourceHomeomorph F F := {
    homeomorph := Homeomorph.refl S
    forward := D
    backward := D
    boundary_image := by simp }
  refine ⟨e, fun _ => F, F.map.continuous.comp continuous_snd, ⟨H⟩, rfl, ?_, ?_⟩
  · rfl
  · intro t x hx
    rfl
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_fixed_boundary_image_isotopic_refl_v475
