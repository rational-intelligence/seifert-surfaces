import OriginalA25SourceDefinitionsV464

open Set Topology Function
open scoped Manifold ContDiff

namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.A6Construction
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe v
noncomputable section
set_option autoImplicit false

private theorem sector_corner_chart_cover_exists (P : CompactSectorPiece.{v}) :
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
  classical
  have hstandard : ∃ Q : CompactCornerPiece.{0},
      Nonempty (Diffeomorph CornerModel ((𝓡∂ 1).prod (𝓡∂ 1)) Q (Time × Time) ∞) := by
    classical
    have hmodelDiffeo : Nonempty (Diffeomorph CornerModel
        ((𝓡∂ 1).prod (𝓡∂ 1)) (EuclideanQuadrant 2)
          (ModelProd (EuclideanHalfSpace 1) (EuclideanHalfSpace 1)) ∞) := by
      let split : Euc 2 → Euc 1 × Euc 1 := fun x => (!₂[x 0], !₂[x 1])
      let join : Euc 1 × Euc 1 → Euc 2 := fun p => !₂[p.1 0, p.2 0]
      have hsplit : ContDiff ℝ ∞ split := by
        have ha : ContDiff ℝ ∞ (fun x : Euc 2 => (!₂[x 0] : Euc 1)) := by
          apply (contDiff_piLp 2).mpr
          intro i
          fin_cases i
          exact contDiff_piLp_apply 2
        have hb : ContDiff ℝ ∞ (fun x : Euc 2 => (!₂[x 1] : Euc 1)) := by
          apply (contDiff_piLp 2).mpr
          intro i
          fin_cases i
          exact contDiff_piLp_apply 2
        exact ha.prodMk hb
      have hjoin : ContDiff ℝ ∞ join := by
        apply (contDiff_piLp 2).mpr
        intro i
        fin_cases i
        · change ContDiff ℝ ∞ (fun p : Euc 1 × Euc 1 => p.1 0)
          exact (contDiff_piLp_apply 2).comp contDiff_fst
        · change ContDiff ℝ ∞ (fun p : Euc 1 × Euc 1 => p.2 0)
          exact (contDiff_piLp_apply 2).comp contDiff_snd
      let e : EuclideanQuadrant 2 ≃ₜ
          ModelProd (EuclideanHalfSpace 1) (EuclideanHalfSpace 1) := {
        toFun := fun q => (⟨!₂[q.val 0], q.property 0⟩, ⟨!₂[q.val 1], q.property 1⟩)
        invFun := fun p => ⟨!₂[p.1.val 0, p.2.val 0], by
          intro i
          fin_cases i
          · exact p.1.property
          · exact p.2.property⟩
        left_inv := by intro q; apply Subtype.ext; ext i; fin_cases i <;> rfl
        right_inv := by
          intro p
          apply Prod.ext <;> apply Subtype.ext <;> ext i <;> fin_cases i <;> rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
      have hs : ContMDiff CornerModel 𝓘(ℝ, Euc 1 × Euc 1) ∞ (split ∘ CornerModel) :=
        hsplit.contMDiff.comp CornerModel.contMDiff
      have ht : ∀ q : EuclideanQuadrant 2,
          split (CornerModel q) ∈ range ((𝓡∂ 1).prod (𝓡∂ 1)) := by
        intro q
        exact ⟨e q, rfl⟩
      have hforward : ContMDiff CornerModel ((𝓡∂ 1).prod (𝓡∂ 1)) ∞ e := by
        have h := ((𝓡∂ 1).prod (𝓡∂ 1)).contMDiffOn_symm.comp_contMDiff hs ht
        convert h using 1
        funext q
        change e q = ((𝓡∂ 1).prod (𝓡∂ 1)).symm (((𝓡∂ 1).prod (𝓡∂ 1)) (e q))
        exact (((𝓡∂ 1).prod (𝓡∂ 1)).left_inv (e q)).symm
      have hs' : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, Euc 2) ∞
          (join ∘ ((𝓡∂ 1).prod (𝓡∂ 1))) :=
        hjoin.contMDiff.comp ((𝓡∂ 1).prod (𝓡∂ 1)).contMDiff
      have ht' : ∀ p : ModelProd (EuclideanHalfSpace 1) (EuclideanHalfSpace 1),
          join (((𝓡∂ 1).prod (𝓡∂ 1)) p) ∈ range CornerModel := by
        intro p
        exact ⟨e.symm p, rfl⟩
      have hbackward : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) CornerModel ∞ e.symm := by
        have h := CornerModel.contMDiffOn_symm.comp_contMDiff hs' ht'
        convert h using 1
        funext p
        change e.symm p = CornerModel.symm (CornerModel (e.symm p))
        exact (CornerModel.left_inv (e.symm p)).symm
      exact ⟨{toEquiv := e.toEquiv, contMDiff_toFun := hforward, contMDiff_invFun := hbackward}⟩
    let e := hmodelDiffeo.some
    let H := ModelProd (EuclideanHalfSpace 1) (EuclideanHalfSpace 1)
    let J := ((𝓡∂ 1).prod (𝓡∂ 1))
    let I := modelWithCornersEuclideanQuadrant 2
    let he := e.toHomeomorph.toOpenPartialHomeomorph
    let cs : ChartedSpace (EuclideanQuadrant 2) (Time × Time) := {
      atlas := (fun c : OpenPartialHomeomorph (Time × Time) H => c.trans he.symm) ''
        atlas H (Time × Time)
      chartAt := fun x => (chartAt H x).trans he.symm
      mem_chart_source := by intro x; simp [he, mfld_simps]
      chart_mem_atlas := by
        intro x
        exact ⟨chartAt H x, chart_mem_atlas H x, rfl⟩ }
    letI : ChartedSpace (EuclideanQuadrant 2) (Time × Time) := cs
    have hs : IsManifold I ∞ (Time × Time) := by
      apply isManifold_of_contDiffOn I ∞ (Time × Time)
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
    letI : IsManifold I ∞ (Time × Time) := hs
    let Q : CompactCornerPiece.{0} := {carrier := Time × Time}
    have hf : ContMDiff I J ∞ (id : Q → Time × Time) := by
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
    have hb : ContMDiff J I ∞ (id : Time × Time → Q) := by
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
      toEquiv := Equiv.refl (Time × Time)
      contMDiff_toFun := hf
      contMDiff_invFun := hb }⟩⟩
  have hlift (P : CompactCornerPiece.{0}) :
      ∃ Q : CompactCornerPiece.{v}, Nonempty (Diffeomorph CornerModel CornerModel Q P ∞) := by
    classical
    let down : ULift.{v} P ≃ₜ P := Homeomorph.ulift
    let hd := down.toOpenPartialHomeomorph
    let H := EuclideanQuadrant 2
    let I := CornerModel
    let cs : ChartedSpace H (ULift.{v} P) := {
      atlas := (fun c : OpenPartialHomeomorph P H => hd.trans c) '' atlas H P
      chartAt := fun x => hd.trans (chartAt H (down x))
      mem_chart_source := by intro x; simp only [hd,mfld_simps]
      chart_mem_atlas := by
        intro x
        exact ⟨chartAt H (down x), chart_mem_atlas H (down x),rfl⟩ }
    letI : ChartedSpace H (ULift.{v} P) := cs
    have hs : IsManifold I ∞ (ULift.{v} P) := by
      apply isManifold_of_contDiffOn I ∞ (ULift.{v} P)
      intro c d hc hd'
      obtain ⟨a,ha,rfl⟩ := hc
      obtain ⟨b,hb,rfl⟩ := hd'
      have ht : ContMDiffOn I I ∞ (a.symm.trans b) (a.symm.trans b).source :=
        contMDiffOn_of_mem_contDiffGroupoid ((contDiffGroupoid ∞ I).compatible ha hb)
      have hu : ContMDiffOn I I ∞ ((hd.trans a).symm.trans (hd.trans b))
          ((hd.trans a).symm.trans (hd.trans b)).source := by
        simpa [hd,mfld_simps,Function.comp_def,Set.preimage,Homeomorph.apply_symm_apply] using ht
      exact (I.contMDiff.comp_contMDiffOn
        (hu.comp (I.contMDiffOn_symm.mono inter_subset_right)
          (by intro x hx; exact hx.1))).contDiffOn
    letI : IsManifold I ∞ (ULift.{v} P) := hs
    letI : SecondCountableTopology (ULift.{v} P) := down.isEmbedding.secondCountableTopology
    let Q : CompactCornerPiece.{v} := {carrier := ULift.{v} P}
    have hf : ContMDiff I I ∞ (down : Q → P) := by
      intro x
      apply contMDiffWithinAt_iff'.mpr
      refine ⟨down.continuous.continuousWithinAt, ?_⟩
      have h := contMDiff_id (I := I) (M := P) (n := ∞) (down x)
      change ContMDiffWithinAt I I ∞ id univ (down x) at h
      rw [contMDiffWithinAt_iff'] at h
      have hc : chartAt H (x : Q) = hd.trans (chartAt H (down x)) := rfl
      simp only [I, extChartAt, hc]
      simpa [I,Q,extChartAt,cs,hd,down,mfld_simps,Function.comp_def,Set.preimage] using h.2
    have hb : ContMDiff I I ∞ (down.symm : P → Q) := by
      intro x
      apply contMDiffWithinAt_iff'.mpr
      refine ⟨down.symm.continuous.continuousWithinAt, ?_⟩
      have h := contMDiff_id (I := I) (M := P) (n := ∞) x
      change ContMDiffWithinAt I I ∞ id univ x at h
      rw [contMDiffWithinAt_iff'] at h
      have hc : chartAt H (down.symm x : Q) = hd.trans (chartAt H (down (down.symm x))) := rfl
      simp only [I, extChartAt, hc]
      simpa [I,Q,extChartAt,cs,hd,down,mfld_simps,Function.comp_def,Set.preimage] using h.2
    exact ⟨Q,⟨{toEquiv := down.toEquiv,contMDiff_toFun := hf,contMDiff_invFun := hb}⟩⟩
  obtain ⟨Q₀,⟨e₀⟩⟩ := hstandard
  obtain ⟨Q,⟨d⟩⟩ := hlift Q₀
  let e : Diffeomorph CornerModel ((𝓡∂ 1).prod (𝓡∂ 1)) Q (Time × Time) ∞ := d.trans e₀
  have hpatches (Q : CompactCornerPiece.{v})
      (e : Diffeomorph CornerModel ((𝓡∂ 1).prod (𝓡∂ 1)) Q (Time × Time) ∞)
      (A : SectorModel) (y : Euc 2) (hy : y ∈ A.domain) :
      ∃ f : Fin 4 → C(Q,Euc 2),
        (∀ k, IsEmbedding (f k)) ∧ (∀ k, MapsTo (f k) univ A.domain) ∧
        (∀ k, ContMDiff CornerModel 𝓘(ℝ,Euc 2) ∞ (f k)) ∧
        (∀ k q, Injective (mfderiv CornerModel 𝓘(ℝ,Euc 2) (f k) q)) ∧
        (∀ k, MapsTo (f k) (CornerModel.interior Q) (interior A.domain)) ∧
        (⋃ k,range (f k)) ∈ 𝓝[A.domain] y := by
    classical
    have hrect (A : SectorModel) (y : Euc 2) (hy : y ∈ A.domain) :
        ∃ L : Fin 4 → ((ℝ × ℝ) ≃L[ℝ] Euc 2), ∃ a b : Fin 4 → ℝ × ℝ,
          (∀ k, 0 ≤ (a k).1 ∧ (a k).1 < (b k).1 ∧ 0 ≤ (a k).2 ∧ (a k).2 < (b k).2) ∧
          (∀ k, (L k) '' (Icc (a k).1 (b k).1 ×ˢ Icc (a k).2 (b k).2) ⊆ A.domain) ∧
          (⋃ k, (L k) '' (Icc (a k).1 (b k).1 ×ˢ Icc (a k).2 (b k).2)) ∈ 𝓝[A.domain] y := by
      classical
      have hplane : ∃ L : Fin 4 → ((ℝ × ℝ) ≃L[ℝ] Euc 2),
          (⋃ k, (L k) '' (Ici (0:ℝ) ×ˢ Ici (0:ℝ))) = univ := by
        let base : (ℝ × ℝ) ≃ₗ[ℝ] Euc 2 := {
          toFun := fun z => !₂[z.1,z.2]
          invFun := fun x => (x 0,x 1)
          map_add' := by intro x y; ext i; fin_cases i <;> rfl
          map_smul' := by intro r x; ext i; fin_cases i <;> rfl
          left_inv := by intro z; rfl
          right_inv := by intro x; ext i; fin_cases i <;> rfl }
        let pp := base.toContinuousLinearEquiv
        let np := ((LinearEquiv.neg ℝ).prodCongr (LinearEquiv.refl ℝ ℝ)).trans base |>.toContinuousLinearEquiv
        let pn := ((LinearEquiv.refl ℝ ℝ).prodCongr (LinearEquiv.neg ℝ)).trans base |>.toContinuousLinearEquiv
        let nn := ((LinearEquiv.neg ℝ).prodCongr (LinearEquiv.neg ℝ)).trans base |>.toContinuousLinearEquiv
        let L : Fin 4 → ((ℝ × ℝ) ≃L[ℝ] Euc 2) := ![pp,np,pn,nn]
        refine ⟨L,?_⟩
        apply eq_univ_of_forall
        intro x
        apply mem_iUnion.mpr
        by_cases h₀ : 0 ≤ x 0
        · by_cases h₁ : 0 ≤ x 1
          · refine ⟨0,⟨(x 0,x 1),⟨h₀,h₁⟩,?_⟩⟩
            change (!₂[x 0,x 1] : Euc 2) = x
            ext i; fin_cases i <;> rfl
          · refine ⟨2,⟨(x 0,-x 1),⟨h₀,neg_nonneg.mpr (lt_of_not_ge h₁).le⟩,?_⟩⟩
            change (!₂[x 0,-(-x 1)] : Euc 2) = x
            ext i; fin_cases i <;> simp
        · by_cases h₁ : 0 ≤ x 1
          · refine ⟨1,⟨(-x 0,x 1),⟨neg_nonneg.mpr (lt_of_not_ge h₀).le,h₁⟩,?_⟩⟩
            change (!₂[-(-x 0),x 1] : Euc 2) = x
            ext i; fin_cases i <;> simp
          · refine ⟨3,⟨(-x 0,-x 1),⟨neg_nonneg.mpr (lt_of_not_ge h₀).le,neg_nonneg.mpr (lt_of_not_ge h₁).le⟩,?_⟩⟩
            change (!₂[-(-x 0),-(-x 1)] : Euc 2) = x
            ext i; fin_cases i <;> simp
      have hfan (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < 2*Real.pi) :
          ∃ L : Fin 4 → ((ℝ × ℝ) ≃L[ℝ] Euc 2),
            planarSector θ = ⋃ k, (L k) '' (Ici (0:ℝ) ×ˢ Ici (0:ℝ)) ∧
            (∀ k, IsClosed ((L k) '' (Ici (0:ℝ) ×ˢ Ici (0:ℝ)))) := by
        classical
        have hcoords (a b t r : ℝ) (hs : Real.sin (b-a) ≠ 0) :
            r • sectorUnit t =
              (r * Real.sin (b-t) / Real.sin (b-a)) • sectorUnit a +
              (r * Real.sin (t-a) / Real.sin (b-a)) • sectorUnit b := by
          ext i
          fin_cases i
          · change r * Real.cos t =
              (r * Real.sin (b-t) / Real.sin (b-a)) * Real.cos a +
              (r * Real.sin (t-a) / Real.sin (b-a)) * Real.cos b
            field_simp (disch := first | assumption | positivity)
            simp only [Real.sin_sub]
            ring
          · change r * Real.sin t =
              (r * Real.sin (b-t) / Real.sin (b-a)) * Real.sin a +
              (r * Real.sin (t-a) / Real.sin (b-a)) * Real.sin b
            field_simp (disch := first | assumption | positivity)
            simp only [Real.sin_sub]
            ring
        have hnonneg (a b t r : ℝ) (hab : a < b) (hwidth : b-a < Real.pi)
            (ht : t ∈ Icc a b) (hr : 0 ≤ r) :
            0 ≤ r * Real.sin (b-t) / Real.sin (b-a) ∧
              0 ≤ r * Real.sin (t-a) / Real.sin (b-a) := by
          have hs : 0 < Real.sin (b-a) := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) hwidth
          constructor
          · apply div_nonneg (mul_nonneg hr ?_) hs.le
            exact Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr ht.2) (by linarith [ht.1])
          · apply div_nonneg (mul_nonneg hr ?_) hs.le
            exact Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr ht.1) (by linarith [ht.2])
        have hbasis (a b : ℝ) (hs : Real.sin (b-a) ≠ 0) :
            ∃ e : (ℝ × ℝ) ≃L[ℝ] Euc 2,
              ∀ z, e z = z.1 • sectorUnit a + z.2 • sectorUnit b := by
          let d := Real.sin (b-a)
          have hd : d = Real.cos a * Real.sin b - Real.sin a * Real.cos b := by
            dsimp [d]
            rw [Real.sin_sub]
            ring
          have hd0 : d ≠ 0 := hs
          let e : (ℝ × ℝ) ≃ₗ[ℝ] Euc 2 := {
            toFun := fun z => z.1 • sectorUnit a + z.2 • sectorUnit b
            invFun := fun x => ((x 0 * Real.sin b - x 1 * Real.cos b)/d,
              (Real.cos a * x 1 - Real.sin a * x 0)/d)
            map_add' := by
              intro x y
              simp only [Prod.fst_add,Prod.snd_add,add_smul]
              exact add_add_add_comm _ _ _ _
            map_smul' := by
              intro r z
              simp [smul_add,smul_smul]
            left_inv := by
              intro z
              apply Prod.ext
              · change ((z.1 * Real.cos a + z.2 * Real.cos b) * Real.sin b -
                  (z.1 * Real.sin a + z.2 * Real.sin b) * Real.cos b)/d = z.1
                field_simp (disch := first | assumption | positivity)
                rw [hd]
                ring
              · change (Real.cos a * (z.1 * Real.sin a + z.2 * Real.sin b) -
                  Real.sin a * (z.1 * Real.cos a + z.2 * Real.cos b))/d = z.2
                field_simp (disch := first | assumption | positivity)
                rw [hd]
                ring
            right_inv := by
              intro x
              ext i
              fin_cases i
              · change ((x 0 * Real.sin b - x 1 * Real.cos b)/d) * Real.cos a +
                  ((Real.cos a * x 1 - Real.sin a * x 0)/d) * Real.cos b = x 0
                field_simp (disch := first | assumption | positivity)
                rw [hd]
                ring
              · change ((x 0 * Real.sin b - x 1 * Real.cos b)/d) * Real.sin a +
                  ((Real.cos a * x 1 - Real.sin a * x 0)/d) * Real.sin b = x 1
                field_simp (disch := first | assumption | positivity)
                rw [hd]
                ring }
          exact ⟨e.toContinuousLinearEquiv,fun z => rfl⟩
        have hcontain (a b u v : ℝ) (hab : a < b) (hwidth : b-a < Real.pi/2)
            (hu : 0 ≤ u) (hv : 0 ≤ v) :
            ∃ r : ℝ, 0 ≤ r ∧ ∃ t ∈ Icc a b, u • sectorUnit a + v • sectorUnit b = r • sectorUnit t := by
          let f : ℝ → ℝ := fun t => u * Real.sin (a-t) + v * Real.sin (b-t)
          have hf : ContinuousOn f (Icc a b) := by fun_prop
          have hfa : 0 ≤ f a := by
            dsimp only [f]
            rw [sub_self, Real.sin_zero, mul_zero, zero_add]
            exact mul_nonneg hv (Real.sin_nonneg_of_nonneg_of_le_pi
              (sub_nonneg.mpr hab.le) (by linarith [Real.pi_pos]))
          have hfb : f b ≤ 0 := by
            dsimp only [f]
            rw [sub_self, Real.sin_zero, mul_zero, add_zero]
            have hsin : Real.sin (a-b) ≤ 0 := by
              rw [show a-b = -(b-a) by ring, Real.sin_neg]
              exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi
                (sub_nonneg.mpr hab.le) (by linarith [Real.pi_pos]))
            exact mul_nonpos_of_nonneg_of_nonpos hu hsin
          obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hab.le hf ⟨hfb,hfa⟩
          let r := u * Real.cos (a-t) + v * Real.cos (b-t)
          have hr : 0 ≤ r := by
            apply add_nonneg
            · exact mul_nonneg hu (Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.2], by linarith [ht.1]⟩)
            · exact mul_nonneg hv (Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.2], by linarith [ht.1]⟩)
          refine ⟨r,hr,t,ht,?_⟩
          dsimp only [f] at hft
          ext i
          fin_cases i
          · change u * Real.cos a + v * Real.cos b = r * Real.cos t
            dsimp only [r]
            simp only [Real.cos_sub, Real.sin_sub] at *
            have h := Real.sin_sq_add_cos_sq t
            have hzero := congrArg (fun z : ℝ => z * Real.sin t) hft
            simp only [zero_mul] at hzero
            nlinarith [hzero, congrArg (fun z : ℝ => z * (u * Real.cos a + v * Real.cos b)) h]
          · change u * Real.sin a + v * Real.sin b = r * Real.sin t
            dsimp only [r]
            simp only [Real.cos_sub, Real.sin_sub] at *
            have h := Real.sin_sq_add_cos_sq t
            have hzero := congrArg (fun z : ℝ => z * Real.cos t) hft
            simp only [zero_mul] at hzero
            nlinarith [hzero, congrArg (fun z : ℝ => z * (u * Real.sin a + v * Real.sin b)) h]
        let α : Fin 4 → ℝ := fun k => (k.val : ℝ)*θ/4
        let β : Fin 4 → ℝ := fun k => ((k.val+1 : ℕ) : ℝ)*θ/4
        have hw (k : Fin 4) : 0 < β k - α k ∧ β k - α k < Real.pi/2 := by
          have hh : β k - α k = θ/4 := by dsimp [α,β]; push_cast; ring
          rw [hh]
          constructor
          · positivity
          · linarith [Real.pi_pos]
        have hbounds (k : Fin 4) : 0 ≤ α k ∧ β k ≤ θ := by
          have hk : (k.val : ℝ) ≤ 3 := by exact_mod_cast (Nat.le_of_lt_succ k.isLt)
          have hk0 : 0 ≤ (k.val : ℝ) := Nat.cast_nonneg _
          dsimp [α,β]
          push_cast
          constructor
          · positivity
          · nlinarith
        have hsin (k : Fin 4) : Real.sin (β k - α k) ≠ 0 := by
          apply ne_of_gt
          exact Real.sin_pos_of_pos_of_lt_pi (hw k).1 (by linarith [(hw k).2,Real.pi_pos])
        choose e he using fun k => hbasis (α k) (β k) (hsin k)
        refine ⟨e, ?_, ?_⟩
        · ext x
          constructor
          · rintro ⟨r,hr,t,ht,rfl⟩
            have hinterval : ∃ k : Fin 4, t ∈ Icc (α k) (β k) := by
              by_cases h1 : t ≤ θ/4
              · refine ⟨0,?_⟩
                simpa [α,β] using (show t ∈ Icc (0:ℝ) (θ/4) from ⟨ht.1,h1⟩)
              · by_cases h2 : t ≤ 2*θ/4
                · refine ⟨1,?_⟩
                  norm_num [α,β]
                  exact ⟨(lt_of_not_ge h1).le,h2⟩
                · by_cases h3 : t ≤ 3*θ/4
                  · refine ⟨2,?_⟩
                    norm_num [α,β]
                    exact ⟨(lt_of_not_ge h2).le,h3⟩
                  · refine ⟨3,?_⟩
                    norm_num [α,β]
                    exact ⟨(lt_of_not_ge h3).le,ht.2⟩
            obtain ⟨k,hk⟩ := hinterval
            apply mem_iUnion.mpr
            refine ⟨k,?_⟩
            let u := r * Real.sin (β k-t)/Real.sin (β k-α k)
            let v := r * Real.sin (t-α k)/Real.sin (β k-α k)
            have hn := hnonneg (α k) (β k) t r (by linarith [(hw k).1])
              (by linarith [(hw k).2,Real.pi_pos]) hk hr
            refine ⟨(u,v),hn,?_⟩
            rw [he]
            exact (hcoords (α k) (β k) t r (hsin k)).symm
          · intro hx
            obtain ⟨k,z,hz,rfl⟩ := mem_iUnion.mp hx
            rw [he]
            obtain ⟨r,hr,t,ht,heq⟩ := hcontain (α k) (β k) z.1 z.2
              (by linarith [(hw k).1]) (hw k).2 hz.1 hz.2
            refine ⟨r,hr,t,⟨?_,?_⟩,heq⟩
            · linarith [(hbounds k).1,ht.1]
            · linarith [(hbounds k).2,ht.2]
        · intro k
          exact (e k).toHomeomorph.isClosedMap _ (isClosed_Ici.prod isClosed_Ici)
      have hboxes {n : ℕ} (L : Fin n → ((ℝ × ℝ) ≃L[ℝ] Euc 2))
          (B : Set (Euc 2)) (hB : IsOpen B) (h0 : (0 : Euc 2) ∈ B)
          (y : Euc 2) (hy : y ∈ B) :
          ∃ a b : Fin n → ℝ × ℝ,
            (∀ k, 0 ≤ (a k).1 ∧ (a k).1 < (b k).1 ∧ 0 ≤ (a k).2 ∧ (a k).2 < (b k).2) ∧
            (∀ k, (L k) '' (Icc (a k).1 (b k).1 ×ˢ Icc (a k).2 (b k).2) ⊆ B) ∧
            (⋃ k, (L k) '' (Icc (a k).1 (b k).1 ×ˢ Icc (a k).2 (b k).2)) ∈
              𝓝[B ∩ (⋃ k, (L k) '' (Ici (0:ℝ) ×ˢ Ici (0:ℝ)))] y := by
        classical
        have hbox (x : ℝ × ℝ) (hx : x ∈ Ici (0:ℝ) ×ˢ Ici (0:ℝ))
            (U : Set (ℝ × ℝ)) (hU : U ∈ 𝓝 x) :
            ∃ a b : ℝ × ℝ,
              (0 ≤ a.1 ∧ a.1 < b.1 ∧ 0 ≤ a.2 ∧ a.2 < b.2) ∧
              (Icc a.1 b.1 ×ˢ Icc a.2 b.2) ⊆ U ∧
              (Icc a.1 b.1 ×ˢ Icc a.2 b.2) ∈ 𝓝[Ici (0:ℝ) ×ˢ Ici (0:ℝ)] x := by
          rw [nhds_prod_eq] at hU
          obtain ⟨U₁,hU₁,U₂,hU₂,hsub⟩ := Filter.mem_prod_iff.mp hU
          obtain ⟨l₁,u₁,hl₁,hs₁⟩ := mem_nhds_iff_exists_Ioo_subset.mp hU₁
          obtain ⟨l₂,u₂,hl₂,hs₂⟩ := mem_nhds_iff_exists_Ioo_subset.mp hU₂
          let L₁ := (l₁+x.1)/2
          let L₂ := (l₂+x.2)/2
          let R₁ := (x.1+u₁)/2
          let R₂ := (x.2+u₂)/2
          have hL₁ : l₁ < L₁ ∧ L₁ < x.1 := by dsimp [L₁]; constructor <;> linarith [hl₁.1]
          have hL₂ : l₂ < L₂ ∧ L₂ < x.2 := by dsimp [L₂]; constructor <;> linarith [hl₂.1]
          have hR₁ : x.1 < R₁ ∧ R₁ < u₁ := by dsimp [R₁]; constructor <;> linarith [hl₁.2]
          have hR₂ : x.2 < R₂ ∧ R₂ < u₂ := by dsimp [R₂]; constructor <;> linarith [hl₂.2]
          refine ⟨(max 0 L₁,max 0 L₂),(R₁,R₂),?_,?_,?_⟩
          · exact ⟨le_max_left _ _,max_lt (lt_of_le_of_lt hx.1 hR₁.1) (hL₁.2.trans hR₁.1),
              le_max_left _ _,max_lt (lt_of_le_of_lt hx.2 hR₂.1) (hL₂.2.trans hR₂.1)⟩
          · intro z hz
            apply hsub
            refine ⟨hs₁ ⟨?_,?_⟩,hs₂ ⟨?_,?_⟩⟩
            · exact hL₁.1.trans_le ((le_max_right _ _).trans hz.1.1)
            · exact hz.1.2.trans_lt hR₁.2
            · exact hL₂.1.trans_le ((le_max_right _ _).trans hz.2.1)
            · exact hz.2.2.trans_lt hR₂.2
          · have hn : Ioo L₁ R₁ ×ˢ Ioo L₂ R₂ ∈ 𝓝 x := by
              rw [nhds_prod_eq]
              exact Filter.prod_mem_prod (Ioo_mem_nhds hL₁.2 hR₁.1) (Ioo_mem_nhds hL₂.2 hR₂.1)
            filter_upwards [nhdsWithin_le_nhds hn,self_mem_nhdsWithin] with z hz hzS
            exact ⟨⟨max_le hzS.1 hz.1.1.le,hz.1.2.le⟩,
              ⟨max_le hzS.2 hz.2.1.le,hz.2.2.le⟩⟩
        let S := Ici (0:ℝ) ×ˢ Ici (0:ℝ)
        let C : Fin n → Set (Euc 2) := fun k => (L k) '' S
        let z : Fin n → ℝ × ℝ := fun k => if y ∈ C k then (L k).symm y else 0
        have hz (k : Fin n) : z k ∈ S := by
          by_cases hk : y ∈ C k
          · obtain ⟨p,hp,he⟩ := hk
            dsimp [z]
            rw [if_pos (show y ∈ C k from ⟨p,hp,he⟩),← he,(L k).symm_apply_apply]
            exact hp
          · dsimp [z]
            rw [if_neg hk]
            change 0 ≤ (0:ℝ) ∧ 0 ≤ (0:ℝ)
            exact ⟨le_rfl,le_rfl⟩
        have hLz (k : Fin n) : L k (z k) ∈ B := by
          by_cases hk : y ∈ C k
          · simpa [z,hk] using hy
          · simpa [z,hk] using h0
        have hU (k : Fin n) : (L k) ⁻¹' B ∈ 𝓝 (z k) :=
          (L k).continuous.continuousAt.preimage_mem_nhds (hB.mem_nhds (hLz k))
        choose a b hab hsub hnhds using fun k => hbox (z k) (hz k) ((L k) ⁻¹' B) (hU k)
        refine ⟨a,b,hab,?_,?_⟩
        · intro k x hx
          obtain ⟨p,hp,rfl⟩ := hx
          exact hsub k hp
        · apply nhdsWithin_mono y inter_subset_right
          rw [nhdsWithin_iUnion,Filter.mem_iSup]
          intro k
          by_cases hk : y ∈ C k
          · have hn : (L k) '' (Icc (a k).1 (b k).1 ×ˢ Icc (a k).2 (b k).2) ∈ 𝓝[C k] y := by
              have hz' : L k (z k) = y := by simp [z,hk]
              rw [← hz']
              change (L k) '' (Icc (a k).1 (b k).1 ×ˢ Icc (a k).2 (b k).2) ∈ 𝓝[(L k) '' S] (L k (z k))
              have he : Filter.map (L k) (𝓝[S] (z k)) = 𝓝[(L k) '' S] (L k (z k)) := by
                simpa using (L k).toHomeomorph.isEmbedding.map_nhdsWithin_eq S (z k)
              rw [← he]
              apply Filter.mem_of_superset (hnhds k)
              intro p hp
              exact ⟨p,hp,rfl⟩
            exact Filter.mem_of_superset hn (subset_iUnion_of_subset k (subset_refl _))
          · have hC : IsClosed (C k) := (L k).toHomeomorph.isClosedMap S (isClosed_Ici.prod isClosed_Ici)
            filter_upwards [nhdsWithin_le_nhds (hC.isOpen_compl.mem_nhds hk),self_mem_nhdsWithin] with x hx hxC
            exact False.elim (hx hxC)
      let S : Set (Euc 2) := if A.interiorChart then univ else planarSector A.angle
      obtain ⟨L,hL⟩ : ∃ L : Fin 4 → ((ℝ × ℝ) ≃L[ℝ] Euc 2),
          (⋃ k, (L k) '' (Ici (0:ℝ) ×ˢ Ici (0:ℝ))) = S := by
        cases h : A.interiorChart
        · obtain ⟨L,hL,_⟩ := hfan A.angle A.angle_positive A.angle_lt_two_pi
          exact ⟨L,by simpa [S,h] using hL.symm⟩
        · obtain ⟨L,hL⟩ := hplane
          exact ⟨L,by simpa [S,h] using hL⟩
      have hyB : y ∈ Metric.ball (0:Euc 2) A.radius := hy.1
      have h0B : (0:Euc 2) ∈ Metric.ball (0:Euc 2) A.radius := by
        simpa using A.radius_positive
      obtain ⟨a,b,hab,hsub,hn⟩ := hboxes L (Metric.ball (0:Euc 2) A.radius)
        Metric.isOpen_ball h0B y hyB
      refine ⟨L,a,b,hab,?_,?_⟩
      · intro k x hx
        refine ⟨hsub k hx,?_⟩
        change x ∈ S
        rw [← hL]
        apply mem_iUnion.mpr
        obtain ⟨z,hz,rfl⟩ := hx
        exact ⟨k,⟨z,⟨(hab k).1.trans hz.1.1,(hab k).2.2.1.trans hz.2.1⟩,rfl⟩⟩
      · change (⋃ k, (L k) '' (Icc (a k).1 (b k).1 ×ˢ Icc (a k).2 (b k).2)) ∈
          𝓝[Metric.ball (0:Euc 2) A.radius ∩ S] y
        rwa [hL] at hn
    have hsq (Q : CompactCornerPiece.{v})
        (e : Diffeomorph CornerModel ((𝓡∂ 1).prod (𝓡∂ 1)) Q (Time × Time) ∞) :
        let f : Q → ℝ × ℝ := fun q => ((e q).1.val,(e q).2.val)
        ContMDiff CornerModel 𝓘(ℝ,ℝ × ℝ) ∞ f ∧
          (∀ q, Injective (mfderiv CornerModel 𝓘(ℝ,ℝ × ℝ) f q)) ∧ IsEmbedding f := by
      classical
      dsimp only
      let c : Time × Time → ℝ × ℝ := Prod.map Subtype.val Subtype.val
      have hc : Manifold.IsSmoothEmbedding ((𝓡∂ 1).prod (𝓡∂ 1))
          ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ)) ∞ c :=
        isSmoothEmbedding_subtypeVal_Icc.prodMap isSmoothEmbedding_subtypeVal_Icc
      letI : ChartedSpace (ℝ × ℝ) (ℝ × ℝ) := chartedSpaceSelf (ℝ × ℝ)
      have hc' : Manifold.IsSmoothEmbedding ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ,ℝ × ℝ) ∞ c := by
        rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hc
        exact hc
      have hcf : ContMDiff CornerModel 𝓘(ℝ,ℝ × ℝ) ∞ (c ∘ e) := hc'.contMDiff.comp e.contMDiff
      refine ⟨hcf,?_,hc'.isEmbedding.comp e.toHomeomorph.isEmbedding⟩
      intro q
      change Injective (mfderiv CornerModel 𝓘(ℝ,ℝ × ℝ) (c ∘ e) q)
      rw [mfderiv_comp q (hc'.contMDiff.mdifferentiable (by simp) _) (e.contMDiff.mdifferentiable (by simp) _)]
      exact (hc'.isImmersion.mfderiv_injective (by simp) (e q)).comp
        (e.mfderivToContinuousLinearEquiv (by simp) q).injective
    have hD (a b : ℝ × ℝ) (hab₁ : a.1 < b.1) (hab₂ : a.2 < b.2)
        (L : (ℝ × ℝ) ≃L[ℝ] Euc 2) :
        ∃ D : Diffeomorph 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Euc 2) (ℝ × ℝ) (Euc 2) ∞,
          ∀ z, D z = L (a.1+(b.1-a.1)*z.1,a.2+(b.2-a.2)*z.2) := by
      let f : ℝ × ℝ → Euc 2 := fun z => L (a.1+(b.1-a.1)*z.1,a.2+(b.2-a.2)*z.2)
      let g : Euc 2 → ℝ × ℝ := fun y => (((L.symm y).1-a.1)/(b.1-a.1),
        ((L.symm y).2-a.2)/(b.2-a.2))
      have h₁ : b.1-a.1 ≠ 0 := ne_of_gt (sub_pos.mpr hab₁)
      have h₂ : b.2-a.2 ≠ 0 := ne_of_gt (sub_pos.mpr hab₂)
      have hleft : LeftInverse g f := by
        intro z
        dsimp [f,g]
        rw [L.symm_apply_apply]
        apply Prod.ext <;> dsimp <;> field_simp (disch := first | assumption | positivity) <;> ring
      have hright : RightInverse g f := by
        intro y
        dsimp [f,g]
        apply L.symm.injective
        rw [L.symm_apply_apply]
        apply Prod.ext <;> dsimp
        · field_simp (disch := first | assumption | positivity)
          ring
        · field_simp (disch := first | assumption | positivity)
          ring
      have hf : ContDiff ℝ ∞ f := by
        exact L.contDiff.comp (by fun_prop)
      have hg : ContDiff ℝ ∞ g := by fun_prop
      let E : (ℝ × ℝ) ≃ Euc 2 := {toFun := f,invFun := g,left_inv := hleft,right_inv := hright}
      refine ⟨{toEquiv := E,contMDiff_toFun := hf.contMDiff,contMDiff_invFun := hg.contMDiff},?_⟩
      intro z
      rfl
    have hrange (a b : ℝ × ℝ) (hab₁ : a.1 < b.1) (hab₂ : a.2 < b.2)
        (L : (ℝ × ℝ) ≃L[ℝ] Euc 2) :
        range (fun q : Q => L (a.1+(b.1-a.1)*(e q).1.val,a.2+(b.2-a.2)*(e q).2.val)) =
          L '' (Icc a.1 b.1 ×ˢ Icc a.2 b.2) := by
      have h₁ : 0 < b.1-a.1 := sub_pos.mpr hab₁
      have h₂ : 0 < b.2-a.2 := sub_pos.mpr hab₂
      ext y
      constructor
      · rintro ⟨q,rfl⟩
        refine ⟨_,⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,rfl⟩
        · nlinarith [(e q).1.property.1]
        · nlinarith [(e q).1.property.2]
        · nlinarith [(e q).2.property.1]
        · nlinarith [(e q).2.property.2]
      · rintro ⟨z,hz,rfl⟩
        have ht₁ : (z.1-a.1)/(b.1-a.1) ∈ Icc (0:ℝ) 1 := by
          constructor
          · exact div_nonneg (sub_nonneg.mpr hz.1.1) h₁.le
          · apply (div_le_iff₀ h₁).mpr
            linarith [hz.1.2]
        have ht₂ : (z.2-a.2)/(b.2-a.2) ∈ Icc (0:ℝ) 1 := by
          constructor
          · exact div_nonneg (sub_nonneg.mpr hz.2.1) h₂.le
          · apply (div_le_iff₀ h₂).mpr
            linarith [hz.2.2]
        let t : Time × Time := (⟨(z.1-a.1)/(b.1-a.1),ht₁⟩,⟨(z.2-a.2)/(b.2-a.2),ht₂⟩)
        refine ⟨e.symm t,?_⟩
        change L (a.1+(b.1-a.1)*(e (e.symm t)).1.val,
          a.2+(b.2-a.2)*(e (e.symm t)).2.val) = L z
        rw [e.apply_symm_apply]
        apply congrArg L
        apply Prod.ext <;> dsimp [t]
        · field_simp (disch := first | assumption | positivity)
          ring
        · field_simp (disch := first | assumption | positivity)
          ring
    have hinter (a b : ℝ × ℝ) (hab₁ : a.1 < b.1) (hab₂ : a.2 < b.2)
        (L : (ℝ × ℝ) ≃L[ℝ] Euc 2) (T : Set (Euc 2))
        (hsub : L '' (Icc a.1 b.1 ×ˢ Icc a.2 b.2) ⊆ T) :
        MapsTo (fun q : Q => L (a.1+(b.1-a.1)*(e q).1.val,a.2+(b.2-a.2)*(e q).2.val))
          (CornerModel.interior Q) (interior T) := by
      have hc : MapsTo (fun q => ((e q).1.val,(e q).2.val)) (CornerModel.interior Q)
          (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) := by
        intro q hq
        have heq : e q ∈ ((𝓡∂ 1).prod (𝓡∂ 1)).interior (Time × Time) := by
          rw [← e.preimage_interior (by simp)] at hq
          exact hq
        rw [ModelWithCorners.interior_prod] at heq
        have hcoord (t : Time) (ht : t ∈ (𝓡∂ 1).interior Time) : t.val ∈ Ioo (0:ℝ) 1 := by
          rw [← ModelWithCorners.compl_boundary,mem_compl_iff,boundary_Icc] at ht
          obtain h | h | h := eq_endpoints_or_mem_Ioo_of_mem_Icc t.property
          · have hh : t = ⊥ := Subtype.ext h
            exact False.elim (ht (by simp [hh]))
          · have hh : t = ⊤ := Subtype.ext h
            exact False.elim (ht (by simp [hh]))
          · exact h
        exact ⟨hcoord _ heq.1,hcoord _ heq.2⟩
      intro q hq
      have ht := hc hq
      have hx₁ : a.1 < a.1+(b.1-a.1)*(e q).1.val ∧
          a.1+(b.1-a.1)*(e q).1.val < b.1 := by constructor <;> nlinarith [ht.1.1,ht.1.2]
      have hx₂ : a.2 < a.2+(b.2-a.2)*(e q).2.val ∧
          a.2+(b.2-a.2)*(e q).2.val < b.2 := by constructor <;> nlinarith [ht.2.1,ht.2.2]
      apply mem_interior.mpr
      refine ⟨L '' (Ioo a.1 b.1 ×ˢ Ioo a.2 b.2),?_,?_,?_⟩
      · rintro y ⟨z,hz,rfl⟩
        exact hsub ⟨z,⟨⟨hz.1.1.le,hz.1.2.le⟩,⟨hz.2.1.le,hz.2.2.le⟩⟩,rfl⟩
      · exact L.toHomeomorph.isOpenMap _ (isOpen_Ioo.prod isOpen_Ioo)
      · exact ⟨(a.1+(b.1-a.1)*(e q).1.val,a.2+(b.2-a.2)*(e q).2.val),⟨hx₁,hx₂⟩,rfl⟩
    obtain ⟨L,a,b,hab,hsub,hn⟩ := hrect A y hy
    choose D hDspec using fun k => hD (a k) (b k) (hab k).2.1 (hab k).2.2.2 (L k)
    let c : Q → ℝ × ℝ := fun q => ((e q).1.val,(e q).2.val)
    obtain ⟨hc,hcinj,hcemb⟩ := hsq Q e
    let f : Fin 4 → C(Q,Euc 2) := fun k => ⟨D k ∘ c,(D k).contMDiff.continuous.comp hc.continuous⟩
    have hfeq (k : Fin 4) : (f k : Q → Euc 2) =
        (fun q : Q => L k ((a k).1+((b k).1-(a k).1)*(e q).1.val,
          (a k).2+((b k).2-(a k).2)*(e q).2.val)) := by
      funext q
      exact hDspec k (c q)
    have hfrange (k : Fin 4) : range (f k) =
        L k '' (Icc (a k).1 (b k).1 ×ˢ Icc (a k).2 (b k).2) := by
      rw [hfeq]
      exact hrange (a k) (b k) (hab k).2.1 (hab k).2.2.2 (L k)
    refine ⟨f,?_,?_,?_,?_,?_,?_⟩
    · intro k
      exact (D k).toHomeomorph.isEmbedding.comp hcemb
    · intro k q hq
      apply hsub k
      rw [← hfrange]
      exact mem_range_self q
    · intro k
      exact (D k).contMDiff.comp hc
    · intro k q
      change Injective (mfderiv CornerModel 𝓘(ℝ,Euc 2) (D k ∘ c) q)
      rw [mfderiv_comp q ((D k).contMDiff.mdifferentiable (by simp) _)
        (hc.mdifferentiable (by simp) _)]
      exact ((D k).mfderivToContinuousLinearEquiv (by simp) (c q)).injective.comp (hcinj q)
    · intro k
      rw [hfeq]
      exact hinter (a k) (b k) (hab k).2.1 (hab k).2.2.2 (L k) A.domain (hsub k)
    · simpa only [hfrange] using hn
  have htransfer (P : CompactSectorPiece.{v}) (x : P) (j : Fin P.count)
      (hx : x ∈ (P.chart j).map.source) (Q : Fin 4 → CompactCornerPiece.{v})
      (f : (k : Fin 4) → C(Q k,Euc 2)) (hf : ∀ k, Injective (f k))
      (hs : ∀ k, MapsTo (f k) univ (P.chart j).map.target)
      (hn : (⋃ k,range (f k)) ∈ 𝓝[(P.chart j).map.target] ((P.chart j).map x)) :
      ∃ p : (k : Fin 4) → C(Q k,P),
        (∀ k, IsEmbedding (p k)) ∧
        (∀ k, MapsTo (p k) univ (P.chart j).map.source) ∧
        (∀ k, (P.chart j).map ∘ p k = f k) ∧ (⋃ k,range (p k)) ∈ 𝓝 x := by
    let c := (P.chart j).map
    have hpcont (k : Fin 4) : Continuous (c.symm ∘ f k) := by
      apply continuousOn_univ.mp
      exact c.continuousOn_symm.comp (f k).continuous.continuousOn (hs k)
    let p : (k : Fin 4) → C(Q k,P) := fun k => ⟨c.symm ∘ f k,hpcont k⟩
    have hcp (k : Fin 4) : c ∘ p k = f k := by
      funext q
      exact c.right_inv (hs k trivial)
    refine ⟨p,?_,?_,hcp,?_⟩
    · intro k
      refine ((p k).continuous.isClosedEmbedding ?_).isEmbedding
      intro q r hqr
      apply hf k
      have hh := congrArg c hqr
      change (c ∘ p k) q = (c ∘ p k) r at hh
      rwa [hcp k] at hh
    · intro k q hq
      exact c.map_target (hs k trivial)
    · have hn' : (⋃ k,range (f k)) ∈ 𝓝[c '' c.source] (c x) := by
        rw [c.image_source_eq_target]
        exact hn
      have ht : c ⁻¹' (⋃ k,range (f k)) ∈ 𝓝[c.source] x :=
        (c.continuousOn x hx).preimage_mem_nhdsWithin' hn'
      have hsrc : c.source ∈ 𝓝 x := (P.chart j).source_open.mem_nhds hx
      rw [nhdsWithin_eq_nhds.mpr hsrc] at ht
      filter_upwards [ht,hsrc] with z hz hzsrc
      obtain ⟨k,q,hq⟩ := mem_iUnion.mp hz
      apply mem_iUnion.mpr
      refine ⟨k,q,?_⟩
      change c.symm (f k q) = z
      rw [hq,c.left_inv hzsrc]
  have hlocal : ∀ x : P,
      ∃ n : ℕ, ∃ Q : Fin n → CompactCornerPiece.{v},
        ∃ j : Fin n → Fin P.count, ∃ p : (i : Fin n) → C(Q i, P),
          (∀ i, IsEmbedding (p i)) ∧
          (∀ i, MapsTo (p i) univ (P.chart (j i)).map.source) ∧
          (∀ i, ContMDiff CornerModel 𝓘(ℝ, Euc 2) ∞ ((P.chart (j i)).map ∘ p i)) ∧
          (∀ i z, Injective (mfderiv CornerModel 𝓘(ℝ, Euc 2) ((P.chart (j i)).map ∘ p i) z)) ∧
          (∀ i, MapsTo ((P.chart (j i)).map ∘ p i) (CornerModel.interior (Q i))
            (interior (P.chart (j i)).map.target)) ∧ (⋃ i,range (p i)) ∈ 𝓝 x := by
    intro x
    have hx : x ∈ ⋃ j, (P.chart j).map.source := by rw [P.covers]; trivial
    obtain ⟨j,hxj⟩ := mem_iUnion.mp hx
    have hy : (P.chart j).map x ∈ (P.chart j).model.domain := by
      rw [← (P.chart j).target_eq]
      exact (P.chart j).map.map_source hxj
    obtain ⟨f,hemb,hmap,hsmooth,hrank,hinterior,hnhds⟩ := hpatches Q e (P.chart j).model ((P.chart j).map x) hy
    have hs : ∀ k, MapsTo (f k) univ (P.chart j).map.target := by
      intro k
      rw [(P.chart j).target_eq]
      exact hmap k
    have hn : (⋃ k,range (f k)) ∈ 𝓝[(P.chart j).map.target] ((P.chart j).map x) := by
      rwa [(P.chart j).target_eq]
    obtain ⟨p,hemp,hsource,hcp,hpnhds⟩ := htransfer P x j hxj (fun _ => Q) f (fun k => (hemb k).injective) hs hn
    refine ⟨4,(fun _ => Q),(fun _ => j),p,hemp,hsource,?_,?_,?_,hpnhds⟩
    · intro k
      rw [hcp k]
      exact hsmooth k
    · intro k z
      rw [hcp k]
      exact hrank k z
    · intro k
      rw [hcp k,(P.chart j).target_eq]
      exact hinterior k
  classical
  choose n Q j p hemb hsource hsmooth hregular hinterior hnhds using hlocal
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover
    (fun x => ⋃ i, Set.range (p x i)) hnhds
  let Index := (x : s) × Fin (n x.1)
  let e : Fin (Fintype.card Index) ≃ Index := (Fintype.equivFin Index).symm
  refine ⟨Fintype.card Index, (fun i => Q (e i).1.1 (e i).2),
    (fun i => j (e i).1.1 (e i).2), (fun i => p (e i).1.1 (e i).2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hemb (e i).1.1 (e i).2
  · intro i
    exact hsource (e i).1.1 (e i).2
  · apply eq_univ_of_forall
    intro z
    have hz : z ∈ ⋃ x ∈ s, ⋃ i, Set.range (p x i) := by
      rw [hs]
      trivial
    obtain ⟨x, hx, hxz⟩ := mem_iUnion₂.mp hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp hxz
    apply mem_iUnion.mpr
    refine ⟨e.symm ⟨⟨x, hx⟩, k⟩, ?_⟩
    change z ∈ Set.range (p (e (e.symm ⟨⟨x, hx⟩, k⟩)).1.1
      (e (e.symm ⟨⟨x, hx⟩, k⟩)).2)
    rw [e.apply_symm_apply]
    exact hk
  · intro i
    exact hsmooth (e i).1.1 (e i).2
  · intro i z
    exact hregular (e i).1.1 (e i).2 z
  · intro i
    exact hinterior (e i).1.1 (e i).2

end
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.A6Construction



noncomputable section
open Set Topology Function
open scoped Manifold ContDiff

namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.A6Construction
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

private theorem geometric_identity_source_subdivision {S : CompactOrientedSurface.{v}}
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
    exact sector_corner_chart_cover_exists P
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

private theorem geometric_static_cylinder_subdivision {S : CompactOrientedSurface.{v}}
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
    exact geometric_identity_source_subdivision F
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

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.A6Construction

end

namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.A6Construction
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- The original F belongs to its exact fixed-boundary image isotopy class.
The identity source subdivision and constant track are actual constructions. -/
theorem fixed_boundary_image_isotopic_refl
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier) :
    FixedBoundaryImageIsotopic E F F := by
  classical
  obtain ⟨D⟩ := geometric_identity_source_subdivision F
  obtain ⟨H⟩ := geometric_static_cylinder_subdivision F
  let e : GeometricSourceHomeomorph F F := {
    homeomorph := Homeomorph.refl S
    forward := D
    backward := D
    boundary_image := by simp }
  refine ⟨e, fun _ => F, F.map.continuous.comp continuous_snd, ⟨H⟩, rfl, ?_, ?_⟩
  · rfl
  · intro t x hx
    rfl

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.A6Construction
