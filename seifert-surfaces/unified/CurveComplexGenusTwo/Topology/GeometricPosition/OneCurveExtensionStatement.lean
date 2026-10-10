import CurveComplexGenusTwo.Topology.GeometricPosition.TrimmedCrosscutsV2
import CurveComplexGenusTwo.Topology.GeometricPosition.PreparedFamilyCover
import CurveComplexGenusTwo.Topology.GeometricPosition.LocalizedSeamRepairV2
import CurveComplexGenusTwo.Topology.GeometricPosition.FiniteCompatibleCrosscutsV2
import CurveComplexGenusTwo.Topology.GeometricPosition.ProperAffineCrosscut
import CurveComplexGenusTwo.Topology.GeometricPosition.FiniteSurfaceReplacement
import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
import Schoenflies.Plane
import Schoenflies.Square
import Schoenflies.SimpleArc

namespace CurveComplex

/- The exact geometric producer needed by position_finite_assembly.
The pre-existing representatives remain the same function r. -/
theorem position_extend_transverse_family
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [ClosedSurface S]
    (J : Type*) [Fintype J]
    (r : J → EssentialCurve S)
    (hr : ∀ i j, i ≠ j → Transverse (r i).val (r j).val)
    (c : EssentialCurve S) :
    ∃ d : EssentialCurve S,
      Quotient.mk (essentialCurveSetoid S) d =
        Quotient.mk (essentialCurveSetoid S) c ∧
      ∀ i, Transverse (r i).val d.val := by
  have hcrossingsFinite (a b : Curve S)
      (hcross : ∀ p ∈ a.image ∩ b.image, CrossesAt a b p) : Transverse a b := by
    have hc : IsCompact (a.image ∩ b.image) :=
      (isCompact_range a.embedded.continuous).inter (isCompact_range b.embedded.continuous)
    have hex (p : ↥(a.image ∩ b.image)) : ∃ U : Set S, IsOpen U ∧ p.val ∈ U ∧
        ∀ x ∈ U, x ∈ a.image ∩ b.image → x = p.val := by
      obtain ⟨U, V, hpU, e, hU, hV, hp0, he⟩ := hcross p.val p.property
      refine ⟨U, hU, hpU, ?_⟩
      intro x hx hxI
      have hx0 : (e ⟨x, hx⟩ : ℝ × ℝ) = (0, 0) :=
        Prod.ext ((he x hx).1.mp hxI.1) ((he x hx).2.mp hxI.2)
      exact congrArg Subtype.val (e.injective (Subtype.ext (hx0.trans hp0.symm)))
    choose U hU hpU hUniq using hex
    obtain ⟨A, hA⟩ := hc.elim_finite_subcover U hU
      (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hpU ⟨x, hx⟩⟩)
    refine ⟨(A.finite_toSet.image Subtype.val).subset ?_, hcross⟩
    intro x hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hA hx)
    obtain ⟨hpA, hxU⟩ := Set.mem_iUnion.mp hp
    exact ⟨p, hpA, (hUniq p x hxU hx).symm⟩
  have hcrossPlanar (a b : Curve S)
      (E : OpenPartialHomeomorph S Schoenflies.Plane) (p : S)
      (hp : p ∈ E.source) (hp0 : E p 0 = 0) (m : ℝ)
      (ha : ∀ x ∈ E.source, x ∈ a.image ↔ E x 0 = 0)
      (hb : ∀ x ∈ E.source, x ∈ b.image ↔ E x 1 = E p 1 + m * E x 0) :
      CrossesAt a b p := by
    let L : Schoenflies.Plane ≃ₜ ℝ × ℝ :=
      ((EuclideanSpace.equiv (Fin 2) ℝ).trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
    let shear : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
      toEquiv := {
        toFun := fun z => (z.1,z.2-E p 1-m*z.1)
        invFun := fun z => (z.1,z.2+E p 1+m*z.1)
        left_inv := by intro z; apply Prod.ext <;> simp <;> ring
        right_inv := by intro z; apply Prod.ext <;> simp <;> ring }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let F := L.trans shear
    let V : Set (ℝ × ℝ) := F '' E.target
    let e : E.source ≃ₜ V := E.toHomeomorphSourceTarget.trans (F.image E.target)
    refine ⟨E.source,V,hp,e,E.open_source,F.isOpenMap _ E.open_target,?_,?_⟩
    · change (E p 0,E p 1-E p 1-m*E p 0) = (0,0)
      simp [hp0]
    · intro x hx
      change (x ∈ a.image ↔ E x 0 = 0) ∧
        (x ∈ b.image ↔ E x 1-E p 1-m*E x 0 = 0)
      refine ⟨ha x hx,?_⟩
      rw [hb x hx]
      constructor <;> intro h <;> linarith
  have hcompose (H G : AmbientIsotopy S) :
      ∃ K : AmbientIsotopy S, ∀ t x, K.map (t,x) = G.map (t,H.map (t,x)) := by
    refine ⟨{
      map := ⟨fun z => G.map (z.1,H.map z),
      G.map.continuous.comp (continuous_fst.prodMk H.map.continuous)⟩,
      homeomorphism_at := ?_, at_zero := ?_ },fun _ _ => rfl⟩
    · intro t
      obtain ⟨e,he⟩ := H.homeomorphism_at t
      obtain ⟨f,hf⟩ := G.homeomorphism_at t
      exact ⟨e.trans f,fun x => (hf (e x)).trans
        (congrArg (fun z => G.map (t,z)) (he x))⟩
    · intro x
      change G.map (⟨0,by norm_num⟩,H.map (⟨0,by norm_num⟩,x)) = x
      rw [H.at_zero,G.at_zero]
  have hreverse (H : AmbientIsotopy S) :
      ∃ G : AmbientIsotopy S, ∀ x, H.finalMap (G.finalMap x) = x := by
    obtain ⟨e,he⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
    let rev : Interval → Interval := fun t => ⟨1-t,by constructor <;> linarith [t.property.1,t.property.2]⟩
    have hrev : Continuous rev := (continuous_const.sub continuous_subtype_val).subtype_mk _
    let G : AmbientIsotopy S := {
      map := ⟨fun z => H.map (rev z.1,e.symm z.2),
        H.map.continuous.comp ((hrev.comp continuous_fst).prodMk
          (e.symm.continuous.comp continuous_snd))⟩
      homeomorphism_at := by
        intro t
        obtain ⟨f,hf⟩ := H.homeomorphism_at (rev t)
        exact ⟨e.symm.trans f,fun x => hf (e.symm x)⟩
      at_zero := by
        intro x
        change H.map (rev ⟨0,by norm_num⟩,e.symm x) = x
        have hr : rev ⟨0,by norm_num⟩ = ⟨1,by norm_num⟩ := by
          apply Subtype.ext; norm_num [rev]
        rw [hr,← he,e.apply_symm_apply] }
    refine ⟨G,?_⟩
    intro x
    change H.finalMap (H.map (rev ⟨1,by norm_num⟩,e.symm x)) = x
    have hr : rev ⟨1,by norm_num⟩ = ⟨0,by norm_num⟩ := by
      apply Subtype.ext; norm_num [rev]
    rw [hr,H.at_zero]
    exact (he (e.symm x)).symm.trans (e.apply_symm_apply x)
  have hhorizontal : segment ℝ (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) =
      {z : Schoenflies.Plane | z ∈ Schoenflies.Plane.closedSquare 0 1 ∧ z 1 = 0} := by
    ext z
    constructor
    · intro hz
      rw [segment_eq_image_lineMap] at hz
      obtain ⟨t,ht,rfl⟩ := hz
      have h0 : (AffineMap.lineMap (Schoenflies.Plane.mk (-1) 0)
          (Schoenflies.Plane.mk 1 0) t) 0 = 2*t-1 := by
        simp [AffineMap.lineMap_apply_module,Schoenflies.Plane.mk]; ring
      have h1 : (AffineMap.lineMap (Schoenflies.Plane.mk (-1) 0)
          (Schoenflies.Plane.mk 1 0) t) 1 = 0 := by
        simp [AffineMap.lineMap_apply_module,Schoenflies.Plane.mk]
      refine ⟨?_,h1⟩
      change Schoenflies.Plane.supDist (AffineMap.lineMap (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) t) 0 ≤ 1
      simp only [Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,sub_zero]
      rw [h0,h1,abs_zero,max_le_iff]
      constructor
      · rw [abs_le]; constructor <;> linarith [ht.1,ht.2]
      · norm_num
    · intro hz
      have hnorm : Schoenflies.Plane.supNorm z ≤ 1 := by
        simpa [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist] using hz.1
      have hbound : |z 0| ≤ 1 :=
        (Schoenflies.Plane.abs_zero_le_supNorm z).trans hnorm
      rw [abs_le] at hbound
      rw [segment_eq_image_lineMap]
      refine ⟨(z 0+1)/2,⟨by linarith [hbound.1],by linarith [hbound.2]⟩,?_⟩
      ext i
      fin_cases i
      · simp [AffineMap.lineMap_apply_module,Schoenflies.Plane.mk]; ring
      · simpa [AffineMap.lineMap_apply_module,Schoenflies.Plane.mk] using hz.2.symm
  classical
  obtain ⟨d0,hd0,e0,he0,hlabel0⟩ := position_prepared_family_cover S J r hr c
  have hcover0 : d0.val.image ⊆ ⋃ p : d0.val.image, (e0 p).source := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩,he0 ⟨x,hx⟩⟩
  obtain ⟨n,hn,chart,arc,harcEmbed,harc,hcover,hchart⟩ := position_curve_chart_subdivision
    d0.val (fun p => (e0 p).source) (fun p => (e0 p).open_source) hcover0
  let e : Fin n → OpenPartialHomeomorph S Schoenflies.Plane := fun k => e0 (chart k)
  choose label hlabel using (fun k : Fin n => hlabel0 (chart k))
  obtain ⟨U,H,hU,hpU,hUW,hUdis,hinc,hmiss,hseam,hfix,hstay,hwhole⟩ :=
    PositionUniverseV2.position_localized_seam_repair S J (fun j => (r j).val)
      d0.val n hn arc harc e hchart (fun _ => Set.univ)
      (fun _ => isOpen_univ) (fun _ => Set.mem_univ _)
  obtain ⟨f,hf⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hffinal (x : S) : f x = H.finalMap x := hf x
  let c1 : Curve S := ⟨f ∘ d0.val.map,f.isEmbedding.comp d0.val.embedded⟩
  have hc1image : c1.image = H.finalMap '' d0.val.image := by
    change Set.range (f ∘ d0.val.map) = H.finalMap '' Set.range d0.val.map
    rw [Set.range_comp]
    exact Set.image_congr (fun x _ => hffinal x)
  have hc1rel : (curveSetoid S).r d0.val c1 := ⟨H,hc1image.symm⟩
  let d1 : EssentialCurve S := ⟨c1,(essential_isotopy_invariant hc1rel).mp d0.property⟩
  have hd1 : Quotient.mk (essentialCurveSetoid S) d1 =
      Quotient.mk (essentialCurveSetoid S) c :=
    (Quotient.sound (s := essentialCurveSetoid S) (a := d0) (b := d1) hc1rel).symm.trans hd0
  let arc1 : Fin n → C(Interval,S) := fun k => ⟨fun t => f (arc k t),
    f.continuous.comp (arc k).continuous⟩
  have harc1 (k : Fin n) (t : Interval) : arc1 k t = d1.val.map (Circle.exp
      (-Real.pi+2*Real.pi*(((k.val:ℝ)+(t:ℝ))/n))) := by
    change f (arc k t) = f (d0.val.map _)
    rw [harc]
  have hcover1 : d1.val.image = ⋃ k, Set.range (arc1 k) := by
    change c1.image = _
    rw [hc1image,hcover,Set.image_iUnion]
    apply Set.iUnion_congr
    intro k
    rw [← Set.range_comp]
    ext x
    simp only [Set.mem_range]
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨t,hffinal (arc k t)⟩
    · rintro ⟨t,rfl⟩
      exact ⟨t,(hffinal (arc k t)).symm⟩
  have hchart1 (k : Fin n) : Set.range (arc1 k) ⊆ (e k).source := by
    rintro x ⟨t,rfl⟩
    rw [show arc1 k t = H.finalMap (arc k t) from hffinal (arc k t)]
    exact hwhole k ⟨1,by norm_num⟩ (Set.mem_image_of_mem _ (Set.mem_range_self t))
  have hendpoint (k : Fin n) : ∃ l : Fin n,
      arc k ⟨1,by norm_num⟩ = arc l ⟨0,by norm_num⟩ := by
    have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    by_cases hnext : k.val+1 < n
    · let l : Fin n := ⟨k.val+1,hnext⟩
      refine ⟨l,?_⟩
      rw [harc,harc]
      congr 2
      simp [l,Nat.cast_add]
    · have hk : k.val+1 = n := by omega
      have hkr : (k.val:ℝ)+1 = n := by exact_mod_cast hk
      let l : Fin n := ⟨0,by omega⟩
      refine ⟨l,?_⟩
      rw [harc,harc]
      have ha : -Real.pi+2*Real.pi*(((k.val:ℝ)+1)/n) = -Real.pi+2*Real.pi := by
        rw [hkr,div_self hnpos.ne']; ring
      simpa only [ha,l,Nat.cast_zero,add_zero,zero_div,mul_zero] using
        congrArg d0.val.map (Circle.exp_add_two_pi (-Real.pi))
  have hends1 (k : Fin n) (j : J) : arc1 k ⟨0,by norm_num⟩ ∉ (r j).val.image ∧
      arc1 k ⟨1,by norm_num⟩ ∉ (r j).val.image := by
    constructor
    · simpa only [arc1,ContinuousMap.coe_mk,hffinal] using hseam k j
    · obtain ⟨l,hl⟩ := hendpoint k
      change f (arc k ⟨1,by norm_num⟩) ∉ (r j).val.image
      rw [hl,hffinal]
      exact hseam l j
  obtain ⟨a,b,hab,hlen,hsub,hdis,hends,hremainder⟩ :=
    PositionTrimV2.position_trimmed_crosscuts S J (fun j => (r j).val) d1.val n hn
      arc1 harc1 hcover1 e hchart1 hends1
  obtain ⟨E,hEsub,hEdis,hEsquare,hcentral,hEends,hEcurve,hEslice⟩ :=
    PositionUniverseV2.position_finite_compatible_crosscuts S d1.val (Fin n)
      a b hab hlen e hsub hdis
  let A : Set Schoenflies.Plane := segment ℝ (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0)
  have hA : Schoenflies.IsArcBetween A (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) :=
    Schoenflies.isArcBetween_segment (by intro h; have hh := congrArg (fun z : Schoenflies.Plane => z 0) h; norm_num [Schoenflies.Plane.mk] at hh)
  have hAi : A \ {Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} ⊆
      Schoenflies.Plane.openSquare 0 1 := by
    intro z hz
    have hzline := hhorizontal.le hz.1
    have h0 : |z 0| ≤ 1 := by
      have hnorm : Schoenflies.Plane.supNorm z ≤ 1 := by
        simpa [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist] using hzline.1
      exact (Schoenflies.Plane.abs_zero_le_supNorm z).trans hnorm
    have hne0 : z 0 ≠ -1 := by
      intro h
      apply hz.2
      left
      ext i
      fin_cases i
      · simpa [Schoenflies.Plane.mk] using h
      · simpa [Schoenflies.Plane.mk] using hzline.2
    have hne1 : z 0 ≠ 1 := by
      intro h
      apply hz.2
      right
      apply Set.mem_singleton_iff.mpr
      ext i
      fin_cases i
      · simpa [Schoenflies.Plane.mk] using h
      · simpa [Schoenflies.Plane.mk] using hzline.2
    rw [Schoenflies.Plane.mem_openSquare_iff]
    intro i
    fin_cases i
    · simp only [PiLp.zero_apply,sub_zero]
      rw [abs_lt]
      exact ⟨lt_of_le_of_ne (abs_le.mp h0).1 hne0.symm,
        lt_of_le_of_ne (abs_le.mp h0).2 hne1⟩
    · simp [hzline.2]
  have hselected (k : Fin n) :
      {x : S | x ∈ (E k).source ∧ E k x ∈ A} =
      (fun t => d1.val.map (Circle.exp t)) '' Set.Icc (a k) (b k) := by
    rw [← hEslice k]
    ext x
    constructor
    · intro hx
      have hz := hhorizontal.le hx.2
      exact ⟨⟨hx.1,hz.1⟩,(hEcurve k x hx.1).mpr hz.2⟩
    · intro hx
      exact ⟨hx.1.1,hhorizontal.ge ⟨hx.1.2,(hEcurve k x hx.1.1).mp hx.2⟩⟩
  have hactual (k : Fin n) :
      {x : S | x ∈ (E k).source ∧ E k x ∈ Schoenflies.Plane.closedSquare 0 1} ∩ d1.val.image =
      {x : S | x ∈ (E k).source ∧ E k x ∈ A} := (hEslice k).trans (hselected k).symm
  let T : Fin n → OpenPartialHomeomorph Schoenflies.Plane Schoenflies.Plane :=
    fun k => (E k).symm.trans (e k)
  have hTsquare (k : Fin n) : Schoenflies.Plane.closedSquare 0 1 ⊆ (T k).source := by
    intro z hz
    have hzE : z ∈ (E k).target := hEsquare k hz
    exact ⟨hzE,hEsub k ((E k).symm.map_source hzE)⟩
  have hleftSource (k : Fin n) : d1.val.map (Circle.exp (a k)) ∈ (E k).source :=
    hcentral k (Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr (hab k).le))
  have hrightSource (k : Fin n) : d1.val.map (Circle.exp (b k)) ∈ (E k).source :=
    hcentral k (Set.mem_image_of_mem _ (Set.right_mem_Icc.mpr (hab k).le))
  have hleftInv (k : Fin n) : (E k).symm (Schoenflies.Plane.mk (-1) 0) =
      d1.val.map (Circle.exp (a k)) := by
    rw [← (hEends k).1,(E k).left_inv (hleftSource k)]
  have hrightInv (k : Fin n) : (E k).symm (Schoenflies.Plane.mk 1 0) =
      d1.val.map (Circle.exp (b k)) := by
    rw [← (hEends k).2,(E k).left_inv (hrightSource k)]
  have hTargets (k : Fin n) : ∃ B : Set Schoenflies.Plane,
      Schoenflies.IsArcBetween B (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) ∧
      B \ {Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} ⊆ Schoenflies.Plane.openSquare 0 1 ∧
      ∀ j, label k = some j → ∀ p ∈ (T k '' B) ∩ {z : Schoenflies.Plane | z 0 = 0},
        ∃ W : Set Schoenflies.Plane, IsOpen W ∧ p ∈ W ∧ W ⊆ (T k).target ∧
        ∃ m : ℝ, ∀ z ∈ W, (z ∈ T k '' B ↔ z 1 = p 1 + m*z 0) := by
    cases hL : label k with
    | none =>
      refine ⟨A,hA,hAi,?_⟩
      intro j hj
      cases hj
    | some j =>
      have ha0 : T k (Schoenflies.Plane.mk (-1) 0) 0 ≠ 0 := by
        intro h0
        have hh : (e k) (d1.val.map (Circle.exp (a k))) 0 = 0 := by
          simpa only [T,OpenPartialHomeomorph.trans_apply,hleftInv] using h0
        exact (hends k j).1 ((hlabel k j _ (hEsub k (hleftSource k))).mpr ⟨hL,hh⟩)
      have hb0 : T k (Schoenflies.Plane.mk 1 0) 0 ≠ 0 := by
        intro h0
        have hh : (e k) (d1.val.map (Circle.exp (b k))) 0 = 0 := by
          simpa only [T,OpenPartialHomeomorph.trans_apply,hrightInv] using h0
        exact (hends k j).2 ((hlabel k j _ (hEsub k (hrightSource k))).mpr ⟨hL,hh⟩)
      obtain ⟨B,hB,hBi,_,hgraph⟩ := position_proper_affine_crosscut (T k) (hTsquare k) ha0 hb0
      exact ⟨B,hB,hBi,fun _ _ => hgraph⟩
  choose B hB hBi hBgraph using hTargets
  obtain ⟨G,d2,hd2image,hd2class,hd2replace⟩ := position_finite_surface_replacement S d1
    (Fin n) E hEdis hEsquare A hA hAi hactual B hB hBi
  have hBsq (k : Fin n) : B k ⊆ Schoenflies.Plane.closedSquare 0 1 := by
    intro z hz
    by_cases he : z ∈ ({Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} : Set Schoenflies.Plane)
    · rcases he with rfl | he
      · norm_num [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,Schoenflies.Plane.mk]
      · rw [Set.mem_singleton_iff.mp he]
        norm_num [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,Schoenflies.Plane.mk]
    · exact Schoenflies.Plane.openSquare_subset_closedSquare 0 1 (hBi k ⟨hz,he⟩)
  have hd2local (k : Fin n) (x : S) (hx : x ∈ (E k).source)
      (hxo : E k x ∈ Schoenflies.Plane.openSquare 0 1) :
      x ∈ d2.val.image ↔ E k x ∈ B k := by
    rw [hd2replace]
    constructor
    · intro h
      rcases h with h | h
      · have hAselect : x ∈ {x : S | x ∈ (E k).source ∧ E k x ∈ A} := by
          rw [← hactual k]
          exact ⟨⟨hx,Schoenflies.Plane.openSquare_subset_closedSquare 0 1 hxo⟩,h.1⟩
        exact False.elim (h.2 (Set.mem_iUnion.mpr ⟨k,hAselect⟩))
      · obtain ⟨l,hl⟩ := Set.mem_iUnion.mp h
        by_cases hkl : k = l
        · subst l
          exact hl.2
        · exact False.elim (Set.disjoint_left.mp (hEdis k l hkl) hx hl.1)
    · intro h
      exact Or.inr (Set.mem_iUnion.mpr ⟨k,hx,h⟩)
  have hTimage (k : Fin n) (x : S) (hx : x ∈ (E k).source) :
      e k x ∈ T k '' B k ↔ E k x ∈ B k := by
    constructor
    · rintro ⟨z,hz,heq⟩
      have hzT := hTsquare k (hBsq k hz)
      have hzE : z ∈ (E k).target := hzT.1
      have hze : (E k).symm z ∈ (e k).source := hzT.2
      have hsymm : (E k).symm z = x :=
        (e k).injOn hze (hEsub k hx) heq
      have hzcoord : z = E k x := by rw [← hsymm,(E k).right_inv hzE]
      exact hzcoord ▸ hz
    · intro hz
      refine ⟨E k x,hz,?_⟩
      change e k ((E k).symm (E k x)) = e k x
      rw [(E k).left_inv hx]
  refine ⟨d2,hd2class.trans hd1,?_⟩
  intro j
  apply hcrossingsFinite
  intro p hp
  have hpBunion : p ∈ ⋃ k, {x : S | x ∈ (E k).source ∧ E k x ∈ B k} := by
    rw [hd2replace] at hp
    rcases hp.2 with hrem | hBmem
    · have hrem' : p ∈ d1.val.image \ ⋃ k,
          (fun t => d1.val.map (Circle.exp t)) '' Set.Icc (a k) (b k) := by
        simpa only [hselected] using hrem
      exact False.elim (Set.disjoint_left.mp (hremainder j) hrem' hp.1)
    · exact hBmem
  obtain ⟨k,hpk⟩ := Set.mem_iUnion.mp hpBunion
  have hpe : p ∈ (e k).source := hEsub k hpk.1
  have hplabel : label k = some j := ((hlabel k j p hpe).mp hp.1).1
  have hp0 : e k p 0 = 0 := ((hlabel k j p hpe).mp hp.1).2
  have hpint : E k p ∈ Schoenflies.Plane.openSquare 0 1 := by
    apply hBi k
    refine ⟨hpk.2,?_⟩
    intro he
    rcases he with he | he
    · have hpa : p = d1.val.map (Circle.exp (a k)) := by
        rw [← hleftInv k,← he,(E k).left_inv hpk.1]
      exact (hends k j).1 (hpa ▸ hp.1)
    · have hpb : p = d1.val.map (Circle.exp (b k)) := by
        rw [← hrightInv k,← Set.mem_singleton_iff.mp he,(E k).left_inv hpk.1]
      exact (hends k j).2 (hpb ▸ hp.1)
  have hpT : e k p ∈ T k '' B k := (hTimage k p hpk.1).mpr hpk.2
  obtain ⟨W,hWo,hpW,hWtarget,m,hm⟩ := hBgraph k j hplabel (e k p) ⟨hpT,hp0⟩
  have hnear : (E k).source ∩ ((E k) ⁻¹' Schoenflies.Plane.openSquare 0 1 ∩ (e k) ⁻¹' W) ∈ nhds p :=
    Filter.inter_mem ((E k).open_source.mem_nhds hpk.1)
      (Filter.inter_mem (((E k).continuousAt hpk.1).preimage_mem_nhds
        ((Schoenflies.Plane.isOpen_openSquare 0 1).mem_nhds hpint))
        (((e k).continuousAt hpe).preimage_mem_nhds (hWo.mem_nhds hpW)))
  obtain ⟨V,hVsub,hVo,hpV⟩ := mem_nhds_iff.mp hnear
  let F := (e k).restr V
  have hFsource : F.source = (e k).source ∩ V := by
    rw [OpenPartialHomeomorph.restr_source,hVo.interior_eq]
  have hpF : p ∈ F.source := hFsource.symm ▸ ⟨hpe,hpV⟩
  apply hcrossPlanar (r j).val d2.val F p hpF hp0 m
  · intro x hx
    have hxe := (hFsource.le hx).1
    change x ∈ (r j).val.image ↔ e k x 0 = 0
    simpa only [hplabel,eq_self,true_and] using hlabel k j x hxe
  · intro x hx
    have hxV := (hFsource.le hx).2
    have hxloc := hVsub hxV
    change x ∈ d2.val.image ↔ e k x 1 = e k p 1+m*e k x 0
    rw [hd2local k x hxloc.1 hxloc.2.1,← hTimage k x hxloc.1]
    exact hm (e k x) hxloc.2.2


end CurveComplex
