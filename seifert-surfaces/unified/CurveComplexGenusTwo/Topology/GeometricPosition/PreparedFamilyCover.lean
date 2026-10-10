import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChartV2
import CurveComplexGenusTwo.Topology.GeometricPosition.FiniteSeamAvoidanceV2
import CurveComplexGenusTwo.Topology.IsotopyCurveTransport
namespace CurveComplex
open Set
/-- Move the new actual curve off all pair intersections of the unchanged
finite transverse family, then cover it by old-family coordinate patches.
Each patch contains either no old member or exactly one old member as axis 0. -/
theorem position_prepared_family_cover
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (J : Type*) [Fintype J] (r : J → EssentialCurve S)
    (hr : ∀ i j, i ≠ j → Transverse (r i).val (r j).val)
    (c : EssentialCurve S) :
    ∃ d : EssentialCurve S,
      Quotient.mk (essentialCurveSetoid S) d = Quotient.mk (essentialCurveSetoid S) c ∧
      ∃ e : d.val.image → OpenPartialHomeomorph S Schoenflies.Plane,
        (∀ p, p.val ∈ (e p).source) ∧
        (∀ p, ∃ i : Option J, ∀ j x, x ∈ (e p).source →
          (x ∈ (r j).val.image ↔ i = some j ∧ e p x 0 = 0)) := by
  classical
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
  let Pair := {ij : J × J // ij.1 ≠ ij.2}
  let bad : Set S := ⋃ ij : Pair, (r ij.val.1).val.image ∩ (r ij.val.2).val.image
  have hbad : bad.Finite := Set.finite_iUnion (fun ij => (hr _ _ ij.property).1)
  obtain ⟨H,hHavoid,_⟩ := PositionUniverseV2.position_finite_seam_avoidance S Unit
    (fun _ => c.val) hbad.toFinset Set.univ isOpen_univ (subset_univ _)
  obtain ⟨G,hG⟩ := hreverse H
  obtain ⟨d,hdimage,hdclass⟩ := position_essential_curve_of_isotopy G c
  have hdavoid : Disjoint d.val.image bad := by
    rw [Set.disjoint_left]
    intro p hp hpb
    rw [hdimage] at hp
    obtain ⟨x,hx,hxp⟩ := hp
    have hh : H.finalMap p = x := by rw [← hxp,hG]
    exact hHavoid p (hbad.mem_toFinset.mpr hpb) () (hh ▸ hx)
  have hunique (p : S) (hp : p ∈ d.val.image) (i j : J)
      (hi : p ∈ (r i).val.image) (hj : p ∈ (r j).val.image) : i = j := by
    by_contra hij
    exact (Set.disjoint_left.mp hdavoid) hp
      (Set.mem_iUnion.mpr ⟨⟨(i,j),hij⟩,hi,hj⟩)
  have hclosed (j : J) : IsClosed (r j).val.image :=
    (isCompact_range (r j).val.embedded.continuous).isClosed
  let L : Schoenflies.Plane ≃ₜ ℝ × ℝ :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
  let flip : Schoenflies.Plane ≃ₜ Schoenflies.Plane :=
    (L.trans (Homeomorph.prodComm ℝ ℝ)).trans L.symm
  have hflip (z : Schoenflies.Plane) : flip z 0 = z 1 := rfl
  have hlocal (p : d.val.image) :
      ∃ E : OpenPartialHomeomorph S Schoenflies.Plane,
        p.val ∈ E.source ∧ ∃ i : Option J, ∀ j x, x ∈ E.source →
          (x ∈ (r j).val.image ↔ i = some j ∧ E x 0 = 0) := by
    by_cases hex : ∃ i : J, p.val ∈ (r i).val.image
    · obtain ⟨i,hpi⟩ := hex
      let other : Set S := ⋃ j : {j : J // j ≠ i}, (r j.val).val.image
      have ho : IsOpen otherᶜ :=
        (isClosed_iUnion_of_finite (fun j : {j : J // j ≠ i} => hclosed j.val)).isOpen_compl
      have hpo : p.val ∉ other := by
        intro hpother
        obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hpother
        exact j.property (hunique p.val p.property j.val i hj hpi)
      obtain ⟨E0,hpE0,_,hE0sub,_,hflat⟩ :=
        PositionUniverseV2.position_curve_crosscut_chart S (r i).val p.val hpi otherᶜ ho hpo
      let E := E0.trans flip.toOpenPartialHomeomorph
      have hsource : E.source = E0.source := by
        ext x; simp [E,OpenPartialHomeomorph.trans_source]
      refine ⟨E,hsource.symm ▸ hpE0,some i,?_⟩
      intro j x hx
      have hx0 : x ∈ E0.source := hsource ▸ hx
      have hcoord : E x 0 = E0 x 1 := hflip (E0 x)
      by_cases hij : i = j
      · subst j
        simpa only [Option.some.injEq,eq_self,true_and,hcoord] using hflat x hx0
      · have hxnot : x ∉ (r j).val.image := by
          intro hj
          exact hE0sub hx0 (Set.mem_iUnion.mpr ⟨⟨j,Ne.symm hij⟩,hj⟩)
        simp only [Option.some.injEq,hij,false_and,iff_false]
        exact hxnot
    · let other : Set S := ⋃ j, (r j).val.image
      have ho : IsOpen otherᶜ := (isClosed_iUnion_of_finite hclosed).isOpen_compl
      have hpo : p.val ∉ other := by
        intro hpother
        obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hpother
        exact hex ⟨j,hj⟩
      let E0 := chartAt Schoenflies.Plane p.val
      let E := E0.restr otherᶜ
      have hsource : E.source = E0.source ∩ otherᶜ := by
        rw [OpenPartialHomeomorph.restr_source,ho.interior_eq]
      refine ⟨E,hsource.symm ▸ ⟨mem_chart_source _ _,hpo⟩,none,?_⟩
      intro j x hx
      have hx' := hsource.le hx
      constructor
      · intro hj
        exact False.elim (hx'.2 (Set.mem_iUnion.mpr ⟨j,hj⟩))
      · rintro ⟨h,_⟩; cases h
  choose e hp hi using hlocal
  exact ⟨d,hdclass,e,hp,hi⟩

end CurveComplex
