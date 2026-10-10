import CurveComplexGenusTwo.Topology.BandGlobalGluing.NestedOverlapScaffold
import CurveComplexGenusTwo.Topology.CrosscutGlue
open Set Topology unitInterval
namespace CurveComplex
open Schoenflies

/-- Extend the given actual square embedding pointwise over the whole plane,
including agreement on its interior rather than just its boundary. -/
theorem exists_ambient_extension_of_embedded_closed_square
    (e : ↥(Plane.closedSquare 0 1) → Plane) (he : IsEmbedding e) :
    ∃ H : Plane ≃ₜ Plane, ∀ z : ↥(Plane.closedSquare 0 1), H z = e z := by
  classical
  have hboundary (k : ↥modelCurve → Plane) (hk : IsEmbedding k) :
      IsJordanCurve (Set.range k) ∧
        ∃ F : Plane ≃ₜ Plane, ∀ z : ↥modelCurve, F z = k z := by
  
    classical
    obtain ⟨f,hf,hfim⟩ := isJordanCurve_modelCurve
    have hfmem (t : I) : f t ∈ modelCurve := by
      rw [← hfim]
      exact ⟨t,t.property,rfl⟩
    let q : I → ↥modelCurve := fun t => ⟨f t,hfmem t⟩
    have hq : Continuous q := by
      exact (continuousOn_iff_continuous_restrict.mp hf.continuousOn).subtype_mk _
    let g : ℝ → Plane := fun t => k (q (projIcc 0 1 zero_le_one t))
    have hg : Continuous g := hk.continuous.comp
      (hq.comp continuous_projIcc)
    have hqeq (t : ℝ) (ht : t ∈ (Icc (0 : ℝ) 1)) :
        (q (projIcc 0 1 zero_le_one t) : Plane) = f t := by
      dsimp [q]
      rw [projIcc_of_mem zero_le_one ht]
    have hloop : IsLoop g := by
      refine ⟨hg.continuousOn, ?_, ?_⟩
      · apply congrArg k
        apply Subtype.ext
        rw [hqeq 0 (by norm_num),hqeq 1 (by norm_num)]
        exact hf.closes
      · intro s hs t ht he
        apply hf.injOn hs ht
        have hh := congrArg Subtype.val (hk.injective he)
        rw [hqeq s ⟨hs.1,hs.2.le⟩,hqeq t ⟨ht.1,ht.2.le⟩] at hh
        exact hh
    have him : g '' (Icc (0 : ℝ) 1) = Set.range k := by
      ext z
      constructor
      · rintro ⟨t,ht,rfl⟩
        exact Set.mem_range_self _
      · rintro ⟨v,rfl⟩
        have hvm : (v : Plane) ∈ f '' (Icc (0 : ℝ) 1) := hfim.symm ▸ v.property
        obtain ⟨t,ht,he⟩ := hvm
        refine ⟨t,ht,?_⟩
        apply congrArg k
        apply Subtype.ext
        exact (hqeq t ht).trans he
    have hJ : IsJordanCurve (Set.range k) := ⟨g,hloop,him⟩
    obtain ⟨F,hF⟩ := jordan_schoenflies_of_homeomorph
      isJordanCurve_modelCurve hJ hk.toHomeomorph
    exact ⟨hJ,F,fun z => hF z⟩
  
  have hinterior (e : ↥(Plane.closedSquare 0 1) → Plane) (he : IsEmbedding e) :
      IsPreconnected (interior (Set.range e)) ∧
        (interior (Set.range e)).Nonempty := by
  
    let K := Plane.closedSquare 0 1
    let A : Set ↥K := {z | (z : Plane) ∈ interior K}
    have hAimage : Subtype.val '' A = interior K := by
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩; exact hw
      · intro hz; exact ⟨⟨z,interior_subset hz⟩,hz,rfl⟩
    have hAconn : IsPreconnected A := by
      apply IsInducing.subtypeVal.isPreconnected_image.mp
      rw [hAimage]
      change IsPreconnected (interior (Plane.closedSquare 0 1))
      rw [Plane.interior_closedSquare]
      exact (Plane.convex_openSquare 0 1).isPreconnected
    have heA : e '' A = interior (Set.range e) := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact (embedded_planar_region_interior_iff_probe K e he z).mpr hz
      · intro hy
        obtain ⟨z,rfl⟩ := interior_subset hy
        exact ⟨z,(embedded_planar_region_interior_iff_probe K e he z).mp hy,rfl⟩
    have hzero : (0 : Plane) ∈ interior K := by
      change (0 : Plane) ∈ interior (Plane.closedSquare 0 1)
      rw [Plane.interior_closedSquare]
      simp [Plane.openSquare,Plane.supNorm]
    refine ⟨heA ▸ hAconn.image e he.continuous.continuousOn, ?_⟩
    exact ⟨e ⟨0,interior_subset hzero⟩,
      (embedded_planar_region_interior_iff_probe K e he _).mpr hzero⟩
  have hside (K : Set Plane) (hK : IsCompact K)
      (hconn : IsPreconnected (interior K)) (hne : (interior K).Nonempty)
      (hJ : IsJordanCurve (frontier K)) :
      K = frontier K ∪ inside (frontier K) := by
  
    obtain ⟨x,hx⟩ := hne
    have hsub : interior K ⊆ (frontier K)ᶜ := by
      intro z hz hzfr
      exact hzfr.2 hz
    have hfr : frontier (interior K) ∩ (frontier K)ᶜ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hz.2 (frontier_interior_subset hz.1)
    have hcomp : connectedComponentIn (frontier K)ᶜ x = interior K :=
      Plane.connectedComponentIn_eq_of_frontier_disjoint
        isOpen_interior hconn hsub hfr hx
    have hxin : x ∈ inside (frontier K) := by
      refine ⟨hsub hx, ?_⟩
      rw [hcomp]
      exact hK.isBounded.subset interior_subset
    have hi : interior K = inside (frontier K) :=
      hcomp.symm.trans ((jordan_curve_theorem hJ).connectedComponentIn_eq_inside hxin)
    calc
      K = interior K ∪ frontier K := by
        rw [← closure_eq_interior_union_frontier, hK.isClosed.closure_eq]
      _ = frontier K ∪ inside (frontier K) := by rw [hi,union_comm]
  
  let b : ↥modelCurve → ↥(Plane.closedSquare 0 1) :=
    fun z => ⟨z,modelCurve_subset_closedSquare z.property⟩
  have hbc : Continuous b := continuous_subtype_val.subtype_mk _
  have hbi : Function.Injective b := by
    intro z w hh
    apply Subtype.ext
    exact congrArg (fun v : ↥(Plane.closedSquare 0 1) => (v : Plane)) hh
  letI : CompactSpace ↥modelCurve :=
    isCompact_iff_compactSpace.mp isJordanCurve_modelCurve.isCompact
  have hb : IsEmbedding b := (hbc.isClosedEmbedding hbi).isEmbedding
  letI : CompactSpace ↥(Plane.closedSquare 0 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
  let k : ↥modelCurve → Plane := e ∘ b
  have hk : IsEmbedding k := he.comp hb
  have hfr : Set.range k = frontier (Set.range e) := by
    have hclosed : IsClosed (Set.range e) := (isCompact_range he.continuous).isClosed
    rw [hclosed.frontier_eq]
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      refine ⟨Set.mem_range_self (b z), ?_⟩
      intro hi
      have hizin := (embedded_planar_region_interior_iff_probe
        (Plane.closedSquare 0 1) e he (b z)).mp hi
      have hzfront : (z : Plane) ∈ frontier (Plane.closedSquare 0 1) := by
        rw [← modelCurve_eq_frontier]; exact z.property
      exact hzfront.2 hizin
    · rintro ⟨⟨z,rfl⟩,hzout⟩
      have hzfront : (z : Plane) ∈ frontier (Plane.closedSquare 0 1) := by
        rw [(Plane.isClosed_closedSquare 0 1).frontier_eq]
        refine ⟨z.property, ?_⟩
        intro hizin
        exact hzout ((embedded_planar_region_interior_iff_probe
          (Plane.closedSquare 0 1) e he z).mpr hizin)
      have hzm : (z : Plane) ∈ modelCurve := by
        rw [modelCurve_eq_frontier]; exact hzfront
      refine ⟨⟨z,hzm⟩,?_⟩
      change e (b _) = e z
      congr 1
  have hJ : IsJordanCurve (frontier (Set.range e)) :=
    hfr ▸ (hboundary k hk).1
  have hK : Set.range e = frontier (Set.range e) ∪ inside (frontier (Set.range e)) :=
    hside (Set.range e) (isCompact_range he.continuous)
      (hinterior e he).1 (hinterior e he).2 hJ
  let J := frontier (Set.range e)
  let Q := Plane.closedSquare 0 1
  have hQ : Q = modelCurve ∪ inside modelCurve := by
    rw [inside_modelCurve, modelCurve_eq_frontier, ← Plane.interior_closedSquare]
    rw [union_comm, ← closure_eq_interior_union_frontier,
      (Plane.isClosed_closedSquare 0 1).closure_eq]
  let eb : ↥modelCurve ≃ₜ ↥J :=
    hk.toHomeomorph.trans (Homeomorph.setCongr hfr)
  obtain ⟨f,g,hfg,hfe⟩ := exists_isHomeoOn_of_homeomorph eb
  obtain ⟨Fi,Gi,hFi,hFie⟩ := exists_isHomeoOn_of_homeomorph he.toHomeomorph
  obtain ⟨Fe,Ge,hFe,hFee⟩ := exterior_extension_of_squareExtension
    squareExtension isJordanCurve_modelCurve hJ hfg
  have hmeet (C : Set Plane) : (C ∪ inside C) ∩ (C ∪ outside C) = C := by
    ext z
    constructor
    · rintro ⟨hz,hz'⟩
      rcases hz with hz | hz
      · exact hz
      rcases hz' with hz' | hz'
      · exact hz'
      exact False.elim (Set.disjoint_left.mp disjoint_inside_outside hz hz')
    · intro hz; exact ⟨Or.inl hz,Or.inl hz⟩
  have hagree : ∀ z ∈ Q ∩ (modelCurve ∪ outside modelCurve), Fi z = Fe z := by
    intro z hz
    have hzm : z ∈ modelCurve := by rw [hQ,hmeet] at hz; exact hz
    rw [hFie z (modelCurve_subset_closedSquare hzm),hFee hzm,hfe z hzm]
    rfl
  have him : Fi '' (Q ∩ (modelCurve ∪ outside modelCurve)) =
      Set.range e ∩ (J ∪ outside J) := by
    rw [hQ,hmeet,hK,hmeet]
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      rw [hFie z (modelCurve_subset_closedSquare hz)]
      change e (b ⟨z,hz⟩) ∈ J
      change e (b ⟨z,hz⟩) ∈ frontier (Set.range e)
      rw [← hfr]
      exact ⟨(⟨z,hz⟩ : ↥modelCurve),rfl⟩
    · intro hy
      rw [← hfr] at hy
      obtain ⟨z,rfl⟩ := hy
      refine ⟨z,z.property,?_⟩
      exact hFie z (modelCurve_subset_closedSquare z.property)
  obtain ⟨F,G,hFG,hFQ,_⟩ := glue_closed_homeoOn
    (Plane.isClosed_closedSquare 0 1)
    (isClosed_union_outside (jordan_curve_theorem isJordanCurve_modelCurve))
    (isCompact_range he.continuous).isClosed
    (isClosed_union_outside (jordan_curve_theorem hJ)) hFi hFe hagree him
  have hdom : Q ∪ (modelCurve ∪ outside modelCurve) = Set.univ := by
    rw [hQ,union_inside_union_outside]
  have htar : Set.range e ∪ (J ∪ outside J) = Set.univ := by
    change Set.range e ∪ (frontier (Set.range e) ∪ outside (frontier (Set.range e))) = Set.univ
    nth_rw 1 [hK]
    exact union_inside_union_outside _
  have hglobal : IsHomeoOn F G Set.univ Set.univ := by
    change IsHomeoOn F G (Q ∪ (modelCurve ∪ outside modelCurve))
      (Set.range e ∪ (J ∪ outside J)) at hFG
    simpa only [hdom,htar] using hFG
  refine ⟨hglobal.homeomorphOfUniv,?_⟩
  intro z
  exact (hFQ z z.property).trans (hFie z z.property)
end CurveComplex
