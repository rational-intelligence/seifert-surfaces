import CurveComplexGenusTwo.Topology.ActualModelHomology.SourceSurvivingRawCircleIntervalHomeomorphism
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryHandleEdges
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryRawInteriorFibers
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryRawCurveCover

namespace CurveComplex.Hyperbolic.OneBoundaryRay
open Set Topology

abbrev ActualEdgeParameterSpace (p : ℕ) :=
  ((Fin p × Bool) × unitInterval) ⊕ Ico (0 : ℝ) 1

noncomputable def survivingSeamRaw (p : ℕ) (t : Ico (0 : ℝ) 1) :
    RawSurvivingBoundary p := by
  refine ⟨⟨rawBoundaryPoint p (-t.val), ?_⟩, Circle.norm_coe _⟩
  change Complex.ClosedUnitDisc.bdyPtOfReal (-t.val / modelSideCount p) ∉ rawDeletedArc p
  rw [rawDeletedArc_scaled_boundary_iff]
  have he : 3 + 2 * (-t.val) = 3 - 2 * t.val := by ring
  rw [he, seam_cap_cos_iff p t.val t.property.1 t.property.2.le]
  exact ne_of_lt t.property.2

noncomputable def actualEdgeParameterMap (p : ℕ) :
    ActualEdgeParameterSpace p → actualSurvivingBoundary p :=
  Sum.elim (fun x => handleEdge p x.1.1 x.1.2 x.2)
    (fun t => survivingBoundaryQuotientMap p (survivingSeamRaw p t))

private theorem actualEdgeParameterMap_continuous (p : ℕ) :
    Continuous (actualEdgeParameterMap p) := by
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_prod_of_discrete_left.mpr (fun k => (handleEdge p k.1 k.2).continuous)
  · apply (survivingBoundaryQuotientMap p).continuous.comp
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by
      fun_prop))

private noncomputable def pairedHandleRaw (p : ℕ) (i : Fin p) (b : Bool) (e : Bool) :
    C(unitInterval, RawSurvivingBoundary p) where
  toFun t := ⟨⟨rawEdgePoint (.inl (i,b)) t e, by
    cases e
    · simpa [handleEdgeRaw, rawEdgePoint_handle, rawBoundaryPoint, handleNumerator] using
        (handleEdgeRaw p i b t).val.property
    · exact (rawDeletedArc_rel_invariant p (raw_edge_points_related (.inl (i,b)) t)).not.mp
        (by simpa [handleEdgeRaw, rawEdgePoint_handle, rawBoundaryPoint, handleNumerator] using
          (handleEdgeRaw p i b t).val.property)⟩, Circle.norm_coe _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by
      unfold rawEdgeNumerator rawEdgeSlot rawEdgeFraction
      cases e <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop))

private theorem pairedHandleRaw_quotient (p : ℕ) (i : Fin p) (b e : Bool) (t : unitInterval) :
    survivingBoundaryQuotientMap p (pairedHandleRaw p i b e t) = handleEdge p i b t := by
  apply Subtype.ext
  apply Subtype.ext
  change Quot.mk _ (rawEdgePoint (.inl (i,b)) t e) =
    Quot.mk _ (Complex.ClosedUnitDisc.bdyPtOfReal (handleNumerator i b t / modelSideCount p))
  have hf : rawEdgePoint (.inl (i,b)) t false =
    Complex.ClosedUnitDisc.bdyPtOfReal (handleNumerator i b t / modelSideCount p) := by
    simp [rawEdgePoint_handle, rawBoundaryPoint, handleNumerator]
  rw [← hf]
  cases e
  · rfl
  · exact (Quot.sound (raw_edge_points_related (.inl (i,b)) t)).symm

private theorem raw_handle_numeric_side_cover (p : ℕ) (s : ℝ) (hs0 : 0≤ s) (hs1 : s<4*(p:ℝ)) :
    ∃ i : Fin p, ∃ b : Bool, ∃ t : unitInterval, ∃ e : Bool,
      rawBoundaryPoint p s = rawEdgePoint (.inl (i,b)) t e := by
  let k : ℕ := Nat.floor s
  have hklt : k<4*p := by
    apply (Nat.floor_lt hs0).mpr
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hs1
  let i : Fin p := ⟨k/4,by omega⟩
  have hk0 : (k:ℝ)≤ s := Nat.floor_le hs0
  have hk1 : s<(k:ℝ)+1 := Nat.lt_floor_add_one s
  let x : unitInterval := ⟨s-(k:ℝ),by constructor <;> linarith⟩
  have hk : k=4*i.val+k%4 := by dsimp [i]; omega
  have hkr : (k:ℝ)=4*(i:ℝ)+((k%4:ℕ):ℝ) := by exact_mod_cast hk
  have hn : s=4*(i:ℝ)+((k%4:ℕ):ℝ)+(x:ℝ) := by dsimp [x]; linarith
  have hj : k%4=0 ∨ k%4=1 ∨ k%4=2 ∨ k%4=3 := by omega
  rcases hj with hj|hj|hj|hj
  · refine ⟨i,false,x,false,?_⟩
    have hp : rawEdgePoint (.inl (i,false)) x false=rawBoundaryPoint p s := by
      rw [rawEdgePoint_handle]
      simp only [Bool.false_eq_true,↓reduceIte,add_zero]
      congr 1
      simpa only [hj,Nat.cast_zero,add_zero] using hn.symm
    exact hp.symm
  · refine ⟨i,true,x,false,?_⟩
    have hp : rawEdgePoint (.inl (i,true)) x false=rawBoundaryPoint p s := by
      rw [rawEdgePoint_handle]
      simp only [Bool.false_eq_true,Bool.true_eq,↓reduceIte]
      congr 1
      simpa only [hj,Nat.cast_one] using hn.symm
    exact hp.symm
  · refine ⟨i,false,unitInterval.symm x,true,?_⟩
    have hp : rawEdgePoint (.inl (i,false)) (unitInterval.symm x) true=rawBoundaryPoint p s := by
      rw [rawEdgePoint_handle]
      change rawBoundaryPoint p (4*(i:ℝ)+3-(1-(x:ℝ)))=rawBoundaryPoint p s
      congr 1
      norm_num [hj] at hn
      linarith
    exact hp.symm
  · refine ⟨i,true,unitInterval.symm x,true,?_⟩
    have hp : rawEdgePoint (.inl (i,true)) (unitInterval.symm x) true=rawBoundaryPoint p s := by
      rw [rawEdgePoint_handle]
      change rawBoundaryPoint p (4*(i:ℝ)+4-(1-(x:ℝ)))=rawBoundaryPoint p s
      congr 1
      norm_num [hj] at hn
      linarith
    exact hp.symm


private theorem raw_numeric_full_cover (p : ℕ) (s : ℝ)
    (hs0 : -1 < s) (hs1 : s < 4*(p:ℝ)+1) :
    (∃ i : Fin p, ∃ b : Bool, ∃ t : unitInterval, ∃ e : Bool,
      rawBoundaryPoint p s = rawEdgePoint (.inl (i,b)) t e) ∨
    (∃ t : Ico (0:ℝ) 1, ∃ e : Bool,
      rawBoundaryPoint p s = rawEdgePoint (p:=p) (.inr ())
        ⟨t.val, t.property.1, t.property.2.le⟩ e) := by
  by_cases hn : s < 0
  · right
    refine ⟨⟨-s, by constructor <;> linarith⟩, false, ?_⟩
    rw [rawEdgePoint_seam]
    change rawBoundaryPoint p s = rawBoundaryPoint p (-(-s))
    rw [neg_neg]
  · by_cases hm : s < 4*(p:ℝ)
    · exact Or.inl (raw_handle_numeric_side_cover p s (le_of_not_gt hn) hm)
    · right
      refine ⟨⟨s-4*(p:ℝ), by constructor <;> linarith⟩, true, ?_⟩
      have he : s = 4*(p:ℝ)+(s-4*(p:ℝ)) := by ring
      exact (congrArg (rawBoundaryPoint p) he).trans
        (seam_right_normalized_point p ⟨s-4*(p:ℝ), by constructor <;> linarith⟩)

private noncomputable def seamCoordinate (p : ℕ) (e : Bool) :
    Ico (0:ℝ) 1 → Ioo (-1:ℝ) (4*(p:ℝ)+1) := fun t =>
  ⟨if e then 4*(p:ℝ)+t.val else -t.val, by
    have hp : (0:ℝ) ≤ p := by positivity
    cases e <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith [t.property.1, t.property.2]⟩

private theorem seamCoordinate_isClosedMap (p : ℕ) (e : Bool) :
    IsClosedMap (seamCoordinate p e) := by
  let A : Set (Ioo (-1:ℝ) (4*(p:ℝ)+1)) :=
    {s | if e then 4*(p:ℝ) ≤ s.val else s.val ≤ 0}
  have hA : IsClosed A := by
    cases e <;> simp only [A, Bool.false_eq_true, ↓reduceIte]
    · exact isClosed_le continuous_subtype_val continuous_const
    · exact isClosed_le continuous_const continuous_subtype_val
  let H : Ico (0:ℝ) 1 ≃ₜ A := {
    toFun t := ⟨seamCoordinate p e t, by
      cases e
      · change -t.val ≤ 0
        linarith [t.property.1]
      · change 4*(p:ℝ) ≤ 4*(p:ℝ)+t.val
        linarith [t.property.1]⟩
    invFun s := ⟨if e then s.val.val-4*(p:ℝ) else -s.val.val, by
      have ha := s.property
      have hs := s.val.property
      cases e <;> simp only [A, Set.mem_setOf_eq, Bool.false_eq_true, ↓reduceIte] at ha ⊢
      all_goals constructor <;> linarith [hs.1, hs.2]⟩
    left_inv := by intro t; apply Subtype.ext; cases e <;> simp [seamCoordinate]
    right_inv := by intro s; apply Subtype.ext; apply Subtype.ext
                    cases e <;> simp [seamCoordinate]
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      cases e <;> simp only [seamCoordinate, Bool.false_eq_true, ↓reduceIte]
      all_goals fun_prop
    continuous_invFun := by
      apply Continuous.subtype_mk
      cases e <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals fun_prop
  }
  exact hA.isClosedEmbedding_subtypeVal.isClosedMap.comp H.isClosedMap

private theorem finite_family_isClosedMap {ι X Y : Type*} [Finite ι]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace ι]
    (f : ι × X → Y) (hf : ∀ i, IsClosedMap (fun x => f (i,x))) : IsClosedMap f := by
  intro A hA
  have he : f '' A = ⋃ i, (fun x => f (i,x)) '' ((fun x => (i,x)) ⁻¹' A) := by
    ext y
    simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨⟨i,x⟩, hx, rfl⟩
      exact ⟨i,x,hx,rfl⟩
    · rintro ⟨i,x,hx,rfl⟩
      exact ⟨(i,x),hx,rfl⟩
  rw [he]
  exact isClosed_iUnion_of_finite (fun i => hf i _ (hA.preimage (continuous_const.prodMk continuous_id)))

theorem source_actual_edge_parameter_map_isQuotientMap (p : ℕ) :
    IsQuotientMap (actualEdgeParameterMap p) := by
  classical
  obtain ⟨T,hT⟩ := source_surviving_raw_circle_interval_homeomorphism p
  let Fh : ((Fin p × Bool) × Bool) × unitInterval → RawSurvivingBoundary p :=
    fun x => pairedHandleRaw p x.1.1.1 x.1.1.2 x.1.2 x.2
  let Fc : Bool × Ico (0:ℝ) 1 → RawSurvivingBoundary p :=
    fun x => T (seamCoordinate p x.1 x.2)
  let F := Sum.elim Fh Fc
  have hFh : Continuous Fh := continuous_prod_of_discrete_left.mpr
    (fun k => (pairedHandleRaw p k.1.1 k.1.2 k.2).continuous)
  have hFc : Continuous Fc := by
    apply continuous_prod_of_discrete_left.mpr
    intro e
    apply T.continuous.comp
    apply Continuous.subtype_mk
    cases e <;> simp only [seamCoordinate, Bool.false_eq_true, ↓reduceIte]
    all_goals fun_prop
  have hFC : Continuous F := continuous_sum_dom.mpr ⟨hFh,hFc⟩
  have hFclosed : IsClosedMap F := isClosedMap_sumElim.mpr ⟨hFh.isClosedMap,
    finite_family_isClosedMap Fc (fun e => T.isClosedMap.comp (seamCoordinate_isClosedMap p e))⟩
  have hFcval (e : Bool) (t : Ico (0:ℝ) 1) :
      (Fc (e,t)).val.val = rawEdgePoint (p:=p) (.inr ())
        ⟨t.val,t.property.1,t.property.2.le⟩ e := by
    rw [show (Fc (e,t)).val.val = rawBoundaryPoint p (seamCoordinate p e t).val from hT _]
    cases e
    · rw [rawEdgePoint_seam]; rfl
    · exact seam_right_normalized_point p ⟨t.val,t.property.1,t.property.2.le⟩
  have hFsurj : Function.Surjective F := by
    intro z
    obtain ⟨s,hs0,hs1,hs⟩ := surviving_raw_circle_normalization p z.val z.property
    rcases raw_numeric_full_cover p s hs0 hs1 with hh | hc
    · obtain ⟨i,b,t,e,he⟩ := hh
      refine ⟨Sum.inl (((i,b),e),t),?_⟩
      apply Subtype.ext; apply Subtype.ext
      exact he.symm.trans hs.symm
    · obtain ⟨t,e,he⟩ := hc
      refine ⟨Sum.inr (e,t),?_⟩
      apply Subtype.ext; apply Subtype.ext
      exact (hFcval e t).trans (he.symm.trans hs.symm)
  have hFQ : IsQuotientMap F := hFclosed.isQuotientMap hFC hFsurj
  let G : (((Fin p × Bool) × Bool) × unitInterval) ⊕ (Bool × Ico (0:ℝ) 1) →
      ActualEdgeParameterSpace p := Sum.elim
    (fun x => Sum.inl (x.1.1,x.2)) (fun x => Sum.inr x.2)
  have hGC : Continuous G := by
    apply continuous_sum_dom.mpr
    constructor
    · exact continuous_inl.comp ((continuous_fst.fst).prodMk continuous_snd)
    · exact continuous_inr.comp continuous_snd
  have hfactor : (survivingBoundaryQuotientMap p) ∘ F = actualEdgeParameterMap p ∘ G := by
    funext x
    cases x with
    | inl x => exact pairedHandleRaw_quotient p x.1.1.1 x.1.1.2 x.1.2 x.2
    | inr x =>
      apply Subtype.ext; apply Subtype.ext
      change Quot.mk _ (Fc x).val.val = Quot.mk _ (survivingSeamRaw p x.2).val.val
      rw [hFcval]
      have hf : (survivingSeamRaw p x.2).val.val = rawEdgePoint (p:=p) (.inr ())
          ⟨x.2.val,x.2.property.1,x.2.property.2.le⟩ false := by
        rw [rawEdgePoint_seam]; rfl
      rw [hf]
      cases he : x.1
      · rfl
      · exact (Quot.sound (raw_edge_points_related (p:=p) (.inr ())
          ⟨x.2.val,x.2.property.1,x.2.property.2.le⟩)).symm
  have hQ := (survivingBoundaryQuotientMap_isQuotientMap p).comp hFQ
  rw [hfactor] at hQ
  exact IsQuotientMap.of_comp hGC (actualEdgeParameterMap_continuous p) hQ

end CurveComplex.Hyperbolic.OneBoundaryRay
