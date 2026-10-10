import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundarySurvivingArcNormalization

namespace CurveComplex.Hyperbolic.OneBoundaryRay
open LeanEval.Topology.ClassificationOfSurfaces

theorem raw_handle_numeric_cover (p : ℕ) (s : ℝ) (hs0 : 0≤ s) (hs1 : s<4*(p:ℝ)) :
    ∃ i : Fin p, ∃ b : Bool, ∃ t : unitInterval,
      Quot.mk (OrientableRel p 1) (rawBoundaryPoint p s)=
        Quot.mk (OrientableRel p 1) (rawEdgePoint (.inl (i,b)) t false) := by
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
  · refine ⟨i,false,x,?_⟩
    have hp : rawEdgePoint (.inl (i,false)) x false=rawBoundaryPoint p s := by
      rw [rawEdgePoint_handle]
      simp only [Bool.false_eq_true,↓reduceIte,add_zero]
      congr 1
      simpa only [hj,Nat.cast_zero,add_zero] using hn.symm
    exact congrArg (Quot.mk (OrientableRel p 1)) hp.symm
  · refine ⟨i,true,x,?_⟩
    have hp : rawEdgePoint (.inl (i,true)) x false=rawBoundaryPoint p s := by
      rw [rawEdgePoint_handle]
      simp only [Bool.false_eq_true,Bool.true_eq,↓reduceIte]
      congr 1
      simpa only [hj,Nat.cast_one] using hn.symm
    exact congrArg (Quot.mk (OrientableRel p 1)) hp.symm
  · refine ⟨i,false,unitInterval.symm x,?_⟩
    have hp : rawEdgePoint (.inl (i,false)) (unitInterval.symm x) true=rawBoundaryPoint p s := by
      rw [rawEdgePoint_handle]
      change rawBoundaryPoint p (4*(i:ℝ)+3-(1-(x:ℝ)))=rawBoundaryPoint p s
      congr 1
      norm_num [hj] at hn
      linarith
    exact (congrArg (Quot.mk (OrientableRel p 1)) hp.symm).trans
      (Quot.sound (raw_edge_points_related (.inl (i,false)) (unitInterval.symm x))).symm
  · refine ⟨i,true,unitInterval.symm x,?_⟩
    have hp : rawEdgePoint (.inl (i,true)) (unitInterval.symm x) true=rawBoundaryPoint p s := by
      rw [rawEdgePoint_handle]
      change rawBoundaryPoint p (4*(i:ℝ)+4-(1-(x:ℝ)))=rawBoundaryPoint p s
      congr 1
      norm_num [hj] at hn
      linarith
    exact (congrArg (Quot.mk (OrientableRel p 1)) hp.symm).trans
      (Quot.sound (raw_edge_points_related (.inl (i,true)) (unitInterval.symm x))).symm

theorem surviving_raw_class_curve_cover (p : ℕ) (z : RawOpenDisk p)
    (hz : ‖(z.val:ℂ)‖=1) :
    (∃ i : Fin p, ∃ b : Bool, ∃ t : unitInterval,
      Quot.mk (OrientableRel p 1) z.val=
        Quot.mk (OrientableRel p 1) (rawEdgePoint (.inl (i,b)) t false)) ∨
    (∃ t : unitInterval, (t:ℝ)<1 ∧ Quot.mk (OrientableRel p 1) z.val=
      Quot.mk (OrientableRel p 1) (rawEdgePoint (p:=p) (.inr ()) t false)) := by
  obtain ⟨s,hs0,hs1,he⟩ := surviving_raw_circle_normalization p z hz
  rw [he]
  by_cases hn : s<0
  · right
    let t : unitInterval := ⟨-s,by constructor <;> linarith⟩
    refine ⟨t,by dsimp [t]; linarith,?_⟩
    have hp : rawEdgePoint (p:=p) (.inr ()) t false=rawBoundaryPoint p s := by
      rw [rawEdgePoint_seam]
      change rawBoundaryPoint p (-(-s))=rawBoundaryPoint p s
      rw [neg_neg]
    exact congrArg (Quot.mk (OrientableRel p 1)) hp.symm
  · by_cases hm : s<4*(p:ℝ)
    · exact Or.inl (raw_handle_numeric_cover p s (le_of_not_gt hn) hm)
    · right
      let t : unitInterval := ⟨s-4*(p:ℝ),by constructor <;> linarith⟩
      refine ⟨t,by dsimp [t]; linarith,?_⟩
      have hp : rawBoundaryPoint p s=rawEdgePoint (p:=p) (.inr ()) t true := by
        have he' : s=4*(p:ℝ)+(t:ℝ) := by dsimp [t]; ring
        rw [he']
        exact seam_right_normalized_point p t
      exact (congrArg (Quot.mk (OrientableRel p 1)) hp).trans
        (Quot.sound (raw_edge_points_related (p:=p) (.inr ()) t)).symm

end CurveComplex.Hyperbolic.OneBoundaryRay
