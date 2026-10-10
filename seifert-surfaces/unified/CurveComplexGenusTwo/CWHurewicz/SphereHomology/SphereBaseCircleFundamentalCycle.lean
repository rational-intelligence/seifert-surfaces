import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseStatements
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseCycleClasses
import CurveComplexGenusTwo.Foundations.OctagonQuotient
import CurveComplexGenusTwo.Octagon.OctagonAtlasCoverageWave10
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Convexity
open CurveComplexGenusTwo.CWHurewicz CircleHomologyComputation CurveComplex.Octagon
open scoped Simplicial
namespace CircleFundamentalCycle

noncomputable def coord {n : ℕ} (j : Fin (n+1)) :
    C(StdSimplex ℝ (Fin (n+1)), unitInterval) :=
  ⟨fun z => ⟨z.weights j, z.weights_nonneg j, z.weights_apply_le_one j⟩,
    (StdSimplex.continuous_weights_apply ℝ j).subtype_mk _⟩
noncomputable def circleSide (i : Side) : C(unitInterval, Circle) :=
  ⟨fun t => Circle.exp (2 * Real.pi * ((i.val : ℝ) + t) / 8), by fun_prop⟩
abbrev CircleSing (n : ℕ) := (TopCat.toSSet.obj (TopCat.of Circle)) _⦋n⦌
noncomputable def circleSideSimplex (i : Side) : CircleSing 1 :=
  (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌)).symm
    ((circleSide i).comp (coord 1))
noncomputable def circleBoundaryChain : CircleSing 1 →₀ ℤ :=
  ∑ i : Side, Finsupp.single (circleSideSimplex i) 1
noncomputable def circleVertex (i : Side) : CircleSing 0 :=
  (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋0⦌)).symm
    (ContinuousMap.const _ (circleSide i 0))
theorem circle_face1 (i : Side) :
    (TopCat.toSSet.obj (TopCat.of Circle)).δ 1 (circleSideSimplex i) = circleVertex i := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋0⦌)).injective
  apply ContinuousMap.ext
  intro z
  change circleSide i (coord 1 (z.map (1 : Fin 2).succAbove)) = circleSide i 0
  apply congrArg (circleSide i)
  apply Subtype.ext
  simp [coord, StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
    Fin.sum_univ_succ, Fin.succAbove]
theorem circle_face0 (i : Side) :
    (TopCat.toSSet.obj (TopCat.of Circle)).δ 0 (circleSideSimplex i) =
      circleVertex (next i) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋0⦌)).injective
  apply ContinuousMap.ext
  intro z
  change circleSide i (coord 1 (z.map (0 : Fin 2).succAbove)) = circleSide (next i) 0
  have hz : coord 1 (z.map (0 : Fin 2).succAbove) = 1 := by
    apply Subtype.ext
    simp [coord, StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
      Fin.sum_univ_succ, Fin.succAbove]
  rw [hz]
  apply Subtype.ext
  exact congrArg (fun x : Disk => (x : ℂ)) (side_end_next i)
theorem circle_boundary_is_cycle :
    singularBoundaryFinsupp (TopCat.of Circle) 0 circleBoundaryChain = 0 := by
  simp only [circleBoundaryChain, map_sum, singularBoundaryFinsupp_single]
  simp [Fin.sum_univ_succ, circle_face0, circle_face1, next]
  abel

abbrev X := TopCat.of Circle
abbrev U : Set X := CircleCoverGeometry.eastArc
abbrev V : Set X := CircleCoverGeometry.westArc

def eastPart : CircleSing 1 →₀ ℤ :=
  Finsupp.single (circleSideSimplex 1) 1 + Finsupp.single (circleSideSimplex 2) 1 +
  Finsupp.single (circleSideSimplex 3) 1 + Finsupp.single (circleSideSimplex 4) 1

def westPart : CircleSing 1 →₀ ℤ :=
  Finsupp.single (circleSideSimplex 5) 1 + Finsupp.single (circleSideSimplex 6) 1 +
  Finsupp.single (circleSideSimplex 7) 1 + Finsupp.single (circleSideSimplex 0) 1

def overlapBoundary : CircleSing 0 →₀ ℤ :=
  Finsupp.single (circleVertex 5) 1 - Finsupp.single (circleVertex 1) 1

theorem parts_sum : eastPart + westPart = circleBoundaryChain := by
  simp only [eastPart, westPart, circleBoundaryChain]
  simp [Fin.sum_univ_succ]
  abel

theorem east_boundary : singularBoundaryFinsupp X 0 eastPart = overlapBoundary := by
  simp only [eastPart, overlapBoundary, map_add, singularBoundaryFinsupp_single]
  simp [Fin.sum_univ_succ, circle_face0, circle_face1, next]
  abel

theorem west_boundary : singularBoundaryFinsupp X 0 westPart = -overlapBoundary := by
  simp only [westPart, overlapBoundary, map_add, singularBoundaryFinsupp_single]
  simp [Fin.sum_univ_succ, circle_face0, circle_face1, next]
  abel

lemma exp_ne_one_between {t : ℝ} (h0 : 0 < t) (h2 : t < 2 * Real.pi) :
    Circle.exp t ≠ 1 := by
  intro he
  have h := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by linarith)
    ⟨h0.le,h2⟩ ⟨le_rfl, by positivity⟩ (he.trans Circle.exp_zero.symm)
  linarith

lemma circleSide_mem_east (i : Side) (hi : 1 ≤ i.val ∧ i.val ≤ 4) (t : unitInterval) :
    circleSide i t ∈ U := by
  change Circle.exp _ ≠ 1
  apply exp_ne_one_between
  · have hti := t.property.1
    have hi' : (1:ℝ) ≤ i.val := by exact_mod_cast hi.1
    positivity
  · have hti := t.property.2
    have hi' : (i.val:ℝ) ≤ 4 := by exact_mod_cast hi.2
    nlinarith [Real.pi_pos]

lemma circle_exp_pi : Circle.exp Real.pi = -1 := by
  apply Subtype.ext
  exact Complex.exp_pi_mul_I

lemma circleSide_mem_west (i : Side) (hi : i = 0 ∨ 5 ≤ i.val) (t : unitInterval) :
    circleSide i t ∈ V := by
  change Circle.exp _ ≠ -1
  intro he
  rw [← circle_exp_pi] at he
  rcases hi with rfl | hi
  · norm_num only [Fin.val_zero, Nat.cast_zero] at he
    have ht0 := t.property.1
    have h := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by linarith)
      (x₁ := 2 * Real.pi * ((0:ℝ) + t) / 8) (x₂ := Real.pi) ?_ ?_ he
    · have := t.property.2
      nlinarith [Real.pi_pos]
    · constructor
      · positivity
      · have := t.property.2
        nlinarith [Real.pi_pos]
    · constructor <;> linarith [Real.pi_pos]
  · have hi' : (5:ℝ) ≤ i.val := by exact_mod_cast hi
    have hi'' : (i.val:ℝ) ≤ 7 := by exact_mod_cast (show i.val ≤ 7 by omega)
    have ht0 := t.property.1
    have ht1 := t.property.2
    have h := Circle.exp_injOn_Ioc (a := 0) (b := 2 * Real.pi) (by linarith)
      (x₁ := 2 * Real.pi * ((i.val:ℝ) + t) / 8) (x₂ := Real.pi) ?_ ?_ he
    · nlinarith [Real.pi_pos]
    · constructor <;> nlinarith [Real.pi_pos]
    · constructor <;> linarith [Real.pi_pos]


lemma single_supported {n : ℕ} (s : CircleSing n)
    (A : Set X) (h : ∀ t, TopCat.toSSetObjEquiv X (.op ⦋n⦌) s t ∈ A) :
    Finsupp.single s (1:ℤ) ∈ excisionSubspaceChains X A n := by
  intro q hq z hz
  have hqs : q = s := Finset.mem_singleton.mp (Finsupp.support_single_subset hq)
  subst q
  obtain ⟨t,rfl⟩ := hz
  exact h t

lemma east_supported : eastPart ∈ excisionSubspaceChains X U 1 := by
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact single_supported _ _ (fun t => circleSide_mem_east 1 (by decide) (coord 1 t))
      · exact single_supported _ _ (fun t => circleSide_mem_east 2 (by decide) (coord 1 t))
    · exact single_supported _ _ (fun t => circleSide_mem_east 3 (by decide) (coord 1 t))
  · exact single_supported _ _ (fun t => circleSide_mem_east 4 (by decide) (coord 1 t))

lemma west_supported : westPart ∈ excisionSubspaceChains X V 1 := by
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact single_supported _ _ (fun t => circleSide_mem_west 5 (by decide) (coord 1 t))
      · exact single_supported _ _ (fun t => circleSide_mem_west 6 (by decide) (coord 1 t))
    · exact single_supported _ _ (fun t => circleSide_mem_west 7 (by decide) (coord 1 t))
  · exact single_supported _ _ (fun t => circleSide_mem_west 0 (by decide) (coord 1 t))

def upperPoint : ↥(U ∩ V) := ⟨circleSide 1 0,
  circleSide_mem_east 1 (by decide) 0, by
    convert circleSide_mem_west 0 (by decide) 1 using 1 <;> norm_num [circleSide]⟩

def lowerPoint : ↥(U ∩ V) := ⟨circleSide 5 0, by
  convert circleSide_mem_east 4 (by decide) 1 using 1 <;> norm_num [circleSide],
  circleSide_mem_west 5 (by decide) 0⟩

def pointSimplex (p : ↥(U ∩ V)) : (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))) _⦋0⦌ :=
  (TopCat.toSSetObjEquiv _ (.op ⦋0⦌)).symm (ContinuousMap.const _ p)

def overlapOrdinaryChain : coverOrdinaryChains X (U ∩ V) 0 :=
  Finsupp.single (pointSimplex lowerPoint) 1 - Finsupp.single (pointSimplex upperPoint) 1

lemma overlapOrdinaryChain_push :
    coverOrdinaryPush X (U ∩ V) 0 overlapOrdinaryChain = overlapBoundary := by
  simp only [overlapOrdinaryChain, map_sub, coverOrdinaryPush,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

def eastOrdinaryChain : coverOrdinaryChains X U 1 :=
  (coverOrdinaryEquiv X U 1).symm ⟨eastPart,east_supported⟩
def westOrdinaryChain : coverOrdinaryChains X V 1 :=
  (coverOrdinaryEquiv X V 1).symm ⟨westPart,west_supported⟩

lemma eastOrdinaryChain_push : coverOrdinaryPush X U 1 eastOrdinaryChain = eastPart :=
  congrArg Subtype.val ((coverOrdinaryEquiv X U 1).apply_symm_apply _)
lemma westOrdinaryChain_push : coverOrdinaryPush X V 1 westOrdinaryChain = westPart :=
  congrArg Subtype.val ((coverOrdinaryEquiv X V 1).apply_symm_apply _)

def pairChain : (mvPairComplex X U V).X 1 := (eastOrdinaryChain,westOrdinaryChain)
def smallCycle : (mvSmallComplex X U V).X 1 := coverOrdinarySum X U V 1 pairChain

lemma smallCycle_val : smallCycle.val = circleBoundaryChain := by
  change coverOrdinaryPush X U 1 eastOrdinaryChain + coverOrdinaryPush X V 1 westOrdinaryChain = _
  rw [eastOrdinaryChain_push,westOrdinaryChain_push,parts_sum]

lemma pairChain_boundary :
    (mvDifference X U V).f 0 overlapOrdinaryChain = (mvPairComplex X U V).d 1 0 pairChain := by
  apply (coverOrdinaryPairEquiv X U V 0).injective
  apply Prod.ext <;> apply Subtype.ext
  · change coverOrdinaryPush X U 0 (coverOrdinaryDifference X U V 0 overlapOrdinaryChain).1 =
      coverOrdinaryPush X U 0 (singularBoundaryFinsupp (TopCat.of U) 0 eastOrdinaryChain)
    rw [coverOrdinaryDifference_push_fst, ← coverOrdinaryPush_boundary,
      overlapOrdinaryChain_push,eastOrdinaryChain_push,east_boundary]
  · change coverOrdinaryPush X V 0 (coverOrdinaryDifference X U V 0 overlapOrdinaryChain).2 =
      coverOrdinaryPush X V 0 (singularBoundaryFinsupp (TopCat.of V) 0 westOrdinaryChain)
    rw [coverOrdinaryDifference_push_snd, ← coverOrdinaryPush_boundary,
      overlapOrdinaryChain_push,westOrdinaryChain_push,west_boundary]

lemma smallCycle_is_cycle : (mvSmallComplex X U V).d 1 0 smallCycle = 0 := by
  apply Subtype.ext
  change singularBoundaryFinsupp X 0 smallCycle.val = 0
  rw [smallCycle_val]
  exact circle_boundary_is_cycle

def fundamentalClass : H Circle 1 :=
  (singularHomologyRepresentation X 1).hom
    (cycleClass (mvAmbientComplex X) 1 circleBoundaryChain circle_boundary_is_cycle)

/-- Exact source-chain representative and actual generator target, for statement review. -/
def FundamentalClassGenerates : Prop := ∀ x : H Circle 1, ∃ n : ℤ, n • fundamentalClass = x



lemma smallCycle_connecting :
    mvConnecting X U V 0 (cycleClass (mvSmallComplex X U V) 1 smallCycle smallCycle_is_cycle) =
      cycleClass (mvOrdinaryComplex X (U ∩ V)) 0 overlapOrdinaryChain (by rw [HomologicalComplex.shape _ _ _ (by simp)]; rfl) := by
  have h := (mvShortExact X U V).δ_eq 1 0 (by simp)
    (scalar _ smallCycle) (by dsimp only [mvShortComplex]; rw [scalar_naturality,smallCycle_is_cycle,scalar_eq_zero])
    (scalar _ pairChain) (by dsimp only [mvShortComplex]; rw [scalar_naturality]; rfl)
    (scalar _ overlapOrdinaryChain) (by dsimp only [mvShortComplex]; rw [scalar_naturality,scalar_naturality,pairChain_boundary])
    0 (by simp)
  exact congrArg (fun f => f (1:ℤ)) h

lemma fundamental_ambient_as_small :
    cycleClass (mvAmbientComplex X) 1 circleBoundaryChain circle_boundary_is_cycle =
      HomologicalComplex.homologyMap (mvSmallInclusion X U V) 1
        (cycleClass (mvSmallComplex X U V) 1 smallCycle smallCycle_is_cycle) := by
  have h := cycleClass_map (mvSmallInclusion X U V) 1 smallCycle smallCycle_is_cycle
    (show (mvAmbientComplex X).d 1 (1-1) ((mvSmallInclusion X U V).f 1 smallCycle) = 0 by
      change singularBoundaryFinsupp X 0 smallCycle.val = 0
      rw [smallCycle_val]; exact circle_boundary_is_cycle)
  symm
  simpa only [show (mvSmallInclusion X U V).f 1 smallCycle = circleBoundaryChain from smallCycle_val] using h

lemma fundamental_connecting :
    mvAmbientConnecting X U V CircleCoverGeometry.eastArc_open CircleCoverGeometry.westArc_open
      CircleCoverGeometry.arcs_cover 0
        (cycleClass (mvAmbientComplex X) 1 circleBoundaryChain circle_boundary_is_cycle) =
      cycleClass (mvOrdinaryComplex X (U ∩ V)) 0 overlapOrdinaryChain (by rw [HomologicalComplex.shape _ _ _ (by simp)]; rfl) := by
  rw [fundamental_ambient_as_small]
  have h := congrArg (fun f => f
    (cycleClass (mvSmallComplex X U V) 1 smallCycle smallCycle_is_cycle))
      (mvAmbientConnecting_comparison X U V CircleCoverGeometry.eastArc_open
        CircleCoverGeometry.westArc_open CircleCoverGeometry.arcs_cover 0)
  exact h.trans smallCycle_connecting



lemma upperPoint_upper : upperPoint.val ∈ CircleCoverGeometry.upperArc := by
  change 0 < ((circleSide 1 0 : Circle) : ℂ).im
  norm_num [circleSide, Circle.coe_exp, Complex.exp_im]
  apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]

lemma lowerPoint_lower : lowerPoint.val ∈ CircleCoverGeometry.lowerArc := by
  change ((circleSide 5 0 : Circle) : ℂ).im < 0
  norm_num [circleSide, Circle.coe_exp, Complex.exp_im]
  have h : Real.sin (Real.pi / 4 + Real.pi) < 0 := by
    rw [Real.sin_add_pi]
    exact neg_neg_of_pos (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos]))
  convert h using 1 <;> congr 1 <;> ring

lemma overlapMap_upper (p : ↥(U ∩ V)) (hp : p.val ∈ CircleCoverGeometry.upperArc) :
    overlapHomotopyEquiv p = Sum.inl () := by
  have h : CircleCoverGeometry.intersectionHomeomorph p = Sum.inl ⟨p.val,hp⟩ := by
    apply CircleCoverGeometry.intersectionHomeomorph.symm.injective
    rw [Homeomorph.symm_apply_apply]
    apply Subtype.ext
    rfl
  change Sum.map _ _ (CircleCoverGeometry.intersectionHomeomorph p) = _
  rw [h]
  congr 1

lemma overlapMap_lower (p : ↥(U ∩ V)) (hp : p.val ∈ CircleCoverGeometry.lowerArc) :
    overlapHomotopyEquiv p = Sum.inr () := by
  have h : CircleCoverGeometry.intersectionHomeomorph p = Sum.inr ⟨p.val,hp⟩ := by
    apply CircleCoverGeometry.intersectionHomeomorph.symm.injective
    rw [Homeomorph.symm_apply_apply]
    apply Subtype.ext
    rfl
  change Sum.map _ _ (CircleCoverGeometry.intersectionHomeomorph p) = _
  rw [h]
  congr 1

lemma pointSimplex_image (p : ↥(U ∩ V)) :
    ((TopCat.toSSet.map (TopCat.ofHom overlapHomotopyEquiv.toFun)).app (.op ⦋0⦌))
      (pointSimplex p) = TopCat.toSSetObj₀Equiv.symm (overlapHomotopyEquiv p) := by
  apply TopCat.toSSetObj₀Equiv.injective
  rfl

lemma overlapPoint_coordinates (p : ↥(U ∩ V)) :
    pointClass (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))) (pointSimplex p) ≫
      overlapCoordinatesIso.hom =
        (match overlapHomotopyEquiv p with
          | .inl _ => ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ)
          | .inr _ => ModuleCat.ofHom (LinearMap.inr ℤ ℤ ℤ)) := by
  change pointClass _ _ ≫
    (HomologicalComplex.homologyMap (SSet.chainComplexMap
      (TopCat.toSSet.map (TopCat.ofHom overlapHomotopyEquiv.toFun)) RZ) 0 ≫
      twoHomologyIso.hom) = _
  rw [← Category.assoc, pointClass_map, pointSimplex_image]
  exact two_pointClass _

lemma overlapBoundary_coordinates :
    overlapCoordinatesIso.hom ((ordinaryHomologyIso X (U ∩ V) 0).hom
      (cycleClass (mvOrdinaryComplex X (U ∩ V)) 0 overlapOrdinaryChain
        (by rw [HomologicalComplex.shape _ _ _ (by simp)]; rfl))) = (-1,1) := by
  rw [← zeroClassMap_apply]
  change overlapCoordinatesIso.hom ((singularHomologyRepresentation (TopCat.of ↥(U ∩ V)) 0).hom
    (zeroClassMap (mvAmbientComplex (TopCat.of ↥(U ∩ V)))
      (Finsupp.single (pointSimplex lowerPoint) 1 - Finsupp.single (pointSimplex upperPoint) 1))) = _
  rw [map_sub,map_sub,singular_point_class,singular_point_class,map_sub]
  have hl := congrArg (fun f => f (1:ℤ)) (overlapPoint_coordinates lowerPoint)
  have hu := congrArg (fun f => f (1:ℤ)) (overlapPoint_coordinates upperPoint)
  rw [overlapMap_lower lowerPoint lowerPoint_lower] at hl
  rw [overlapMap_upper upperPoint upperPoint_upper] at hu
  change overlapCoordinatesIso.hom (pointClass _ (pointSimplex lowerPoint) 1) = (0,1) at hl
  change overlapCoordinatesIso.hom (pointClass _ (pointSimplex upperPoint) 1) = (1,0) at hu
  rw [hl,hu]
  rfl



/-- The actual positively oriented eight-side source cycle has primitive coordinate -1.
The sign comes from choosing sides 1–4 as the east-arc lift. -/
theorem fundamentalClass_coordinate : circleH1Iso.hom fundamentalClass = -1 := by
  change (overlapCoordinatesIso.hom ((ordinaryHomologyIso X (U ∩ V) 0).hom
    (mvAmbientConnecting X U V CircleCoverGeometry.eastArc_open CircleCoverGeometry.westArc_open
      CircleCoverGeometry.arcs_cover 0
      ((singularHomologyRepresentation X 1).inv ((singularHomologyRepresentation X 1).hom
        (cycleClass (mvAmbientComplex X) 1 circleBoundaryChain circle_boundary_is_cycle)))))).1 = -1
  rw [Iso.hom_inv_id_apply, fundamental_connecting, overlapBoundary_coordinates]

/-- Every integral singular H₁ class is an integer multiple of this exact cycle. -/
theorem fundamentalClass_generates : FundamentalClassGenerates := by
  intro x
  refine ⟨-(circleH1Iso.hom x), ?_⟩
  apply circleH1Iso.toLinearEquiv.injective
  change circleH1Iso.hom.hom ((-(circleH1Iso.hom x) : ℤ) • fundamentalClass) = circleH1Iso.hom x
  refine (map_zsmul circleH1Iso.hom.hom (-(circleH1Iso.hom x) : ℤ) fundamentalClass).trans ?_
  rw [fundamentalClass_coordinate]
  change -(circleH1Iso.hom x) * -1 = circleH1Iso.hom x
  ring


end CircleFundamentalCycle
