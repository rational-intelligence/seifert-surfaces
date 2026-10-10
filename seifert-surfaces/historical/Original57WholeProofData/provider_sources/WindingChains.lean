import CircleCore
import SimplexLog

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped Simplicial BigOperators
open CategoryTheory CategoryTheory.Limits Convexity

namespace SeifertSurfaces.GenusLinking.CircleConstruction
noncomputable section

def singularWinding (s : (TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌) : ℤ :=
  edgeWinding (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌) s)

theorem singular_face_eq (s : (TopCat.toSSet.obj (TopCat.of Circle)) _⦋2⦌) (i : Fin 3) :
    TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌)
      ((TopCat.toSSet.obj (TopCat.of Circle)).δ i s) =
    (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋2⦌) s).comp (simplexFace i) := by
  ext z : 1
  rfl

theorem singularWinding_boundary (s : (TopCat.toSSet.obj (TopCat.of Circle)) _⦋2⦌) :
    singularWinding ((TopCat.toSSet.obj (TopCat.of Circle)).δ 0 s) -
      singularWinding ((TopCat.toSSet.obj (TopCat.of Circle)).δ 1 s) +
      singularWinding ((TopCat.toSSet.obj (TopCat.of Circle)).δ 2 s) = 0 := by
  unfold singularWinding
  rw [singular_face_eq s 0, singular_face_eq s 1, singular_face_eq s 2]
  exact edgeWinding_boundary _

def windingChainMap : (integralChains Circle).X 1 ⟶ ModuleCat.of ℤ ℤ :=
  Sigma.desc (fun s => ModuleCat.ofHom
    (LinearMap.toSpanSingleton ℤ ℤ (singularWinding s)))

@[simp] theorem simplex_windingChainMap (s : (TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌) :
    (TopCat.toSSet.obj (TopCat.of Circle)).ιChainComplex s ≫ windingChainMap =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ (singularWinding s)) := by
  simp [SSet.ιChainComplex, windingChainMap]

theorem windingChainMap_boundary : (integralChains Circle).d 2 1 ≫ windingChainMap = 0 := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj (TopCat.of Circle))
  intro s
  change (TopCat.toSSet.obj (TopCat.of Circle)).ιChainComplex s ≫
    ((TopCat.toSSet.obj (TopCat.of Circle)).chainComplex (ModuleCat.of ℤ ℤ)).d (1 + 1) 1 ≫
    windingChainMap = _
  rw [SSet.ιChainComplex_d_assoc]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, simplex_windingChainMap]
  ext
  have hb := singularWinding_boundary s
  simp [Fin.sum_univ_succ]
  simpa [sub_eq_add_neg, add_assoc] using hb

theorem singularWinding_circleLoop : singularWinding circleLoopSimplex = 1 := by
  let s := TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌) circleLoopSimplex
  let F : C(StdSimplex ℝ (Fin 2), ℝ) :=
    ⟨fun z => 2 * Real.pi * z.weights 1,
      continuous_const.mul (StdSimplex.continuous_weights_apply ℝ 1)⟩
  have hfirst : F (.single 0) = Complex.arg (s (.single 0)) := by
    simp [F, s, circleLoopSimplex]
  have hexp (z) : Circle.exp (F z) = s z := by
    simp [F, s, circleLoopSimplex]
  have hlog : F = simplexLog s := simplexLog_unique s F hfirst hexp
  have hw := edgeWinding_spec s
  rw [← hlog] at hw
  simp [F, s, circleLoopSimplex] at hw
  simpa only [singularWinding, s, circleLoopSimplex, Equiv.apply_symm_apply] using hw

def windingHomologyMap : integralHomology Circle 1 ⟶ ModuleCat.of ℤ ℤ :=
  ((integralChains Circle).sc 1).descHomology
    ((integralChains Circle).iCycles 1 ≫ windingChainMap) (by
      change ((integralChains Circle).sc 1).toCycles ≫
        (((integralChains Circle).sc 1).iCycles ≫ windingChainMap) = 0
      rw [← Category.assoc, ShortComplex.toCycles_i]
      change (integralChains Circle).d ((ComplexShape.down ℕ).prev 1) 1 ≫ windingChainMap = 0
      have hn : (ComplexShape.down ℕ).prev 1 = 2 := ChainComplex.prev ℕ 1
      rw [hn]
      exact windingChainMap_boundary)

theorem circleClass_winding_map :
    (integralChains Circle).liftCycles circleLoopChain 0 (by simp) circleLoopChain_boundary ≫
      (integralChains Circle).homologyπ 1 ≫ windingHomologyMap =
    circleLoopChain ≫ windingChainMap := by
  unfold windingHomologyMap
  change _ ≫ ((integralChains Circle).sc 1).homologyπ ≫ _ = _
  rw [ShortComplex.π_descHomology]
  exact HomologicalComplex.liftCycles_i_assoc _ _ _ _ _ _

def windingHomology : integralHomology Circle 1 →ₗ[ℤ] ℤ := windingHomologyMap.hom

theorem windingHomology_circleFundamentalClass : windingHomology circleFundamentalClass = 1 := by
  have h := congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => f 1) circleClass_winding_map
  change windingHomologyMap
    (((integralChains Circle).liftCycles circleLoopChain 0 (by simp) circleLoopChain_boundary ≫
      (integralChains Circle).homologyπ 1) 1) = 1
  change windingHomologyMap
    (((integralChains Circle).liftCycles circleLoopChain 0 (by simp) circleLoopChain_boundary ≫
      (integralChains Circle).homologyπ 1) 1) = (circleLoopChain ≫ windingChainMap) 1 at h
  simpa only [circleLoopChain, simplex_windingChainMap,
    ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply_one, singularWinding_circleLoop] using h

theorem circleFundamentalClass_multiple_injective :
    Function.Injective (fun k : ℤ => k • circleFundamentalClass) := by
  intro i j hij
  have h := congrArg windingHomology hij
  simpa [windingHomology_circleFundamentalClass] using h

end
end SeifertSurfaces.GenusLinking.CircleConstruction
