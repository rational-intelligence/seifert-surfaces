import TriangleFill

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped Simplicial BigOperators
open CategoryTheory CategoryTheory.Limits Convexity

namespace SeifertSurfaces.GenusLinking.CircleConstruction
noncomputable section

def rayMap : (integralChains Circle).X 0 ⟶ (integralChains Circle).opcycles 1 :=
  Sigma.desc (fun z => ModuleCat.ofHom
    (LinearMap.toSpanSingleton ℤ Op1 (pointRayClass (TopCat.toSSetObj₀Equiv (X := TopCat.of Circle) z))))

def edgeGeneratorMap : (integralChains Circle).X 1 ⟶ (integralChains Circle).opcycles 1 :=
  Sigma.desc (fun s => ModuleCat.ofHom
    (LinearMap.toSpanSingleton ℤ Op1 (edgeClass
      (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌) s))))

def loopClassHom : ModuleCat.of ℤ ℤ ⟶ (integralChains Circle).opcycles 1 :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ Op1 (edgeClass (loopEdge 1)))

@[simp] theorem edgeGeneratorMap_apply (s : (TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌) :
    (TopCat.toSSet.obj (TopCat.of Circle)).ιChainComplex s ≫ edgeGeneratorMap =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ Op1 (edgeClass
        (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌) s))) := by
  simp [edgeGeneratorMap, SSet.ιChainComplex]

@[simp] theorem pOpcycles_apply (s : (TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌) :
    (TopCat.toSSet.obj (TopCat.of Circle)).ιChainComplex s ≫ (integralChains Circle).pOpcycles 1 =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ Op1 (edgeClass
        (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌) s))) := by
  ext
  simp [edgeClass]

theorem edgeGenerator_eq_pOpcycles : edgeGeneratorMap = (integralChains Circle).pOpcycles 1 := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj (TopCat.of Circle))
  intro s
  rw [edgeGeneratorMap_apply, pOpcycles_apply]

@[simp] theorem rayMap_apply (z : (TopCat.toSSet.obj (TopCat.of Circle)) _⦋0⦌) :
    (TopCat.toSSet.obj (TopCat.of Circle)).ιChainComplex z ≫ rayMap =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ Op1 (pointRayClass
        (TopCat.toSSetObj₀Equiv (X := TopCat.of Circle) z))) := by
  simp [rayMap, SSet.ιChainComplex]

theorem generator_boundary_relation :
    edgeGeneratorMap = (integralChains Circle).d 1 0 ≫ rayMap +
      windingChainMap ≫ loopClassHom := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj (TopCat.of Circle))
  intro s
  change (TopCat.toSSet.obj (TopCat.of Circle)).ιChainComplex s ≫ edgeGeneratorMap = _
  rw [edgeGeneratorMap_apply]
  let e := TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌) s
  let v0 := TopCat.toSSetObj₀Equiv (X := TopCat.of Circle)
      ((TopCat.toSSet.obj (TopCat.of Circle)).δ 0 s)
  let v1 := TopCat.toSSetObj₀Equiv (X := TopCat.of Circle)
      ((TopCat.toSSet.obj (TopCat.of Circle)).δ 1 s)
  have hrel := geometricEdge_winding e
  have hfaces : v0 = e (.single 1) ∧ v1 = e (.single 0) := by
    constructor
    · dsimp only [v0]
      rw [← TopCat.toSSetObj₁Equiv_apply_one]
      change e (TopCat.stdSimplexHomeomorphI.symm (1 : TopCat.I.{0})) = e (.single 1)
      simp
    · dsimp only [v1]
      rw [← TopCat.toSSetObj₁Equiv_apply_zero]
      change e (TopCat.stdSimplexHomeomorphI.symm (0 : TopCat.I.{0})) = e (.single 0)
      simp
  rw [← hfaces.1, ← hfaces.2] at hrel
  simp only [Preadditive.comp_add, Preadditive.add_comp]
  change _ = CircleSSet.ιChainComplex s ≫
    (CircleSSet.chainComplex (ModuleCat.of ℤ ℤ)).d (0 + 1) 0 ≫ rayMap + _
  rw [SSet.ιChainComplex_d_assoc]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, rayMap_apply,
    simplex_windingChainMap]
  rw [← Category.assoc, simplex_windingChainMap]
  ext
  simp [CircleSSet, Fin.sum_univ_succ, loopClassHom, singularWinding, e, v0, v1,
    sub_eq_add_neg, add_assoc]
  convert hrel using 1
  simp only [v0, v1, e, sub_eq_add_neg, add_assoc]
  congr 2
  exact Int.cast_smul_eq_zsmul ℤ (edgeWinding e) (edgeClass (loopEdge 1))


theorem circleLoop_affine :
    TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌) circleLoopSimplex = loopEdge 1 := by
  ext z : 1
  simp [circleLoopSimplex, loopEdge, affineEdge, mul_comm]

theorem generatorClass_homologyι :
    (integralChains Circle).homologyι 1 circleFundamentalClass = edgeClass (loopEdge 1) := by
  have h := HomologicalComplex.homology_π_ι (K := integralChains Circle) 1
  have hh := congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ (integralChains Circle).opcycles 1 => f 1)
    (congrArg (fun f => (integralChains Circle).liftCycles circleLoopChain 0 (by simp)
      circleLoopChain_boundary ≫ f) h)
  simp only [Category.assoc, HomologicalComplex.liftCycles_i_assoc] at hh
  change (integralChains Circle).homologyι 1 circleFundamentalClass =
    (circleLoopChain ≫ (integralChains Circle).pOpcycles 1) 1 at hh
  rw [circleLoopChain, pOpcycles_apply, circleLoop_affine] at hh
  simpa using hh

theorem circle_cycles_generate (z : (integralChains Circle).cycles 1) :
    (integralChains Circle).homologyπ 1 z =
      windingChainMap ((integralChains Circle).iCycles 1 z) • circleFundamentalClass := by
  apply (ModuleCat.mono_iff_injective ((integralChains Circle).homologyι 1)).mp inferInstance
  have hg := generator_boundary_relation
  rw [edgeGenerator_eq_pOpcycles] at hg
  have hz : (integralChains Circle).d 1 0 ((integralChains Circle).iCycles 1 z) = 0 := by
    have h := congrArg (fun f : (integralChains Circle).cycles 1 ⟶ (integralChains Circle).X 0 => f z)
      ((integralChains Circle).iCycles_d 1 0)
    change (integralChains Circle).d 1 0 ((integralChains Circle).iCycles 1 z) = 0 at h
    exact h
  have hh := congrArg (fun f : (integralChains Circle).X 1 ⟶ (integralChains Circle).opcycles 1 =>
    f ((integralChains Circle).iCycles 1 z)) hg
  have hi := congrArg (fun f : (integralChains Circle).cycles 1 ⟶ (integralChains Circle).opcycles 1 => f z)
    (HomologicalComplex.homology_π_ι (K := integralChains Circle) 1)
  simp only [ModuleCat.comp_apply] at hi hh
  rw [hi]
  simpa [loopClassHom, hz, generatorClass_homologyι, ← Int.cast_smul_eq_zsmul ℤ] using hh

theorem circleFundamentalClass_generates :
    ∀ x : integralHomology Circle 1, ∃! k : ℤ, k • circleFundamentalClass = x := by
  intro x
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective ((integralChains Circle).homologyπ 1)).mp
    inferInstance x
  refine ⟨windingChainMap ((integralChains Circle).iCycles 1 z), ?_, ?_⟩
  · exact (circle_cycles_generate z).symm.trans hz
  · intro l hl
    exact circleFundamentalClass_multiple_injective (hl.trans
      ((circle_cycles_generate z).symm.trans hz).symm)

end
end SeifertSurfaces.GenusLinking.CircleConstruction
