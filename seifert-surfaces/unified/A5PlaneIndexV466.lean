import TopologicalOrientation_v395

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource

private def planeLocalIntegerIso : relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 ≅ ModuleCat.of ℤ ℤ := by
  have hz1 := CircleHomologyComputation.contractible_positive_homology ℂ 1 (by decide)
  have hz2 := CircleHomologyComputation.contractible_positive_homology ℂ 2 (by decide)
  have he1 := (pairHomology_exact_at_relative ℂ ({0}ᶜ) 1).choose_spec
  have he0 := (pairHomology_exact_at_subspace ℂ ({0}ᶜ) 1).choose_spec
  letI : Mono (relativeConnecting ℂ ({0}ᶜ) 1) := he1.mono_g (hz2.eq_of_src _ _)
  letI : Epi (relativeConnecting ℂ ({0}ᶜ) 1) := he0.epi_f (hz1.eq_of_tgt _ _)
  letI : IsIso (relativeConnecting ℂ ({0}ᶜ) 1) := isIso_of_mono_of_epi _
  exact asIso (relativeConnecting ℂ ({0}ᶜ) 1) ≪≫
    ReflectionRadial.circlePuncturedIso 1 ≪≫ CircleHomologyComputation.circleH1Iso

private theorem integerEnd_eval (f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ) (z : ℤ) :
    f z = z * f 1 := by
  have h := f.hom.map_smul z (1 : ℤ)
  simpa only [smul_eq_mul,mul_one] using h

private theorem integerAuto_one (f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ) [IsIso f] :
    f = 𝟙 _ ∨ f = -(𝟙 _) := by
  have hmul : f 1 * inv f 1 = 1 := by
    have hi := congrArg (fun q : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => q (1:ℤ)) (IsIso.hom_inv_id f)
    change inv f (f 1) = 1 at hi
    rwa [integerEnd_eval] at hi
  have hunit := Int.eq_one_or_neg_one_of_mul_eq_one hmul
  rcases hunit with hp|hn
  · left
    ext z
    rw [integerEnd_eval,hp,mul_one]
    rfl
  · right
    ext z
    rw [integerEnd_eval,hn,mul_neg_one]
    rfl

private theorem planeLocalAuto_sign
    (f : relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 ⟶ relativeHomology ℂ ({0}ᶜ : Set ℂ) 2)
    [IsIso f] : f = 𝟙 _ ∨ f = -(𝟙 _) := by
  let e := planeLocalIntegerIso
  let g := e.inv ≫ f ≫ e.hom
  letI : IsIso g := by dsimp [g]; infer_instance
  have hg := integerAuto_one g
  rcases hg with hp|hn
  · left
    have h := congrArg (fun q => e.hom ≫ q ≫ e.inv) hp
    simpa [g] using h
  · right
    have h := congrArg (fun q => e.hom ≫ q ≫ e.inv) hn
    simpa [g] using h

private def paidOrientationName (leaf : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num (Lean.Name.str (Lean.Name.str .anonymous "_private") "TopologicalOrientation_v395") 0)
      "SeifertSurfaces") "GenusLinking") leaf

private def oldChartIndex (S : SeifertSurfaces.Foundations.CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : e.source) :
    relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 ⟶ relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 := by
  run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| exact
    $(Lean.mkIdent (paidOrientationName "actualTopologicalChartIndex")) $(Lean.mkIdent `S) $(Lean.mkIdent `e) $(Lean.mkIdent `x)))

private theorem oldChartIndex_isIso (S : SeifertSurfaces.Foundations.CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : e.source) : IsIso (oldChartIndex S e x) := by
  run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| exact
    $(Lean.mkIdent (paidOrientationName "actual_topological_chart_index_isIso")) $(Lean.mkIdent `S) $(Lean.mkIdent `e) $(Lean.mkIdent `x)))

private theorem oldChartIndex_locally_constant (S : SeifertSurfaces.Foundations.CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) : IsLocallyConstant (oldChartIndex S e) := by
  run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| exact
    $(Lean.mkIdent (paidOrientationName "actual_chart_index_locally_constant")) $(Lean.mkIdent `S) $(Lean.mkIdent `e)))

private def oldChartSign (S : SeifertSurfaces.Foundations.CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : e.source) : ℝ :=
  by
    classical
    exact if oldChartIndex S e x = 𝟙 _ then 1 else -1

private theorem oldChartIndex_sign (S : SeifertSurfaces.Foundations.CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : e.source) :
    oldChartIndex S e x = 𝟙 _ ∨ oldChartIndex S e x = -(𝟙 _) := by
  letI := oldChartIndex_isIso S e x
  exact planeLocalAuto_sign _

private theorem oldChartSign_unit (S : SeifertSurfaces.Foundations.CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : e.source) :
    oldChartSign S e x = 1 ∨ oldChartSign S e x = -1 := by
  classical
  unfold oldChartSign
  split_ifs <;> simp

private theorem oldChartSign_locally_constant (S : SeifertSurfaces.Foundations.CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) : IsLocallyConstant (oldChartSign S e) := by
  classical
  exact (oldChartIndex_locally_constant S e).comp (fun a => if a = 𝟙 _ then (1:ℝ) else -1)

private def paidChartLocalIso (S : SeifertSurfaces.Foundations.CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : S) (hx : x ∈ e.source) :
    relativeHomology S ({x}ᶜ : Set S) 2 ≅ relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 := by
  run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| exact
    $(Lean.mkIdent (paidOrientationName "actualChartLocalIso")) $(Lean.mkIdent `e) $(Lean.mkIdent `x) $(Lean.mkIdent `hx)))

private def paidShiftChart (S : SeifertSurfaces.Foundations.CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : S) : OpenPartialHomeomorph S ℂ := by
  run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| exact
    $(Lean.mkIdent (paidOrientationName "actualShiftChart")) $(Lean.mkIdent `e) $(Lean.mkIdent `x)))

private theorem oldChartIndex_derivative_comparison
    (S : SeifertSurfaces.Foundations.CompactOrientedSurface.{0})
    (e f : OpenPartialHomeomorph S ℂ) (x : S) (he : x ∈ e.source) (hf : x ∈ f.source)
    (A : ℂ ≃L[ℝ] ℂ)
    (hder : HasFDerivAt ((paidShiftChart S e x).symm.trans (paidShiftChart S f x))
      A.toContinuousLinearMap 0) :
    oldChartIndex S f ⟨x,hf⟩ =
      if 0 < LinearMap.det A.toLinearEquiv.toLinearMap
      then oldChartIndex S e ⟨x,he⟩ else -(oldChartIndex S e ⟨x,he⟩) := by
  have hc : (paidChartLocalIso S f x hf).hom =
      if 0 < LinearMap.det A.toLinearEquiv.toLinearMap
      then (paidChartLocalIso S e x he).hom else -(paidChartLocalIso S e x he).hom := by
    run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| exact
      $(Lean.mkIdent (paidOrientationName "actual_derivative_chart_comparison")) $(Lean.mkIdent `e) $(Lean.mkIdent `f) $(Lean.mkIdent `x) $(Lean.mkIdent `he) $(Lean.mkIdent `hf) $(Lean.mkIdent `A) $(Lean.mkIdent `hder)))
  by_cases hpos : 0 < LinearMap.det A.toLinearEquiv.toLinearMap
  · simp only [hpos,ite_true] at hc ⊢
    apply (cancel_epi (paidChartLocalIso S f x hf).hom).mp
    dsimp only [oldChartIndex,paidChartLocalIso]
    dsimp only [paidChartLocalIso] at hc
    run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| unfold
      $(Lean.mkIdent (paidOrientationName "actualTopologicalChartIndex"))))
    rw [←Category.assoc,Iso.hom_inv_id,Category.id_comp,hc,
      ←Category.assoc,Iso.hom_inv_id,Category.id_comp]
  · simp only [hpos,ite_false] at hc ⊢
    apply (cancel_epi (paidChartLocalIso S f x hf).hom).mp
    dsimp only [oldChartIndex,paidChartLocalIso]
    dsimp only [paidChartLocalIso] at hc
    run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| unfold
      $(Lean.mkIdent (paidOrientationName "actualTopologicalChartIndex"))))
    rw [←Category.assoc,Iso.hom_inv_id,Category.id_comp,Preadditive.comp_neg,hc,
      Preadditive.neg_comp,←Category.assoc,Iso.hom_inv_id,Category.id_comp,neg_neg]

#print axioms oldChartIndex_derivative_comparison

#print axioms planeLocalAuto_sign
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
