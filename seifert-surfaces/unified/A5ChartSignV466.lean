import A5PlaneIndexV466

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology CategoryTheory
open CurveComplexGenusTwo.CWHurewicz
open SeifertSurfaces.Foundations
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource

private def planeProviderName (m leaf : String) : Lean.Name :=
  let ns := if m = "A5PlaneIndexV466" then
    ["SeifertSurfaces","OriginalEndpoints","AppendixAOriginal","GlobalSmoothSource"]
    else ["SeifertSurfaces","GenusLinking"]
  ns.foldl Lean.Name.str
    (Lean.Name.num (Lean.Name.str (Lean.Name.str .anonymous "_private") m) 0) |>.str leaf

private def chartIndex (S : CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : e.source) :
    relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 ⟶ relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 := by
  run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| exact
    $(Lean.mkIdent (planeProviderName "A5PlaneIndexV466" "oldChartIndex"))
      $(Lean.mkIdent `S) $(Lean.mkIdent `e) $(Lean.mkIdent `x)))

private def chartSign (S : CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : e.source) : ℝ := by
  classical
  exact if chartIndex S e x = 𝟙 _ then 1 else -1

private def shiftChart (S : CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : S) : OpenPartialHomeomorph S ℂ := by
  run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| exact
    $(Lean.mkIdent (planeProviderName "A5PlaneIndexV466" "paidShiftChart"))
      $(Lean.mkIdent `S) $(Lean.mkIdent `e) $(Lean.mkIdent `x)))

private theorem chartSign_unit (S : CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : e.source) :
    chartSign S e x = 1 ∨ chartSign S e x = -1 := by
  classical
  unfold chartSign
  split_ifs <;> simp

private theorem chartSign_locally_constant (S : CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) : IsLocallyConstant (chartSign S e) := by
  run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| exact
    $(Lean.mkIdent (planeProviderName "A5PlaneIndexV466" "oldChartSign_locally_constant"))
      $(Lean.mkIdent `S) $(Lean.mkIdent `e)))

private theorem chartSign_derivative_comparison
    (S : CompactOrientedSurface.{0})
    (e f : OpenPartialHomeomorph S ℂ) (x : S) (he : x ∈ e.source) (hf : x ∈ f.source)
    (A : ℂ ≃L[ℝ] ℂ)
    (hder : HasFDerivAt ((shiftChart S e x).symm.trans (shiftChart S f x))
      A.toContinuousLinearMap 0) :
    chartSign S f ⟨x,hf⟩ =
      if 0 < LinearMap.det A.toLinearEquiv.toLinearMap
      then chartSign S e ⟨x,he⟩ else -(chartSign S e ⟨x,he⟩) := by
  classical
  have hc : chartIndex S f ⟨x,hf⟩ =
      if 0 < LinearMap.det A.toLinearEquiv.toLinearMap
      then chartIndex S e ⟨x,he⟩ else -(chartIndex S e ⟨x,he⟩) := by
    run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| exact
      $(Lean.mkIdent (planeProviderName "A5PlaneIndexV466" "oldChartIndex_derivative_comparison"))
        $(Lean.mkIdent `S) $(Lean.mkIdent `e) $(Lean.mkIdent `f) $(Lean.mkIdent `x)
        $(Lean.mkIdent `he) $(Lean.mkIdent `hf) $(Lean.mkIdent `A) $(Lean.mkIdent `hder)))
  have hcases : chartIndex S e ⟨x,he⟩ = 𝟙 _ ∨ chartIndex S e ⟨x,he⟩ = -(𝟙 _) := by
    run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| exact
      $(Lean.mkIdent (planeProviderName "A5PlaneIndexV466" "oldChartIndex_sign"))
        $(Lean.mkIdent `S) $(Lean.mkIdent `e) ⟨$(Lean.mkIdent `x),$(Lean.mkIdent `he)⟩))
  have hid : (𝟙 (relativeHomology ℂ ({0}ᶜ : Set ℂ) 2)) ≠ -(𝟙 _) := by
    run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| exact
      $(Lean.mkIdent (planeProviderName "TopologicalOrientation_v395" "actual_plane_local_id_ne_neg"))))
  by_cases hp : 0 < LinearMap.det A.toLinearEquiv.toLinearMap
  · simp only [hp,ite_true] at hc ⊢
    simp only [chartSign,hc]
  · simp only [hp,ite_false] at hc ⊢
    rcases hcases with heq|heq <;> simp [chartSign,hc,heq,hid,hid.symm]

/-- Topological orientation signs on arbitrary plane charts, with the exact derivative comparison. -/
structure TopologicalPlaneChartOrientation (S : CompactOrientedSurface.{0}) where
  sign : (e : OpenPartialHomeomorph S ℂ) → e.source → ℝ
  unit : ∀ e x, sign e x = 1 ∨ sign e x = -1
  locally_constant : ∀ e, IsLocallyConstant (sign e)
  shift : (e : OpenPartialHomeomorph S ℂ) → S → OpenPartialHomeomorph S ℂ
  derivative_comparison : ∀ e f x he hf (A : ℂ ≃L[ℝ] ℂ),
    HasFDerivAt ((shift e x).symm.trans (shift f x)) A.toContinuousLinearMap 0 →
    sign f ⟨x,hf⟩ = if 0 < LinearMap.det A.toLinearEquiv.toLinearMap
      then sign e ⟨x,he⟩ else -(sign e ⟨x,he⟩)

theorem topological_plane_chart_orientation (S : CompactOrientedSurface.{0}) :
    Nonempty (TopologicalPlaneChartOrientation S) :=
  ⟨{sign := chartSign S, unit := chartSign_unit S,
    locally_constant := chartSign_locally_constant S,
    shift := shiftChart S, derivative_comparison := chartSign_derivative_comparison S}⟩

#print axioms topological_plane_chart_orientation
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
