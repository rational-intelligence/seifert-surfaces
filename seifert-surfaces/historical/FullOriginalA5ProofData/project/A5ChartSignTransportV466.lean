import A5ChartSignV466

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology CategoryTheory
open CurveComplexGenusTwo.CWHurewicz
open SeifertSurfaces.Foundations
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource

private def chartSignProviderName (leaf : String) : Lean.Name :=
  ["SeifertSurfaces","OriginalEndpoints","AppendixAOriginal","GlobalSmoothSource"].foldl Lean.Name.str
    (Lean.Name.num (Lean.Name.str (Lean.Name.str .anonymous "_private") "A5ChartSignV466") 0) |>.str leaf

def nativeTopologicalChartSign (S : CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : e.source) : ℝ := by
  run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| exact
    $(Lean.mkIdent (chartSignProviderName "chartSign"))
      $(Lean.mkIdent `S) $(Lean.mkIdent `e) $(Lean.mkIdent `x)))

theorem nativeTopologicalChartSign_unit (S : CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) (x : e.source) :
    nativeTopologicalChartSign S e x = 1 ∨ nativeTopologicalChartSign S e x = -1 := by
  run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| exact
    $(Lean.mkIdent (chartSignProviderName "chartSign_unit"))
      $(Lean.mkIdent `S) $(Lean.mkIdent `e) $(Lean.mkIdent `x)))

theorem nativeTopologicalChartSign_locally_constant (S : CompactOrientedSurface.{0})
    (e : OpenPartialHomeomorph S ℂ) : IsLocallyConstant (nativeTopologicalChartSign S e) := by
  run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| exact
    $(Lean.mkIdent (chartSignProviderName "chartSign_locally_constant"))
      $(Lean.mkIdent `S) $(Lean.mkIdent `e)))

theorem nativeTopologicalChartSign_derivative_comparison
    (S : CompactOrientedSurface.{0})
    (e f : OpenPartialHomeomorph S ℂ) (x : S) (he : x ∈ e.source) (hf : x ∈ f.source)
    (A : ℂ ≃L[ℝ] ℂ)
    (hder : HasFDerivAt
      ((e.trans (Homeomorph.addRight (-e x)).toOpenPartialHomeomorph).symm.trans
        (f.trans (Homeomorph.addRight (-f x)).toOpenPartialHomeomorph))
      A.toContinuousLinearMap 0) :
    nativeTopologicalChartSign S f ⟨x,hf⟩ =
      if 0 < LinearMap.det A.toLinearEquiv.toLinearMap
      then nativeTopologicalChartSign S e ⟨x,he⟩ else -(nativeTopologicalChartSign S e ⟨x,he⟩) := by
  run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| exact
    $(Lean.mkIdent (chartSignProviderName "chartSign_derivative_comparison"))
      $(Lean.mkIdent `S) $(Lean.mkIdent `e) $(Lean.mkIdent `f) $(Lean.mkIdent `x)
      $(Lean.mkIdent `he) $(Lean.mkIdent `hf) $(Lean.mkIdent `A) $(Lean.mkIdent `hder)))

#print axioms nativeTopologicalChartSign_derivative_comparison
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
