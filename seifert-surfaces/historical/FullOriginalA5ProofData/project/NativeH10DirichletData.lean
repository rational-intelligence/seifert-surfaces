import IsothermalPDEData
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section
set_option autoImplicit false
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
open SeifertSurfaces.AppendixACoordinates

/-- Scalar and supplied-gradient L² classes with the L² product norm. -/
abbrev Pair (U : Set E2) :=
  WithLp 2 (Lp ℝ 2 (volume.restrict U) × Lp E2 2 (volume.restrict U))

def pack (U : Set E2) (u : E2 → ℝ) (du : E2 → E2)
    (hu : MemLp u 2 (volume.restrict U))
    (hdu : MemLp du 2 (volume.restrict U)) : Pair U :=
  WithLp.toLp 2 (hu.toLp u, hdu.toLp du)

def SmoothGraph (U : Set E2) : Set (Pair U) :=
  {p | ∃ (φ : E2 → ℝ) (hu : MemLp φ 2 (volume.restrict U))
      (hg : MemLp (planarGradient φ) 2 (volume.restrict U)),
    ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
      p = pack U φ (planarGradient φ) hu hg}

abbrev space (U : Set E2) : Submodule ℝ (Pair U) :=
  (Submodule.span ℝ (SmoothGraph U)).topologicalClosure

abbrev X (U : Set E2) := ↥(space U)

def valLp (U : Set E2) (p : X U) : Lp ℝ 2 (volume.restrict U) :=
  (WithLp.ofLp p.val).1

def gradLp (U : Set E2) (p : X U) : Lp E2 2 (volume.restrict U) :=
  (WithLp.ofLp p.val).2

def val (U : Set E2) (p : X U) : E2 → ℝ := valLp U p

def grad (U : Set E2) (p : X U) : E2 → E2 := gradLp U p

def b (U : Set E2) (N : E2 → Mat2) (p q : X U) : ℝ :=
  ∫ x in U, inner ℝ (matrixAction (N x) (grad U p x)) (grad U q x)

def load (U : Set E2) (N : E2 → Mat2) (q : X U) : ℝ :=
  -(∫ x in U, inner ℝ (matrixAction (N x) (coordinateVector 2 0)) (grad U q x))

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
