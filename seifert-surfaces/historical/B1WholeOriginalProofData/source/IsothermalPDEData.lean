import VM03BranchResiduals

noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower
open SeifertSurfaces.AppendixACoordinates

/-- The coefficient of the scalar divergence equation for the supplied metric. -/
def normalizedInverse (M : E2 → Mat2) (x : E2) : Mat2 :=
  Real.sqrt (Matrix.det (M x)) • (M x)⁻¹

def rotation (v : E2) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]

def affineDatum (y x : E2) : ℝ := (x - y) 0

/-- Native weak gradient, L2 data, and H1_0 approximation of the affine difference. -/
def AffineWeakSolution (M : E2 → Mat2) (y : E2) (r : ℝ)
    (a : E2 → ℝ) (da : E2 → E2) : Prop :=
  H1On (Metric.ball y r) a da ∧
  H10On (Metric.ball y r) (fun x => a x - affineDatum y x)
    (fun x => da x - coordinateVector 2 0) ∧
  WeakLinearEquationOn (Metric.ball y r) (normalizedInverse M)
    (fun _ => 0) (fun _ => 0) a da

/-- C1 on an open set and local original-exponent Holder bounds on each derivative entry. -/
def ScalarC1AlphaOn (alpha : ℝ≥0) (a : E2 → ℝ) (U : Set E2) : Prop :=
  ContDiffOn ℝ 1 a U ∧
  ∀ x ∈ U, ∃ s : ℝ, 0 < s ∧ Metric.ball x s ⊆ U ∧
    ∀ i : Fin 2, ∃ C : ℝ≥0,
      HolderOnWith C alpha (fun z => planarGradient a z i) (Metric.ball x s)

def MapC1AlphaOn (alpha : ℝ≥0) (h : E2 → E2) (U : Set E2) : Prop :=
  ContDiffOn ℝ 1 h U ∧
  ∀ x ∈ U, ∃ s : ℝ, 0 < s ∧ Metric.ball x s ⊆ U ∧
    ∀ i j : Fin 2, ∃ C : ℝ≥0,
      HolderOnWith C alpha (fun z => jacobian h z i j) (Metric.ball x s)

def ScalarCAlphaOn (alpha : ℝ≥0) (a : E2 → ℝ) (U : Set E2) : Prop :=
  ∀ x ∈ U, ∃ s : ℝ, 0 < s ∧ Metric.ball x s ⊆ U ∧
    ∃ C : ℝ≥0, HolderOnWith C alpha a (Metric.ball x s)

def conjugateCoordinates (a b : E2 → ℝ) (x : E2) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![a x, b x]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower
