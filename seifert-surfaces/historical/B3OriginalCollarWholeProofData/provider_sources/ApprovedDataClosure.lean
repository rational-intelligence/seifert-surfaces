import WeakDivergenceData
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder

abbrev SobolevPair (Ω : Set V) :=
  WithLp 2 (Lp ℝ 2 (volume.restrict Ω) × Lp V 2 (volume.restrict Ω))

def witnessPair {Ω : Set V} {v : V → ℝ} (hv : H1Witness v Ω) : SobolevPair Ω :=
  WithLp.toLp 2 (hv.memLp.toLp v, (weak_gradient_memLp Ω v hv).toLp hv.weakGrad)

def smoothPairs (Ω : Set V) : Set (SobolevPair Ω) :=
  {p | ∃ (v : V → ℝ) (hv : H1Witness v Ω),
    ContDiff ℝ (⊤ : ℕ∞) v ∧ HasCompactSupport v ∧ tsupport v ⊆ Ω ∧ p = witnessPair hv}

def H01Space (Ω : Set V) : Submodule ℝ (SobolevPair Ω) :=
  (Submodule.span ℝ (smoothPairs Ω)).topologicalClosure

def frozenForm (A : Mat) (Ω : Set V) (p : H01Space Ω × H01Space Ω) : ℝ :=
  ∫ x in Ω, inner ℝ
    (DeGiorgi.matMulE A ((p.1.val.ofLp.2 : V → V) x))
    ((p.2.val.ofLp.2 : V → V) x)

def frozenLoad (A : Mat) {Ω : Set V} {v : V → ℝ}
    (hv : H1Witness v Ω) (p : H01Space Ω) : ℝ :=
  -∫ x in Ω, inner ℝ (DeGiorgi.matMulE A (hv.weakGrad x))
    ((p.val.ofLp.2 : V → V) x)

def classicalGradient (v : V → ℝ) (x : V) : V :=
  WithLp.toLp 2 (fun i => (fderiv ℝ v x) (EuclideanSpace.single i 1))

def pulledBackBall (P : V ≃L[ℝ] V) (center : V) (R : ℝ) : Set V :=
  {y | P y ∈ Metric.ball center R}

end SeifertSurfaces.WeakSchauder
