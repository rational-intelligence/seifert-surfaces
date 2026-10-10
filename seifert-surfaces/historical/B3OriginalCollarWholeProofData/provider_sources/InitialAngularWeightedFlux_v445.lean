import InitialSmoothCircleChain_v445

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates

local macro "paid_circle_chain" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialSmoothCircleChain_v445 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.native_smooth_circle_chain_v445)⟩

private theorem native_weighted_angular_integrand_v445
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (phi : E2 → ℝ) (hphi : ContDiff ℝ ∞ phi) (x : E2) (q : ℝ) :
    let grad : E2 → E2 := fun z =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun j => fderiv ℝ phi z (coordinateVector 2 j))
    let dp : Fin 2 → E2 → E2 := fun i z => phi z • d i z + f z i • grad z
    let J : E2 → E2 := fun v =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
    let chi : ℝ → ℝ := fun t => phi (x + q • unitCircleParameter t)
    ∀ (i : Fin 2) (t : ℝ),
      q * inner ℝ ((disc 1).indicator (dp i) (x + q • unitCircleParameter t))
          (J (unitCircleParameter t)) =
        chi t * (q * inner ℝ ((disc 1).indicator (d i)
          (x + q • unitCircleParameter t)) (J (unitCircleParameter t))) +
        (disc 1).indicator f (x + q • unitCircleParameter t) i * deriv chi t := by
  classical
  dsimp only
  intro i t
  by_cases hz : x + q • unitCircleParameter t ∈ disc 1
  · simp only [indicator_of_mem hz]
    have hc := paid_circle_chain phi hphi x q t
    dsimp only at hc
    rw [hc, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  · simp [indicator_of_notMem hz]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
