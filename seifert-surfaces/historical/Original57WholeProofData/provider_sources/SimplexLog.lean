import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false
open Convexity Set Topology

namespace SeifertSurfaces.GenusLinking.CircleConstruction
noncomputable section

def radial {n : ℕ} (p : unitInterval × StdSimplex ℝ (Fin (n + 1))) :
    StdSimplex ℝ (Fin (n + 1)) :=
  convexCombPair (R := ℝ) (unitInterval.symm p.1) p.1
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) (.single 0) p.2

theorem radial_continuous (n : ℕ) :
    Continuous (radial (n := n)) := by
  apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff.mpr
  apply continuous_pi
  intro i
  simp only [Function.comp_def, radial, StdSimplex.weights_convexCombPair,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    unitInterval.coe_symm_eq]
  fun_prop

@[simp] theorem radial_zero {n : ℕ} (z : StdSimplex ℝ (Fin (n + 1))) :
    radial (0, z) = .single 0 := by simp [radial]

@[simp] theorem radial_one {n : ℕ} (z : StdSimplex ℝ (Fin (n + 1))) :
    radial (1, z) = z := by simp [radial]

/-- A logarithm on every actual topological simplex, anchored at its first vertex. -/
theorem simplex_log_exists {n : ℕ} (s : C(StdSimplex ℝ (Fin (n + 1)), Circle)) :
    ∃ F : C(StdSimplex ℝ (Fin (n + 1)), ℝ),
      F (.single 0) = Complex.arg (s (.single 0)) ∧
      ∀ z, Circle.exp (F z) = s z := by
  let H : C(unitInterval × StdSimplex ℝ (Fin (n + 1)), Circle) :=
    s.comp ⟨radial, radial_continuous n⟩
  let f : C(StdSimplex ℝ (Fin (n + 1)), ℝ) :=
    .const _ (Complex.arg (s (.single 0)))
  have h0 : ∀ z, H (0, z) = Circle.exp (f z) := by simp [H, f]
  let G := Circle.isCoveringMap_exp.liftHomotopy H f h0
  let L : C(StdSimplex ℝ (Fin (n + 1)), ℝ) :=
    G.comp ((ContinuousMap.const _ (1 : unitInterval)).prodMk (ContinuousMap.id _))
  have hL (z) : Circle.exp (L z) = s z := by
    change Circle.exp (G (1, z)) = s z
    have hh : Circle.exp (G (1, z)) = H (1, z) :=
      congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts H f h0) (1, z)
    simpa only [H, ContinuousMap.comp_apply, ContinuousMap.coe_mk, radial_one] using hh
  let F : C(StdSimplex ℝ (Fin (n + 1)), ℝ) :=
    ⟨fun z => L z - L (.single 0) + Complex.arg (s (.single 0)), by fun_prop⟩
  refine ⟨F, by simp [F], ?_⟩
  intro z
  simp [F, Circle.exp_add, Circle.exp_sub, hL]

def simplexLog {n : ℕ} (s : C(StdSimplex ℝ (Fin (n + 1)), Circle)) :
    C(StdSimplex ℝ (Fin (n + 1)), ℝ) := (simplex_log_exists s).choose

@[simp] theorem simplexLog_first {n : ℕ} (s : C(StdSimplex ℝ (Fin (n + 1)), Circle)) :
    simplexLog s (.single 0) = Complex.arg (s (.single 0)) :=
  (simplex_log_exists s).choose_spec.1

@[simp] theorem simplexLog_exp {n : ℕ} (s : C(StdSimplex ℝ (Fin (n + 1)), Circle))
    (z : StdSimplex ℝ (Fin (n + 1))) : Circle.exp (simplexLog s z) = s z :=
  (simplex_log_exists s).choose_spec.2 z

theorem simplexLog_unique {n : ℕ} (s : C(StdSimplex ℝ (Fin (n + 1)), Circle))
    (F : C(StdSimplex ℝ (Fin (n + 1)), ℝ))
    (hfirst : F (.single 0) = Complex.arg (s (.single 0)))
    (hexp : ∀ z, Circle.exp (F z) = s z) : F = simplexLog s := by
  apply DFunLike.ext
  have hcomp : Circle.exp ∘ F = Circle.exp ∘ simplexLog s := by ext z; simp [hexp]
  have heq : F (.single 0) = simplexLog s (.single 0) := by simp [hfirst]
  exact congrFun (Circle.isCoveringMap_exp.eq_of_comp_eq F.continuous
    (simplexLog s).continuous hcomp (.single 0) heq)

theorem edge_winding_exists (s : C(StdSimplex ℝ (Fin 2), Circle)) :
    ∃! k : ℤ, simplexLog s (.single 1) =
      Complex.arg (s (.single 1)) + k * (2 * Real.pi) := by
  have he : Circle.exp (simplexLog s (.single 1)) =
      Circle.exp (Complex.arg (s (.single 1))) := by simp
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he
  refine ⟨k, hk, ?_⟩
  intro m hm
  apply Int.cast_injective (α := ℝ)
  nlinarith [Real.pi_pos]

def edgeWinding (s : C(StdSimplex ℝ (Fin 2), Circle)) : ℤ :=
  (edge_winding_exists s).exists.choose

theorem edgeWinding_spec (s : C(StdSimplex ℝ (Fin 2), Circle)) :
    simplexLog s (.single 1) = Complex.arg (s (.single 1)) +
      edgeWinding s * (2 * Real.pi) :=
  (edge_winding_exists s).exists.choose_spec

/-- Changing the real lift changes only its additive constant. -/
theorem simplexLog_eq_shift {n : ℕ} (s : C(StdSimplex ℝ (Fin (n + 1)), Circle))
    (F : C(StdSimplex ℝ (Fin (n + 1)), ℝ)) (hexp : ∀ z, Circle.exp (F z) = s z)
    (z : StdSimplex ℝ (Fin (n + 1))) :
    simplexLog s z = F z - F (.single 0) + Complex.arg (s (.single 0)) := by
  let G : C(StdSimplex ℝ (Fin (n + 1)), ℝ) :=
    ⟨fun z => F z - F (.single 0) + Complex.arg (s (.single 0)), by fun_prop⟩
  have hG : G = simplexLog s := simplexLog_unique s G (by simp [G]) (by
    intro y
    simp [G, Circle.exp_add, Circle.exp_sub, hexp])
  exact congrArg (fun g : C(_, ℝ) => g z) hG.symm

theorem edgeWinding_from_lift (s : C(StdSimplex ℝ (Fin 2), Circle))
    (F : C(StdSimplex ℝ (Fin 2), ℝ)) (hexp : ∀ z, Circle.exp (F z) = s z) :
    (edgeWinding s : ℝ) * (2 * Real.pi) =
      F (.single 1) - F (.single 0) +
        Complex.arg (s (.single 0)) - Complex.arg (s (.single 1)) := by
  have h := edgeWinding_spec s
  rw [simplexLog_eq_shift s F hexp] at h
  linarith

def simplexFace (i : Fin 3) : C(StdSimplex ℝ (Fin 2), StdSimplex ℝ (Fin 3)) :=
  ⟨StdSimplex.map i.succAbove, StdSimplex.continuous_map ℝ _⟩

/-- The alternating winding of the three geometric faces vanishes. -/
theorem edgeWinding_boundary (s : C(StdSimplex ℝ (Fin 3), Circle)) :
    edgeWinding (s.comp (simplexFace 0)) - edgeWinding (s.comp (simplexFace 1)) +
      edgeWinding (s.comp (simplexFace 2)) = 0 := by
  have hh (i : Fin 3) := edgeWinding_from_lift (s.comp (simplexFace i))
    ((simplexLog s).comp (simplexFace i)) (by
      intro z
      exact simplexLog_exp s (simplexFace i z))
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  simp [simplexFace, StdSimplex.map_single, Fin.succAbove] at h0 h1 h2
  apply Int.cast_injective (α := ℝ)
  push_cast
  simp only [simplexFace, Fin.succAbove_zero] at *
  nlinarith [Real.pi_pos]

end
end SeifertSurfaces.GenusLinking.CircleConstruction
