import Mathlib
import MetricBounded
import MetricPullback

/-!
# Appendix C.7: smooth representatives of a conformal metric field

Source: `references/seifert-surfaces.txt`, lines 2124–2144.
A conformal class is expressed by positive pointwise multiples of positive
definite bilinear forms on the *actual tangent bundle*. Local smooth metric
representatives carry smoothness of their bundle sections, not a bare predicate.
-/

noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace SeifertSurfaces.AppendixC

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1500000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Pointwise conformal equivalence of tangent metrics. -/
def PointwiseConformal
    (g h : ∀ p : M, TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) : Prop :=
  ∀ p, ∃ c : ℝ, 0 < c ∧ ∀ v w, g p v w = c * h p v w

/-- A smooth conformal field is represented pointwise by `representative`,
with local positive smooth metric representatives. No global smoothness of
the initially chosen representative is assumed. -/
structure SmoothConformalField where
  representative : ∀ p : M,
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ
  symmetric : ∀ p v w, representative p v w = representative p w v
  positive : ∀ p v, v ≠ 0 → 0 < representative p v v
  local_smooth : ∀ p : M, ∃ (U : Set M)
      (g : ∀ q : M, TangentSpace I q →L[ℝ] TangentSpace I q →L[ℝ] ℝ),
    IsOpen U ∧ p ∈ U ∧
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun q => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) q (g q)) U ∧
      (∀ q ∈ U, ∀ v w, g q v w = g q w v) ∧
      (∀ q ∈ U, ∀ v, v ≠ 0 → 0 < g q v v) ∧
      (∀ q ∈ U, ∃ c : ℝ, 0 < c ∧
        ∀ v w, g q v w = c * representative q v w)

/-- The conformal data furnished only on the interior by the cited limiting
argument. The values of `representative` at the boundary are irrelevant;
all positivity, smoothness and comparison claims are restricted to the
manifold interior. This avoids assuming the boundary extension sought in C.9. -/
structure InteriorConformalField where
  representative : ∀ p : M,
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ
  symmetric : ∀ p ∈ I.interior M, ∀ v w,
    representative p v w = representative p w v
  positive : ∀ p ∈ I.interior M, ∀ v, v ≠ 0 → 0 < representative p v v
  local_smooth : ∀ p ∈ I.interior M, ∃ (U : Set M)
      (g : ∀ q : M, TangentSpace I q →L[ℝ] TangentSpace I q →L[ℝ] ℝ),
    IsOpen U ∧ p ∈ U ∧ U ⊆ I.interior M ∧
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun q => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) q (g q)) U ∧
      (∀ q ∈ U, ∃ c : ℝ, 0 < c ∧
        ∀ v w, g q v w = c * representative q v w)

def ConformalOnInterior
    (g h : ∀ p : M, TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) : Prop :=
  ∀ p ∈ I.interior M, ∃ c : ℝ, 0 < c ∧ ∀ v w, g p v w = c * h p v w

/-- C.7's global representative, bundled using Mathlib's smooth Riemannian
metric type. The source assumes a smooth surface with partitions of unity;
Hausdorffness and second countability are explicit here. -/
theorem c7_smooth_metric_representative
    [T2Space M] [SecondCountableTopology M]
    (t : SmoothConformalField I M) :
    ∃ g : ContMDiffRiemannianMetric I ∞ E (fun p : M => TangentSpace I p),
      PointwiseConformal I M g.inner t.representative := by
  classical
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  letI : SigmaCompactSpace M := inferInstance
  let V := fun p : M => TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ
  let rays : ∀ p : M, Set (V p) := fun p =>
    {B | ∃ c : ℝ, 0 < c ∧ ∀ v w, B v w = c * t.representative p v w}
  have hconv : ∀ p, Convex ℝ (rays p) := by
    intro p B hB C hC a b ha hb hab
    rcases hB with ⟨c, hc, hBc⟩
    rcases hC with ⟨d, hd, hCd⟩
    refine ⟨a * c + b * d, ?_, ?_⟩
    · by_cases ha' : a = 0
      · have hb' : b = 1 := by linarith
        simp [ha', hb', hd]
      · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha')) hc)
          (mul_nonneg hb hd.le)
    · intro v w
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, hBc, hCd]
      ring
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local I V rays hconv
    (n := ⊤) (F_fiber := E →L[ℝ] E →L[ℝ] ℝ) (by
      intro p
      rcases t.local_smooth p with ⟨U, B, hU, hp, hB, _, _, hc⟩
      exact ⟨U, hU.mem_nhds hp, B, hB, hc⟩)
  have hsym : ∀ p v w, s p v w = s p w v := by
    intro p v w
    rcases hs p with ⟨c, _, hc⟩
    rw [hc, hc, t.symmetric]
  have hpos : ∀ p v, v ≠ 0 → 0 < s p v v := by
    intro p v hv
    rcases hs p with ⟨c, hc, heq⟩
    rw [heq]
    exact mul_pos hc (t.positive p v hv)
  refine ⟨{ inner := s
            symm := hsym
            pos := hpos
            isVonNBounded := fun p =>
              positive_bilinear_unitBall_bounded (s p) (hsym p) (hpos p)
            contMDiff := s.contMDiff }, hs⟩

/-- Restriction/pullback of a smooth representative is smooth up to the
boundary of a smooth compact subsurface. This declares the genuine smooth
embedding and tangent pullback; constructing the double/subsurface is separate. -/
theorem c7_restrict_metric_smooth_up_to_boundary
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES]
    [FiniteDimensional ℝ ES]
    {HS : Type*} [TopologicalSpace HS] (IS : ModelWithCorners ℝ ES HS)
    (S : Type*) [TopologicalSpace S] [ChartedSpace HS S] [IsManifold IS ∞ S]
    (j : S → M) (hj : ContMDiff IS I ∞ j)
    (himmersion : ∀ p, Function.Injective (mfderiv IS I j p))
    (g : ContMDiffRiemannianMetric I ∞ E (fun p : M => TangentSpace I p)) :
    ∃ gs : ContMDiffRiemannianMetric IS ∞ ES (fun p : S => TangentSpace IS p),
      ∀ p v w, gs.inner p v w =
        g.inner (j p) (mfderiv IS I j p v) (mfderiv IS I j p w) := by
  let B := fun p => pullbackBilinear (g.inner (j p)) (mfderiv IS I j p)
  have hsym : ∀ p v w, B p v w = B p w v := by
    intro p v w
    exact g.symm (j p) _ _
  have hpos : ∀ p v, v ≠ 0 → 0 < B p v v := by
    intro p v hv
    apply g.pos
    intro hz
    apply hv
    apply himmersion p
    simpa using hz
  refine ⟨{ inner := B
            symm := hsym
            pos := hpos
            isVonNBounded := fun p =>
              positive_bilinear_unitBall_bounded (B p) (hsym p) (hpos p)
            contMDiff := contMDiff_pullback_bilinear j hj g.inner g.contMDiff }, ?_⟩
  intro p v w
  rfl

end SeifertSurfaces.AppendixC
