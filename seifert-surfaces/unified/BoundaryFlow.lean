import DifferentialGeometry.Topology.Diffeomorph.TimeDependentFlow
import Mathlib.Topology.Order.IntermediateValue

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.Foundations.AmbientNeatTransport

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Restrict a Euclidean time-dependent field to the boundary hyperplane. -/
def boundaryField (V : ℝ × (ℝ × E) → ℝ × E) (p : ℝ × E) : E :=
  (V (p.1, (0, p.2))).2

omit [FiniteDimensional ℝ E] in
theorem boundaryField_contDiff {V : ℝ × (ℝ × E) → ℝ × E}
    (hV : ContDiff ℝ ∞ V) : ContDiff ℝ ∞ (boundaryField V) :=
  (hV.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))).snd

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem boundaryField_hasCompactSupport {V : ℝ × (ℝ × E) → ℝ × E}
    (hs : HasCompactSupport V) : HasCompactSupport (boundaryField V) := by
  have he : IsClosedEmbedding (fun p : ℝ × E => (p.1, ((0 : ℝ), p.2))) := by
    have hi : IsClosedEmbedding (fun z : E => ((0 : ℝ), z)) :=
      ⟨isEmbedding_prodMkRight 0, by
        have hr : range (fun z : E => ((0 : ℝ), z)) =
            {q : ℝ × E | q.1 = 0} := by
          ext q
          simp only [mem_range, mem_ofPred_eq]
          constructor
          · rintro ⟨z, rfl⟩
            rfl
          · intro hq
            exact ⟨q.2, Prod.ext hq.symm rfl⟩
        rw [hr]
        exact isClosed_eq continuous_fst continuous_const⟩
    exact IsClosedEmbedding.id.prodMap hi
  exact (hs.comp_isClosedEmbedding he).comp_left (g := Prod.snd) rfl

/-- Tangency on the boundary suffices to keep its Euclidean flow in the boundary.
The tangential velocity may be nonzero. -/
theorem timeDependentFlow_boundary {V : ℝ × (ℝ × E) → ℝ × E}
    (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, (V (t, (0, z))).1 = 0) (s t : ℝ) (z : E) :
    (Diffeomorph.timeDependentFlow V hV hs s t (0, z)).1 = 0 := by
  let W := boundaryField V
  have hW := boundaryField_contDiff hV
  have hWs := boundaryField_hasCompactSupport hs
  let γ : ℝ → ℝ × E := fun u =>
    (0, Diffeomorph.timeDependentFlow W hW hWs s u z)
  have hγ : IsIntegralCurve γ (fun u q => V (u, q)) := by
    intro u
    have hd := Diffeomorph.isIntegralCurve_timeDependentFlow W hW hWs s z u
    have hg := (hasDerivAt_const u (0 : ℝ)).prodMk hd
    convert hg using 1
    exact Prod.ext (hb u _) rfl
  have he := Diffeomorph.timeDependentFlow_apply_eq_of_isIntegralCurve V hV hs hγ s t
  have hstart : γ s = (0, z) := by
    simp only [γ, Diffeomorph.timeDependentFlow_refl, Diffeomorph.coe_refl, id_eq]
  rw [hstart] at he
  exact congrArg Prod.fst he

theorem timeDependentFlow_boundary_iff {V : ℝ × (ℝ × E) → ℝ × E}
    (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, (V (t, (0, z))).1 = 0) (s t : ℝ) (x : ℝ × E) :
    (Diffeomorph.timeDependentFlow V hV hs s t x).1 = 0 ↔ x.1 = 0 := by
  constructor
  · intro hx
    have h := timeDependentFlow_boundary hV hs hb t s
      (Diffeomorph.timeDependentFlow V hV hs s t x).2
    have he : (0, (Diffeomorph.timeDependentFlow V hV hs s t x).2) =
        Diffeomorph.timeDependentFlow V hV hs s t x := Prod.ext hx.symm rfl
    rw [he, ← Diffeomorph.timeDependentFlow_symm,
      Diffeomorph.symm_apply_apply] at h
    exact h
  · intro hx
    have he : x = (0, x.2) := Prod.ext hx rfl
    rw [he]
    exact timeDependentFlow_boundary hV hs hb s t x.2

/-- An interior point cannot cross a boundary preserved by every forward and
backward flow map. -/
theorem timeDependentFlow_pos {V : ℝ × (ℝ × E) → ℝ × E}
    (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, (V (t, (0, z))).1 = 0) (s t : ℝ) (x : ℝ × E)
    (hx : 0 < x.1) :
    0 < (Diffeomorph.timeDependentFlow V hV hs s t x).1 := by
  let a : ℝ → ℝ := fun u => (Diffeomorph.timeDependentFlow V hV hs s u x).1
  have ha : Continuous a :=
    continuous_iff_continuousAt.mpr (fun u =>
      (Diffeomorph.isIntegralCurve_timeDependentFlow V hV hs s x u).continuousAt.fst)
  have hstart : a s = x.1 := by
    simp only [a, Diffeomorph.timeDependentFlow_refl, Diffeomorph.coe_refl, id_eq]
  by_contra! h
  have hz : 0 ∈ Icc (a t) (a s) := ⟨h, hstart.symm ▸ hx.le⟩
  obtain ⟨u, hu⟩ := intermediate_value_univ t s ha hz
  have hzero : x.1 = 0 := (timeDependentFlow_boundary_iff hV hs hb s u x).mp hu
  exact hx.ne' hzero

theorem timeDependentFlow_pos_iff {V : ℝ × (ℝ × E) → ℝ × E}
    (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, (V (t, (0, z))).1 = 0) (s t : ℝ) (x : ℝ × E) :
    0 < (Diffeomorph.timeDependentFlow V hV hs s t x).1 ↔ 0 < x.1 := by
  constructor
  · intro hx
    have h := timeDependentFlow_pos hV hs hb t s
      (Diffeomorph.timeDependentFlow V hV hs s t x) hx
    rwa [← Diffeomorph.timeDependentFlow_symm, Diffeomorph.symm_apply_apply] at h
  · exact timeDependentFlow_pos hV hs hb s t x

theorem timeDependentFlow_nonneg_iff {V : ℝ × (ℝ × E) → ℝ × E}
    (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, (V (t, (0, z))).1 = 0) (s t : ℝ) (x : ℝ × E) :
    0 ≤ (Diffeomorph.timeDependentFlow V hV hs s t x).1 ↔ 0 ≤ x.1 := by
  simpa only [le_iff_eq_or_lt, eq_comm] using
    or_congr (timeDependentFlow_boundary_iff hV hs hb s t x)
      (timeDependentFlow_pos_iff hV hs hb s t x)

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
