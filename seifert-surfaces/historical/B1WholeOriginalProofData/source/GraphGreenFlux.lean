import GraphGreenTransport
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
open Set MeasureTheory
open scoped ContDiff

namespace SeifertSurfaces.GraphGreenTransport
noncomputable section

def pullF (a b : ℝ) (L U : ℝ → ℝ) (f g : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  f (transport L U z) - slope a b L U z * g (transport L U z)

def pullG (L U : ℝ → ℝ) (g : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  (U z.2 - L z.2) * g (transport L U z)

theorem clm_first (A : (ℝ × ℝ) →L[ℝ] ℝ) (w : ℝ) : A (w, 0) = w * A (1, 0) := by
  have he : (w, (0 : ℝ)) = w • (1, (0 : ℝ)) := by ext <;> simp
  rw [he, map_smul, smul_eq_mul]

theorem clm_second (A : (ℝ × ℝ) →L[ℝ] ℝ) (v : ℝ) :
    A (v, 1) = v * A (1, 0) + A (0, 1) := by
  have he : (v, (1 : ℝ)) = v • (1, (0 : ℝ)) + (0, (1 : ℝ)) := by ext <;> simp
  rw [he, map_add, map_smul, smul_eq_mul]

theorem pullF_first {a b : ℝ} {L U : ℝ → ℝ} {f g : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f (transport L U z))
    (hg : DifferentiableAt ℝ g (transport L U z))
    (hA : DifferentiableAt ℝ (pullF a b L U f g) z) :
    fderiv ℝ (pullF a b L U f g) z (1, 0) =
      (U z.2 - L z.2) * fderiv ℝ f (transport L U z) (1, 0) -
        ((derivWithin U (Icc a b) z.2 - derivWithin L (Icc a b) z.2) *
            g (transport L U z) +
          slope a b L U z * (U z.2 - L z.2) *
            fderiv ℝ g (transport L U z) (1, 0)) := by
  have hT : HasDerivAt (fun u : ℝ => transport L U (u, z.2))
      (U z.2 - L z.2, 0) z.1 := by
    simpa [transport] using
      ((hasDerivAt_const z.1 (L z.2)).add
        ((hasDerivAt_id z.1).mul_const (U z.2 - L z.2))).prodMk
        (hasDerivAt_const z.1 z.2)
  have hS : HasDerivAt (fun u : ℝ => slope a b L U (u, z.2))
      (derivWithin U (Icc a b) z.2 - derivWithin L (Icc a b) z.2) z.1 := by
    convert!
      (hasDerivAt_const z.1 (derivWithin L (Icc a b) z.2)).add
        ((hasDerivAt_id z.1).mul_const
          (derivWithin U (Icc a b) z.2 - derivWithin L (Icc a b) z.2)) using 1
    ·
      simp only [one_mul, zero_add]
  have he := (hf.hasFDerivAt.comp_hasDerivAt (f := fun u : ℝ => transport L U (u, z.2)) z.1 hT).sub
    (hS.mul (hg.hasFDerivAt.comp_hasDerivAt (f := fun u : ℝ => transport L U (u, z.2)) z.1 hT))
  have hd := hA.hasFDerivAt.comp_hasDerivAt (f := fun u : ℝ => (u, z.2)) z.1
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  have hh := hd.unique he
  rw [clm_first (fderiv ℝ f (transport L U z)),
    clm_first (fderiv ℝ g (transport L U z))] at hh
  simpa only [mul_assoc, Function.comp_apply, Prod.mk.eta] using hh

theorem pullG_second {a b : ℝ} {L U : ℝ → ℝ} {g : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hL : ContDiffOn ℝ 2 L (Icc a b)) (hU : ContDiffOn ℝ 2 U (Icc a b))
    (hz : z.2 ∈ Ioo a b)
    (hg : DifferentiableAt ℝ g (transport L U z))
    (hB : DifferentiableAt ℝ (pullG L U g) z) :
    fderiv ℝ (pullG L U g) z (0, 1) =
      (derivWithin U (Icc a b) z.2 - derivWithin L (Icc a b) z.2) *
          g (transport L U z) +
        (U z.2 - L z.2) *
          (slope a b L U z * fderiv ℝ g (transport L U z) (1, 0) +
            fderiv ℝ g (transport L U z) (0, 1)) := by
  have hLd := graph_hasDerivAt hL hz
  have hUd := graph_hasDerivAt hU hz
  have hT : HasDerivAt (fun y : ℝ => transport L U (z.1, y))
      (slope a b L U z, 1) z.2 := by
    simpa [transport, slope] using
      (hLd.add ((hUd.sub hLd).const_mul z.1)).prodMk (hasDerivAt_id z.2)
  have he := (hUd.sub hLd).mul
    (hg.hasFDerivAt.comp_hasDerivAt (f := fun y : ℝ => transport L U (z.1, y)) z.2 hT)
  have hd := hB.hasFDerivAt.comp_hasDerivAt (f := fun y : ℝ => (z.1, y)) z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  have hh := hd.unique he
  rw [clm_second (fderiv ℝ g (transport L U z))] at hh
  simpa only [Function.comp_apply, Prod.mk.eta, Pi.sub_apply] using hh

theorem pull_divergence {a b : ℝ} {L U : ℝ → ℝ} {f g : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hL : ContDiffOn ℝ 2 L (Icc a b)) (hU : ContDiffOn ℝ 2 U (Icc a b))
    (hz : z.2 ∈ Ioo a b)
    (hf : DifferentiableAt ℝ f (transport L U z))
    (hg : DifferentiableAt ℝ g (transport L U z))
    (hA : DifferentiableAt ℝ (pullF a b L U f g) z)
    (hB : DifferentiableAt ℝ (pullG L U g) z) :
    fderiv ℝ (pullF a b L U f g) z (1, 0) +
      fderiv ℝ (pullG L U g) z (0, 1) =
      (U z.2 - L z.2) *
        (fderiv ℝ f (transport L U z) (1, 0) +
          fderiv ℝ g (transport L U z) (0, 1)) := by
  rw [pullF_first hf hg hA, pullG_second hL hU hz hg hB]
  ring

theorem contDiffOn_pulls {a b : ℝ} (hab : a < b) {L U : ℝ → ℝ}
    (hL : ContDiffOn ℝ 2 L (Icc a b)) (hU : ContDiffOn ℝ 2 U (Icc a b))
    {f g : ℝ × ℝ → ℝ} {Ω : Set (ℝ × ℝ)}
    (hm : MapsTo (transport L U) (Icc (0 : ℝ) 1 ×ˢ Icc a b) Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω) :
    ContDiffOn ℝ 1 (pullF a b L U f g) (Icc (0 : ℝ) 1 ×ˢ Icc a b) ∧
      ContDiffOn ℝ 1 (pullG L U g) (Icc (0 : ℝ) 1 ×ˢ Icc a b) := by
  have hT := (contDiffOn_transport hL hU).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
  have hF := (hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp hT hm
  have hG := (hg.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp hT hm
  have hs : MapsTo (fun z : ℝ × ℝ => z.2) (Icc (0 : ℝ) 1 ×ˢ Icc a b) (Icc a b) :=
    fun _ hz => hz.2
  have hW := ((hU.sub hL).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).comp contDiffOn_snd hs
  exact ⟨hF.sub ((contDiffOn_slope hab hL hU).mul hG), hW.mul hG⟩

end
end SeifertSurfaces.GraphGreenTransport
