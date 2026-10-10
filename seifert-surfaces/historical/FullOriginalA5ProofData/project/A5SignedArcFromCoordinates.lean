import CurvedSignedDivergence
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff BigOperators
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC CurvedDivergence

/-- A genuine smooth plane coordinate chart gives the exact signed-arc
geometry, including properness of the open arc over every compact test set.
The first coordinate is normal and the second is the arc parameter. -/
theorem signed_arc_geometry_of_smooth_coordinates
    (e : OpenPartialHomeomorph E2 E2)
    (he : ContDiffOn ℝ ∞ (e : E2 → E2) e.source)
    (hi : ContDiffOn ℝ ∞ (e.symm : E2 → E2) e.target)
    (her : ∀ z ∈ e.source, Function.Bijective (fderiv ℝ (e : E2 → E2) z))
    (hir : ∀ z ∈ e.target, Function.Bijective (fderiv ℝ (e.symm : E2 → E2) z))
    (D : Set E2) (hD : IsOpen D) (hDt : D ⊆ e.target)
    (left right : ℝ)
    (hline : ∀ t ∈ Ioo left right, t • coordinateVector 2 1 ∈ e.source)
    (hparam : ∀ z ∈ D, e.symm z 1 ∈ Ioo left right) :
    SignedArcGeometry D (fun z => e.symm z 0)
      (fun t => e (t • coordinateVector 2 1)) left right := by
  let s : E2 → ℝ := fun z => e.symm z 0
  let line : ℝ →L[ℝ] E2 := ContinuousLinearMap.toSpanSingleton ℝ (coordinateVector 2 1)
  let γ : ℝ → E2 := e ∘ line
  have hcoord (z : E2) : z 0 = 0 → z = z 1 • coordinateVector 2 1 := by
    intro hz
    ext k
    fin_cases k <;> simp [coordinateVector, EuclideanSpace.single, hz]
  have hszero (t : ℝ) (ht : t ∈ Ioo left right) : s (γ t) = 0 := by
    change e.symm (e (t • coordinateVector 2 1)) 0 = 0
    rw [e.left_inv (hline t ht)]
    simp [coordinateVector, EuclideanSpace.single]
  have hs : ContDiffOn ℝ ∞ s D :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp_contDiffOn (hi.mono hDt)
  have hγ : ContDiffOn ℝ ∞ γ (Ioo left right) := he.comp line.contDiff.contDiffOn hline
  have hlineemb : IsEmbedding line := by
    apply IsEmbedding.of_comp line.continuous
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous
    have heq : (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) ∘ line = id := by
      funext t
      simp [line, coordinateVector, EuclideanSpace.single]
    rw [heq]
    exact IsEmbedding.id
  have hγemb : IsEmbedding (fun t : Ioo left right => γ t) := by
    let l : Ioo left right → e.source := fun t => ⟨line t, hline t t.property⟩
    have hl : Continuous l := (line.continuous.comp continuous_subtype_val).subtype_mk _
    have hle : IsEmbedding l := IsEmbedding.of_comp hl continuous_subtype_val
      (hlineemb.comp IsEmbedding.subtypeVal)
    exact e.isEmbedding_restrict.comp hle
  refine ⟨hD, hs, ?_, hγ, hγemb, ?_, ?_, ?_⟩
  · intro z hz hzero
    have hd : fderiv ℝ s z =
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).comp (fderiv ℝ (e.symm : E2 → E2) z) := by
      exact ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.comp z
        ((hi.contDiffAt (e.open_target.mem_nhds (hDt hz))).differentiableAt (by simp)).hasFDerivAt).fderiv
    obtain ⟨v, hv⟩ := (hir z (hDt hz)).2 (coordinateVector 2 0)
    have hone : fderiv ℝ s z v = 1 := by
      rw [hd]
      change fderiv ℝ (e.symm : E2 → E2) z v 0 = 1
      rw [hv]
      simp [coordinateVector, EuclideanSpace.single]
    intro hgrad
    have hpair : inner ℝ (planarGradient s z) v = fderiv ℝ s z v := by
      have hvv : v = v 0 • coordinateVector 2 0 + v 1 • coordinateVector 2 1 := by
        ext k
        fin_cases k <;> simp [coordinateVector, EuclideanSpace.single]
      conv_rhs => rw [hvv]
      simp [planarGradient, PiLp.inner_apply, Fin.sum_univ_two, coordinateVector,
        EuclideanSpace.single, PiLp.single_apply, map_add, map_smul]
    rw [hgrad, inner_zero_left, hone] at hpair
    exact zero_ne_one hpair
  · intro t ht
    change fderiv ℝ γ t 1 ≠ 0
    have hd := ((he.contDiffAt (e.open_source.mem_nhds (hline t ht))).differentiableAt
      (by simp)).hasFDerivAt.comp t line.hasFDerivAt
    have hh : fderiv ℝ γ t = (fderiv ℝ (e : E2 → E2) (line t)).comp line := hd.fderiv
    rw [hh]
    intro hzero
    have hz := (her (line t) (hline t ht)).1 (a₁ := line 1) (a₂ := 0)
      (by simpa only [ContinuousLinearMap.comp_apply, map_zero] using hzero)
    have hone := congrArg (fun z : E2 => z 1) hz
    simp [line, coordinateVector, EuclideanSpace.single] at hone
  · ext z
    constructor
    · intro hz
      refine ⟨⟨e.symm z 1, hparam z hz.1, ?_⟩, hz.1⟩
      change e (e.symm z 1 • coordinateVector 2 1) = z
      rw [← hcoord (e.symm z) hz.2, e.right_inv (hDt hz.1)]
    · rintro ⟨⟨t, ht, rfl⟩, hz⟩
      exact ⟨hz, hszero t ht⟩
  · intro K hK hKD
    change IsCompact {t ∈ Ioo left right | γ t ∈ K}
    let B := e.symm '' K ∩ {z : E2 | z 0 = 0}
    have hB : IsCompact B :=
      (hK.image_of_continuousOn (e.symm.continuousOn.mono (hKD.trans hDt))).inter_right
        (isClosed_eq (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous continuous_const)
    have heq : {t ∈ Ioo left right | γ t ∈ K} = (fun z : E2 => z 1) '' B := by
      ext t
      constructor
      · intro ht
        refine ⟨line t, ⟨⟨γ t, ht.2, ?_⟩, ?_⟩, ?_⟩
        · exact e.left_inv (hline t ht.1)
        · simp [line, coordinateVector, EuclideanSpace.single]
        · simp [line, coordinateVector, EuclideanSpace.single]
      · rintro ⟨z, ⟨⟨y, hy, rfl⟩, hz⟩, rfl⟩
        refine ⟨hparam y (hKD hy), ?_⟩
        have hh := hcoord (e.symm y) hz
        change e (e.symm y 1 • coordinateVector 2 1) ∈ K
        rw [← hh, e.right_inv (hDt (hKD hy))]
        exact hy
    rw [heq]
    exact hB.image (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
