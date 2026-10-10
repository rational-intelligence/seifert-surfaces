import A5SectorC1Extension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

set_option autoImplicit false
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- A transverse projection of a native noncorner sector map agrees locally
with a genuine ambient C1 diffeomorphism. Both the inverse and its exact
derivative are retained. -/
theorem C1_sector_projected_local_diffeomorphism
    (A : SectorModel) (G : Euc 2 → Euc 3) (x : Euc 2) (hx : x ∈ A.domain)
    (hregular : x ≠ 0 ∨ A.angle = Real.pi)
    (hG : ContDiffWithinAt ℝ 1 G A.domain x)
    (P : Euc 3 →L[ℝ] Euc 2)
    (hP : Function.Bijective (P.comp (fderivWithin ℝ G A.domain x))) :
    ∃ e : OpenPartialHomeomorph (Euc 2) (Euc 2),
      x ∈ e.source ∧ e x = P (G x) ∧
      e =ᶠ[𝓝[A.domain] x] (P ∘ G) ∧
      ContDiffAt ℝ 1 e x ∧ ContDiffAt ℝ 1 e.symm (P (G x)) ∧
      fderiv ℝ e x = P.comp (fderivWithin ℝ G A.domain x) ∧
      (fderiv ℝ e.symm (P (G x))).comp (P.comp (fderivWithin ℝ G A.domain x)) =
        ContinuousLinearMap.id ℝ (Euc 2) := by
  obtain ⟨g, hg, heq, hd⟩ := C1_sector_model_extension A G x hx hregular hG
  let D := P.comp (fderivWithin ℝ G A.domain x)
  let L := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr hP.injective) (LinearMap.range_eq_top.mpr hP.surjective)
  have hPg : ContDiffAt ℝ 1 (P ∘ g) x := P.contDiff.contDiffAt.comp x hg
  have hder : HasFDerivAt (P ∘ g) (L : Euc 2 →L[ℝ] Euc 2) x := by
    change HasFDerivAt (P ∘ g) (P.comp (fderivWithin ℝ G A.domain x)) x
    rw [← hd]
    exact P.hasFDerivAt.comp x (hg.differentiableAt (by norm_num)).hasFDerivAt
  let e := hPg.toOpenPartialHomeomorph (P ∘ g) hder (by norm_num)
  have hxe : x ∈ e.source := hPg.mem_toOpenPartialHomeomorph_source hder (by norm_num)
  have hp : e x = P (G x) := congrArg P (heq.self_of_nhdsWithin hx)
  have hei : ContDiffAt ℝ 1 e.symm (P (G x)) := by
    rw [← hp]
    exact hPg.to_localInverse hder (by norm_num)
  refine ⟨e, hxe, hp, heq.mono (fun z hz => congrArg P hz), hPg, hei, hder.fderiv, ?_⟩
  have hleft : (e.symm ∘ e) =ᶠ[𝓝 x] id := e.eventually_left_inverse hxe
  have hi : HasFDerivAt e.symm (fderiv ℝ e.symm (P (G x))) (e x) :=
    hp.symm ▸ (hei.differentiableAt (by norm_num)).hasFDerivAt
  have hchain := hi.comp x hder
  have he : fderiv ℝ (e.symm ∘ e) x = ContinuousLinearMap.id ℝ (Euc 2) :=
    hleft.fderiv_eq.trans fderiv_id
  exact hchain.fderiv.symm.trans he

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
