import ProviderBridgeData
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff ENNReal
namespace SeifertSurfaces.QuasilinearProviderBridge.Helpers
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

lemma weakGrad_ae_eq {d : ℕ} [NeZero d]
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : IsOpen B)
    {v : EuclideanSpace ℝ (Fin d) → ℝ} (hv hw : DeGiorgi.MemW1pWitness 2 v B) :
    hv.weakGrad =ᵐ[volume.restrict B] hw.weakGrad := by
  have hc : ∀ i, (fun x => hv.weakGrad x i) =ᵐ[volume.restrict B] (fun x => hw.weakGrad x i) := by
    intro i
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hB (hv.isWeakGrad i) (hw.isWeakGrad i)
      ((hv.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
      ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
  filter_upwards [ae_all_iff.mpr hc] with x hx
  ext i
  exact hx i

lemma l2_pairing_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} {gseq : ℕ → α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hseq : ∀ n, MemLp (gseq n) 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => gseq n x - g x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f x * gseq n x ∂μ) atTop (𝓝 (∫ x, f x * g x ∂μ)) := by
  have hLp : Tendsto (fun n => (hseq n).toLp (gseq n)) atTop (𝓝 (hg.toLp g)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm _ g hg).mpr
    convert hlim using 1
    funext n
    exact eLpNorm_congr_ae ((hseq n).coeFn_toLp.sub (ae_eq_refl g))
  have he (h : α → ℝ) (hh : MemLp h 2 μ) :
      inner ℝ (hf.toLp f) (hh.toLp h) = ∫ x, f x * h x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hh.coeFn_toLp] with x hx hy
    simp [hx, hy, mul_comm]
  have ht : Tendsto (fun n => inner ℝ (hf.toLp f) ((hseq n).toLp (gseq n)))
      atTop (𝓝 (inner ℝ (hf.toLp f) (hg.toLp g))) :=
    ((continuous_const.inner continuous_id).tendsto (hg.toLp g)).comp hLp
  simpa only [he] using ht

end SeifertSurfaces.QuasilinearProviderBridge.Helpers
