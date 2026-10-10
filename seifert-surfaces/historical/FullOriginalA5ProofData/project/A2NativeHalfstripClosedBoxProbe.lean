import A2MetricFluxV468

set_option autoImplicit false
open Set Topology Filter
open scoped ContDiff
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.A2NativeTests
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen
open SeifertSurfaces.OriginalEndpoints.A2MetricFlux

/-- The native clock selects the SAME straight-frame closed rectangle
inside the actual halfstrip; its positive open part stays in the original
sector interior. The bulk map remains affine. -/
theorem native_halfstrip_closed_affine_box_maps
    (D : Set E2) (p e m : E2) (clock : ℝ → ℝ) (H h a b l r : ℝ)
    (hh : 0 < h) (hhH : h < H) (hwindow : Icc l r ⊆ Ioo (-1 : ℝ) 1)
    (himage : clock '' Icc l r = Icc a b)
    (hclosed : MapsTo (fun z : ℝ × ℝ => p + clock z.1 • e + z.2 • m)
      (Ioo (-1 : ℝ) 1 ×ˢ Ico 0 H) D)
    (hpositive : MapsTo (fun z : ℝ × ℝ => p + clock z.1 • e + z.2 • m)
      (Ioo (-1 : ℝ) 1 ×ˢ Ioo 0 H) (interior D)) :
    MapsTo (fun z : ℝ × ℝ => p + z.1 • e + z.2 • m) (Icc a b ×ˢ Icc 0 h) D ∧
    MapsTo (fun z : ℝ × ℝ => p + z.1 • e + z.2 • m)
      (Ioo a b ×ˢ Ioo 0 h) (interior D) := by
  constructor
  · intro z hz
    have hc : z.1 ∈ clock '' Icc l r := himage.symm ▸ hz.1
    obtain ⟨t,ht,heq⟩ := hc
    have hb : (t,z.2) ∈ Ioo (-1 : ℝ) 1 ×ˢ Ico 0 H :=
      ⟨hwindow ht,⟨hz.2.1,hz.2.2.trans_lt hhH⟩⟩
    simpa only [heq] using hclosed hb
  · intro z hz
    have hc : z.1 ∈ clock '' Icc l r := himage.symm ▸
      (show z.1 ∈ Icc a b from ⟨hz.1.1.le,hz.1.2.le⟩)
    obtain ⟨t,ht,heq⟩ := hc
    have hb : (t,z.2) ∈ Ioo (-1 : ℝ) 1 ×ˢ Ioo 0 H :=
      ⟨hwindow ht,⟨hz.2.1,hz.2.2.trans hhH⟩⟩
    simpa only [heq] using hpositive hb

#print axioms native_halfstrip_closed_affine_box_maps
end SeifertSurfaces.OriginalEndpoints.A2NativeTests
