import A3SharedGraph
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.CurvedDivergence
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

def planarDivergence (F : E2 → E2) (x : E2) : ℝ :=
  ∑ i : Fin 2, fderiv ℝ (fun y => F y i) x (coordinateVector 2 i)

/-- False is the negative side; true is the positive side. -/
def signedDomain (disc : Set E2) (s : E2 → ℝ) (positive : Bool) : Set E2 :=
  {x ∈ disc | if positive then 0 < s x else s x < 0}

def signedNormal (s : E2 → ℝ) (positive : Bool) (x : E2) : E2 :=
  if positive then -(‖planarGradient s x‖⁻¹ • planarGradient s x)
  else ‖planarGradient s x‖⁻¹ • planarGradient s x

def arcParameters (disc : Set E2) (γ : ℝ → E2) (left right : ℝ) : Set ℝ :=
  {t ∈ Ioo left right | γ t ∈ disc}

/-- Pure geometry and parametrization; no flux, equation or weak PDE field. -/
structure SignedArcGeometry (disc : Set E2) (s : E2 → ℝ)
    (γ : ℝ → E2) (left right : ℝ) : Prop where
  disc_open : IsOpen disc
  signed_smooth : ContDiffOn ℝ ∞ s disc
  signed_regular : ∀ x ∈ disc, s x = 0 → planarGradient s x ≠ 0
  arc_smooth : ContDiffOn ℝ ∞ γ (Ioo left right)
  arc_embedding : IsEmbedding (fun t : Ioo left right => γ t)
  arc_regular : ∀ t ∈ Ioo left right, fderiv ℝ γ t 1 ≠ 0
  zero_set_exact : {x ∈ disc | s x = 0} = (γ '' Ioo left right) ∩ disc
  compact_parameter_control : ∀ K : Set E2, IsCompact K → K ⊆ disc →
    IsCompact {t ∈ Ioo left right | γ t ∈ K}

/-- Test-local properness is explicit, with the exact open parameter endpoints. -/
theorem compact_arc_test_integrability (disc : Set E2) (s : E2 → ℝ)
    (γ : ℝ → E2) (left right : ℝ) (G : SignedArcGeometry disc s γ left right)
    (F : E2 → E2) (hF : ContinuousOn F disc)
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ disc) :
    ∀ positive : Bool, IntegrableOn (fun t =>
      inner ℝ (F (γ t)) (signedNormal s positive (γ t)) * φ (γ t) *
        ‖fderiv ℝ γ t 1‖) (arcParameters disc γ left right) := by
  let T : Set ℝ := {t ∈ Ioo left right | γ t ∈ tsupport φ}
  have hT : IsCompact T := G.compact_parameter_control (tsupport φ) hc hs
  have hTI : T ⊆ Ioo left right := fun _ ht => ht.1
  have hTd : MapsTo γ T disc := fun _ ht => hs ht.2
  have hγ : ContinuousOn γ T := G.arc_smooth.continuousOn.mono hTI
  have hgrad : ContinuousOn (planarGradient s) disc := by
    apply continuousOn_finsetSum
    intro i hi
    exact ((G.signed_smooth.continuousOn_fderiv_of_isOpen G.disc_open (by simp)).clm_apply
      continuousOn_const).smul continuousOn_const
  have hgradγ : ContinuousOn (fun t => planarGradient s (γ t)) T :=
    hgrad.comp hγ hTd
  have hnonzero : ∀ t ∈ T, planarGradient s (γ t) ≠ 0 := by
    intro t ht
    apply G.signed_regular (γ t) (hTd ht)
    have hx : γ t ∈ {x ∈ disc | s x = 0} := by
      rw [G.zero_set_exact]
      exact ⟨⟨t, ht.1, rfl⟩, hTd ht⟩
    exact hx.2
  have hnormal : ContinuousOn (fun t => ‖planarGradient s (γ t)‖⁻¹ •
      planarGradient s (γ t)) T :=
    (hgradγ.norm.inv₀ (fun t ht => norm_ne_zero_iff.mpr (hnonzero t ht))).smul hgradγ
  have hspeed : ContinuousOn (fun t => ‖fderiv ℝ γ t 1‖) T :=
    (((G.arc_smooth.continuousOn_fderiv_of_isOpen isOpen_Ioo (by simp)).clm_apply
      continuousOn_const).mono hTI).norm
  have hFγ : ContinuousOn (fun t => F (γ t)) T := hF.comp hγ hTd
  have hφγ : ContinuousOn (fun t => φ (γ t)) T := hφ.continuous.continuousOn.comp hγ
    (fun _ _ => mem_univ _)
  have hparam : MeasurableSet (arcParameters disc γ left right) :=
    (G.arc_smooth.continuousOn.isOpen_inter_preimage isOpen_Ioo G.disc_open).measurableSet
  intro positive
  have hn : ContinuousOn (fun t => signedNormal s positive (γ t)) T := by
    cases positive
    · exact hnormal
    · exact hnormal.neg
  have hcint : IntegrableOn (fun t => inner ℝ (F (γ t)) (signedNormal s positive (γ t)) *
      φ (γ t) * ‖fderiv ℝ γ t 1‖) T :=
    ((hFγ.inner hn).mul hφγ |>.mul hspeed).integrableOn_compact hT
  apply hcint.of_forall_sdiff_eq_zero hparam
  intro t ht
  have hnot : γ t ∉ tsupport φ := by
    intro hm
    exact ht.2 ⟨ht.1.1, hm⟩
  have hz : φ (γ t) = 0 := image_eq_zero_of_notMem_tsupport hnot
  rw [hz, mul_zero, zero_mul]



end SeifertSurfaces.OriginalEndpoints.CurvedDivergence
