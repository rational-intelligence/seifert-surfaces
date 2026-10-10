import Section5DistanceExtensionV489
import Section5TorusPositiveInverseV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.LongitudeProducers SeifertSurfaces.LongitudeProducers.CollarCutHelpers
noncomputable section
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {D : TubeCoordinates T} (P : GivenExteriorPolarCollar E D)

include P in
/-- The original polar radius is replaced by the actual unit-gradient inward
metric distance, uniformly at the entire boundary torus. -/
theorem polar_distance_reparametrization (g : SmoothMetric E.Carrier)
    {U : Set E.Carrier} (hU : IsOpen U) {r : E.Carrier → ℝ}
    (hr : IsInwardDistanceCoordinate g U r) (hb : (𝓡∂ 3).boundary E.Carrier ⊆ U) :
    ∃ b : ℝ, 0 < b ∧ ∃ tau : ℝ × (Circle × Circle) → ℝ,
      ContMDiff (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ) ∞ tau ∧
      (∀ p, tau (0,p) = 0) ∧
      (∀ s ∈ Icc (0 : ℝ) b, ∀ p,
        tau (s,p) ∈ Ico (0 : ℝ) 1 ∧
        givenExteriorPolarMap E (p.1,p.2,projIcc 0 1 (by norm_num) (tau (s,p))) ∈ U ∧
        r (givenExteriorPolarMap E (p.1,p.2,projIcc 0 1 (by norm_num) (tau (s,p)))) = s) ∧
      (∀ s ∈ Ioc (0 : ℝ) b, ∀ p, 0 < tau (s,p)) := by
  obtain ⟨a,ha,ha1,F,hF,hmatch,hF0,htrans⟩ := polar_distance_real_extension P g hU hr hb
  obtain ⟨a2,ha2,ha21,hinside⟩ := polar_collar_uniform_inside P hU hb
  obtain ⟨e,he,hsource,htarget,hinitial⟩ := torus_radial_compact_partialDiffeomorph_v489
    F hF hF0 (fun p => (htrans p).ne')
  let R : Set (ℝ × (Circle × Circle)) := Iio (min a a2) ×ˢ univ
  have hR : IsOpen R := isOpen_Iio.prod isOpen_univ
  have hR0 : ({0} ×ˢ (univ : Set (Circle × Circle))) ⊆ R := by
    rintro ⟨s,p⟩ ⟨hs,hp⟩
    have hs0 : s = 0 := hs
    subst s
    exact ⟨lt_min ha ha2,hp⟩
  obtain ⟨b,sign,hbpos,hsign,tau0,htau0,htau00,htau0right,htau0pos⟩ :=
    torus_positive_radial_inverse_v489 F hF0 e he hsource htarget hinitial R hR hR0
  obtain ⟨tau,htau,heq⟩ := Manifold.exists_contMDiff_extension_Icc htau0
  have hzero (p : Circle × Circle) : tau (0,p) = 0 := by
    rw [heq ⟨⟨le_rfl,hbpos.le⟩,mem_univ p⟩]
    exact htau00 p
  have hright (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) (p : Circle × Circle) :
      tau (s,p) < min a a2 ∧ F (tau (s,p),p) = sign*s := by
    rw [heq ⟨hs,mem_univ p⟩]
    exact ⟨(htau0right s hs p).1.1,(htau0right s hs p).2⟩
  have hpositive (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) b) (p : Circle × Circle) :
      0 < tau (s,p) := by
    rw [heq ⟨⟨hs.1.le,hs.2⟩,mem_univ p⟩]
    exact htau0pos s hs p
  have hlegal (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) (p : Circle × Circle) :
      tau (s,p) ∈ Ico (0 : ℝ) 1 := by
    refine ⟨?_,((hright s hs p).1.trans_le (min_le_left _ _)).trans ha1⟩
    rcases eq_or_lt_of_le hs.1 with hs0 | hsp
    · rw [← hs0,hzero]
    · exact (hpositive s ⟨hsp,hs.2⟩ p).le
  have hpoint (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) (p : Circle × Circle) :
      givenExteriorPolarMap E (p.1,p.2,projIcc 0 1 (by norm_num) (tau (s,p))) ∈ U ∧
      r (givenExteriorPolarMap E (p.1,p.2,projIcc 0 1 (by norm_num) (tau (s,p)))) = sign*s := by
    have hpr : (projIcc 0 1 (by norm_num) (tau (s,p)) : ℝ) = tau (s,p) :=
      congrArg Subtype.val (projIcc_of_mem (show (0:ℝ) ≤ 1 by norm_num)
        ⟨(hlegal s hs p).1,(hlegal s hs p).2.le⟩)
    refine ⟨hinside p _ (by rw [hpr]; exact ((hright s hs p).1.trans_le (min_le_right _ _)).le),?_⟩
    have hh := hmatch p (projIcc 0 1 (by norm_num) (tau (s,p))) (by
      rw [hpr]; exact ((hright s hs p).1.trans_le (min_le_left _ _)).le)
    rw [hpr] at hh
    exact hh.symm.trans (hright s hs p).2
  have hsignOne : sign = 1 := by
    rcases hsign with hsOne | hsNeg
    · exact hsOne
    have hs : b/2 ∈ Icc (0 : ℝ) b := ⟨(half_pos hbpos).le,half_le_self hbpos.le⟩
    have hn := hr.2.1 _ (hpoint (b/2) hs (1,1)).1
    rw [(hpoint (b/2) hs (1,1)).2,hsNeg] at hn
    linarith
  refine ⟨b,hbpos,tau,htau,hzero,?_,hpositive⟩
  intro s hs p
  refine ⟨hlegal s hs p,(hpoint s hs p).1,?_⟩
  simpa only [hsignOne,one_mul] using (hpoint s hs p).2

#print axioms polar_distance_reparametrization
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
