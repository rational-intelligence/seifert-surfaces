import Section5DistanceReparametrizationV489
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
theorem polar_distance_inverse_data (g : SmoothMetric E.Carrier)
    {U : Set E.Carrier} (hU : IsOpen U) {r : E.Carrier → ℝ}
    (hr : IsInwardDistanceCoordinate g U r) (hb : (𝓡∂ 3).boundary E.Carrier ⊆ U) :
    ∃ a b : ℝ, 0 < a ∧ a < 1 ∧ 0 < b ∧
    ∃ F tau : ℝ × (Circle × Circle) → ℝ,
    ∃ e : PartialDiffeomorph (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1)))
        (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (ℝ × (Circle × Circle)) (ℝ × (Circle × Circle)) ∞,
      ContMDiff (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ) ∞ F ∧
      ContMDiff (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ) ∞ tau ∧
      (∀ p, F (0,p) = 0) ∧ (∀ p, tau (0,p) = 0) ∧
      ((e : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) = fun q => (F q,q.2)) ∧
      (({0} ×ˢ (univ : Set (Circle × Circle))) ⊆ e.source) ∧
      (∀ p : Circle × Circle, ∀ t : Time, (t : ℝ) ≤ a →
        F ((t : ℝ),p) = r (givenExteriorPolarMap E (p.1,p.2,t)) ∧
        givenExteriorPolarMap E (p.1,p.2,t) ∈ U ∧ 0 ≤ F ((t : ℝ),p)) ∧
      (∀ s ∈ Icc (0 : ℝ) b, ∀ p,
        (tau (s,p),p) ∈ e.source ∧ tau (s,p) ∈ Ico (0 : ℝ) a ∧ F (tau (s,p),p) = s) ∧
      (∀ s ∈ Ioc (0 : ℝ) b, ∀ p, 0 < tau (s,p)) := by
  obtain ⟨a0,ha0,ha01,F,hF,hmatch,hF0,htrans⟩ := polar_distance_real_extension P g hU hr hb
  obtain ⟨a2,ha2,ha21,hinside⟩ := polar_collar_uniform_inside P hU hb
  let a := min a0 a2
  have ha : 0 < a := lt_min ha0 ha2
  have ha1 : a < 1 := (min_le_left _ _).trans_lt ha01
  have hFactual (p : Circle × Circle) (t : Time) (ht : (t : ℝ) ≤ a) :
      F ((t : ℝ),p) = r (givenExteriorPolarMap E (p.1,p.2,t)) ∧
      givenExteriorPolarMap E (p.1,p.2,t) ∈ U ∧ 0 ≤ F ((t : ℝ),p) := by
    have hm := hmatch p t (ht.trans (min_le_left _ _))
    have hi := hinside p t (ht.trans (min_le_right _ _))
    exact ⟨hm,hi,hm ▸ hr.2.1 _ hi⟩
  obtain ⟨e,he,hsource,htarget,hinitial⟩ := torus_radial_compact_partialDiffeomorph_v489
    F hF hF0 (fun p => (htrans p).ne')
  let R : Set (ℝ × (Circle × Circle)) := e.source ∩ (Iio a ×ˢ univ)
  have hR : IsOpen R := e.open_source.inter (isOpen_Iio.prod isOpen_univ)
  have hR0 : ({0} ×ˢ (univ : Set (Circle × Circle))) ⊆ R := by
    rintro ⟨s,p⟩ ⟨hs,hp⟩
    have hs0 : s = 0 := hs
    subst s
    exact ⟨hsource ⟨rfl,hp⟩,ha,hp⟩
  obtain ⟨b,sign,hbpos,hsign,tau0,htau0,htau00,htau0right,htau0pos⟩ :=
    torus_positive_radial_inverse_v489 F hF0 e he hsource htarget hinitial R hR hR0
  obtain ⟨tau,htau,heq⟩ := Manifold.exists_contMDiff_extension_Icc htau0
  have hzero (p : Circle × Circle) : tau (0,p) = 0 := by
    rw [heq ⟨⟨le_rfl,hbpos.le⟩,mem_univ p⟩]
    exact htau00 p
  have hright (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) (p : Circle × Circle) :
      (tau (s,p),p) ∈ e.source ∧ tau (s,p) < a ∧ F (tau (s,p),p) = sign*s := by
    rw [heq ⟨hs,mem_univ p⟩]
    exact ⟨(htau0right s hs p).1.1,(htau0right s hs p).1.2.1,(htau0right s hs p).2⟩
  have hpositive (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) b) (p : Circle × Circle) :
      0 < tau (s,p) := by
    rw [heq ⟨⟨hs.1.le,hs.2⟩,mem_univ p⟩]
    exact htau0pos s hs p
  have hlegal (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) (p : Circle × Circle) :
      tau (s,p) ∈ Ico (0 : ℝ) a := by
    refine ⟨?_,(hright s hs p).2.1⟩
    rcases eq_or_lt_of_le hs.1 with hs0 | hsp
    · rw [← hs0,hzero]
    · exact (hpositive s ⟨hsp,hs.2⟩ p).le
  have hsignOne : sign = 1 := by
    rcases hsign with hsOne | hsNeg
    · exact hsOne
    have hs : b/2 ∈ Icc (0 : ℝ) b := ⟨(half_pos hbpos).le,half_le_self hbpos.le⟩
    let t : Time := ⟨tau (b/2,(1,1)),(hlegal _ hs _).1,((hlegal _ hs _).2.trans ha1).le⟩
    have hn := (hFactual (1,1) t (hlegal _ hs _).2.le).2.2
    change 0 ≤ F (tau (b/2,(1,1)),(1,1)) at hn
    rw [(hright _ hs _).2.2,hsNeg] at hn
    linarith
  refine ⟨a,b,ha,ha1,hbpos,F,tau,e,hF,htau,hF0,hzero,he,hsource,hFactual,?_,hpositive⟩
  intro s hs p
  exact ⟨(hright s hs p).1,hlegal s hs p,by simpa only [hsignOne,one_mul] using (hright s hs p).2.2⟩

#print axioms polar_distance_inverse_data
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
