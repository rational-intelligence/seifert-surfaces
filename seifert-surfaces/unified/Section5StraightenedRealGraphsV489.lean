import Section5StraightenedRealCollarV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

def straightenedRealHeight (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞)
    (FA FB : Circle × ℝ → ℝ) (b : ℝ) (s : Circle) (r : ℝ) : ℝ :=
  FA (rho s,r/b)-FB (rho s,r/b)

theorem straightened_real_height_smooth
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞)
    (FA FB : Circle × ℝ → ℝ)
    (hFA : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ FA)
    (hFB : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ FB) (b : ℝ) :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun p : Circle × ℝ => straightenedRealHeight rho FA FB b p.1 p.2) :=
  (hFA.sub hFB).comp ((rho.contMDiff.comp contMDiff_fst).prodMk (contMDiff_snd.div_const b))

theorem real_radial_time_scaling {b d eta : ℝ} (hb : 0 < b) (hd : 0 < d)
    {p : T2Coordinate} (hp : p ∈ halfCylinder (b*d) eta) :
    d*((radialCylinderRescaling (b*d) p).2.1:ℝ) = p.2.1/b := by
  rw [radial_cylinder_rescaling_value (mul_pos hb hd) hp]
  field_simp

variable (a : Circle) (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞)
  (FB : Circle × ℝ → ℝ) (d : ℝ) (hd : 0 < d) (hd1 : d < 1)
  (V : TopologicalSpace.Opens E.Carrier)
  (C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞)
  (b : ℝ) (hb : 0 < b)

include hb in
theorem straightened_real_collar_radial (r : E.Carrier → ℝ)
    (hCr : ∀ q : longitudeProductStrip, r (C q) = b*(q.val.2:ℝ))
    (p : T2Coordinate) (hp : p ∈ halfCylinder (b*d) 1) :
    r (straightenedRealCollar a rho FB d hd hd1 V C (b*d) p) = p.2.1 := by
  rw [straightenedRealCollar,Function.comp_apply,
    straightened_time_collar_radial a rho FB d hd hd1 V C r b hCr,
    radial_cylinder_rescaling_value (mul_pos hb hd) hp,mul_div_cancel₀ _ (mul_pos hb hd).ne']

theorem straightened_real_collar_leaf (hFB0 : ∀ z, FB (z,0) = 0)
    (J : LongitudeFoliation.{0} E)
    (hC0 : ∀ p : Circle × Circle,
      (C ⟨(p,0),by change (0:ℝ)<1; norm_num⟩ : E.Carrier) = J.torus p)
    (s : Circle) :
    straightenedRealCollar a rho FB d hd hd1 V C (b*d) (s,0,0) = J.torus (a,rho s) := by
  have he : radialCylinderRescaling (b*d) (s,0,0) = (s,0,0) := by
    simp [radialCylinderRescaling,projIcc_of_mem]
  rw [straightenedRealCollar,Function.comp_apply,he]
  exact straightened_time_collar_leaf a rho FB hFB0 d hd hd1 V C J hC0 s

theorem straightened_real_collar_flow (hsmall : d ≤ 1/4)
    (J : LongitudeFoliation.{0} E) (Phi : B1SourceFoliationFlow J)
    (hflow : ∀ y : ℝ, ∀ q : longitudeProductStrip,
      Phi.ambient y (C q : E.Carrier) = (C (longitudeStripFlow y q) : E.Carrier))
    (s : Circle) (r y : ℝ) :
    straightenedRealCollar a rho FB d hd hd1 V C (b*d) (s,r,y) =
      Phi.ambient y (straightenedRealCollar a rho FB d hd hd1 V C (b*d) (s,r,0)) :=
  straightened_time_collar_flow a rho FB d hd hd1 hsmall V C J Phi hflow
    s (projIcc 0 1 (by norm_num) (r/(b*d))) y

include hb in
theorem straightened_real_collar_mem_iff (FA : Circle × ℝ → ℝ)
    (X : Set E.Carrier)
    (hX : ∀ q : longitudeProductStrip, (q.val.2:ℝ) ≤ d →
      ((C q : E.Carrier) ∈ X ↔ q.val.1.1 = longitudeLabelFlow (FA (q.val.1.2,(q.val.2:ℝ))) a))
    (hsmall : ∀ z : Circle, ∀ t : Time, (t:ℝ) ≤ d → |FA (z,(t:ℝ))-FB (z,(t:ℝ))| ≤ 1)
    (p : T2Coordinate) (hp : p ∈ halfCylinder (b*d) 1) :
    straightenedRealCollar a rho FB d hd hd1 V C (b*d) p ∈ X ↔
      p.2.2 = straightenedRealHeight rho FA FB b p.1 p.2.1 := by
  rw [straightenedRealCollar,Function.comp_apply,
    straightened_time_collar_mem_iff a rho FA FB d hd hd1 V C X hX hsmall _ hp.2.le]
  change p.2.2 = FA (rho p.1,d*((radialCylinderRescaling (b*d) p).2.1:ℝ))-
    FB (rho p.1,d*((radialCylinderRescaling (b*d) p).2.1:ℝ)) ↔ _
  rw [real_radial_time_scaling hb hd hp]
  rfl

/-- Pointwise graph membership yields exactly the source's image intersection. -/
theorem exact_graph_image_of_membership {R eta : ℝ} (kappa : T2Coordinate → E.Carrier)
    (X : Set E.Carrier) (f : Circle → ℝ → ℝ)
    (hinside : ∀ s r, r ∈ Icc (0:ℝ) R → |f s r| < eta)
    (hmem : ∀ p ∈ halfCylinder R eta, kappa p ∈ X ↔ p.2.2 = f p.1 p.2.1) :
    X ∩ (kappa '' halfCylinder R eta) =
      (fun p : Circle × ℝ => kappa (p.1,p.2,f p.1 p.2)) '' radialCylinder R := by
  ext x
  constructor
  · rintro ⟨hx,p,hp,rfl⟩
    have he := (hmem p hp).mp hx
    refine ⟨(p.1,p.2.1),hp.1,?_⟩
    change kappa (p.1,p.2.1,f p.1 p.2.1) = kappa p
    rw [← he]
  · rintro ⟨p,hp,rfl⟩
    have hh : (p.1,p.2,f p.1 p.2) ∈ halfCylinder R eta := ⟨hp,hinside p.1 p.2 hp⟩
    exact ⟨(hmem _ hh).mpr rfl,mem_image_of_mem _ hh⟩

#print axioms straightened_real_height_smooth
#print axioms real_radial_time_scaling
#print axioms straightened_real_collar_radial
#print axioms straightened_real_collar_leaf
#print axioms straightened_real_collar_flow
#print axioms straightened_real_collar_mem_iff
#print axioms exact_graph_image_of_membership
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
