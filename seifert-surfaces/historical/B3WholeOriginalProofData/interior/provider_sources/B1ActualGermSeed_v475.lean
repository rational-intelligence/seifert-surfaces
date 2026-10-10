import B1ActualCollarTopology_v475

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- A zero height patch produces equality of the two actual ambient image
germs. The open three-dimensional collar image excludes other sheets. -/
theorem actual_local_zero_ambient_germ_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (hzero : ∃ U : Set E2, IsOpen U ∧ U.Nonempty ∧ U ⊆ halfDisc W.R ∧
      ∀ x ∈ U, localHeight D s x = 0) :
    ∃ p : E.Carrier, ∃ O : Set E.Carrier,
      IsOpen O ∧ p ∈ O ∧ p ∈ D.A.1.image ∩ D.B.1.image ∧
      p ∉ (𝓡∂ 3).boundary E.Carrier ∧ D.A.1.image ∩ O = D.B.1.image ∩ O := by
  obtain ⟨U,hU,hUne,hsub,hzero⟩ := hzero
  let b : E3 → E2 := fun y => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![y 0,y 1]
  have hb0 (y : E3) : b y 0 = y 0 := rfl
  have hb1 (y : E3) : b y 1 = y 1 := rfl
  have hb : Continuous b := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i <;> exact (EuclideanSpace.proj (𝕜 := ℝ) _).continuous
  let V : Set E3 := {y | b y ∈ U ∧ |y 2| < D.eta}
  have hV : IsOpen V := (hU.preimage hb).inter
    (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.abs continuous_const)
  have hVC : V ⊆ collarDomain D W.R := by
    intro y hy
    have hbase := hsub hy.1
    have hn : ‖b y‖ < W.R := by
      simpa only [halfDisc,disc,Metric.mem_ball,dist_zero_right] using hbase.1
    have hcoord : |y 0| ≤ ‖b y‖ := by
      simpa only [hb0,Real.norm_eq_abs] using PiLp.norm_apply_le (b y) 0
    exact ⟨by linarith [W.R_pos],
      ⟨(actual_halfdisc_radial_membership_v474 D s W (b y) hbase).1.le,
       (actual_halfdisc_radial_membership_v474 D s W (b y) hbase).2.le⟩,hy.2⟩
  let O := localCollar D s '' V
  have hO : IsOpen O := actual_localCollar_open_image_v475 D s W V hV hVC
  have hsame : D.A.1.image ∩ O = D.B.1.image ∩ O := by
    ext p
    constructor
    · rintro ⟨hpA,y,hy,rfl⟩
      have hyC := hVC hy
      have ha : localCollar D s y ∈ D.A.1.image ∩
          (D.collar '' halfCylinder D.r0 D.eta) :=
        ⟨hpA,⟨(localCircle D s (y 0),y 1,y 2),⟨hyC.2.1,hyC.2.2⟩,rfl⟩⟩
      rw [D.A_graph_exact] at ha
      obtain ⟨z,hz,hzeq⟩ := ha
      have hpre : (z.1,z.2,D.f z.1 z.2) = (localCircle D s (y 0),y 1,y 2) := by
        have he := D.collar_embedding.injective
          (a₁ := ⟨(z.1,z.2,D.f z.1 z.2),⟨hz,D.graph_inside _ _ hz⟩⟩)
          (a₂ := ⟨(localCircle D s (y 0),y 1,y 2),⟨hyC.2.1,hyC.2.2⟩⟩) hzeq
        exact congrArg Subtype.val he
      have hs : z.1 = localCircle D s (y 0) := congrArg Prod.fst hpre
      have hr : z.2 = y 1 := congrArg (fun q : Circle × (ℝ × ℝ) => q.2.1) hpre
      have hf : D.f z.1 z.2 = y 2 := congrArg (fun q : Circle × (ℝ × ℝ) => q.2.2) hpre
      have hyzero : y 2 = 0 := by
        calc y 2 = D.f z.1 z.2 := hf.symm
          _ = localHeight D s (b y) := by rw [hs,hr]; rfl
          _ = 0 := hzero (b y) hy.1
      have hB := (actual_halfdisc_graph_membership_v474 D s W (b y) (hsub hy.1)).2.1
      refine ⟨?_,⟨y,hy,rfl⟩⟩
      simpa only [localCollar,hb0,hb1,hyzero] using hB
    · rintro ⟨hpB,y,hy,rfl⟩
      have hyC := hVC hy
      have hb' : localCollar D s y ∈ D.B.1.image ∩
          (D.collar '' halfCylinder D.r0 D.eta) :=
        ⟨hpB,⟨(localCircle D s (y 0),y 1,y 2),⟨hyC.2.1,hyC.2.2⟩,rfl⟩⟩
      rw [D.B_graph_exact] at hb'
      obtain ⟨z,hz,hzeq⟩ := hb'
      have hpre : (z.1,z.2,(0 : ℝ)) = (localCircle D s (y 0),y 1,y 2) := by
        have he := D.collar_embedding.injective
          (a₁ := ⟨(z.1,z.2,(0 : ℝ)),⟨hz,by simpa using D.eta_pos⟩⟩)
          (a₂ := ⟨(localCircle D s (y 0),y 1,y 2),⟨hyC.2.1,hyC.2.2⟩⟩) hzeq
        exact congrArg Subtype.val he
      have hyzero : y 2 = 0 :=
        (congrArg (fun q : Circle × (ℝ × ℝ) => q.2.2) hpre).symm
      have hA := (actual_halfdisc_graph_membership_v474 D s W (b y) (hsub hy.1)).1
      rw [hzero (b y) hy.1] at hA
      refine ⟨?_,⟨y,hy,rfl⟩⟩
      simpa only [localCollar,hb0,hb1,hyzero] using hA
  obtain ⟨x,hx⟩ := hUne
  let y : E3 := jetPoint (x,0,(0 : E2))
  have hby : b y = x := by ext i; fin_cases i <;> rfl
  have hyV : y ∈ V := by
    refine ⟨?_,?_⟩
    · change b y ∈ U
      rwa [hby]
    · change |(0 : ℝ)| < D.eta
      simpa using D.eta_pos
  have hpoint := actual_halfdisc_graph_membership_v474 D s W x (hsub hx)
  have hA := hpoint.1
  rw [hzero x hx] at hA
  exact ⟨localCollar D s y,O,hO,⟨y,hyV,rfl⟩,⟨hA,hpoint.2.1⟩,hpoint.2.2.2,hsame⟩

#print axioms actual_local_zero_ambient_germ_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
