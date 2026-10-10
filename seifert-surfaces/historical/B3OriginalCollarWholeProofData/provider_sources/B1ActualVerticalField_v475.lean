import B1ActualChartVectorField_v475

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
set_option backward.isDefEq.respectTransparency false

/-- The first two coordinates of the literal B1 collar. -/
def native_collar_base_v475 (y : E3) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![y 0,y 1]

theorem native_collar_base_smooth_v475 : ContDiff ℝ ∞ native_collar_base_v475 := by
  unfold native_collar_base_v475
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff

/-- One supported vertical ambient field acts on an entire compact attained
graph. The collar and exterior-interior conditions are derived from D. -/
theorem actual_compact_graph_vertical_field_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (A : Set E2) (hA : IsCompact A) (hAhalf : A ⊆ halfDisc W.R)
    (u φ : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u W.U)
    (hheight : ∀ x ∈ A, |u x| < D.eta) (hφ : ContDiff ℝ ∞ φ) :
    ∃ (c : SmoothAmbientChart ThreeSphere)
      (X : NativeInteriorSmoothVectorField_v475 E) (χ : ThreeSphere → ℝ),
      ContMDiff (𝓡 3) 𝓘(ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      χ =ᶠ[𝓝ˢ ((fun x => E.toSphere (localCollar D s (jetPoint (x,u x,0)))) '' A)] 1 ∧
      (∀ x ∈ A, E.toSphere (localCollar D s (jetPoint (x,u x,0))) ∈ c.chart.source) ∧
      (∀ x ∈ A, c.chart (E.toSphere (localCollar D s (jetPoint (x,u x,0)))) =
        jetPoint (x,u x,0)) ∧
      (∀ q ∈ c.chart.source,
        chartDifferential c q (X.field q) =
          χ q • (φ (native_collar_base_v475 (c.chart q)) • coordinateVector 3 2)) ∧
      closure {q | X.field q ≠ 0} ⊆ c.chart.source ∧
      (∀ y ∈ c.chart.target, y ∈ collarDomain D W.R ∧ 0 < y 1 ∧
        c.chart.symm y = E.toSphere (localCollar D s y)) := by
  let O : Set E3 := {y | |y 0| < 2 * W.R ∧ y 1 ∈ Ioo (0 : ℝ) D.r0 ∧ |y 2| < D.eta}
  have hO : IsOpen O :=
    (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).continuous.abs continuous_const).inter
      (((isOpen_Ioo.preimage (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).continuous)).inter
        (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.abs continuous_const))
  have hOC : O ⊆ collarDomain D W.R := fun y hy => ⟨hy.1,⟨hy.2.1.1.le,hy.2.1.2.le⟩,hy.2.2⟩
  have hgraph : ∀ x ∈ A, jetPoint (x,u x,0) ∈ O := by
    intro x hx
    have hxhalf := hAhalf hx
    have hb : ‖x‖ < W.R := by simpa only [disc,Metric.mem_ball,dist_zero_right] using hxhalf.1
    have hc : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
    have hx0 : |x 0| < 2 * W.R := by linarith [hc,hb,W.R_pos]
    simpa [O,jetPoint] using And.intro hx0
      (And.intro (actual_halfdisc_radial_membership_v474 D s W x hxhalf) (hheight x hx))
  obtain ⟨c,hcsource,hctarget,hc,hcinv⟩ :=
    actual_interior_collar_ambient_chart_v475 D s W O hO hOC
  let F : E3 → ThreeSphere := E.toSphere ∘ localCollar D s
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hFU : ContMDiffOn 𝓘(ℝ,E3) (𝓡 3) ∞ F O :=
    hinc.contMDiff.comp_contMDiffOn ((actual_localCollar_smooth_v475 D s W.R).mono hOC)
  have hGU : ContDiffOn ℝ ∞ (fun x => jetPoint (x,u x,0)) W.U := by
    unfold jetPoint
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.contDiffOn
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.contDiffOn
    · exact hu
  have hAU : A ⊆ W.U := fun x hx => W.U_contains
    ⟨Metric.ball_subset_closedBall (hAhalf hx).1,(hAhalf hx).2.le⟩
  have hGF : ContinuousOn (fun x => F (jetPoint (x,u x,0))) A :=
    hFU.continuousOn.comp (hGU.continuousOn.mono hAU) hgraph
  have hcompact : IsCompact ((fun x => F (jetPoint (x,u x,0))) '' A) :=
    hA.image_of_continuousOn hGF
  have hsrc : (fun x => F (jetPoint (x,u x,0))) '' A ⊆ c.chart.source := by
    rw [hcsource]
    rintro p ⟨x,hx,rfl⟩
    exact ⟨_,hgraph x hx,rfl⟩
  have hE : c.chart.source ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier := by
    rw [hcsource]
    rintro p ⟨y,hy,rfl⟩
    refine ⟨localCollar D s y,?_,rfl⟩
    rw [← (𝓡∂ 3).compl_boundary]
    intro hbd
    have hh := (D.collar_boundary (localCircle D s (y 0),y 1,y 2)
      ⟨⟨hy.2.1.1.le,hy.2.1.2.le⟩,hy.2.2⟩).mp hbd
    exact hy.2.1.1.ne' hh
  let V : E3 → E3 := fun y => φ (native_collar_base_v475 y) • coordinateVector 3 2
  have hV : ContDiff ℝ ∞ V := (hφ.comp native_collar_base_smooth_v475).smul contDiff_const
  obtain ⟨X,χ,hχ,hχc,hχbounds,hχone,hXsupport,hXcoord⟩ :=
    native_chart_compact_cutoff_field_v475 c c.chart.source _ c.chart.open_source
      (fun _ h => h) hE hcompact hsrc V hV.contDiffOn
  refine ⟨c,X,χ,hχ,hχc,hχone,?_,?_,hXcoord,hXsupport,?_⟩
  · intro x hx
    exact hsrc ⟨x,hx,rfl⟩
  · intro x hx
    exact hc _ (hgraph x hx)
  · intro y hy
    rw [hctarget] at hy
    exact ⟨hOC hy,hy.2.1.1,hcinv y hy⟩

#print axioms native_collar_base_smooth_v475
#print axioms actual_compact_graph_vertical_field_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
