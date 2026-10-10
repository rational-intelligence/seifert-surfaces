import B1HalfDiscNativeTower_v468
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
set_option maxHeartbeats 0

/-- Planar gluing of the actual local smooth representatives; identical local
values are established from continuity and a.e. agreement on open overlaps. -/
theorem planar_glued_smooth_ae_v468 (Ω : Set E2) (u : E2 → ℝ)
    (hloc : ∀ x : Ω, ∃ r : ℝ, 0 < r ∧ Metric.ball (x : E2) r ⊆ Ω ∧
      ∃ f : E2 → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball (x : E2) r) ∧
        u =ᵐ[volume.restrict (Metric.ball (x : E2) r)] f) :
    ∃ f : E2 → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧ u =ᵐ[volume.restrict Ω] f := by
  classical
  choose rad hrad_pos hball_subset frep hfrep_cdiff hfrep_ae using hloc
  set S : Ω → Set E2 := fun x => Metric.ball (x : E2) (rad x) with hS_def
  have hS_open : ∀ x : Ω, IsOpen (S x) := fun x => Metric.isOpen_ball
  have hS_subset : ∀ x : Ω, S x ⊆ Ω := hball_subset
  have hx_mem_S : ∀ x : Ω, (x : E2) ∈ S x := fun x => by
    rw [hS_def]; exact Metric.mem_ball_self (hrad_pos x)
  have hΩ_subset_iUnion : Ω ⊆ ⋃ x : Ω, S x := fun y hy =>
    Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hx_mem_S ⟨y, hy⟩⟩
  have hfrep_cont : ∀ x : Ω, ContinuousOn (frep x) (S x) := fun x =>
    (hfrep_cdiff x).continuousOn
  have h_consistent : ∀ (x y : Ω) (z : E2) (hzx : z ∈ S x) (hzy : z ∈ S y),
      frep x z = frep y z := by
    intro x y z hzx hzy
    set W : Set E2 := S x ∩ S y with hW_def
    have hW_open : IsOpen W := (hS_open x).inter (hS_open y)
    have hW_sub_x : W ⊆ S x := Set.inter_subset_left
    have hW_sub_y : W ⊆ S y := Set.inter_subset_right
    have hae_x : u =ᵐ[volume.restrict W] frep x :=
      ae_restrict_of_ae_restrict_of_subset hW_sub_x (hfrep_ae x)
    have hae_y : u =ᵐ[volume.restrict W] frep y :=
      ae_restrict_of_ae_restrict_of_subset hW_sub_y (hfrep_ae y)
    have hae_xy : frep x =ᵐ[volume.restrict W] frep y := (hae_x.symm).trans hae_y
    have h_eqOn : Set.EqOn (frep x) (frep y) W :=
      MeasureTheory.Measure.eqOn_open_of_ae_eq hae_xy hW_open
        ((hfrep_cont x).mono hW_sub_x) ((hfrep_cont y).mono hW_sub_y)
    exact h_eqOn ⟨hzx, hzy⟩
  set gΩ : ↥Ω → ℝ :=
    Set.iUnionLift S (fun x z => frep x (z : E2))
      (fun x y z hzx hzy => h_consistent x y z hzx hzy) Ω hΩ_subset_iUnion
    with hgΩ_def
  set u_smooth : E2 → ℝ := fun y => if h : y ∈ Ω then gΩ ⟨y, h⟩ else 0
    with hu_smooth_def
  have h_u_smooth_eq : ∀ (x : Ω) (z : E2), z ∈ S x →
      u_smooth z = frep x z := by
    intro x z hz
    have hz_Ω : z ∈ Ω := hS_subset x hz
    have h_lift : gΩ ⟨z, hz_Ω⟩ = frep x (z : E2) :=
      Set.iUnionLift_of_mem (S := S) (T := (Ω : Set E2)) ⟨z, hz_Ω⟩ hz
    rw [hu_smooth_def]
    simp only [hz_Ω, dite_eq_left]
    exact h_lift
  refine ⟨u_smooth, ?_, ?_⟩
  · refine contDiffOn_of_locally_contDiffOn ?_
    intro y hy
    refine ⟨S ⟨y, hy⟩, hS_open ⟨y, hy⟩, hx_mem_S ⟨y, hy⟩, ?_⟩
    refine ((hfrep_cdiff ⟨y, hy⟩).mono (Set.inter_subset_right)).congr ?_
    intro z hz
    exact h_u_smooth_eq ⟨y, hy⟩ z hz.2
  · obtain ⟨T, hT_countable, hT_cover⟩ :=
      TopologicalSpace.isOpen_iUnion_countable S hS_open
    have hΩ_sub_biUnion : Ω ⊆ ⋃ x ∈ T, S x := by
      rw [hT_cover]; exact hΩ_subset_iUnion
    have hae_each : ∀ x ∈ T, u =ᵐ[volume.restrict (S x)] u_smooth := by
      intro x _hxT
      have h1 : u =ᵐ[volume.restrict (S x)] frep x := hfrep_ae x
      refine h1.trans ?_
      refine (ae_restrict_iff' (hS_open x).measurableSet).mpr ?_
      exact Filter.Eventually.of_forall fun z hz => (h_u_smooth_eq x z hz).symm
    have hae_biUnion :
        u =ᵐ[volume.restrict (⋃ x ∈ T, S x)] u_smooth :=
      (MeasureTheory.ae_eq_restrict_biUnion_iff S hT_countable u u_smooth).mpr
        hae_each
    exact hae_biUnion.filter_mono
      (MeasureTheory.ae_mono (Measure.restrict_mono hΩ_sub_biUnion le_rfl))


universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

/-- The actual native weak solution has one smooth representative on the entire
interior, obtained from the fully discharged Sobolev bootstrap. -/
theorem actual_halfdisc_native_smooth_interior_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (R : ℝ) (hRW : R < W.R) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On (halfDisc R) u du)
    (heq : WeakLinearEquationOn (halfDisc R) W.a W.b W.c u du) :
    ∃ f : E2 → ℝ, ContDiffOn ℝ ∞ f (halfDisc R) ∧
      u =ᵐ[volume.restrict (halfDisc R)] f := by
  let U := halfDisc R
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  apply planar_glued_smooth_ae_v468 U u
  intro x
  obtain ⟨rho,hrho,hball⟩ := Metric.isOpen_iff.mp hU x.val x.property
  let r := rho/2
  have hr : 0 < r := half_pos hrho
  have hsub : closure (Metric.ball x.val r) ⊆ U := by
    apply subset_trans (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
    intro y hy
    apply hball
    change dist y x.val < rho
    have hh : dist y x.val ≤ r := hy
    dsimp [r] at hh
    linarith
  have hcompact : IsCompact (closure (Metric.ball x.val r)) :=
    (isCompact_closedBall x.val r).of_isClosed_subset isClosed_closure
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
  obtain ⟨f,hf,hae⟩ := actual_halfdisc_native_smooth_patch_v468 D s W R hRW u du hu heq
    (Metric.ball x.val r) Metric.isOpen_ball hcompact hsub
  exact ⟨r,hr,subset_closure.trans hsub,f,hf,hae⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency
