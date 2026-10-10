import SchoenfliesNativeCoimportProbeV754
import ClassificationOfSurfaces.Moise.Brouwer
import Mathlib.Topology.Instances.AddCircle.Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
noncomputable section
namespace CompressionActualPlanarWholeDiskExtensionV756

abbrev Plane := Schoenflies.Plane
abbrev Disk := Metric.closedBall (0 : Plane) 1

/-- An embedded circle gives Schoenflies' literal interval-loop definition. -/
theorem circle_isJordanCurve (r : C(Circle, Plane)) (hr : IsEmbedding r) :
    Schoenflies.IsJordanCurve (Set.range r) := by
  classical
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  let f : ℝ → Plane := fun t => r (e (t : AddCircle (1 : ℝ)))
  have hfcont : Continuous f := r.continuous.comp
    (e.continuous.comp (AddCircle.continuous_mk' 1))
  have hfclose : f 0 = f 1 := by
    change r (e (0 : AddCircle (1 : ℝ))) = r (e ((1 : ℝ) : AddCircle (1 : ℝ)))
    rw [AddCircle.coe_period]
  have hfinj : Set.InjOn f (Set.Ico (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (a := (0 : ℝ)) (p := (1 : ℝ)) (by simpa using hx) (by simpa using hy)).mp
        (e.injective (hr.injective hxy))
  have hfimage : f '' Set.Icc (0 : ℝ) 1 = Set.range r := by
    ext z
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨e (t : AddCircle (1 : ℝ)),rfl⟩
    · rintro ⟨y,rfl⟩
      obtain ⟨t,ht,hte⟩ := AddCircle.eq_coe_Ico (e.symm y)
      refine ⟨t,⟨ht.1,le_of_lt ht.2⟩,?_⟩
      change r (e (t : AddCircle (1 : ℝ))) = r y
      rw [hte,e.apply_symm_apply]
  exact ⟨f,⟨hfcont.continuousOn,hfclose,hfinj⟩,hfimage⟩

/-- The WHOLE image of an embedded closed disk is the closed bounded Jordan side.
    This derives the interior; no unproved planar filling hypothesis is used. -/
theorem embedded_disk_image (f : C(Disk,Plane)) (hf : IsEmbedding f)
    (hC : Schoenflies.IsJordanCurve
      (f '' {x : Disk | (x : Plane) ∈ Metric.sphere 0 1})) :
    f '' {x : Disk | (x : Plane) ∈ Metric.ball 0 1} =
      Schoenflies.inside (f '' {x : Disk | (x : Plane) ∈ Metric.sphere 0 1}) ∧
    Set.range f =
      Schoenflies.inside (f '' {x : Disk | (x : Plane) ∈ Metric.sphere 0 1}) ∪
      (f '' {x : Disk | (x : Plane) ∈ Metric.sphere 0 1}) := by
  classical
  let g : Plane → Plane := Function.extend Subtype.val f (fun _ => f ⟨0,by simp⟩)
  have hgf (x : Disk) : g x = f x := Subtype.val_injective.extend_apply _ _ x
  have hgc : ContinuousOn g Disk := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact f.continuous.congr (fun x => (hgf x).symm)
  have hgi : InjOn g Disk := by
    intro x hx y hy he
    have he' : f ⟨x,hx⟩ = f ⟨y,hy⟩ := by
      rw [← hgf ⟨x,hx⟩,← hgf ⟨y,hy⟩]
      exact he
    exact congrArg Subtype.val (hf.injective he')
  let O : Set Plane := g '' Metric.ball 0 1
  let C : Set Plane := f '' {x : Disk | (x : Plane) ∈ Metric.sphere 0 1}
  let K : Set Plane := Set.range f
  have hOimage : O = f '' {x : Disk | (x : Plane) ∈ Metric.ball 0 1} := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,Metric.ball_subset_closedBall hy⟩,hy,(hgf _).symm⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y,hy,hgf y⟩
  have hKimage : g '' Disk = K := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,(hgf _).symm⟩
    · rintro ⟨y,rfl⟩
      exact ⟨y,y.property,hgf y⟩
  have hOopen : IsOpen O :=
    LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.invariance_of_domain_open_map
      g (Metric.ball 0 1) Metric.isOpen_ball
      (hgc.mono Metric.ball_subset_closedBall) (hgi.mono Metric.ball_subset_closedBall)
  have hOconn : IsPreconnected O := (convex_ball (0 : Plane) 1).isPreconnected.image g
    (hgc.mono Metric.ball_subset_closedBall)
  have hKclosed : IsClosed K := (isCompact_range f.continuous).isClosed
  have hclO : closure O = K := by
    apply Set.Subset.antisymm
    · exact closure_minimal (by rw [hOimage]; exact image_subset_range _ _) hKclosed
    · have hc : closure (Metric.ball (0 : Plane) 1) = Disk := by
        exact closure_ball (0 : Plane) (by norm_num)
      have hh := ContinuousOn.image_closure (hc.symm ▸ hgc)
      rw [hc,hKimage] at hh
      exact hh
  have hKsplit : K = O ∪ C := by
    rw [hOimage]
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      have hle : ‖(x : Plane)‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using x.property
      rcases lt_or_eq_of_le hle with hlt | he
      · exact Or.inl ⟨x,show (x : Plane) ∈ Metric.ball 0 1 from mem_ball_zero_iff.mpr hlt,rfl⟩
      · exact Or.inr ⟨x,show (x : Plane) ∈ Metric.sphere 0 1 from mem_sphere_zero_iff_norm.mpr he,rfl⟩
    · rintro (⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩) <;> exact mem_range_self x
  have hOC : Disjoint O C := by
    rw [Set.disjoint_left,hOimage]
    rintro y ⟨x,hx,rfl⟩ ⟨z,hz,he⟩
    have hzx : z = x := hf.injective he
    have hn : ‖(z : Plane)‖ = ‖(x : Plane)‖ := congrArg (fun w : Disk => ‖(w : Plane)‖) hzx
    have hnx : ‖(x : Plane)‖ < 1 := mem_ball_zero_iff.mp hx
    have hnz : ‖(z : Plane)‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    linarith
  have hfr : frontier O = C := by
    rw [hOopen.frontier_eq,hclO,hKsplit]
    ext x
    have hd : x ∈ C → x ∉ O := fun hxC hxO => Set.disjoint_left.mp hOC hxO hxC
    simp only [mem_sdiff,mem_union]
    tauto
  have hOsub : O ⊆ Cᶜ := fun _ hx hc => Set.disjoint_left.mp hOC hx hc
  have hfrdisj : frontier O ∩ Cᶜ = ∅ := by rw [hfr]; exact Set.inter_compl_self _
  have hzero : g 0 ∈ O := ⟨0,by simp,rfl⟩
  have hcomp := Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint
    hOopen hOconn hOsub hfrdisj hzero
  have hzinside : g 0 ∈ Schoenflies.inside C := by
    refine ⟨hOsub hzero,?_⟩
    rw [hcomp]
    exact (isCompact_range f.continuous).isBounded.subset
      (by
        change O ⊆ K
        rw [← hclO]
        exact subset_closure)
  have hinside : O = Schoenflies.inside C :=
    hcomp.symm.trans ((Schoenflies.jordan_curve_theorem hC).connectedComponentIn_eq_inside hzinside)
  exact ⟨hOimage.symm.trans hinside,hKsplit.trans (by rw [hinside])⟩

end CompressionActualPlanarWholeDiskExtensionV756
