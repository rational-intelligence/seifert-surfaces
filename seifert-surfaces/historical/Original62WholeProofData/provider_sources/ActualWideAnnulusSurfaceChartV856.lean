import ActualAnnulusEmbeddingOpenMiddleV853

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped Manifold ContDiff
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualPlanarPolarCoordinatesV761
noncomputable section
namespace CompressionActualWideAnnulusSurfaceChartV856

/-- Build an actual open planar chart on the whole widened annulus middle,
    retaining every circle and radial parameter. -/
theorem wide_annulus_surface_chart (S : CompactOrientedSurface.{0})
    (w : C(Circle × Time,S)) (hw : IsEmbedding w) :
    ∃ e : OpenPartialHomeomorph Plane S,
      e.source = {x : Plane | 1 < ‖x‖ ∧ ‖x‖ < 3} ∧
      e.target = w '' {p : Circle × Time | 0 < p.2.val ∧ p.2.val < 1} ∧
      ∀ (z : Circle) (t : Time),0 < t.val → t.val < 1 →
        e ((1+2*t.val) • circleVector z) = w (z,t) := by
  classical
  let U : Set Plane := {x | 1 < ‖x‖ ∧ ‖x‖ < 3}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  let T : Plane → Time := fun x => Set.projIcc 0 1 zero_le_one ((‖x‖-1)/2)
  have hTc : Continuous T := continuous_projIcc.comp ((continuous_norm.sub continuous_const).div_const 2)
  have hTv (x : Plane) (hx : x ∈ U) : (T x).val = (‖x‖-1)/2 :=
    congrArg Subtype.val (Set.projIcc_of_mem zero_le_one (by constructor <;> linarith [hx.1,hx.2]))
  let a : Plane → Circle × Time := fun x => (angle x,T x)
  have ha : ContinuousOn a U := (angle_continuousOn.mono (fun x hx => by
    change x ≠ 0
    intro he
    have hn := hx.1
    rw [he,norm_zero] at hn
    norm_num at hn)).prodMk hTc.continuousOn
  have hrec (x : Plane) (hx : x ∈ U) : (1+2*(T x).val) • circleVector (angle x) = x := by
    rw [hTv x hx,show 1+2*((‖x‖-1)/2) = ‖x‖ by ring]
    exact polar_reconstruction x (norm_ne_zero_iff.mp (by linarith [hx.1]))
  have hai : InjOn a U := by
    intro x hx y hy he
    have h := congrArg (fun p : Circle × Time => (1+2*p.2.val) • circleVector p.1) he
    exact (hrec x hx).symm.trans (h.trans (hrec y hy))
  let f : Plane → S := w ∘ a
  have hf : ContinuousOn f U := w.continuous.comp_continuousOn ha
  have hfi : InjOn f U := fun _ hx _ hy he => hai hx hy (hw.injective he)
  have hfo : IsOpenMap (U.domRestrict f) := by
    intro V hV
    let B : Set Plane := Subtype.val '' V
    have hB : IsOpen B := hU.isOpenMap_subtype_val _ hV
    have hBU : B ⊆ U := by rintro x ⟨p,hp,rfl⟩; exact p.property
    let g : B → S := fun x => f x.val
    have hg : Continuous g := (hf.mono hBU).domRestrict
    have hgi : Function.Injective g := by
      intro x y he
      exact Subtype.ext (hfi (hBU x.property) (hBU y.property) he)
    have hgo : IsOpen (range g) :=
      DifferentialGeometry.Topology.isOpen_range_of_isOpen_of_continuous_injective_real
        (𝓡∂ 2) hB g hg hgi
    have heq : range g = U.domRestrict f '' V := by
      apply Subset.antisymm
      · rintro y ⟨x,rfl⟩
        obtain ⟨p,hp,he⟩ := x.property
        exact ⟨p,hp,congrArg f he⟩
      · rintro y ⟨p,hp,rfl⟩
        exact ⟨⟨p.val,⟨p,hp,rfl⟩⟩,rfl⟩
    exact heq ▸ hgo
  let e : OpenPartialHomeomorph Plane S :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict (hfi.toPartialEquiv f U) hf hfo hU
  have hes : e.source = U := rfl
  have het : e.target = f '' U := rfl
  have hep (x : Plane) : e x = f x := rfl
  have hpoint (z : Circle) (t : Time) (ht : 0 < t.val) (ht1 : t.val < 1) :
      e ((1+2*t.val) • circleVector z) = w (z,t) := by
    let x : Plane := (1+2*t.val) • circleVector z
    have hn : ‖x‖ = 1+2*t.val := by
      dsimp [x]
      rw [norm_smul,circleVector_norm,Real.norm_eq_abs,abs_of_pos (by linarith),mul_one]
    have hx : x ∈ U := by change 1 < ‖x‖ ∧ ‖x‖ < 3; rw [hn]; constructor <;> linarith
    have hangle : angle x = z := (angle_positive_smul _ (by linarith) _
      (norm_ne_zero_iff.mp (by rw [circleVector_norm]; norm_num))).trans (angle_circleVector z)
    have hT : T x = t := Subtype.ext (by rw [hTv x hx,hn]; ring)
    change e x = w (z,t)
    rw [hep]
    change w (angle x,T x) = w (z,t)
    rw [hangle,hT]
  have him : f '' U = w '' {p : Circle × Time | 0 < p.2.val ∧ p.2.val < 1} := by
    apply Subset.antisymm
    · rintro y ⟨x,hx,rfl⟩
      exact ⟨a x,⟨by change 0 < (T x).val; rw [hTv x hx]; linarith [hx.1],
        by change (T x).val < 1; rw [hTv x hx]; linarith [hx.2]⟩,rfl⟩
    · rintro y ⟨⟨z,t⟩,ht,rfl⟩
      refine ⟨(1+2*t.val) • circleVector z,?_,hpoint z t ht.1 ht.2⟩
      rw [mem_setOf_eq,norm_smul,circleVector_norm,Real.norm_eq_abs,
        abs_of_pos (by linarith [ht.1] : 0 < 1+2*t.val),mul_one]
      constructor <;> linarith [ht.1,ht.2]
  exact ⟨e,hes,het.trans him,hpoint⟩

#print axioms wide_annulus_surface_chart
end CompressionActualWideAnnulusSurfaceChartV856
