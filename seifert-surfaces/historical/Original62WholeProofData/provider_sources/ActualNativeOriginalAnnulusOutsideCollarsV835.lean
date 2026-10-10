import ActualNativeOriginalCollarSupportV838
import Schoenflies.ArcComplementPrep
import Schoenflies.PolyLocal
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import Mathlib.Analysis.Convex.Topology
import DifferentialGeometry.Topology.Manifold.ChartSupportedExtension

import Schoenflies.Subarc
import Schoenflies.ModelCurve

open scoped Manifold ContDiff BigOperators
open Set Topology TopologicalSpace
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000

namespace CompressionOriginalAnnulusNativeExteriorV835

private lemma interior_surface_chart (S : CompactOrientedSurface.{0}) (x : S)
    (hx : x ∉ S.boundary) :
    ∃ e : OpenPartialHomeomorph S (Euc 2), x ∈ e.source := by
  let c := extChartAt (𝓡∂ 2) x
  let e : OpenPartialHomeomorph S (Euc 2) := {
    toFun := c
    invFun := c.symm
    source := c.source ∩ c ⁻¹' interior c.target
    target := interior c.target
    map_source' := fun _ hy => hy.2
    map_target' := fun y hy => ⟨c.map_target (interior_subset hy),by
      change c (c.symm y) ∈ interior c.target
      rw [c.right_inv (interior_subset hy)]
      exact hy⟩
    left_inv' := fun _ hy => c.left_inv hy.1
    right_inv' := fun _ hy => c.right_inv (interior_subset hy)
    continuousOn_toFun := (continuousOn_extChartAt x).mono inter_subset_left
    continuousOn_invFun := (continuousOn_extChartAt_symm x).mono interior_subset
    open_source := isOpen_extChartAt_preimage' x isOpen_interior
    open_target := isOpen_interior }
  refine ⟨e,mem_extChartAt_source x,?_⟩
  exact (𝓡∂ 2).isInteriorPoint_iff.mp
    (((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint x).mpr hx)

variable {S : CompactOrientedSurface.{0}} {M : Type}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  {f : NeatEmbedding S M} {D : InteriorCompressingDisk f} (A : CompressionAnnulus D)

private def inwardTime (k : Fin 2) (t : Time) : Time :=
  if k = 0 then t else unitInterval.symm t

private lemma inwardTime_continuous (k : Fin 2) : Continuous (inwardTime k) := by
  change Continuous (fun t : Time => if k = 0 then t else unitInterval.symm t)
  split_ifs
  · fun_prop
  · exact unitInterval.continuous_symm

private lemma inwardTime_injective (k : Fin 2) : Function.Injective (inwardTime k) := by
  intro t s hts
  change (if k = 0 then t else unitInterval.symm t) =
    (if k = 0 then s else unitInterval.symm s) at hts
  by_cases hk : k = 0
  · simpa only [if_pos hk] using hts
  · exact unitInterval.symm_bijective.injective (by simpa only [if_neg hk] using hts)

private lemma inwardTime_zero (k : Fin 2) : inwardTime k 0 = CompressionAnnulus.sideTime k := by
  by_cases hk : k = 0 <;> simp [inwardTime,CompressionAnnulus.sideTime,hk]

private lemma band_mem_removed (p : Circle × Time) :
    A.band p ∈ A.removed ↔ 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1 := by
  constructor
  · rintro ⟨q,hq,hqp⟩
    exact (A.embedded.injective hqp) ▸ hq
  · intro hp
    exact ⟨p,hp,rfl⟩

private lemma halfrectangle_mem_removed (k : Fin 2) (w : Circle)
    (ε : Time) (hε : 0 < (ε : ℝ)) (t : Time) (ht : (t : ℝ) < 1) :
    A.band (w,inwardTime k (ε*t)) ∈ A.removed ↔ 0 < (t : ℝ) := by
  rw [band_mem_removed A]
  have hprod : (ε : ℝ)*(t : ℝ) < 1 := by
    calc
      (ε : ℝ)*(t : ℝ) ≤ 1*(t : ℝ) := mul_le_mul_of_nonneg_right ε.property.2 t.property.1
      _ = (t : ℝ) := one_mul _
      _ < 1 := ht
  have hprod0 : 0 ≤ (ε : ℝ)*(t : ℝ) := mul_nonneg ε.property.1 t.property.1
  by_cases hk : k = 0
  · simp only [inwardTime,if_pos hk]
    change 0 < (ε : ℝ)*(t : ℝ) ∧ (ε : ℝ)*(t : ℝ) < 1 ↔ 0 < (t : ℝ)
    constructor
    · intro h
      exact (mul_pos_iff_of_pos_left hε).mp h.1
    · intro h
      exact ⟨mul_pos hε h,hprod⟩
  · simp only [inwardTime,if_neg hk]
    change 0 < 1-(ε : ℝ)*(t : ℝ) ∧ 1-(ε : ℝ)*(t : ℝ) < 1 ↔ 0 < (t : ℝ)
    constructor
    · intro h
      apply (mul_pos_iff_of_pos_left hε).mp
      linarith [h.2]
    · intro h
      constructor <;> nlinarith [mul_pos hε h]

private def inwardTimeHomeomorph (k : Fin 2) : Time ≃ₜ Time where
  toFun := inwardTime k
  invFun := inwardTime k
  left_inv := by
    intro t
    by_cases hk : k = 0 <;> simp [inwardTime,hk]
  right_inv := by
    intro t
    by_cases hk : k = 0 <;> simp [inwardTime,hk]
  continuous_toFun := inwardTime_continuous k
  continuous_invFun := inwardTime_continuous k

private lemma band_localization
    (K U : Set (Circle × Time)) (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (e : OpenPartialHomeomorph S Schoenflies.Plane)
    (hKe : A.band '' K ⊆ e.source) :
    ∃ V : Set S, IsOpen V ∧ A.band '' K ⊆ V ∧ closure V ⊆ e.source ∧
      ∀ x ∈ closure V, x ∈ Set.range A.band → x ∈ A.band '' U := by
  have hremote : IsClosed (A.band '' Uᶜ) :=
    (hU.isClosed_compl.isCompact.image A.band.continuous).isClosed
  have hlocal : A.band '' K ⊆ e.source ∩ (A.band '' Uᶜ)ᶜ := by
    rintro x ⟨p,hp,rfl⟩
    refine ⟨hKe ⟨p,hp,rfl⟩,?_⟩
    rintro ⟨q,hq,hqp⟩
    exact hq ((A.embedded.injective hqp) ▸ hKU hp)
  obtain ⟨V,hV,hKV,hVO⟩ := normal_exists_closure_subset
    (hK.image A.band.continuous).isClosed
    (e.open_source.inter hremote.isOpen_compl) hlocal
  refine ⟨V,hV,hKV,hVO.trans inter_subset_left,?_⟩
  intro x hx hxband
  obtain ⟨p,rfl⟩ := hxband
  refine ⟨p,?_,rfl⟩
  by_contra hp
  exact (hVO hx).2 ⟨p,hp,rfl⟩

private def squareToTime (x : ↥(Schoenflies.Plane.closedSquare 0 1)) : Time × Time :=
  (⟨((x : Schoenflies.Plane) 0 + 1)/2,by
      have hx := (Schoenflies.mem_closedSquare_zero_one.mp x.property)
      change max |(x : Schoenflies.Plane) 0| |(x : Schoenflies.Plane) 1| ≤ 1 at hx
      have h := abs_le.mp ((le_max_left _ _).trans hx)
      constructor <;> linarith⟩,
    ⟨((x : Schoenflies.Plane) 1 + 1)/2,by
      have hx := (Schoenflies.mem_closedSquare_zero_one.mp x.property)
      change max |(x : Schoenflies.Plane) 0| |(x : Schoenflies.Plane) 1| ≤ 1 at hx
      have h := abs_le.mp ((le_max_right _ _).trans hx)
      constructor <;> linarith⟩)

private def timeToSquare (p : Time × Time) : ↥(Schoenflies.Plane.closedSquare 0 1) :=
  ⟨Schoenflies.Plane.mk (2*(p.1 : ℝ)-1) (2*(p.2 : ℝ)-1),by
    rw [Schoenflies.mem_closedSquare_zero_one]
    change max |2*(p.1 : ℝ)-1| |2*(p.2 : ℝ)-1| ≤ 1
    apply max_le <;> apply abs_le.mpr
    · constructor <;> linarith [p.1.property.1,p.1.property.2]
    · constructor <;> linarith [p.2.property.1,p.2.property.2]⟩

private def squareTimeHomeomorph : ↥(Schoenflies.Plane.closedSquare 0 1) ≃ₜ Time × Time where
  toFun := squareToTime
  invFun := timeToSquare
  left_inv := by
    intro x
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [timeToSquare,squareToTime,Schoenflies.Plane.mk] <;> ring
  right_inv := by
    intro p
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [timeToSquare,squareToTime,Schoenflies.Plane.mk] <;> ring
  continuous_toFun := by
    apply Continuous.prodMk <;> apply Continuous.subtype_mk <;> fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous (fun p : Time × Time =>
      Schoenflies.Plane.mk (2*(p.1 : ℝ)-1) (2*(p.2 : ℝ)-1))
    unfold Schoenflies.Plane.mk
    fun_prop

private lemma halfrectangle_parameter_window (k : Fin 2)
    (a b : ℝ) (hab : a < b) (ε : Time) (hε : 0 < (ε : ℝ))
    (s : Time) (hs0 : 0 < (s : ℝ)) (hs1 : (s : ℝ) < 1) :
    ∃ U : Set (Circle × Time), IsOpen U ∧
      (Circle.exp (a+(b-a)*(s : ℝ)),CompressionAnnulus.sideTime k) ∈ U ∧
      ∀ p ∈ U, ∃ q : Time × Time,
        0 < (q.1 : ℝ) ∧ (q.1 : ℝ) < 1 ∧ (q.2 : ℝ) < 1 ∧
        p = (Circle.exp (a+(b-a)*(q.1 : ℝ)),inwardTime k (ε*q.2)) := by
  let T : Set Time := {t : Time | (t : ℝ) < (ε : ℝ)}
  let U : Set (Circle × Time) :=
    (Circle.exp '' Ioo a b) ×ˢ ((inwardTimeHomeomorph k) '' T)
  have hT : IsOpen T := isOpen_lt continuous_subtype_val continuous_const
  have hU : IsOpen U :=
    (Circle.isCoveringMap_exp.isLocalHomeomorph.isOpenMap _ isOpen_Ioo).prod
      ((inwardTimeHomeomorph k).isOpenMap _ hT)
  have hangle : a+(b-a)*(s : ℝ) ∈ Ioo a b := by
    constructor <;> nlinarith
  refine ⟨U,hU,⟨⟨_,hangle,rfl⟩,⟨0,hε,?_⟩⟩,?_⟩
  · exact inwardTime_zero k
  · rintro ⟨w,t⟩ ⟨⟨θ,hθ,hθw⟩,⟨τ,hτ,hτt⟩⟩
    change (τ : ℝ) < (ε : ℝ) at hτ
    let r : Time := ⟨(θ-a)/(b-a),div_nonneg (sub_pos.mpr hθ.1).le
      (sub_pos.mpr hab).le,(div_le_iff₀ (sub_pos.mpr hab)).mpr (by linarith [hθ.2])⟩
    let u : Time := ⟨(τ : ℝ)/(ε : ℝ),div_nonneg τ.property.1 hε.le,
      (div_le_iff₀ hε).mpr (by simpa only [one_mul] using hτ.le)⟩
    have hrangle : a+(b-a)*(r : ℝ) = θ := by
      dsimp [r]
      field_simp [ne_of_gt (sub_pos.mpr hab)]
      ring
    have hεu : ε*u = τ := by
      apply Subtype.ext
      change (ε : ℝ)*((τ : ℝ)/(ε : ℝ)) = (τ : ℝ)
      field_simp
    refine ⟨(r,u),div_pos (sub_pos.mpr hθ.1) (sub_pos.mpr hab),
      (div_lt_iff₀ (sub_pos.mpr hab)).mpr (by linarith [hθ.2]),
      (div_lt_iff₀ hε).mpr (by simpa only [one_mul] using hτ),?_⟩
    apply Prod.ext
    · rw [hrangle]
      exact hθw.symm
    · rw [hεu]
      exact hτt.symm

private lemma planar_edge_arc (k : Fin 2) (z : Circle) :
    ∃ e : OpenPartialHomeomorph S Schoenflies.Plane,
      (A.edgePoint k z : S) ∈ e.source ∧
      ∃ a b : ℝ, a < Complex.arg z ∧ Complex.arg z < b ∧ b-a < 2*Real.pi ∧
        (∀ t ∈ Icc a b, (A.edgePoint k (Circle.exp t) : S) ∈ e.source) ∧
        ContinuousOn (fun t => e (A.edgePoint k (Circle.exp t) : S)) (Icc a b) ∧
        InjOn (fun t => e (A.edgePoint k (Circle.exp t) : S)) (Icc a b) := by
  obtain ⟨e,he⟩ := interior_surface_chart S (A.edgePoint k z : S)
    (CompressionActualNativeOriginalCollarSupportV838.edgePoint_boundary_compl A k z)
  let γ : ℝ → S := fun t => (A.edgePoint k (Circle.exp t) : S)
  have hγ : Continuous γ := continuous_subtype_val.comp
    ((CompressionActualNativeOriginalCollarSupportV838.edgePoint_continuous A k).comp Circle.exp.continuous)
  let θ : ℝ := Complex.arg z
  have hθ : γ θ = (A.edgePoint k z : S) := by
    change (A.edgePoint k (Circle.exp (Complex.arg z)) : S) = _
    rw [Circle.exp_arg]
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp
    ((e.open_source.preimage hγ).mem_nhds (hθ ▸ he))
  let δ : ℝ := min r Real.pi / 2
  have hδ : 0 < δ := half_pos (lt_min hr Real.pi_pos)
  have hδr : δ < r := lt_of_lt_of_le (half_lt_self (lt_min hr Real.pi_pos))
    (min_le_left r Real.pi)
  have hδπ : δ ≤ Real.pi / 2 := div_le_div_of_nonneg_right
    (min_le_right r Real.pi) (by norm_num)
  have hlocal : ∀ t ∈ Icc (θ-δ) (θ+δ), γ t ∈ e.source := by
    intro t ht
    apply hrs
    rw [Metric.mem_ball,Real.dist_eq]
    exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩) hδr
  have hwidth : (θ+δ) - (θ-δ) < 2*Real.pi := by linarith [Real.pi_pos]
  refine ⟨e,he,θ-δ,θ+δ,by dsimp [θ]; linarith,by dsimp [θ]; linarith,
    hwidth,hlocal,e.continuousOn.comp hγ.continuousOn hlocal,?_⟩
  intro t ht s hs hts
  have heq := e.injOn (hlocal t ht) (hlocal s hs) hts
  have hcircle : Circle.exp t = Circle.exp s := by
    have hband := A.embedded.injective heq
    exact congrArg Prod.fst hband
  exact Circle.exp_injOn_Icc hwidth ht hs hcircle

private lemma planar_edge_rectangle (k : Fin 2) (z : Circle) :
    ∃ e : OpenPartialHomeomorph S Schoenflies.Plane,
      (A.edgePoint k z : S) ∈ e.source ∧
      ∃ a b : ℝ, a < Complex.arg z ∧ Complex.arg z < b ∧ b-a < 2*Real.pi ∧
        ∃ ε : Time, 0 < (ε : ℝ) ∧ ∃ q : C(Time × Time,Schoenflies.Plane),
          IsEmbedding q ∧
          (∀ p : Time × Time,
            A.band (Circle.exp (a+(b-a)*(p.1 : ℝ)), inwardTime k (ε*p.2)) ∈ e.source) ∧
          (∀ p : Time × Time,
            q p = e (A.band (Circle.exp (a+(b-a)*(p.1 : ℝ)), inwardTime k (ε*p.2)))) ∧
          (∀ s : Time, q (s,0) = e (A.edgePoint k
            (Circle.exp (a+(b-a)*(s : ℝ))) : S)) ∧
          ∃ s : Time, q (s,0) = e (A.edgePoint k z : S) := by
  obtain ⟨e,he,a,b,ha,hb,hwidth,hlocal,_,_⟩ := planar_edge_arc A k z
  have hab : a < b := ha.trans hb
  let G : ℝ × Time → S := fun p => A.band (Circle.exp p.1,inwardTime k p.2)
  have hG : Continuous G := A.band.continuous.comp
    ((Circle.exp.continuous.comp continuous_fst).prodMk
      ((inwardTime_continuous k).comp continuous_snd))
  have hpre : IsOpen (G ⁻¹' e.source) := e.open_source.preimage hG
  have hbase : Icc a b ×ˢ ({0} : Set Time) ⊆ G ⁻¹' e.source := by
    rintro ⟨t,u⟩ ⟨ht,hu⟩
    have hu0 : u = 0 := hu
    simpa [G,hu0,inwardTime_zero,CompressionAnnulus.edgePoint] using hlocal t ht
  obtain ⟨V,W,_,hW,hV,h0W,hVW⟩ := generalized_tube_lemma isCompact_Icc
    isCompact_singleton hpre hbase
  have h01 : (0 : Time) < 1 := by change (0 : ℝ) < 1; exact zero_lt_one
  obtain ⟨c,hc,hcW⟩ := exists_Ico_subset_of_mem_nhds
    (hW.mem_nhds (h0W (by simp))) ⟨1,h01⟩
  have hcpos : (0 : ℝ) < c := hc
  let ε : Time := ⟨(c : ℝ)/2,(half_pos hcpos).le,by linarith [c.property.2]⟩
  have hε : 0 < (ε : ℝ) := half_pos hcpos
  let R : Time × Time → ℝ × Time := fun p => (a+(b-a)*(p.1 : ℝ),ε*p.2)
  have hangle (s : Time) : a+(b-a)*(s : ℝ) ∈ Icc a b := by
    constructor <;> nlinarith [s.property.1,s.property.2]
  have hRs (p : Time × Time) : G (R p) ∈ e.source := by
    apply hVW
    refine ⟨hV (hangle p.1),hcW ⟨?_,?_⟩⟩
    · exact (ε*p.2).property.1
    · change (ε : ℝ) * (p.2 : ℝ) < c
      have hεc : (ε : ℝ) < c := half_lt_self hcpos
      exact lt_of_le_of_lt ((mul_le_mul_of_nonneg_left p.2.property.2 hε.le).trans_eq
        (mul_one (ε : ℝ))) hεc
  have hR : Continuous R := by
    apply Continuous.prodMk
    · exact continuous_const.add (continuous_const.mul
        (continuous_subtype_val.comp continuous_fst))
    · apply Continuous.subtype_mk
      exact continuous_const.mul (continuous_subtype_val.comp continuous_snd)
  let q : C(Time × Time,Schoenflies.Plane) :=
    ⟨e ∘ G ∘ R, e.continuousOn.comp_continuous
      (hG.comp hR) hRs⟩
  have hqinj : Function.Injective q := by
    intro p r hpr
    have hGr := e.injOn (hRs p) (hRs r) hpr
    have hband := A.embedded.injective hGr
    have hcircle := congrArg Prod.fst hband
    have htime := congrArg Prod.snd hband
    have hang := Circle.exp_injOn_Icc hwidth (hangle p.1) (hangle r.1) hcircle
    have hfirst : p.1 = r.1 := Subtype.ext (by nlinarith)
    have hsecond := (inwardTime_injective k) htime
    have hprod : (ε : ℝ) * (p.2 : ℝ) = (ε : ℝ) * (r.2 : ℝ) :=
      congrArg (fun t : Time => (t : ℝ)) hsecond
    exact Prod.ext hfirst (Subtype.ext (mul_left_cancel₀ hε.ne' hprod))
  have hqzero (s : Time) : q (s,0) = e (A.edgePoint k
      (Circle.exp (a+(b-a)*(s : ℝ))) : S) := by
    change e (A.band (Circle.exp (a+(b-a)*(s : ℝ)), inwardTime k (ε*0))) = _
    simp [inwardTime_zero,CompressionAnnulus.edgePoint]
  refine ⟨e,he,a,b,ha,hb,hwidth,ε,hε,q,
    (q.continuous.isClosedEmbedding hqinj).isEmbedding,hRs,fun _ => rfl,hqzero,?_⟩
  let s : Time := ⟨(Complex.arg z-a)/(b-a),div_nonneg (sub_pos.mpr ha).le
    (sub_pos.mpr hab).le,(div_le_iff₀ (sub_pos.mpr hab)).mpr (by linarith)⟩
  refine ⟨s,?_⟩
  rw [hqzero]
  have hs : a+(b-a)*(s : ℝ) = Complex.arg z := by
    dsimp [s]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  rw [hs,Circle.exp_arg]

private lemma planar_edge_square (k : Fin 2) (z : Circle) :
    ∃ e : OpenPartialHomeomorph S Schoenflies.Plane,
      (A.edgePoint k z : S) ∈ e.source ∧
      ∃ a b : ℝ, a < Complex.arg z ∧ Complex.arg z < b ∧ b-a < 2*Real.pi ∧
        ∃ ε : Time, 0 < (ε : ℝ) ∧
          ∃ j : C(↥(Schoenflies.Plane.closedSquare 0 1),Schoenflies.Plane),
            IsEmbedding j ∧
            (∀ p : Time × Time,
              A.band (Circle.exp (a+(b-a)*(p.1 : ℝ)), inwardTime k (ε*p.2)) ∈ e.source) ∧
            (∀ p : Time × Time,
              j (timeToSquare p) =
                e (A.band (Circle.exp (a+(b-a)*(p.1 : ℝ)), inwardTime k (ε*p.2)))) ∧
            (∀ s : Time, j (timeToSquare (s,0)) =
              e (A.edgePoint k (Circle.exp (a+(b-a)*(s : ℝ))) : S)) ∧
            ∃ s : Time, 0 < (s : ℝ) ∧ (s : ℝ) < 1 ∧
              j (timeToSquare (s,0)) = e (A.edgePoint k z : S) := by
  obtain ⟨e,he,a,b,ha,hb,hwidth,ε,hε,q,hq,hchart,hqval,hqzero,_⟩ :=
    planar_edge_rectangle A k z
  let j : C(↥(Schoenflies.Plane.closedSquare 0 1),Schoenflies.Plane) :=
    q.comp ⟨squareTimeHomeomorph,squareTimeHomeomorph.continuous⟩
  have hjval (p : Time × Time) : j (timeToSquare p) = q p := by
    change q (squareTimeHomeomorph (squareTimeHomeomorph.symm p)) = q p
    rw [squareTimeHomeomorph.apply_symm_apply]
  refine ⟨e,he,a,b,ha,hb,hwidth,ε,hε,j,hq.comp squareTimeHomeomorph.isEmbedding,
    hchart,fun p => (hjval p).trans (hqval p),
    fun s => (hjval (s,0)).trans (hqzero s),?_⟩
  have hab : a < b := ha.trans hb
  let s : Time := ⟨(Complex.arg z-a)/(b-a),div_nonneg (sub_pos.mpr ha).le
    (sub_pos.mpr hab).le,(div_le_iff₀ (sub_pos.mpr hab)).mpr (by linarith)⟩
  refine ⟨s,div_pos (sub_pos.mpr ha) (sub_pos.mpr hab),
    (div_lt_iff₀ (sub_pos.mpr hab)).mpr (by linarith),?_⟩
  rw [hjval,hqzero]
  have hs : a+(b-a)*(s : ℝ) = Complex.arg z := by
    dsimp [s]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  rw [hs,Circle.exp_arg]

private lemma local_square_buffer (k : Fin 2) (z : Circle)
    (e : OpenPartialHomeomorph S Schoenflies.Plane)
    (he : (A.edgePoint k z : S) ∈ e.source)
    (a b : ℝ) (hab : a < b) (ε : Time) (hε : 0 < (ε : ℝ))
    (j : C(↥(Schoenflies.Plane.closedSquare 0 1),Schoenflies.Plane))
    (hchart : ∀ p : Time × Time,
      A.band (Circle.exp (a+(b-a)*(p.1 : ℝ)),inwardTime k (ε*p.2)) ∈ e.source)
    (hjval : ∀ p : Time × Time, j (timeToSquare p) =
      e (A.band (Circle.exp (a+(b-a)*(p.1 : ℝ)),inwardTime k (ε*p.2))))
    (s : Time) (hs0 : 0 < (s : ℝ)) (hs1 : (s : ℝ) < 1)
    (hsz : Circle.exp (a+(b-a)*(s : ℝ)) = z) :
    ∃ V : Set S, IsOpen V ∧ (A.edgePoint k z : S) ∈ V ∧
      closure V ⊆ e.source ∧
      (∀ x ∈ closure V, x ∈ Set.range A.band ↔ e x ∈ Set.range j) ∧
      ∀ x ∈ closure V, x ∈ Set.range A.band → ∃ q : Time × Time,
        (q.2 : ℝ) < 1 ∧
        A.band (Circle.exp (a+(b-a)*(q.1 : ℝ)),inwardTime k (ε*q.2)) = x := by
  obtain ⟨U,hU,hcenter,hparam⟩ := halfrectangle_parameter_window k a b hab ε hε s hs0 hs1
  rw [hsz] at hcenter
  let p₀ : Circle × Time := (z,CompressionAnnulus.sideTime k)
  obtain ⟨V,hV,hpoint,hVe,hlocal⟩ := band_localization A ({p₀} : Set (Circle × Time)) U
    isCompact_singleton hU (by simpa [p₀] using hcenter)
    e (by simpa [p₀,CompressionAnnulus.edgePoint] using he)
  refine ⟨V,hV,by simpa [p₀,CompressionAnnulus.edgePoint] using hpoint,hVe,?_,?_⟩
  · intro x hx
    constructor
    · intro hxband
      obtain ⟨p,hp,hpx⟩ := hlocal x hx hxband
      obtain ⟨q,_,_,_,hpq⟩ := hparam p hp
      refine ⟨timeToSquare q,?_⟩
      rw [hjval,← hpq,hpx]
    · rintro ⟨y,hy⟩
      let q : Time × Time := squareTimeHomeomorph y
      have hqy : timeToSquare q = y := squareTimeHomeomorph.symm_apply_apply y
      have hjq : j (timeToSquare q) = e x := by rw [hqy]; exact hy
      have hbx : A.band (Circle.exp (a+(b-a)*(q.1 : ℝ)),inwardTime k (ε*q.2)) = x :=
        e.injOn (hchart q) (hVe hx) ((hjval q).symm.trans hjq)
      exact ⟨_,hbx⟩
  · intro x hx hxband
    obtain ⟨p,hp,hpx⟩ := hlocal x hx hxband
    obtain ⟨q,_,_,hq2,hpq⟩ := hparam p hp
    exact ⟨q,hq2,by rw [← hpq,hpx]⟩

private lemma timeToSquare_bottom_mem_modelCurve (s : Time) :
    (timeToSquare (s,0) : Schoenflies.Plane) ∈ Schoenflies.modelCurve := by
  change max |2*(s : ℝ)-1| |2*(0 : ℝ)-1| = 1
  have hs : |2*(s : ℝ)-1| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [s.property.1,s.property.2]
  norm_num
  exact hs

private lemma square_extension_chart (k : Fin 2) (z : Circle)
    (e : OpenPartialHomeomorph S Schoenflies.Plane)
    (j : C(↥(Schoenflies.Plane.closedSquare 0 1),Schoenflies.Plane))
    (F : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    (hboundary : ∀ x : ↥Schoenflies.modelCurve,
      F (x : Schoenflies.Plane) = j ⟨x,Schoenflies.modelCurve_subset_closedSquare x.property⟩)
    (himage : F '' Schoenflies.Plane.closedSquare 0 1 = Set.range j)
    (V : Set S) (hV : IsOpen V) (hpoint : (A.edgePoint k z : S) ∈ V)
    (hVe : closure V ⊆ e.source)
    (hlocal : ∀ x ∈ closure V, x ∈ Set.range A.band ↔ e x ∈ Set.range j)
    (s : Time) (hcenter : j (timeToSquare (s,0)) = e (A.edgePoint k z : S)) :
    ∃ c : OpenPartialHomeomorph S Schoenflies.Plane,
      (A.edgePoint k z : S) ∈ c.source ∧
      c (A.edgePoint k z : S) = (timeToSquare (s,0) : Schoenflies.Plane) ∧
      c.source ⊆ V ∧
      (∀ x : S, c x = F.symm (e x)) ∧
      ∀ x ∈ c.source, x ∈ Set.range A.band ↔ c x ∈ Schoenflies.Plane.closedSquare 0 1 := by
  let c := (e.transHomeomorph F.symm).restrOpen V hV
  have hcsource : c.source = e.source ∩ V := rfl
  have hcval (x : S) : c x = F.symm (e x) := rfl
  have hFbottom : F (timeToSquare (s,0) : Schoenflies.Plane) = j (timeToSquare (s,0)) :=
    hboundary ⟨_,timeToSquare_bottom_mem_modelCurve s⟩
  refine ⟨c,⟨hVe (subset_closure hpoint),hpoint⟩,?_,inter_subset_right,hcval,?_⟩
  · rw [hcval,← hcenter,← hFbottom,F.symm_apply_apply]
  · intro x hx
    rw [hlocal x (subset_closure hx.2),← himage,hcval]
    constructor
    · rintro ⟨y,hy,hyx⟩
      rw [← hyx,F.symm_apply_apply]
      exact hy
    · intro hxQ
      exact ⟨F.symm (e x),hxQ,F.apply_symm_apply (e x)⟩

private lemma square_chart_outside_halfplane (k : Fin 2) (z : Circle)
    (c : OpenPartialHomeomorph S Schoenflies.Plane)
    (hpoint : (A.edgePoint k z : S) ∈ c.source)
    (s : Time) (hs0 : 0 < (s : ℝ)) (hs1 : (s : ℝ) < 1)
    (hcenter : c (A.edgePoint k z : S) = (timeToSquare (s,0) : Schoenflies.Plane))
    (hband : ∀ x ∈ c.source,
      x ∈ Set.range A.band ↔ c x ∈ Schoenflies.Plane.closedSquare 0 1) :
    ∃ d : OpenPartialHomeomorph S Schoenflies.Plane,
      (A.edgePoint k z : S) ∈ d.source ∧
      d (A.edgePoint k z : S) = (timeToSquare (s,0) : Schoenflies.Plane) ∧
      d.source ⊆ c.source ∧
      (∀ x ∈ d.source, d x = c x) ∧
      (∀ x ∈ d.source, |d x 0| < 1 ∧ d x 1 < 0) ∧
      ∀ x ∈ d.source, x ∈ Set.range A.band ↔ -1 ≤ d x 1 := by
  let W : Set Schoenflies.Plane := {y | |y 0| < 1 ∧ y 1 < 0}
  have hW : IsOpen W := by
    change IsOpen ({y : Schoenflies.Plane | |y 0| < 1} ∩ {y : Schoenflies.Plane | y 1 < 0})
    apply IsOpen.inter <;> apply isOpen_lt <;> fun_prop
  have hcenterW : c (A.edgePoint k z : S) ∈ W := by
    rw [hcenter]
    change |2*(s : ℝ)-1| < 1 ∧ 2*(0 : ℝ)-1 < 0
    refine ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,by norm_num⟩
  let d := c.restrOpen (c.source ∩ c ⁻¹' W) (c.isOpen_inter_preimage hW)
  refine ⟨d,⟨hpoint,hpoint,hcenterW⟩,hcenter,inter_subset_left,fun _ _ => rfl,
    fun _ hx => hx.2.2,?_⟩
  intro x hx
  have hxW : |c x 0| < 1 ∧ c x 1 < 0 := hx.2.2
  rw [hband x hx.1,Schoenflies.mem_closedSquare_zero_one]
  change max |c x 0| |c x 1| ≤ 1 ↔ -1 ≤ c x 1
  constructor
  · intro hxQ
    exact (abs_le.mp ((le_max_right _ _).trans hxQ)).1
  · intro hxnormal
    exact max_le hxW.1.le (abs_le.mpr ⟨hxnormal,by linarith [hxW.2]⟩)

private lemma square_chart_removed_halfplane (k : Fin 2)
    (e c : OpenPartialHomeomorph S Schoenflies.Plane)
    (a b : ℝ) (ε : Time) (hε : 0 < (ε : ℝ))
    (j : C(↥(Schoenflies.Plane.closedSquare 0 1),Schoenflies.Plane))
    (F : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    (hFbottom : ∀ s : Time, F (timeToSquare (s,0) : Schoenflies.Plane) = j (timeToSquare (s,0)))
    (hjval : ∀ p : Time × Time, j (timeToSquare p) =
      e (A.band (Circle.exp (a+(b-a)*(p.1 : ℝ)),inwardTime k (ε*p.2))))
    (hchart : ∀ p : Time × Time,
      A.band (Circle.exp (a+(b-a)*(p.1 : ℝ)),inwardTime k (ε*p.2)) ∈ e.source)
    (hce : c.source ⊆ e.source)
    (hcval : ∀ x ∈ c.source, c x = F.symm (e x))
    (hcoords : ∀ x ∈ c.source, |c x 0| < 1 ∧ c x 1 < 0)
    (hband : ∀ x ∈ c.source, x ∈ Set.range A.band ↔ -1 ≤ c x 1)
    (hparam : ∀ x ∈ c.source, x ∈ Set.range A.band → ∃ q : Time × Time,
      (q.2 : ℝ) < 1 ∧
      A.band (Circle.exp (a+(b-a)*(q.1 : ℝ)),inwardTime k (ε*q.2)) = x) :
    ∀ x ∈ c.source, x ∈ A.removed ↔ -1 < c x 1 := by
  intro x hx
  have hbottom (r : Time) :
      e (A.band (Circle.exp (a+(b-a)*(r : ℝ)),inwardTime k (ε*0))) =
        F (timeToSquare (r,0) : Schoenflies.Plane) :=
    (hjval (r,0)).symm.trans (hFbottom r).symm
  have hcx : F (c x) = e x := by rw [hcval x hx,F.apply_symm_apply]
  have haxis_iff (q : Time × Time)
      (hqx : A.band (Circle.exp (a+(b-a)*(q.1 : ℝ)),inwardTime k (ε*q.2)) = x) :
      c x 1 = -1 ↔ (q.2 : ℝ) = 0 := by
    constructor
    · intro hnormal
      let r : Time := ⟨(c x 0+1)/2,by
        have hc0 := abs_lt.mp (hcoords x hx).1
        constructor <;> linarith [hc0.1,hc0.2]⟩
      have hr : (timeToSquare (r,0) : Schoenflies.Plane) = c x := by
        ext i
        fin_cases i
        · change 2*((c x 0+1)/2)-1 = c x 0
          ring
        · change 2*(0 : ℝ)-1 = c x 1
          linarith
      have heq : A.band (Circle.exp (a+(b-a)*(r : ℝ)),inwardTime k (ε*0)) = x :=
        e.injOn (hchart (r,0)) (hce hx) ((hbottom r).trans (by rw [hr,hcx]))
      have htime := congrArg Prod.snd (A.embedded.injective (hqx.trans heq.symm))
      have hprod := congrArg (fun t : Time => (t : ℝ)) ((inwardTime_injective k) htime)
      change (ε : ℝ)*(q.2 : ℝ) = (ε : ℝ)*0 at hprod
      exact mul_left_cancel₀ hε.ne' hprod
    · intro hzero
      have hq0 : q.2 = 0 := Subtype.ext hzero
      have hfx : F (timeToSquare (q.1,0) : Schoenflies.Plane) = F (c x) := by
        rw [hcx,← hbottom q.1,← hqx,hq0]
      have hcoord := congrArg (fun y : Schoenflies.Plane => y 1) (F.injective hfx)
      change 2*(0 : ℝ)-1 = c x 1 at hcoord
      linarith
  constructor
  · intro hxremoved
    have hxband : x ∈ Set.range A.band := by
      obtain ⟨p,_,hpx⟩ := hxremoved
      exact ⟨p,hpx⟩
    obtain ⟨q,hq2,hqx⟩ := hparam x hx hxband
    have hqpos : 0 < (q.2 : ℝ) :=
      (halfrectangle_mem_removed A k _ ε hε q.2 hq2).mp (hqx ▸ hxremoved)
    have hnormal := (hband x hx).mp hxband
    have hne : c x 1 ≠ -1 := fun he => (ne_of_gt hqpos) ((haxis_iff q hqx).mp he)
    exact lt_of_le_of_ne hnormal hne.symm
  · intro hnormal
    have hxband : x ∈ Set.range A.band := (hband x hx).mpr hnormal.le
    obtain ⟨q,hq2,hqx⟩ := hparam x hx hxband
    have hqne : (q.2 : ℝ) ≠ 0 := fun he => (ne_of_gt hnormal) ((haxis_iff q hqx).mpr he)
    have hqpos : 0 < (q.2 : ℝ) := lt_of_le_of_ne q.2.property.1 hqne.symm
    rw [← hqx]
    exact (halfrectangle_mem_removed A k _ ε hε q.2 hq2).mpr hqpos

private lemma square_chart_remainder_halfplane
    (c : OpenPartialHomeomorph S Schoenflies.Plane)
    (hremoved : ∀ x ∈ c.source, x ∈ A.removed ↔ -1 < c x 1) :
    ∀ x ∈ c.source, x ∈ A.removedᶜ ↔ c x 1 ≤ -1 := by
  intro x hx
  rw [Set.mem_compl_iff,hremoved x hx,not_lt]

open Schoenflies
private lemma square_image_of_boundary_fixed
    (g : C(↥(Plane.closedSquare 0 1), Plane)) (hg : IsEmbedding g)
    (hfix : ∀ x : ↥modelCurve, g ⟨x,modelCurve_subset_closedSquare x.property⟩ = (x : Plane)) :
    Set.range g = Plane.closedSquare 0 1 := by
  letI : CompactSpace ↥(Plane.closedSquare 0 1) :=
    isCompact_iff_compactSpace.mp (Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨Plane.isClosed_closedSquare 0 1,Plane.isBounded_closedSquare 0 1⟩)
  let Q := Plane.closedSquare 0 1
  let V : interior Q → Plane := fun x => g ⟨x,interior_subset x.property⟩
  let W := Set.range V
  have hV : Continuous V := g.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hVi : Function.Injective V := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun x : ↥(Plane.closedSquare 0 1) => (x : Plane))
      (hg.injective hxy))
  have hW : IsOpen W :=
    DifferentialGeometry.Topology.isOpen_range_of_isOpen_of_continuous_injective_real
      (modelWithCornersSelf ℝ Plane) isOpen_interior V hV hVi
  have hrange : IsClosed (Set.range g) := (isCompact_range g.continuous).isClosed
  have hWrange : W ⊆ Set.range g := by
    rintro x ⟨y,rfl⟩
    exact ⟨⟨y,interior_subset y.property⟩,rfl⟩
  have hclosure : closure W ∩ modelCurveᶜ ⊆ W := by
    rintro x ⟨hx,hxc⟩
    obtain ⟨y,hxy⟩ := hrange.closure_subset_iff.mpr hWrange hx
    have hyi : (y : Plane) ∈ interior Q := by
      by_contra hyi
      have hyc : (y : Plane) ∈ modelCurve := by
        rw [modelCurve_eq_frontier,(Plane.isClosed_closedSquare 0 1).frontier_eq]
        exact ⟨y.property,hyi⟩
      have hfixed := hfix ⟨y,hyc⟩
      have heq : g y = (y : Plane) := hfixed
      exact hxc (by rw [← hxy,heq]; exact hyc)
    exact ⟨⟨y,hyi⟩,hxy⟩
  have hWc : W ⊆ modelCurveᶜ := by
    rintro x ⟨y,rfl⟩ hxc
    have hfixed := hfix ⟨V y,hxc⟩
    have heq : (y : Plane) = V y :=
      congrArg Subtype.val (hg.injective hfixed.symm)
    have hyfront : (y : Plane) ∈ frontier Q := by
      rw [heq]
      exact modelCurve_eq_frontier ▸ hxc
    exact hyfront.2 y.property
  have hWout : Disjoint W Qᶜ := by
    rw [Set.disjoint_iff_inter_eq_empty]
    by_contra hne
    obtain ⟨x,hxW,hxQ⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have houtside : Qᶜ ⊆ W :=
      (Plane.isConnected_compl_closedSquare 0 1).isPreconnected.subset_of_closure_inter_subset
        hW ⟨x,hxQ,hxW⟩ (by
          rintro y ⟨hy,hyQ⟩
          exact hclosure ⟨hy,fun hyc => hyQ (modelCurve_subset_closedSquare hyc)⟩)
    exact Plane.not_isBounded_compl_closedSquare 0 1
      ((isCompact_range g.continuous).isBounded.subset (houtside.trans hWrange))
  have hWin : W ⊆ interior Q := by
    intro x hx
    have hxQ : x ∈ Q := by
      by_contra hxQ
      exact Set.disjoint_iff.mp hWout ⟨hx,hxQ⟩
    by_contra hxi
    exact hWc hx (by
      rw [modelCurve_eq_frontier,(Plane.isClosed_closedSquare 0 1).frontier_eq]
      exact ⟨hxQ,hxi⟩)
  have hzero : (0 : Plane) ∈ interior Q := by
    rw [interior_closedSquare_zero_one,mem_openSquare_zero_one]
    norm_num [Plane.supNorm]
  have hin : interior Q ⊆ W := by
    have hpre : IsPreconnected (interior Q) :=
      (Plane.convex_closedSquare 0 1).interior.isPreconnected
    exact hpre.subset_of_closure_inter_subset hW
      ⟨V ⟨0,hzero⟩,hWin ⟨⟨0,hzero⟩,rfl⟩,⟨⟨0,hzero⟩,rfl⟩⟩ (by
        rintro x ⟨hx,hxi⟩
        exact hclosure ⟨hx,fun hxc =>
          (modelCurve_eq_frontier ▸ hxc).2 hxi⟩)
  have hQcl : closure (interior Q) = Q := by
    rw [(Plane.convex_closedSquare 0 1).closure_interior_eq_closure_of_nonempty_interior
      ⟨0,hzero⟩,(Plane.isClosed_closedSquare 0 1).closure_eq]
  apply Set.Subset.antisymm
  · rintro x ⟨y,rfl⟩
    by_cases hyi : (y : Plane) ∈ interior Q
    · exact interior_subset (hWin ⟨⟨y,hyi⟩,rfl⟩)
    · have hyc : (y : Plane) ∈ modelCurve := by
        rw [modelCurve_eq_frontier,(Plane.isClosed_closedSquare 0 1).frontier_eq]
        exact ⟨y.property,hyi⟩
      rw [hfix ⟨y,hyc⟩]
      exact y.property
  · change Q ⊆ Set.range g
    rw [← hQcl]
    exact hrange.closure_subset_iff.mpr (hin.trans hWrange)

private lemma jordan_range_of_embedding {C : Set Plane} (hC : IsJordanCurve C)
    (b : C(C,Plane)) (hb : IsEmbedding b) : IsJordanCurve (Set.range b) := by
  classical
  let bfun : Plane → Plane := fun x => if hx : x ∈ C then b ⟨x,hx⟩ else 0
  have hbval (x : C) : bfun x = b x := by simp [bfun,x.property]
  have hbcont : ContinuousOn bfun C := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : C.domRestrict bfun = b := funext hbval
    rw [heq]
    exact b.continuous
  obtain ⟨q,hq,hqC⟩ := hC
  have hqin (t : ℝ) (ht : t ∈ unitInterval) : q t ∈ C := by
    rw [← hqC]
    exact ⟨t,ht,rfl⟩
  refine ⟨bfun ∘ q,⟨hbcont.comp hq.continuousOn hqin,
    congrArg bfun hq.closes,?_⟩,?_⟩
  · intro t ht u hu htu
    have htC := hqin t (Ico_subset_Icc_self ht)
    have huC := hqin u (Ico_subset_Icc_self hu)
    have heq : b ⟨q t,htC⟩ = b ⟨q u,huC⟩ := by
      change bfun (q t) = bfun (q u) at htu
      exact (hbval ⟨q t,htC⟩).symm.trans (htu.trans (hbval ⟨q u,huC⟩))
    exact hq.injOn ht hu (congrArg Subtype.val (hb.injective heq))
  · rw [Set.image_comp,hqC]
    apply Set.Subset.antisymm
    · rintro x ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,(hbval ⟨y,hy⟩).symm⟩
    · rintro x ⟨y,rfl⟩
      exact ⟨y,y.property,hbval y⟩

private lemma native_relative_square
    (j : C(↥(Plane.closedSquare 0 1),Plane)) (hj : IsEmbedding j) :
    ∃ F : Plane ≃ₜ Plane,
      (∀ x : ↥modelCurve, F (x : Plane) =
        j ⟨x,modelCurve_subset_closedSquare x.property⟩) ∧
      F '' Plane.closedSquare 0 1 = Set.range j := by
  letI : CompactSpace modelCurve := isCompact_iff_compactSpace.mp isCompact_modelCurve
  let b : C(modelCurve,Plane) :=
    ⟨fun x => j ⟨x,modelCurve_subset_closedSquare x.property⟩,
      j.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  have hbi : Function.Injective b := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun x : ↥(Plane.closedSquare 0 1) => (x : Plane))
      (hj.injective hxy))
  have hb : IsEmbedding b := (b.continuous.isClosedEmbedding hbi).isEmbedding
  obtain ⟨F,hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
    isJordanCurve_modelCurve (jordan_range_of_embedding isJordanCurve_modelCurve b hb)
    hb.toHomeomorph
  have hboundary (x : modelCurve) : F (x : Plane) =
      j ⟨x,modelCurve_subset_closedSquare x.property⟩ := hF x
  let g : C(↥(Plane.closedSquare 0 1),Plane) := ⟨F.symm ∘ j,F.symm.continuous.comp j.continuous⟩
  have hg : IsEmbedding g := F.symm.isEmbedding.comp hj
  have hgfix (x : modelCurve) : g ⟨x,modelCurve_subset_closedSquare x.property⟩ = (x : Plane) := by
    change F.symm (j ⟨x,modelCurve_subset_closedSquare x.property⟩) = (x : Plane)
    rw [← hboundary x,F.symm_apply_apply]
  have himage := square_image_of_boundary_fixed g hg hgfix
  refine ⟨F,hboundary,?_⟩
  calc
    F '' Plane.closedSquare 0 1 = F '' Set.range g := congrArg (fun T : Set Plane => F '' T) himage.symm
    _ = Set.range j := by
      apply Set.Subset.antisymm
      · rintro x ⟨y,⟨p,rfl⟩,rfl⟩
        exact ⟨p,(F.apply_symm_apply (j p)).symm⟩
      · rintro x ⟨p,rfl⟩
        exact ⟨g p,⟨p,rfl⟩,F.apply_symm_apply (j p)⟩




private lemma extend_closed_homeomorph {X : Type*} [TopologicalSpace X]
    (Q : Set X) (hQ : IsClosed Q) (h : Q ≃ₜ Q)
    (hfix : ∀ x : Q, (x : X) ∈ frontier Q → h x = x) :
    ∃ H : X ≃ₜ X, (∀ x : Q, H (x : X) = (h x : X)) ∧
      ∀ x : X, x ∉ Q → H x = x := by
  classical
  have hifix (x : Q) (hx : (x : X) ∈ frontier Q) : h.symm x = x := by
    apply h.injective
    rw [h.apply_symm_apply,hfix x hx]
  let p : X → X := fun x => if hx : x ∈ Q then (h ⟨x,hx⟩ : X) else x
  let q : X → X := fun x => if hx : x ∈ Q then (h.symm ⟨x,hx⟩ : X) else x
  have hpval (x : Q) : p x = (h x : X) := by simp [p,x.property]
  have hqval (x : Q) : q x = (h.symm x : X) := by simp [q,x.property]
  have hpq : Function.LeftInverse q p := by
    intro x
    by_cases hx : x ∈ Q
    · change q (p (⟨x,hx⟩ : Q)) = x
      rw [hpval,hqval,h.symm_apply_apply]
    · simp only [p,q,dif_neg hx]
  have hqp : Function.LeftInverse p q := by
    intro x
    by_cases hx : x ∈ Q
    · change p (q (⟨x,hx⟩ : Q)) = x
      rw [hqval,hpval,h.apply_symm_apply]
    · simp only [p,q,dif_neg hx]
  have hcover : Q ∪ (interior Q)ᶜ = univ := by
    ext x
    simp only [Set.mem_union,Set.mem_compl_iff,Set.mem_univ,iff_true]
    by_cases hx : x ∈ interior Q
    · exact Or.inl (interior_subset hx)
    · exact Or.inr hx
  have hpcontQ : ContinuousOn p Q := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : Q.domRestrict p = fun x : Q => (h x : X) := funext hpval
    rw [heq]
    exact continuous_subtype_val.comp h.continuous
  have hqcontQ : ContinuousOn q Q := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : Q.domRestrict q = fun x : Q => (h.symm x : X) := funext hqval
    rw [heq]
    exact continuous_subtype_val.comp h.symm.continuous
  have hpout : ∀ x ∈ (interior Q)ᶜ, p x = x := by
    intro x hxi
    by_cases hx : x ∈ Q
    · rw [show p x = (h ⟨x,hx⟩ : X) from hpval ⟨x,hx⟩]
      rw [hfix ⟨x,hx⟩ (by rw [hQ.frontier_eq]; exact ⟨hx,hxi⟩)]
    · simp [p,hx]
  have hqout : ∀ x ∈ (interior Q)ᶜ, q x = x := by
    intro x hxi
    by_cases hx : x ∈ Q
    · rw [show q x = (h.symm ⟨x,hx⟩ : X) from hqval ⟨x,hx⟩]
      rw [hifix ⟨x,hx⟩ (by rw [hQ.frontier_eq]; exact ⟨hx,hxi⟩)]
    · simp [q,hx]
  have hpcont : Continuous p := by
    rw [← continuousOn_univ,← hcover]
    exact (continuousOn_union_iff_of_isClosed hQ isOpen_interior.isClosed_compl).mpr
      ⟨hpcontQ,continuous_id.continuousOn.congr hpout⟩
  have hqcont : Continuous q := by
    rw [← continuousOn_univ,← hcover]
    exact (continuousOn_union_iff_of_isClosed hQ isOpen_interior.isClosed_compl).mpr
      ⟨hqcontQ,continuous_id.continuousOn.congr hqout⟩
  let H : X ≃ₜ X := {
    toFun := p
    invFun := q
    left_inv := hpq
    right_inv := hqp
    continuous_toFun := hpcont
    continuous_invFun := hqcont }
  refine ⟨H,?_,?_⟩
  · exact hpval
  · intro x hx
    exact dif_neg hx

private lemma native_whole_square_extension
    (j : C(↥(Plane.closedSquare 0 1),Plane)) (hj : IsEmbedding j) :
    ∃ G : Plane ≃ₜ Plane, ∀ x : ↥(Plane.closedSquare 0 1), G (x : Plane) = j x := by
  obtain ⟨F,hboundary,himage⟩ := native_relative_square j hj
  let g : C(↥(Plane.closedSquare 0 1),Plane) := ⟨F.symm ∘ j,F.symm.continuous.comp j.continuous⟩
  have hg : IsEmbedding g := F.symm.isEmbedding.comp hj
  have hgfix (x : modelCurve) : g ⟨x,modelCurve_subset_closedSquare x.property⟩ = (x : Plane) := by
    change F.symm (j ⟨x,modelCurve_subset_closedSquare x.property⟩) = (x : Plane)
    rw [← hboundary x,F.symm_apply_apply]
  have hgrange := square_image_of_boundary_fixed g hg hgfix
  let h : ↥(Plane.closedSquare 0 1) ≃ₜ ↥(Plane.closedSquare 0 1) :=
    hg.toHomeomorph.trans (Homeomorph.setCongr hgrange)
  have hval (x : ↥(Plane.closedSquare 0 1)) : (h x : Plane) = F.symm (j x) := rfl
  have hfix (x : ↥(Plane.closedSquare 0 1)) (hx : (x : Plane) ∈ frontier (Plane.closedSquare 0 1)) : h x = x := by
    apply Subtype.ext
    rw [hval]
    have hxc : (x : Plane) ∈ modelCurve := modelCurve_eq_frontier.symm ▸ hx
    exact hgfix ⟨x,hxc⟩
  obtain ⟨H,hH,hHout⟩ := extend_closed_homeomorph (Plane.closedSquare 0 1)
    (Plane.isClosed_closedSquare 0 1) h hfix
  refine ⟨H.trans F,?_⟩
  intro x
  change F (H (x : Plane)) = j x
  rw [hH,hval,F.apply_symm_apply]

private def squareInwardPush (x : ↥(Plane.closedSquare 0 1)) : Plane :=
  Plane.mk (x.val 0) (x.val 1 + (1-|x.val 0|)/2*(1-|x.val 1|))
private lemma squareInwardPush_continuous : Continuous squareInwardPush := by
  unfold squareInwardPush Plane.mk
  fun_prop
private lemma squareInwardPush_injective : Function.Injective squareInwardPush := by
  intro x y hxy
  have hx0 : x.val 0 = y.val 0 := by
    have h0 := congrArg (fun z : Plane => z 0) hxy
    exact h0
  have hx1 : x.val 1 + (1-|x.val 0|)/2*(1-|x.val 1|) =
      y.val 1 + (1-|y.val 0|)/2*(1-|y.val 1|) := congrArg (fun z : Plane => z 1) hxy
  rw [← hx0] at hx1
  have hxQ : max |x.val 0| |x.val 1| ≤ 1 := mem_closedSquare_zero_one.mp x.property
  have ha : 0 ≤ (1-|x.val 0|)/2 := by linarith [(le_max_left _ _).trans hxQ]
  have ha1 : (1-|x.val 0|)/2 ≤ 1/2 := by linarith [abs_nonneg (x.val 0)]
  have heq : x.val 1 = y.val 1 := by
    rcases le_total (x.val 1) (y.val 1) with hle | hle
    · have habs : |y.val 1|-|x.val 1| ≤ y.val 1-x.val 1 := by
        have h := abs_sub_abs_le_abs_sub (y.val 1) (x.val 1)
        rwa [abs_of_nonneg (sub_nonneg.mpr hle)] at h
      have hmul := mul_le_mul_of_nonneg_left habs ha
      nlinarith
    · have habs : |x.val 1|-|y.val 1| ≤ x.val 1-y.val 1 := by
        have h := abs_sub_abs_le_abs_sub (x.val 1) (y.val 1)
        rwa [abs_of_nonneg (sub_nonneg.mpr hle)] at h
      have hmul := mul_le_mul_of_nonneg_left habs ha
      nlinarith
  apply Subtype.ext
  ext i
  fin_cases i
  · exact hx0
  · exact heq
private lemma squareInwardPush_boundary_fixed (x : modelCurve) :
    squareInwardPush ⟨x,modelCurve_subset_closedSquare x.property⟩ = (x : Plane) := by
  have hx : max |x.val 0| |x.val 1| = 1 := x.property
  have heither : |x.val 0| = 1 ∨ |x.val 1| = 1 := by
    rcases le_total |x.val 0| |x.val 1| with h | h
    · exact Or.inr (by rwa [max_eq_right h] at hx)
    · exact Or.inl (by rwa [max_eq_left h] at hx)
  ext i
  fin_cases i
  · rfl
  · change x.val 1+(1-|x.val 0|)/2*(1-|x.val 1|) = x.val 1
    rcases heither with h | h <;> rw [h] <;> ring
private lemma exists_plane_inward_push :
    ∃ G : Plane ≃ₜ Plane,
      (∀ x : Plane, x ∉ Plane.closedSquare 0 1 → G x = x) ∧
      (∀ x : Plane, G x 0 = x 0) ∧
      (∀ x : Plane, x 1 ≤ G x 1) ∧
      ∀ x : Plane, |x 0| < 1 → x 1 = 0 → 0 < G x 1 := by
  letI : CompactSpace ↥(Plane.closedSquare 0 1) :=
    isCompact_iff_compactSpace.mp (Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨Plane.isClosed_closedSquare 0 1,Plane.isBounded_closedSquare 0 1⟩)
  let g : C(↥(Plane.closedSquare 0 1),Plane) :=
    ⟨squareInwardPush,squareInwardPush_continuous⟩
  have hg : IsEmbedding g :=
    (g.continuous.isClosedEmbedding squareInwardPush_injective).isEmbedding
  have hgrange := square_image_of_boundary_fixed g hg squareInwardPush_boundary_fixed
  let h : ↥(Plane.closedSquare 0 1) ≃ₜ ↥(Plane.closedSquare 0 1) :=
    hg.toHomeomorph.trans (Homeomorph.setCongr hgrange)
  have hval (x : ↥(Plane.closedSquare 0 1)) : (h x : Plane) = squareInwardPush x := rfl
  have hfix (x : ↥(Plane.closedSquare 0 1)) (hx : x.val ∈ frontier (Plane.closedSquare 0 1)) : h x = x := by
    apply Subtype.ext
    rw [hval]
    exact squareInwardPush_boundary_fixed ⟨x,modelCurve_eq_frontier.symm ▸ hx⟩
  obtain ⟨G,hG,hGout⟩ := extend_closed_homeomorph (Plane.closedSquare 0 1)
    (Plane.isClosed_closedSquare 0 1) h hfix
  have hGval (x : Plane) (hx : x ∈ Plane.closedSquare 0 1) :
      G x = Plane.mk (x 0) (x 1+(1-|x 0|)/2*(1-|x 1|)) :=
    (hG ⟨x,hx⟩).trans (hval ⟨x,hx⟩)
  refine ⟨G,hGout,?_,?_,?_⟩
  · intro x
    by_cases hx : x ∈ Plane.closedSquare 0 1
    · rw [hGval x hx]
      rfl
    · rw [hGout x hx]
  · intro x
    by_cases hx : x ∈ Plane.closedSquare 0 1
    · have hxQ := mem_closedSquare_zero_one.mp hx
      have hx0 : 0 ≤ 1-|x 0| := by linarith [(le_max_left _ _).trans hxQ]
      have hx1 : 0 ≤ 1-|x 1| := by linarith [(le_max_right _ _).trans hxQ]
      rw [hGval x hx]
      change x 1 ≤ x 1+(1-|x 0|)/2*(1-|x 1|)
      exact le_add_of_nonneg_right (mul_nonneg (by positivity) hx1)
    · rw [hGout x hx]
  · intro x hx0 hx1
    have hxQ : x ∈ Plane.closedSquare 0 1 := by
      rw [mem_closedSquare_zero_one]
      change max |x 0| |x 1| ≤ 1
      exact max_le hx0.le (by rw [hx1]; norm_num)
    rw [hGval x hxQ]
    change 0 < x 1+(1-|x 0|)/2*(1-|x 1|)
    rw [hx1]
    simp only [abs_zero,sub_zero,zero_add,mul_one]
    linarith

private lemma annulus_outside_halfchart
    (k : Fin 2) (z : Circle) :
    ∃ c : OpenPartialHomeomorph S Schoenflies.Plane,
      (A.edgePoint k z : S) ∈ c.source ∧
      c (A.edgePoint k z : S) 1 = -1 ∧
      (∀ x ∈ c.source, x ∈ Set.range A.band ↔ -1 ≤ c x 1) ∧
      (∀ x ∈ c.source, x ∈ A.removed ↔ -1 < c x 1) ∧
      (∀ x ∈ c.source, x ∈ A.removedᶜ ↔ c x 1 ≤ -1) ∧
      ∃ a b : ℝ, a < Complex.arg z ∧ Complex.arg z < b ∧ b-a < 2*Real.pi ∧
        ∀ r : Time, (A.edgePoint k (Circle.exp (a+(b-a)*(r : ℝ))) : S) ∈ c.source →
          c (A.edgePoint k (Circle.exp (a+(b-a)*(r : ℝ))) : S) =
            (timeToSquare (r,0) : Schoenflies.Plane) := by
  obtain ⟨e,he,a,b,ha,hb,hwidth,ε,hε,j,hj,hchart,hjval,hjzero,s,hs0,hs1,hscenter⟩ :=
    planar_edge_square A k z
  have hab : a < b := ha.trans hb
  have hsedge : (A.edgePoint k (Circle.exp (a+(b-a)*(s : ℝ))) : S) ∈ e.source := by
    simpa [CompressionAnnulus.edgePoint,inwardTime_zero] using hchart (s,0)
  have hsz : Circle.exp (a+(b-a)*(s : ℝ)) = z :=
    congrArg Prod.fst (A.embedded.injective
      (e.injOn hsedge he ((hjzero s).symm.trans hscenter)))
  obtain ⟨V,hV,hpoint,hVe,hlocal,hparam⟩ :=
    local_square_buffer A k z e he a b hab ε hε j hchart hjval s hs0 hs1 hsz
  obtain ⟨F,hboundary,himage⟩ := native_relative_square j hj
  have hFbottom (r : Time) : F (timeToSquare (r,0) : Schoenflies.Plane) = j (timeToSquare (r,0)) :=
    hboundary ⟨_,timeToSquare_bottom_mem_modelCurve r⟩
  obtain ⟨c,hcpoint,hccenter,hcV,hcval,hcband⟩ :=
    square_extension_chart A k z e j F hboundary himage V hV hpoint hVe hlocal s hscenter
  obtain ⟨d,hdpoint,hdcenter,hdc,hdval,hdbox,hdband⟩ :=
    square_chart_outside_halfplane A k z c hcpoint s hs0 hs1 hccenter hcband
  have hde : d.source ⊆ e.source := fun x hx => hVe (subset_closure (hcV (hdc hx)))
  have hdF : ∀ x ∈ d.source, d x = F.symm (e x) :=
    fun x hx => (hdval x hx).trans (hcval x)
  have hdparam : ∀ x ∈ d.source, x ∈ Set.range A.band → ∃ q : Time × Time,
      (q.2 : ℝ) < 1 ∧
      A.band (Circle.exp (a+(b-a)*(q.1 : ℝ)),inwardTime k (ε*q.2)) = x :=
    fun x hx hxband => hparam x (subset_closure (hcV (hdc hx))) hxband
  have hdremoved := square_chart_removed_halfplane A k e d a b ε hε j F hFbottom
    hjval hchart hde hdF hdbox hdband hdparam
  refine ⟨d,hdpoint,?_,hdband,hdremoved,square_chart_remainder_halfplane A d hdremoved,
    a,b,ha,hb,hwidth,?_⟩
  · rw [hdcenter]
    change 2*(0 : ℝ)-1 = -1
    norm_num
  · intro r hr
    rw [hdF _ hr,← hjzero r,← hFbottom r,F.symm_apply_apply]


private lemma annulus_whole_inward_chart (k : Fin 2) (z : Circle) :
    ∃ a b : ℝ, a < Complex.arg z ∧ Complex.arg z < b ∧ b-a < 2*Real.pi ∧
      ∃ ε : Time, 0 < (ε : ℝ) ∧
        ∃ c : OpenPartialHomeomorph S Plane,
          (A.edgePoint k z : S) ∈ c.source ∧
          c (A.edgePoint k z : S) 1 = -1 ∧
          (∀ x ∈ c.source, |c x 0| < 1 ∧ c x 1 < 0) ∧
          (∀ x ∈ c.source, x ∈ Set.range A.band ↔ -1 ≤ c x 1) ∧
          (∀ q : Time × Time,
            A.band (Circle.exp (a+(b-a)*(q.1 : ℝ)),inwardTime k (ε*q.2)) ∈ c.source →
            c (A.band (Circle.exp (a+(b-a)*(q.1 : ℝ)),inwardTime k (ε*q.2))) =
              (timeToSquare q : Plane)) ∧
          ∀ x ∈ c.source, x ∈ Set.range A.band → ∃ q : Time × Time,
            (q.2 : ℝ) < 1 ∧
            A.band (Circle.exp (a+(b-a)*(q.1 : ℝ)),inwardTime k (ε*q.2)) = x := by
  obtain ⟨e,he,a,b,ha,hb,hwidth,ε,hε,j,hj,hchart,hjval,hjzero,s,hs0,hs1,hscenter⟩ :=
    planar_edge_square A k z
  have hab : a < b := ha.trans hb
  have hsedge : (A.edgePoint k (Circle.exp (a+(b-a)*(s : ℝ))) : S) ∈ e.source := by
    simpa [CompressionAnnulus.edgePoint,inwardTime_zero] using hchart (s,0)
  have hsz : Circle.exp (a+(b-a)*(s : ℝ)) = z :=
    congrArg Prod.fst (A.embedded.injective
      (e.injOn hsedge he ((hjzero s).symm.trans hscenter)))
  obtain ⟨V,hV,hpoint,hVe,hlocal,hparam⟩ :=
    local_square_buffer A k z e he a b hab ε hε j hchart hjval s hs0 hs1 hsz
  obtain ⟨G,hG⟩ := native_whole_square_extension j hj
  have hboundary (x : modelCurve) : G (x : Plane) =
      j ⟨x,modelCurve_subset_closedSquare x.property⟩ :=
    hG ⟨x,modelCurve_subset_closedSquare x.property⟩
  have himage : G '' Plane.closedSquare 0 1 = Set.range j := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,(hG ⟨y,hy⟩).symm⟩
    · rintro ⟨y,rfl⟩
      exact ⟨y,y.property,hG y⟩
  obtain ⟨c,hcpoint,hccenter,hcV,hcval,hcband⟩ :=
    square_extension_chart A k z e j G hboundary himage V hV hpoint hVe hlocal s hscenter
  obtain ⟨d,hdpoint,hdcenter,hdc,hdval,hdbox,hdband⟩ :=
    square_chart_outside_halfplane A k z c hcpoint s hs0 hs1 hccenter hcband
  refine ⟨a,b,ha,hb,hwidth,ε,hε,d,hdpoint,?_,hdbox,hdband,?_,?_⟩
  · rw [hdcenter]
    change 2*(0 : ℝ)-1 = -1
    norm_num
  · intro q hq
    rw [hdval _ hq,hcval,← hjval q,← hG (timeToSquare q),G.symm_apply_apply]
  · intro x hx hxband
    exact hparam x (subset_closure (hcV (hdc hx))) hxband

private lemma transport_compactly_supported_homeomorph
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (K : Set Y) (hK : IsCompact K)
    (hKt : K ⊆ e.target) (G : Y ≃ₜ Y)
    (hfix : ∀ y : Y, y ∉ K → G y = y) :
    ∃ H : X ≃ₜ X,
      (∀ x ∈ e.source, H x = e.symm (G (e x))) ∧
      (∀ x, x ∉ e.symm '' K → H x = x) := by
  classical
  have hifix (y : Y) (hy : y ∉ K) : G.symm y = y := by
    apply G.injective
    rw [G.apply_symm_apply,hfix y hy]
  have hGtarget : MapsTo G e.target e.target := by
    intro y hy
    by_cases hGy : G y ∈ K
    · exact hKt hGy
    · have heq : G y = y := G.injective (hfix (G y) hGy)
      rwa [heq]
  have hGitarget : MapsTo G.symm e.target e.target := by
    intro y hy
    by_cases hGy : G.symm y ∈ K
    · exact hKt hGy
    · have heq : G.symm y = y := G.symm.injective (hifix (G.symm y) hGy)
      rwa [heq]
  let p : X → X := e.extendById G
  let q : X → X := e.extendById G.symm
  have hpval (x : X) (hx : x ∈ e.source) : p x = e.symm (G (e x)) := ite_eq_left hx
  have hqval (x : X) (hx : x ∈ e.source) : q x = e.symm (G.symm (e x)) := ite_eq_left hx
  have hpout (x : X) (hx : x ∉ e.symm '' K) : p x = x :=
    e.extendById_eq_of_notMem_image G hfix hx
  have hqout (x : X) (hx : x ∉ e.symm '' K) : q x = x :=
    e.extendById_eq_of_notMem_image G.symm hifix hx
  have hcompact : IsCompact (e.symm '' K) :=
    hK.image_of_continuousOn (e.continuousOn_symm.mono hKt)
  have hpsource (x : X) (hx : x ∈ e.source) : p x ∈ e.source := by
    rw [hpval x hx]
    exact e.map_target (hGtarget (e.map_source hx))
  have hqsource (x : X) (hx : x ∈ e.source) : q x ∈ e.source := by
    rw [hqval x hx]
    exact e.map_target (hGitarget (e.map_source hx))
  have hpq : Function.LeftInverse q p := by
    intro x
    by_cases hx : x ∈ e.source
    · rw [hqval _ (hpsource x hx),hpval x hx,
        e.right_inv (hGtarget (e.map_source hx)),G.symm_apply_apply,e.left_inv hx]
    · have hp : p x = x := ite_eq_right hx
      have hq : q x = x := ite_eq_right hx
      rw [hp,hq]
  have hqp : Function.LeftInverse p q := by
    intro x
    by_cases hx : x ∈ e.source
    · rw [hpval _ (hqsource x hx),hqval x hx,
        e.right_inv (hGitarget (e.map_source hx)),G.apply_symm_apply,e.left_inv hx]
    · have hp : p x = x := ite_eq_right hx
      have hq : q x = x := ite_eq_right hx
      rw [hq,hp]
  have hpc : ContinuousOn p e.source :=
    (e.continuousOn_symm.comp (G.continuous.comp_continuousOn e.continuousOn)
      (fun x hx => hGtarget (e.map_source hx))).congr hpval
  have hqc : ContinuousOn q e.source :=
    (e.continuousOn_symm.comp (G.symm.continuous.comp_continuousOn e.continuousOn)
      (fun x hx => hGitarget (e.map_source hx))).congr hqval
  have hpcont : Continuous p := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ e.source
    · exact hpc.continuousAt (e.open_source.mem_nhds hx)
    · have hxK : x ∉ e.symm '' K := by
        rintro ⟨y,hy,hyx⟩
        exact hx (hyx ▸ e.map_target (hKt hy))
      apply continuousAt_id.congr_of_eventuallyEq
      filter_upwards [hcompact.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      exact hpout y hy
  have hqcont : Continuous q := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ e.source
    · exact hqc.continuousAt (e.open_source.mem_nhds hx)
    · have hxK : x ∉ e.symm '' K := by
        rintro ⟨y,hy,hyx⟩
        exact hx (hyx ▸ e.map_target (hKt hy))
      apply continuousAt_id.congr_of_eventuallyEq
      filter_upwards [hcompact.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      exact hqout y hy
  let H : X ≃ₜ X := {
    toFun := p
    invFun := q
    left_inv := hpq
    right_inv := hqp
    continuous_toFun := hpcont
    continuous_invFun := hqcont }
  exact ⟨H,hpval,hpout⟩
private def planeNormalize (p : Plane) (r : ℝ) (hr : r ≠ 0) : Plane ≃ₜ Plane where
  toFun x := r⁻¹ • (x-p)
  invFun x := r • x+p
  left_inv x := by simp [smul_sub,smul_smul,hr]
  right_inv x := by simp [smul_smul,hr]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private lemma exists_local_plane_inward_push
    (p : Plane) (W : Set Plane) (hW : IsOpen W) (hp : p ∈ W) :
    ∃ K : Set Plane, IsCompact K ∧ K ⊆ W ∧
      ∃ G : Plane ≃ₜ Plane,
        (∀ x : Plane, x ∉ K → G x = x) ∧
        (∀ x : Plane, G x 0 = x 0) ∧
        (∀ x : Plane, x 1 ≤ G x 1) ∧ p 1 < G p 1 := by
  obtain ⟨r,hr,_,hrW⟩ := Plane.exists_openSquare_subset hW hp zero_lt_one
  let ρ := r/2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let L := planeNormalize p ρ hρ.ne'
  let K := Plane.closedSquare p ρ
  have hLK (x : Plane) : L x ∈ Plane.closedSquare 0 1 ↔ x ∈ K := by
    rw [mem_closedSquare_zero_one]
    change max |ρ⁻¹*(x 0-p 0)| |ρ⁻¹*(x 1-p 1)| ≤ 1 ↔
      max |x 0-p 0| |x 1-p 1| ≤ ρ
    rw [abs_mul,abs_mul,abs_of_pos (inv_pos.mpr hρ),← mul_max_of_nonneg _ _ (inv_nonneg.mpr hρ.le)]
    rw [inv_mul_le_iff₀ hρ]
    simp
  have hKW : K ⊆ W := by
    intro x hx
    apply hrW
    change Plane.supDist x p < r
    have hx' : Plane.supDist x p ≤ ρ := hx
    dsimp [ρ] at hx'
    linarith
  obtain ⟨g,hgout,hg0,hg1,hgpos⟩ := exists_plane_inward_push
  let G := (L.trans g).trans L.symm
  have hG (x : Plane) : G x = ρ • g (L x)+p := rfl
  refine ⟨K,Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨Plane.isClosed_closedSquare p ρ,Plane.isBounded_closedSquare p ρ⟩,hKW,G,?_,?_,?_,?_⟩
  · intro x hx
    have hxQ : L x ∉ Plane.closedSquare 0 1 := fun h => hx ((hLK x).mp h)
    change L.symm (g (L x)) = x
    rw [hgout _ hxQ,L.symm_apply_apply]
  · intro x
    rw [hG]
    change ρ*g (L x) 0+p 0 = x 0
    rw [hg0]
    change ρ*(ρ⁻¹*(x 0-p 0))+p 0 = x 0
    field_simp
    ring
  · intro x
    have h := mul_le_mul_of_nonneg_left (hg1 (L x)) hρ.le
    rw [hG]
    change x 1 ≤ ρ*g (L x) 1+p 1
    have heq : ρ*(L x 1)+p 1=x 1 := by
      change ρ*(ρ⁻¹*(x 1-p 1))+p 1=x 1
      field_simp
      ring
    linarith
  · have hzero : L p = 0 := by simp [L,planeNormalize]
    have h := hgpos (L p) (by rw [hzero]; norm_num) (by rw [hzero]; rfl)
    rw [hG]
    change p 1 < ρ*g (L p) 1+p 1
    exact lt_add_of_pos_left _ (mul_pos hρ h)

private lemma annulus_local_inward_push (k : Fin 2) (z : Circle) :
    ∃ H : S ≃ₜ S,
      (∀ w : Circle, ∀ t : Time, ∃ u : Time, t ≤ u ∧
        H (A.band (w,inwardTime k t)) = A.band (w,inwardTime k u)) ∧
      ∃ u : Time, 0 < (u : ℝ) ∧ H (A.edgePoint k z : S) = A.band (z,inwardTime k u) := by
  obtain ⟨a,b,ha,hb,hwidth,ε,hε,d,hdpoint,hdcenter,hdbox,hdband,hdcoord,hdparam⟩ :=
    annulus_whole_inward_chart A k z
  obtain ⟨K,hK,hKt,G,hGout,hG0,hG1,hGpos⟩ :=
    exists_local_plane_inward_push (d (A.edgePoint k z : S)) d.target d.open_target
      (d.map_source hdpoint)
  obtain ⟨H,hH,hHout⟩ := transport_compactly_supported_homeomorph d K hK hKt G hGout
  have hGt : MapsTo G d.target d.target := by
    intro y hy
    by_cases hGy : G y ∈ K
    · exact hKt hGy
    · have heq : G y = y := G.injective (hGout (G y) hGy)
      rwa [heq]
  have hHsource (x : S) (hx : x ∈ d.source) : H x ∈ d.source := by
    rw [hH x hx]
    exact d.map_target (hGt (d.map_source hx))
  have hdH (x : S) (hx : x ∈ d.source) : d (H x) = G (d x) := by
    rw [hH x hx,d.right_inv (hGt (d.map_source hx))]
  have hmove (w : Circle) (t : Time) : ∃ u : Time, t ≤ u ∧
      H (A.band (w,inwardTime k t)) = A.band (w,inwardTime k u) := by
    let x := A.band (w,inwardTime k t)
    by_cases hxK : x ∈ d.symm '' K
    · have hx : x ∈ d.source := by
        obtain ⟨y,hy,hyx⟩ := hxK
        exact hyx ▸ d.map_target (hKt hy)
      have hxb : x ∈ Set.range A.band := ⟨(w,inwardTime k t),rfl⟩
      have hHx := hHsource x hx
      have hHxb : H x ∈ Set.range A.band := (hdband _ hHx).mpr (by
        rw [hdH x hx]
        exact ((hdband x hx).mp hxb).trans (hG1 (d x)))
      obtain ⟨q,hq2,hqx⟩ := hdparam x hx hxb
      obtain ⟨q',hq'2,hq'Hx⟩ := hdparam (H x) hHx hHxb
      have hdq : d x = (timeToSquare q : Plane) := by
        rw [← hqx]
        exact hdcoord q (hqx ▸ hx)
      have hdq' : d (H x) = (timeToSquare q' : Plane) := by
        rw [← hq'Hx]
        exact hdcoord q' (hq'Hx ▸ hHx)
      have hq0 : (q.1 : ℝ) = (q'.1 : ℝ) := by
        have h := hG0 (d x)
        rw [← hdH x hx,hdq,hdq'] at h
        change 2*(q'.1 : ℝ)-1=2*(q.1 : ℝ)-1 at h
        linarith
      have hq1 : (q.2 : ℝ) ≤ (q'.2 : ℝ) := by
        have h := hG1 (d x)
        rw [← hdH x hx,hdq,hdq'] at h
        change 2*(q.2 : ℝ)-1≤2*(q'.2 : ℝ)-1 at h
        linarith
      have hparamEq :
          (Circle.exp (a+(b-a)*(q.1 : ℝ)),inwardTime k (ε*q.2)) =
            (w,inwardTime k t) := A.embedded.injective hqx
      have ht : ε*q.2 = t := inwardTime_injective k (congrArg Prod.snd hparamEq)
      refine ⟨ε*q'.2,?_,?_⟩
      · rw [← ht]
        change (ε : ℝ)*(q.2 : ℝ)≤(ε : ℝ)*(q'.2 : ℝ)
        exact mul_le_mul_of_nonneg_left hq1 ε.property.1
      · change H x = A.band (w,inwardTime k (ε*q'.2))
        have hw : Circle.exp (a+(b-a)*(q.1 : ℝ)) = w := congrArg Prod.fst hparamEq
        rw [← hq'Hx,← hq0,hw]
    · exact ⟨t,le_rfl,hHout x hxK⟩
  refine ⟨H,hmove,?_⟩
  obtain ⟨u,hu,hHu⟩ := hmove z 0
  have hHedge : H (A.edgePoint k z : S) = A.band (z,inwardTime k u) := by
    simpa [inwardTime_zero,CompressionAnnulus.edgePoint] using hHu
  refine ⟨u,?_,hHedge⟩
  have hpositive : -1 < d (H (A.edgePoint k z : S)) 1 := by
    rw [hdH _ hdpoint]
    exact hdcenter ▸ hGpos
  by_contra hu0
  have huzero : u = 0 := Subtype.ext (le_antisymm (le_of_not_gt hu0) u.property.1)
  rw [huzero,inwardTime_zero] at hHedge
  change H (A.edgePoint k z : S) = (A.edgePoint k z : S) at hHedge
  rw [hHedge,hdcenter] at hpositive
  exact lt_irrefl _ hpositive

private def composeHomeomorphs {X : Type*} [TopologicalSpace X] : List (X ≃ₜ X) → X ≃ₜ X
  | [] => Homeomorph.refl X
  | G::l => (composeHomeomorphs l).trans G

private lemma compose_inward_pushes (k : Fin 2) (l : List (S ≃ₜ S))
    (hl : ∀ G ∈ l, ∀ w : Circle, ∀ t : Time, ∃ u : Time, t ≤ u ∧
      G (A.band (w,inwardTime k t)) = A.band (w,inwardTime k u)) :
    ∀ w : Circle, ∀ t : Time, ∃ u : Time, t ≤ u ∧
      composeHomeomorphs l (A.band (w,inwardTime k t)) = A.band (w,inwardTime k u) := by
  induction l with
  | nil =>
    intro w t
    exact ⟨t,le_rfl,rfl⟩
  | cons G l ih =>
    have hG := hl G (List.mem_cons_self ..)
    have ht := ih (fun F hF => hl F (List.mem_cons_of_mem G hF))
    intro w t
    obtain ⟨u,htu,heu⟩ := ht w t
    obtain ⟨v,huv,hev⟩ := hG w u
    exact ⟨v,htu.trans huv,by change G (composeHomeomorphs l _) = _; rw [heu,hev]⟩

private lemma inward_push_moves_edge (k : Fin 2) (H : S ≃ₜ S)
    (hH : ∀ w : Circle, ∀ t : Time, ∃ u : Time, t ≤ u ∧
      H (A.band (w,inwardTime k t)) = A.band (w,inwardTime k u))
    (z : Circle) (hz : H (A.edgePoint k z : S) ≠ (A.edgePoint k z : S)) :
    ∃ u : Time, 0 < (u : ℝ) ∧ H (A.edgePoint k z : S) = A.band (z,inwardTime k u) := by
  obtain ⟨u,hu,hHu⟩ := hH z 0
  have heq : H (A.edgePoint k z : S) = A.band (z,inwardTime k u) := by
    simpa [CompressionAnnulus.edgePoint,inwardTime_zero] using hHu
  refine ⟨u,?_,heq⟩
  by_contra hupos
  have hu0 : u = 0 := Subtype.ext (le_antisymm (le_of_not_gt hupos) u.property.1)
  apply hz
  simpa [hu0,CompressionAnnulus.edgePoint,inwardTime_zero] using heq

private lemma compose_inward_pushes_moves (k : Fin 2) (l : List (S ≃ₜ S))
    (hl : ∀ G ∈ l, ∀ w : Circle, ∀ t : Time, ∃ u : Time, t ≤ u ∧
      G (A.band (w,inwardTime k t)) = A.band (w,inwardTime k u))
    (z : Circle) (hz : ∃ G ∈ l, G (A.edgePoint k z : S) ≠ (A.edgePoint k z : S)) :
    composeHomeomorphs l (A.edgePoint k z : S) ≠ (A.edgePoint k z : S) := by
  induction l with
  | nil => simpa using hz
  | cons G l ih =>
    have hG := hl G (List.mem_cons_self ..)
    have htail : ∀ F ∈ l, ∀ w : Circle, ∀ t : Time, ∃ u : Time, t ≤ u ∧
        F (A.band (w,inwardTime k t)) = A.band (w,inwardTime k u) :=
      fun F hF => hl F (List.mem_cons_of_mem G hF)
    by_cases htailmove : composeHomeomorphs l (A.edgePoint k z : S) = (A.edgePoint k z : S)
    · obtain ⟨F,hF,hFmove⟩ := hz
      rcases List.mem_cons.mp hF with hFG | hFl
      · subst F
        change G (composeHomeomorphs l (A.edgePoint k z : S)) ≠ _
        rwa [htailmove]
      · exact False.elim ((ih htail ⟨F,hFl,hFmove⟩) htailmove)
    · obtain ⟨u,hu,hHu⟩ := inward_push_moves_edge A k (composeHomeomorphs l)
        (compose_inward_pushes A k l htail) z htailmove
      obtain ⟨v,huv,hGv⟩ := hG z u
      intro heq
      have hveq : A.band (z,inwardTime k v) = (A.edgePoint k z : S) := by
        change G (composeHomeomorphs l (A.edgePoint k z : S)) = _ at heq
        rwa [hHu,hGv] at heq
      have hvtime : inwardTime k v = CompressionAnnulus.sideTime k :=
        congrArg Prod.snd (A.embedded.injective hveq)
      rw [← inwardTime_zero k] at hvtime
      have hv0 : v = 0 := inwardTime_injective k hvtime
      have hvpos : 0 < (v : ℝ) := hu.trans_le huv
      simpa [hv0] using hvpos

private lemma annulus_global_inward_push (k : Fin 2) :
    ∃ H : S ≃ₜ S,
      (∀ w : Circle, ∀ t : Time, ∃ u : Time, t ≤ u ∧
        H (A.band (w,inwardTime k t)) = A.band (w,inwardTime k u)) ∧
      ∀ z : Circle, ∃ u : Time, 0 < (u : ℝ) ∧
        H (A.edgePoint k z : S) = A.band (z,inwardTime k u) := by
  classical
  choose H hpush hpos using annulus_local_inward_push A k
  let U : Circle → Set Circle := fun z =>
    {w | H z (A.edgePoint k w : S) ≠ (A.edgePoint k w : S)}
  have hedgecont : Continuous (fun w : Circle => (A.edgePoint k w : S)) := by
    change Continuous (fun w : Circle => A.band (w,CompressionAnnulus.sideTime k))
    exact A.band.continuous.comp (continuous_id.prodMk continuous_const)
  have hU : ∀ z, IsOpen (U z) := by
    intro z
    exact isOpen_ne_fun ((H z).continuous.comp hedgecont) hedgecont
  have hcenter (z : Circle) : z ∈ U z := by
    obtain ⟨u,hu,heq⟩ := hpos z
    intro hfix
    have hutime : inwardTime k u = CompressionAnnulus.sideTime k :=
      congrArg Prod.snd (A.embedded.injective (heq.symm.trans hfix))
    rw [← inwardTime_zero k] at hutime
    have h0 : u = 0 := inwardTime_injective k hutime
    simpa [h0] using hu
  obtain ⟨t,ht⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro z _
    exact Set.mem_iUnion.mpr ⟨z,hcenter z⟩)
  let l := t.toList.map H
  have hl : ∀ G ∈ l, ∀ w : Circle, ∀ t : Time, ∃ u : Time, t ≤ u ∧
      G (A.band (w,inwardTime k t)) = A.band (w,inwardTime k u) := by
    intro G hG
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hG
    exact hpush z
  refine ⟨composeHomeomorphs l,compose_inward_pushes A k l hl,?_⟩
  intro z
  have hzcover := ht (Set.mem_univ z)
  obtain ⟨w,hw,hwz⟩ := Set.mem_iUnion₂.mp hzcover
  apply inward_push_moves_edge A k (composeHomeomorphs l) (compose_inward_pushes A k l hl) z
  apply compose_inward_pushes_moves A k l hl z
  exact ⟨H w,List.mem_map.mpr ⟨w,Finset.mem_toList.mpr hw,rfl⟩,hwz⟩

private def inwardBand (k : Fin 2) : C(Circle × Time,S) :=
  A.band.comp ⟨(Homeomorph.refl Circle).prodCongr (inwardTimeHomeomorph k),
    ((Homeomorph.refl Circle).prodCongr (inwardTimeHomeomorph k)).continuous⟩

private lemma inwardBand_embedding (k : Fin 2) : IsEmbedding (inwardBand A k) :=
  A.embedded.comp (((Homeomorph.refl Circle).prodCongr (inwardTimeHomeomorph k)).isEmbedding)

private lemma inwardBand_zero (k : Fin 2) (z : Circle) :
    inwardBand A k (z,0) = (A.edgePoint k z : S) := by
  change A.band (z,inwardTime k 0) = A.band (z,CompressionAnnulus.sideTime k)
  rw [inwardTime_zero]

private lemma inwardBand_range (k : Fin 2) : Set.range (inwardBand A k) = Set.range A.band := by
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨(p.1,inwardTime k p.2),rfl⟩
  · rintro ⟨p,rfl⟩
    refine ⟨(p.1,(inwardTimeHomeomorph k).symm p.2),?_⟩
    change A.band (p.1,(inwardTimeHomeomorph k) ((inwardTimeHomeomorph k).symm p.2)) = A.band p
    rw [Homeomorph.apply_symm_apply]

private lemma inwardBand_mem_removed (k : Fin 2) (p : Circle × Time) :
    inwardBand A k p ∈ A.removed ↔ 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1 := by
  change A.band (p.1,inwardTime k p.2) ∈ A.removed ↔ _
  rw [band_mem_removed A]
  by_cases hk : k = 0
  · simp [inwardTime,hk]
  · simp only [inwardTime,if_neg hk]
    change 0 < 1-(p.2 : ℝ) ∧ 1-(p.2 : ℝ) < 1 ↔ _
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

private lemma removed_inwardBand (k : Fin 2) :
    A.removed = inwardBand A k '' {p : Circle × Time | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1} := by
  ext x
  constructor
  · intro hx
    have hxband : x ∈ Set.range (inwardBand A k) := by
      rw [inwardBand_range]
      obtain ⟨p,hp,hpx⟩ := hx
      exact ⟨p,hpx⟩
    obtain ⟨p,rfl⟩ := hxband
    exact ⟨p,(inwardBand_mem_removed A k p).mp hx,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    exact (inwardBand_mem_removed A k p).mpr hp

private lemma inward_push_height (k : Fin 2) (H : S ≃ₜ S)
    (hH : ∀ w : Circle, ∀ t : Time, ∃ u : Time, t ≤ u ∧
      H (A.band (w,inwardTime k t)) = A.band (w,inwardTime k u)) :
    ∃ ψ : C(Circle × Time,Time),
      (∀ p, H (inwardBand A k p) = inwardBand A k (p.1,ψ p)) ∧
      (∀ p, p.2 ≤ ψ p) ∧
      (∀ z, ψ (z,1)=1) ∧ ∀ z, StrictMono (fun t : Time => ψ (z,t)) := by
  let B := inwardBand A k
  have hB := inwardBand_embedding A k
  have hqmem (p : Circle × Time) : H (B p) ∈ Set.range B := by
    obtain ⟨u,hu,heq⟩ := hH p.1 p.2
    exact ⟨(p.1,u),heq.symm⟩
  let q : C(Circle × Time,Set.range B) :=
    ⟨fun p => ⟨H (B p),hqmem p⟩,
      (H.continuous.comp B.continuous).subtype_mk hqmem⟩
  let Ψ : C(Circle × Time,Circle × Time) :=
    ⟨hB.toHomeomorph.symm ∘ q,hB.toHomeomorph.symm.continuous.comp q.continuous⟩
  have hΨ (p : Circle × Time) : B (Ψ p) = H (B p) :=
    congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply (q p))
  have hΨu (p : Circle × Time) : ∃ u : Time, p.2 ≤ u ∧ Ψ p = (p.1,u) := by
    obtain ⟨u,hu,heq⟩ := hH p.1 p.2
    exact ⟨u,hu,hB.injective ((hΨ p).trans heq)⟩
  let ψ : C(Circle × Time,Time) := ⟨fun p => (Ψ p).2,Ψ.continuous.snd⟩
  have hval (p : Circle × Time) : H (B p) = B (p.1,ψ p) := by
    obtain ⟨u,hu,hΨp⟩ := hΨu p
    exact (hΨ p).symm.trans (congrArg B (by
      change Ψ p = (p.1,(Ψ p).2)
      rw [hΨp]))
  have hle (p : Circle × Time) : p.2 ≤ ψ p := by
    obtain ⟨u,hu,hΨp⟩ := hΨu p
    change p.2 ≤ (Ψ p).2
    rwa [hΨp]
  have htop (z : Circle) : ψ (z,1)=1 := le_antisymm (by exact le_top) (hle (z,1))
  refine ⟨ψ,hval,hle,htop,?_⟩
  intro z
  have hc : Continuous (fun t : Time => ψ (z,t)) :=
    ψ.continuous.comp (continuous_const.prodMk continuous_id)
  apply hc.strictMono_of_inj_boundedOrder
  · change ψ (z,0)≤ψ (z,1)
    rw [htop]
    exact le_top
  · intro t u htu
    have hHeq : H (B (z,t)) = H (B (z,u)) := by
      rw [hval,hval]
      exact congrArg (fun r : Time => B (z,r)) htu
    have heq : B (z,t)=B (z,u) := H.injective hHeq
    exact congrArg Prod.snd (hB.injective heq)

private lemma annulus_raw_outside_collar (k : Fin 2) :
    ∃ ξ : C(Circle × Time,A.Remainder), IsEmbedding ξ ∧
      (∀ z, ξ (z,0)=A.edgePoint k z) ∧
      IsOpen (ξ '' {p : Circle × Time | (p.2 : ℝ) < 1}) := by
  obtain ⟨H,hpush,hpos⟩ := annulus_global_inward_push A k
  obtain ⟨ψ,hψ,hle,htop,hmono⟩ := inward_push_height A k H hpush
  let B := inwardBand A k
  have hB := inwardBand_embedding A k
  let g : C(Circle,Time) := ⟨fun z => ψ (z,0),
    ψ.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hgpos (z : Circle) : 0 < (g z : ℝ) := by
    obtain ⟨u,hu,hHu⟩ := hpos z
    have heq : B (z,g z)=B (z,u) := by
      change inwardBand A k (z,ψ (z,0))=inwardBand A k (z,u)
      rw [← hψ (z,0),inwardBand_zero]
      exact hHu
    have hgu : g z=u := congrArg Prod.snd (hB.injective heq)
    rwa [hgu]
  have hglt (z : Circle) : (g z : ℝ) < 1 := by
    have h01 : (0 : Time)<1 := by norm_num
    have h := hmono z h01
    change ψ (z,0)<ψ (z,1) at h
    rw [htop] at h
    exact h
  let q : C(Circle × Time,Circle × Time) :=
    ⟨fun p => (p.1,g p.1 * unitInterval.symm p.2),by
      apply Continuous.prodMk
      · fun_prop
      · exact (g.continuous.comp continuous_fst).mul
          (unitInterval.continuous_symm.comp continuous_snd)⟩
  let raw : C(Circle × Time,S) :=
    ⟨H.symm ∘ B ∘ q,H.symm.continuous.comp (B.continuous.comp q.continuous)⟩
  have hrawH (p : Circle × Time) : H (raw p) = B (q p) := H.apply_symm_apply _
  have hqle (p : Circle × Time) : ((q p).2 : ℝ) ≤ (g p.1 : ℝ) := by
    change (g p.1 : ℝ)*(1-(p.2 : ℝ)) ≤ (g p.1 : ℝ)
    nlinarith [p.2.property.1,p.2.property.2,(g p.1).property.1]
  have hrawmem (p : Circle × Time) : raw p ∈ A.removedᶜ := by
    intro hx
    rw [removed_inwardBand A k] at hx
    obtain ⟨v,hv,hvx⟩ := hx
    have heq : B (v.1,ψ v) = B (q p) := by rw [← hψ v,hvx,hrawH]
    have hpars := hB.injective heq
    have hw : v.1=p.1 := by
      have h := congrArg Prod.fst hpars
      exact h
    have ht : ψ v=(q p).2 := congrArg Prod.snd hpars
    have hstrict : (g p.1 : ℝ) < (ψ v : ℝ) := by
      change ψ (p.1,0)<ψ v
      rw [← hw]
      exact hmono v.1 hv.1
    exact (not_lt_of_ge (hqle p)) (by rwa [ht] at hstrict)
  let ξ : C(Circle × Time,A.Remainder) := ⟨fun p => ⟨raw p,hrawmem p⟩,
    raw.continuous.subtype_mk _⟩
  have hqi : Function.Injective q := by
    intro p r hpr
    have hw : p.1=r.1 := by
      have h := congrArg Prod.fst hpr
      exact h
    have ht := congrArg (fun v : Circle × Time => (v.2 : ℝ)) hpr
    change (g p.1 : ℝ)*(1-(p.2 : ℝ))=(g r.1 : ℝ)*(1-(r.2 : ℝ)) at ht
    rw [← hw] at ht
    have htime : p.2=r.2 := Subtype.ext (by nlinarith [hgpos p.1])
    exact Prod.ext hw htime
  have hrawi : Function.Injective raw := H.symm.injective.comp (hB.injective.comp hqi)
  have hξi : Function.Injective ξ := fun p r hpr =>
    hrawi (congrArg (fun x : A.Remainder => (x : S)) hpr)
  have hξzero (z : Circle) : ξ (z,0)=A.edgePoint k z := by
    apply Subtype.ext
    change raw (z,0) = (A.edgePoint k z : S)
    apply H.injective
    rw [hrawH,← inwardBand_zero A k z,hψ]
    change B (z,g z * unitInterval.symm 0) = B (z,g z)
    simp
  have himage : ξ '' {p : Circle × Time | (p.2 : ℝ) < 1} =
      {x : A.Remainder | H (x : S) ∈ A.removed} := by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩
      change H (raw p) ∈ A.removed
      rw [hrawH,inwardBand_mem_removed]
      refine ⟨?_,(hqle p).trans_lt (hglt p.1)⟩
      change 0 < (g p.1 : ℝ)*(1-(p.2 : ℝ))
      exact mul_pos (hgpos p.1) (sub_pos.mpr hp)
    · intro hx
      change H (x : S) ∈ A.removed at hx
      have hximage : H (x : S) ∈ inwardBand A k ''
          {p : Circle × Time | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1} :=
        (Set.ext_iff.mp (removed_inwardBand A k) (H (x : S))).mp hx
      obtain ⟨v,hv,hvx⟩ := hximage
      have hvle : v.2 ≤ g v.1 := by
        by_contra hvnot
        have hgv : g v.1 < v.2 := lt_of_not_ge hvnot
        have hc : Continuous (fun t : Time => ψ (v.1,t)) :=
          ψ.continuous.comp (continuous_const.prodMk continuous_id)
        have hvimage : v.2 ∈ Set.Icc (ψ (v.1,0)) (ψ (v.1,1)) :=
          ⟨hgv.le,by rw [htop]; exact le_top⟩
        obtain ⟨t,ht,hψt⟩ := intermediate_value_Icc (show (0 : Time)≤1 by norm_num)
          hc.continuousOn hvimage
        change ψ (v.1,t)=v.2 at hψt
        have ht0 : 0 < (t : ℝ) := by
          by_contra ht0
          have htzero : t=0 := Subtype.ext (le_antisymm (le_of_not_gt ht0) t.property.1)
          rw [htzero] at hψt
          exact (ne_of_lt hgv) hψt
        have ht1 : (t : ℝ)<1 := by
          by_contra ht1
          have htone : t=1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt ht1))
          rw [htone,htop] at hψt
          exact (ne_of_lt hv.2) (congrArg (fun s : Time => (s : ℝ)) hψt.symm)
        have hxt : (x : S)=B (v.1,t) := H.injective (by
          rw [hψ,hψt]
          exact hvx.symm)
        have hxremoved : (x : S) ∈ A.removed := by
          rw [hxt,inwardBand_mem_removed]
          exact ⟨ht0,ht1⟩
        exact x.property hxremoved
      let t : Time := ⟨1-(v.2 : ℝ)/(g v.1 : ℝ),by
        have hdiv : (v.2 : ℝ)/(g v.1 : ℝ)≤1 :=
          (div_le_one (hgpos v.1)).mpr hvle
        linarith,by
        have hdiv : 0≤(v.2 : ℝ)/(g v.1 : ℝ) :=
          div_nonneg v.2.property.1 (hgpos v.1).le
        linarith⟩
      have htlt : (t : ℝ)<1 := by
        dsimp [t]
        linarith [div_pos hv.1 (hgpos v.1)]
      have hqt : q (v.1,t)=v := by
        apply Prod.ext
        · rfl
        apply Subtype.ext
        change (g v.1 : ℝ)*(1-(1-(v.2 : ℝ)/(g v.1 : ℝ)))=(v.2 : ℝ)
        field_simp [(hgpos v.1).ne']
        ring
      refine ⟨(v.1,t),htlt,?_⟩
      apply Subtype.ext
      apply H.injective
      change H (raw (v.1,t))=H (x : S)
      rw [hrawH,hqt]
      exact hvx
  refine ⟨ξ,(ξ.continuous.isClosedEmbedding hξi).isEmbedding,hξzero,?_⟩
  rw [himage]
  exact A.open_middle.preimage (H.continuous.comp continuous_subtype_val)



end CompressionOriginalAnnulusNativeExteriorV835


open scoped Manifold ContDiff BigOperators
open Set Topology TopologicalSpace
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000

namespace CompressionOriginalAnnulusTopologySupportV835

variable {S : CompactOrientedSurface.{0}} {M : Type}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  {f : NeatEmbedding S M} {D : InteriorCompressingDisk f} (A : CompressionAnnulus D)

private lemma dense_open_time :
    closure {p : Circle × Time | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1} = univ := by
  have hne : (0 : Time) ≠ 1 := by
    intro h
    have := congrArg (fun t : Time => (t : ℝ)) h
    norm_num at this
  have htime : closure (Ioo (0 : Time) 1) = univ := by
    rw [closure_Ioo hne, ← unitInterval.univ_eq_Icc]
  have hset : {p : Circle × Time | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1} =
      (univ : Set Circle) ×ˢ Ioo (0 : Time) 1 := by
    ext p
    simp only [mem_ofPred_eq, mem_prod, mem_univ, true_and, mem_Ioo]
    exact Iff.rfl
  rw [hset]
  rw [closure_prod_eq, closure_univ, htime, univ_prod_univ]

private lemma closure_removed_eq_range : closure A.removed = range A.band := by
  apply subset_antisymm
  · exact closure_minimal (image_subset_range _ _) (CompressionActualNativeOriginalCollarSupportV838.band_closed A)
  · rw [← image_univ, ← dense_open_time]
    exact image_closure_subset_closure_image A.band.continuous

private lemma band_edge_ranges_disjoint :
    Disjoint (range (fun z => (A.edgePoint 0 z : S)))
      (range (fun z => (A.edgePoint 1 z : S))) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨z,hz⟩ ⟨w,hw⟩
  have h := A.embedded.injective (hz.trans hw.symm)
  have ht := congrArg Prod.snd h
  simp [CompressionAnnulus.sideTime] at ht

private lemma band_difference_removed :
    range A.band \ A.removed =
      range (fun z => (A.edgePoint 0 z : S)) ∪
      range (fun z => (A.edgePoint 1 z : S)) := by
  ext x
  constructor
  · rintro ⟨⟨⟨z,t⟩,rfl⟩,hx⟩
    have ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1 := by
      by_contra h
      push Not at h
      exact hx ⟨(z,t),⟨lt_of_le_of_ne t.property.1 h.1.symm,
        lt_of_le_of_ne t.property.2 h.2⟩,rfl⟩
    rcases ht with ht | ht
    · left
      refine ⟨z,?_⟩
      have hzero : t = 0 := Subtype.ext ht
      simp [CompressionAnnulus.edgePoint,CompressionAnnulus.sideTime,hzero]
    · right
      refine ⟨z,?_⟩
      have hone : t = 1 := Subtype.ext ht
      simp [CompressionAnnulus.edgePoint,CompressionAnnulus.sideTime,hone]
  · rintro (⟨z,rfl⟩ | ⟨z,rfl⟩)
    · exact ⟨⟨(z,CompressionAnnulus.sideTime 0),rfl⟩,(A.edgePoint 0 z).property⟩
    · exact ⟨⟨(z,CompressionAnnulus.sideTime 1),rfl⟩,(A.edgePoint 1 z).property⟩

private lemma frontier_removed_eq_edges :
    frontier A.removed =
      range (fun z => (A.edgePoint 0 z : S)) ∪
      range (fun z => (A.edgePoint 1 z : S)) := by
  have hInt : interior A.removed = A.removed := A.open_middle.interior_eq
  rw [frontier, closure_removed_eq_range A, hInt, band_difference_removed A]

private lemma frontier_remainder_eq_edges :
    frontier A.removedᶜ =
      range (fun z => (A.edgePoint 0 z : S)) ∪
      range (fun z => (A.edgePoint 1 z : S)) := by
  rw [frontier_compl,frontier_removed_eq_edges A]

private lemma separated_edge_neighborhoods :
    ∃ U : Fin 2 → Set S,
      (∀ k, IsOpen (U k)) ∧
      (∀ k, range (fun z => (A.edgePoint k z : S)) ⊆ U k) ∧
      Disjoint (closure (U 0)) (closure (U 1)) ∧
      ∀ k, Disjoint (closure (U k)) S.boundary := by
  have hc (k : Fin 2) : IsClosed (range (fun z => (A.edgePoint k z : S))) :=
    (isCompact_range (continuous_subtype_val.comp
      (CompressionActualNativeOriginalCollarSupportV838.edgePoint_continuous A k))).isClosed
  obtain ⟨V0,V1,hV0,hV1,h0,h1,hV⟩ := normal_separation (hc 0) (hc 1)
    (band_edge_ranges_disjoint A)
  obtain ⟨B,hB,hAB,hBS⟩ := CompressionActualNativeOriginalCollarSupportV838.exists_band_neighborhood_away_boundary A
  have he (k : Fin 2) : range (fun z => (A.edgePoint k z : S)) ⊆ B := by
    rintro x ⟨z,rfl⟩
    exact hAB ⟨(z,CompressionAnnulus.sideTime k),rfl⟩
  obtain ⟨U0,hU0,h0U,hU0V⟩ := normal_exists_closure_subset (hc 0)
    (hV0.inter hB) (subset_inter h0 (he 0))
  obtain ⟨U1,hU1,h1U,hU1V⟩ := normal_exists_closure_subset (hc 1)
    (hV1.inter hB) (subset_inter h1 (he 1))
  let U : Fin 2 → Set S := fun k => if k = 0 then U0 else U1
  refine ⟨U,?_,?_,?_,?_⟩
  · intro k
    fin_cases k <;> simp [U,hU0,hU1]
  · intro k
    fin_cases k <;> simpa [U] using (show range (fun z => (A.edgePoint _ z : S)) ⊆ _ from
      (by first | exact h0U | exact h1U))
  · simpa [U] using hV.mono (hU0V.trans inter_subset_left)
      (hU1V.trans inter_subset_left)
  · intro k
    have h0S : Disjoint (closure U0) S.boundary :=
      hBS.mono_left ((hU0V.trans inter_subset_right).trans subset_closure)
    have h1S : Disjoint (closure U1) S.boundary :=
      hBS.mono_left ((hU1V.trans inter_subset_right).trans subset_closure)
    fin_cases k <;> simpa [U] using (show Disjoint (closure _) S.boundary from
      (by first | exact h0S | exact h1S))

private lemma uniform_time_neighborhood (ξ : C(Circle × Time, A.Remainder))
    (U : Set S) (hU : IsOpen U)
    (h0 : ∀ z, (ξ (z,0) : S) ∈ U) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      ∀ p : Circle × Time, (p.2 : ℝ) ≤ a → (ξ p : S) ∈ U := by
  have hpre : IsOpen ((fun p : Circle × Time => (ξ p : S)) ⁻¹' U) :=
    hU.preimage (continuous_subtype_val.comp ξ.continuous)
  have hbase : (univ : Set Circle) ×ˢ ({0} : Set Time) ⊆
      (fun p : Circle × Time => (ξ p : S)) ⁻¹' U := by
    rintro ⟨z,t⟩ ⟨_,ht⟩
    have ht0 : t = 0 := ht
    simpa [ht0] using h0 z
  obtain ⟨V,W,_,hW,hV,h0W,hVW⟩ := generalized_tube_lemma isCompact_univ
    isCompact_singleton hpre hbase
  have hW0 : W ∈ 𝓝 (0 : Time) := hW.mem_nhds (h0W (by simp))
  have h01 : (0 : Time) < 1 := by
    change (0 : ℝ) < 1
    exact zero_lt_one
  obtain ⟨b,hb,hbW⟩ := exists_Ico_subset_of_mem_nhds hW0 ⟨1,h01⟩
  have hbpos : (0 : ℝ) < b := hb
  refine ⟨(b : ℝ)/2,half_pos hbpos,?_,?_⟩
  · linarith [b.property.2]
  · intro p hp
    apply hVW
    exact ⟨hV (mem_univ _),hbW ⟨p.2.property.1,by
      change (p.2 : ℝ) < b
      linarith⟩⟩

private lemma open_image_of_open_larger_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {g : X → Y} (hg : IsEmbedding g) {U V : Set X}
    (hU : IsOpen U) (hUV : U ⊆ V) (hV : IsOpen (g '' V)) :
    IsOpen (g '' U) := by
  obtain ⟨W,hW,hUW⟩ := hg.isInducing.isOpen_iff.mp hU
  have himage : g '' U = W ∩ (g '' V) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨?_,⟨x,hUV hx,rfl⟩⟩
      rwa [← hUW] at hx
    · rintro ⟨hy,⟨x,hx,rfl⟩⟩
      refine ⟨x,?_,rfl⟩
      rwa [← hUW]
  rw [himage]
  exact hW.inter hV

private lemma shrink_collar (ξ : C(Circle × Time, A.Remainder))
    (hξ : IsEmbedding ξ)
    (hξopen : IsOpen (ξ '' {p : Circle × Time | (p.2 : ℝ) < 1}))
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ ζ : C(Circle × Time, A.Remainder), IsEmbedding ζ ∧
      (∀ z, ζ (z,0) = ξ (z,0)) ∧
      (∀ p : Circle × Time, ∃ q : Circle × Time,
        (q.2 : ℝ) = a * (p.2 : ℝ) ∧ ζ p = ξ q) ∧
      IsOpen (ζ '' {p : Circle × Time | (p.2 : ℝ) < 1}) := by
  let r : Time → Time := fun t => ⟨a * (t : ℝ),
    mul_nonneg ha.le t.property.1,
    (mul_le_mul_of_nonneg_left t.property.2 ha.le).trans (by simpa using ha1.le)⟩
  let R : Circle × Time → Circle × Time := fun p => (p.1,r p.2)
  have hR : Continuous R := by
    apply Continuous.prodMk continuous_fst
    apply Continuous.subtype_mk
    exact continuous_const.mul (continuous_subtype_val.comp continuous_snd)
  let ζ : C(Circle × Time, A.Remainder) := ⟨ξ ∘ R,ξ.continuous.comp hR⟩
  have hinj : Function.Injective ζ := by
    intro p q hpq
    have h := hξ.injective hpq
    have hz := congrArg Prod.fst h
    change p.1 = q.1 at hz
    have ht : a * (p.2 : ℝ) = a * (q.2 : ℝ) :=
      congrArg (fun p : Circle × Time => (p.2 : ℝ)) h
    exact Prod.ext hz (Subtype.ext (mul_left_cancel₀ ha.ne' ht))
  refine ⟨ζ,(ζ.continuous.isClosedEmbedding hinj).isEmbedding,?_,?_,?_⟩
  · intro z
    change ξ (z,r 0) = ξ (z,0)
    congr 2
    apply Subtype.ext
    simp [r]
  · intro p
    exact ⟨R p,rfl,rfl⟩
  · have himage : ζ '' {p : Circle × Time | (p.2 : ℝ) < 1} =
        ξ '' {p : Circle × Time | (p.2 : ℝ) < a} := by
      ext x
      constructor
      · rintro ⟨p,hp,rfl⟩
        exact ⟨R p,(mul_lt_mul_of_pos_left hp ha).trans_eq (mul_one a),rfl⟩
      · rintro ⟨q,hq,rfl⟩
        let t : Time := ⟨(q.2 : ℝ)/a,div_nonneg q.2.property.1 ha.le,
          (div_le_iff₀ ha).mpr (by simpa using hq.le)⟩
        refine ⟨(q.1,t),(div_lt_iff₀ ha).mpr (by simpa using hq),?_⟩
        change ξ (q.1,r t) = ξ q
        congr 1
        exact Prod.ext rfl (Subtype.ext (by dsimp [r,t]; field_simp))
    rw [himage]
    exact open_image_of_open_larger_image hξ
      (isOpen_Iio.preimage (continuous_subtype_val.comp continuous_snd))
      (fun p hp => hp.trans ha1) hξopen

private lemma assemble_disjoint_away_collars
    (ξ : Fin 2 → C(Circle × Time,A.Remainder))
    (hξ : ∀ k, IsEmbedding (ξ k))
    (hξzero : ∀ k z, ξ k (z,0) = A.edgePoint k z)
    (hξopen : ∀ k, IsOpen ((ξ k) '' {p : Circle × Time | (p.2 : ℝ) < 1})) :
    ∃ κ : Fin 2 → C(Circle × Time,A.Remainder),
      (∀ k, IsEmbedding (κ k)) ∧
      (∀ k z, κ k (z,0) = A.edgePoint k z) ∧
      (∀ k p, 0 < (p.2 : ℝ) → (κ k p : S) ∉ range A.band) ∧
      (∀ k, IsOpen ((κ k) '' {p : Circle × Time | (p.2 : ℝ) < 1})) ∧
      Disjoint (range (κ 0)) (range (κ 1)) ∧
      ∀ k, range (fun p : Circle × Time => (κ k p : S)) ⊆ S.boundaryᶜ := by
  obtain ⟨U,hU,hEU,hdis,haway⟩ := separated_edge_neighborhoods A
  have hzero (k : Fin 2) (z : Circle) : (ξ k (z,0) : S) ∈ U k := by
    rw [hξzero]
    exact hEU k ⟨z,rfl⟩
  choose a ha ha1 hsmall using fun k => uniform_time_neighborhood A (ξ k) (U k) (hU k) (hzero k)
  choose κ hκ hκzero hκresize hκopen using fun k => shrink_collar A (ξ k)
    (hξ k) (hξopen k) (a k) (ha k) (ha1 k)
  have hκU (k : Fin 2) (p : Circle × Time) : (κ k p : S) ∈ U k := by
    obtain ⟨q,hqt,hq⟩ := hκresize k p
    rw [hq]
    exact hsmall k q (hqt.le.trans (by nlinarith [p.2.property.2,ha k]))
  have hstart (k : Fin 2) (z : Circle) : κ k (z,0) = A.edgePoint k z :=
    (hκzero k z).trans (hξzero k z)
  have hself (k : Fin 2) (p : Circle × Time) (hp : 0 < (p.2 : ℝ)) :
      (κ k p : S) ∉ range (fun z => (A.edgePoint k z : S)) := by
    rintro ⟨z,hz⟩
    have heq : κ k p = A.edgePoint k z := Subtype.ext hz.symm
    rw [← hstart] at heq
    have htime := congrArg (fun p : Circle × Time => (p.2 : ℝ)) ((hκ k).injective heq)
    exact hp.ne' htime
  refine ⟨κ,hκ,?_,?_,hκopen,?_,?_⟩
  · exact hstart
  · intro k p hp
    intro hband
    have he : (κ k p : S) ∈ range (fun z => (A.edgePoint 0 z : S)) ∪
        range (fun z => (A.edgePoint 1 z : S)) :=
      (band_difference_removed A).subset ⟨hband,(κ k p).property⟩
    fin_cases k
    · rcases he with he | he
      · exact hself 0 p hp he
      · exact Set.disjoint_left.mp hdis (subset_closure (hκU 0 p))
          (subset_closure (hEU 1 he))
    · rcases he with he | he
      · exact Set.disjoint_left.mp hdis (subset_closure (hEU 0 he))
          (subset_closure (hκU 1 p))
      · exact hself 1 p hp he
  · apply Set.disjoint_left.mpr
    rintro x ⟨p,hp⟩ ⟨q,hq⟩
    have h0 : (x : S) ∈ closure (U 0) := subset_closure (hp ▸ hκU 0 p)
    have h1 : (x : S) ∈ closure (U 1) := subset_closure (hq ▸ hκU 1 q)
    exact Set.disjoint_left.mp hdis h0 h1
  · intro k x hx
    rcases hx with ⟨p,rfl⟩
    exact Set.disjoint_left.mp (haway k) (subset_closure (hκU k p))

end CompressionOriginalAnnulusTopologySupportV835

theorem original_compression_annulus_outside_collars_v835
    {S : CompactOrientedSurface.{0}} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    {f : NeatEmbedding S M} {D : InteriorCompressingDisk f}
    (A : CompressionAnnulus D) :
    ∃ κ : Fin 2 → C(Circle × Time, A.Remainder),
      (∀ k, IsEmbedding (κ k)) ∧
      (∀ k z, κ k (z, 0) = A.edgePoint k z) ∧
      (∀ k p, 0 < (p.2 : ℝ) → (κ k p : S) ∉ Set.range A.band) ∧
      (∀ k, IsOpen ((κ k) '' {p : Circle × Time | (p.2 : ℝ) < 1})) ∧
      Disjoint (Set.range (κ 0)) (Set.range (κ 1)) ∧
      ∀ k, Set.range (fun p : Circle × Time => (κ k p : S)) ⊆ S.boundaryᶜ := by
  classical
  choose ξ hξ hzero hopen using fun k : Fin 2 =>
    CompressionOriginalAnnulusNativeExteriorV835.annulus_raw_outside_collar A k
  exact CompressionOriginalAnnulusTopologySupportV835.assemble_disjoint_away_collars A ξ hξ hzero hopen

#print axioms original_compression_annulus_outside_collars_v835
