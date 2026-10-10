import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChart
import Schoenflies.Topology
import Schoenflies.PolyArcRealize
import Schoenflies.BoundaryContinuity2
import CurveComplexGenusTwo.Topology.TopologicalArcJoin
import CurveComplexGenusTwo.Topology.GeometricPosition.ArcLocalAffine

open Set Schoenflies
namespace CurveComplex
/-- A proper source-square crosscut can be redrawn so that every contact with
an old coordinate axis is an actual affine crossing in the OLD chart. Boundary
endpoints remain exact and stay off that axis. -/
theorem position_proper_affine_crosscut
    (E : OpenPartialHomeomorph Schoenflies.Plane Schoenflies.Plane)
    (hSquare : Schoenflies.Plane.closedSquare 0 1 ⊆ E.source)
    (ha : E (Schoenflies.Plane.mk (-1) 0) 0 ≠ 0)
    (hb : E (Schoenflies.Plane.mk 1 0) 0 ≠ 0) :
    ∃ B : Set Schoenflies.Plane,
      Schoenflies.IsArcBetween B (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) ∧
      B \ {Schoenflies.Plane.mk (-1) 0, Schoenflies.Plane.mk 1 0} ⊆
        Schoenflies.Plane.openSquare 0 1 ∧
      ((E '' B) ∩ {z : Schoenflies.Plane | z 0 = 0}).Finite ∧
      (∀ p ∈ (E '' B) ∩ {z : Schoenflies.Plane | z 0 = 0},
        ∃ W : Set Schoenflies.Plane, IsOpen W ∧ p ∈ W ∧ W ⊆ E.target ∧
        ∃ m : ℝ, ∀ z ∈ W,
          (z ∈ E '' B ↔ z 1 = p 1 + m * z 0)) := by
  classical
  have hsegmentLine (x y p : Plane) (hx : x 0 ≠ 0)
      (hp : p ∈ segment ℝ x y) (hp0 : p 0 = 0) :
      ∃ m : ℝ, ∀ z ∈ segment ℝ x y, z 1 = p 1 + m * z 0 := by
    rw [segment_eq_image_lineMap] at hp
    obtain ⟨s, hs, hsp⟩ := hp
    have hpcoord (i : Fin 2) : p i = (1-s) * x i + s * y i := by
      rw [← hsp]
      simp [AffineMap.lineMap_apply_module]
    have hxy : y 0 - x 0 ≠ 0 := by
      intro h
      have hh := hpcoord 0
      have hyx := sub_eq_zero.mp h
      rw [hyx, hp0] at hh
      exact hx (by nlinarith)
    refine ⟨(y 1 - x 1) / (y 0 - x 0), ?_⟩
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t, ht, htz⟩ := hz
    have hzcoord (i : Fin 2) : z i = (1-t) * x i + t * y i := by
      rw [← htz]
      simp [AffineMap.lineMap_apply_module]
    rw [hzcoord 0, hzcoord 1, hpcoord 1]
    have hh := hpcoord 0
    rw [hp0] at hh
    field_simp
    nlinarith [congrArg (fun a : ℝ => a * (y 1-x 1)) hh]
  have hsegmentFinite (x y : Plane) (hx : x 0 ≠ 0) :
      (segment ℝ x y ∩ {z : Plane | z 0 = 0}).Finite := by
    apply Set.Subsingleton.finite
    intro p hp q hq
    rw [segment_eq_image_lineMap] at hp hq
    obtain ⟨s, hs, hsp⟩ := hp.1
    obtain ⟨t, ht, htq⟩ := hq.1
    have hcoord : ∀ u : ℝ, (AffineMap.lineMap x y u) 0 =
        (1-u) * x 0 + u * y 0 := by
      intro u
      simp [AffineMap.lineMap_apply_module]
    have hps : (1-s) * x 0 + s * y 0 = 0 := by
      rw [← hcoord, hsp]; exact hp.2
    have hqt : (1-t) * x 0 + t * y 0 = 0 := by
      rw [← hcoord, htq]; exact hq.2
    have hxy : y 0 - x 0 ≠ 0 := by
      intro h
      have hh := sub_eq_zero.mp h
      rw [hh] at hps
      exact hx (by nlinarith)
    have hst : s = t := by
      have hh : (s-t) * (y 0-x 0) = 0 := by nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hxy)
    rw [← hsp, ← htq, hst]
  have hpolyFinite (n : ℕ) (Q : PreArc n)
      (hvertex : ∀ i ≤ n+1, Q.vertex i 0 ≠ 0) :
      (Q.carrier ∩ {z : Plane | z 0 = 0}).Finite := by
    have hf : (⋃ i ∈ Finset.range (n+1),
        Q.edge i ∩ {z : Plane | z 0 = 0}).Finite := by
      exact Set.Finite.biUnion (Finset.range (n+1)).finite_toSet
        (fun i hi => hsegmentFinite (Q.vertex i) (Q.vertex (i+1))
          (hvertex i (by have hh := Finset.mem_range.mp hi; omega)))
    apply hf.subset
    intro p hp
    obtain ⟨i, hi, hpi⟩ := PreArc.mem_carrier_iff.mp hp.1
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr (by omega), hpi, hp.2⟩
  have hsmallShift (n : ℕ) (Q : PreArc n) (δ : ℝ) (hδ : 0 < δ) :
      ∃ t ∈ Ioo (0 : ℝ) δ, ∀ i ≤ n+1, Q.vertex i 0 + t ≠ 0 := by
    let bad : Set ℝ := (fun i : ℕ => -(Q.vertex i 0)) ''
      ((Finset.range (n+2) : Finset ℕ) : Set ℕ)
    have hbad : bad.Finite := (Finset.range (n+2)).finite_toSet.image _
    have hex : ∃ t ∈ Ioo (0 : ℝ) δ, t ∉ bad := by
      by_contra h
      have hsub : Ioo (0 : ℝ) δ ⊆ bad := by
        intro t ht
        by_contra hb
        exact h ⟨t, ht, hb⟩
      exact Set.Ioo_infinite hδ (hbad.subset hsub)
    obtain ⟨t, ht, htb⟩ := hex
    refine ⟨t, ht, ?_⟩
    intro i hi heq
    apply htb
    refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
    dsimp
    linarith
  have htranslate (n : ℕ) (Q : PreArc n) (v : Plane) :
      ∃ R : PreArc n, (∀ i, R.vertex i = v + Q.vertex i) ∧
        R.carrier = (fun z => v + z) '' Q.carrier := by
    let R : PreArc n := {
      vertex := fun i => v + Q.vertex i
      vertex_inj := fun i j h => Q.vertex_inj (add_left_cancel h)
      edges_meet := by
        intro i hi j hj hij p hp
        rw [← segment_translate_image ℝ v (Q.vertex i) (Q.vertex (i+1))] at hp
        rw [← segment_translate_image ℝ v (Q.vertex j) (Q.vertex (j+1))] at hp
        obtain ⟨x, hx, hxp⟩ := hp.1
        obtain ⟨y, hy, hyp⟩ := hp.2
        have hxy : x = y := add_left_cancel (hxp.trans hyp.symm)
        have hh := Q.edges_meet i hi j hj hij ⟨hx, hxy ▸ hy⟩
        rcases Set.mem_insert_iff.mp hh with hh | hh
        · exact Set.mem_insert_iff.mpr (Or.inl (by rw [← hxp, hh]))
        · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr
            (by rw [← hxp, Set.mem_singleton_iff.mp hh]))) }
    refine ⟨R, fun _ => rfl, ?_⟩
    ext p
    constructor
    · intro hp
      obtain ⟨i, hi, hpi⟩ := PreArc.mem_carrier_iff.mp hp
      change p ∈ segment ℝ (v + Q.vertex i) (v + Q.vertex (i+1)) at hpi
      rw [← segment_translate_image ℝ] at hpi
      obtain ⟨x, hx, hxp⟩ := hpi
      exact ⟨x, PreArc.mem_carrier_iff.mpr ⟨i,hi,hx⟩,hxp⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, hi, hxi⟩ := PreArc.mem_carrier_iff.mp hx
      apply PreArc.mem_carrier_iff.mpr
      refine ⟨i,hi,?_⟩
      change v+x ∈ segment ℝ (v + Q.vertex i) (v + Q.vertex (i+1))
      rw [← segment_translate_image ℝ]
      exact ⟨x,hxi,rfl⟩
  have hregular (n : ℕ) (Q : PreArc n)
      (hvertex : ∀ i ≤ n+1, Q.vertex i 0 ≠ 0) :
      ∀ p ∈ Q.carrier ∩ {z : Plane | z 0 = 0},
        ∃ W : Set Plane, IsOpen W ∧ p ∈ W ∧
        ∃ m : ℝ, ∀ z ∈ Q.carrier ∩ W, z 1 = p 1 + m * z 0 := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := PreArc.mem_carrier_iff.mp hp.1
    let other : Set Plane := ⋃ j ∈ (Finset.range (n+1)).erase i, Q.edge j
    have hotherClosed : IsClosed other := isClosed_biUnion_finset (fun j hj =>
      (isArcBetween_segment Q.vertex_ne).isArc.isCompact.isClosed)
    have hpother : p ∉ other := by
      intro h
      obtain ⟨j, hj, hpj⟩ := Set.mem_iUnion₂.mp h
      have hjn : j ≤ n := by have hh := Finset.mem_range.mp (Finset.mem_of_mem_erase hj); omega
      have hij : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
      have hend := Q.edges_meet i hi j hjn hij ⟨hpi,hpj⟩
      rcases Set.mem_insert_iff.mp hend with h | h
      · exact hvertex i (by omega) (h ▸ hp.2)
      · have hh : p = Q.vertex (i+1) := Set.mem_singleton_iff.mp h
        exact hvertex (i+1) (by omega) (hh ▸ hp.2)
    obtain ⟨m, hm⟩ := hsegmentLine (Q.vertex i) (Q.vertex (i+1)) p
      (hvertex i (by omega)) hpi hp.2
    refine ⟨otherᶜ, hotherClosed.isOpen_compl, hpother, m, ?_⟩
    intro z hz
    obtain ⟨j, hj, hzj⟩ := PreArc.mem_carrier_iff.mp hz.1
    by_cases hij : j = i
    · subst j
      exact hm z hzj
    · exact (hz.2 (Set.mem_iUnion₂.mpr ⟨j,
        Finset.mem_erase.mpr ⟨hij, Finset.mem_range.mpr (by omega)⟩, hzj⟩)).elim
  have hgeneralPolygon (n : ℕ) (Q : PreArc n) (D : Set Plane)
      (hQcompact : IsCompact Q.carrier) (hD : IsOpen D)
      (hQD : Q.carrier ⊆ D) (ε : ℝ) (hε : 0 < ε) :
      ∃ (t : ℝ) (R : PreArc n), 0 < t ∧ t < ε ∧
        (∀ i, R.vertex i = Plane.mk t 0 + Q.vertex i) ∧
        R.carrier = (fun z => Plane.mk t 0 + z) '' Q.carrier ∧
        R.carrier ⊆ D ∧
        (R.carrier ∩ {z : Plane | z 0 = 0}).Finite ∧
        (∀ p ∈ R.carrier ∩ {z : Plane | z 0 = 0},
          ∃ W : Set Plane, IsOpen W ∧ p ∈ W ∧
          ∃ m : ℝ, ∀ z ∈ R.carrier ∩ W, z 1 = p 1 + m * z 0) := by
    obtain ⟨δ, hδ, hthick⟩ := hQcompact.exists_thickening_subset_open hD hQD
    obtain ⟨t, ht, htv⟩ := hsmallShift n Q (min δ ε) (lt_min hδ hε)
    obtain ⟨R, hRv, hRc⟩ := htranslate n Q (Plane.mk t 0)
    have hvertex : ∀ i ≤ n+1, R.vertex i 0 ≠ 0 := by
      intro i hi
      rw [hRv]
      simpa [Plane.mk, add_comm] using htv i hi
    refine ⟨t,R,ht.1,ht.2.trans_le (min_le_right _ _),hRv,hRc,?_,hpolyFinite n R hvertex,hregular n R hvertex⟩
    intro z hz
    apply hthick
    rw [hRc] at hz
    obtain ⟨x,hx,rfl⟩ := hz
    apply Metric.mem_thickening_iff.mpr
    refine ⟨x,hx,?_⟩
    rw [dist_eq_norm, add_sub_cancel_right]
    have hn : ‖Plane.mk t 0‖ = t := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, Plane.mk, ht.1.le]
    rw [hn]
    exact ht.2.trans_le (min_le_left _ _)
  let g : ℝ → Plane := fun t => Plane.mk (2*t-1) 0
  have hg : Continuous g := by
    unfold g
    exact PiLp.continuous_toLp 2 _ |>.comp
      (continuous_pi (fun i => by fin_cases i <;> simp <;> fun_prop))
  have hgSquare (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      g t ∈ Plane.closedSquare 0 1 := by
    change Plane.supDist (g t) 0 ≤ 1
    simp only [g, Plane.supDist, Plane.supNorm, Plane.mk, sub_zero, max_le_iff]
    constructor
    · change |2*t-1| ≤ 1
      rw [abs_le]; constructor <;> linarith [ht.1,ht.2]
    · norm_num
  have hgOpen (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      g t ∈ Plane.openSquare 0 1 := by
    rw [Plane.mem_openSquare_iff]
    intro i
    fin_cases i
    · simp only [g, PiLp.zero_apply, sub_zero]
      change |2*t-1| < 1
      rw [abs_lt]; constructor <;> linarith [ht.1,ht.2]
    · norm_num [g,Plane.mk]
  let D : Set Plane := E '' Plane.openSquare 0 1
  have hOpenSource : Plane.openSquare 0 1 ⊆ E.source :=
    (Plane.openSquare_subset_closedSquare 0 1).trans hSquare
  have hDopen : IsOpen D := E.isOpen_image_of_subset_source
    (Plane.isOpen_openSquare 0 1) hOpenSource
  have hDconn : IsPreconnected D := (Plane.convex_openSquare 0 1).isPreconnected.image
    E (E.continuousOn.mono hOpenSource)
  let f : ℝ → Plane := fun t => E (g t)
  have hfcont : ContinuousOn f (Icc (0 : ℝ) 1) :=
    E.continuousOn.comp hg.continuousOn (fun t ht => hSquare (hgSquare t ht))
  have hfinj : Set.InjOn f (Icc (0 : ℝ) 1) := by
    intro s hs t ht h
    have hh := E.injOn (hSquare (hgSquare s hs)) (hSquare (hgSquare t ht)) h
    have hh0 := congrArg (fun z : Plane => z 0) hh
    change 2*s-1 = 2*t-1 at hh0
    linarith
  have hfD (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : f t ∈ D :=
    ⟨g t,hgOpen t ht,rfl⟩
  have hf0 : f 0 = E (Plane.mk (-1) 0) := by simp [f,g]
  have hf1 : f 1 = E (Plane.mk 1 0) := by norm_num [f,g]
  let O : Set Plane := {z | z 0 ≠ 0}
  have hOopen : IsOpen O := isOpen_ne.preimage (Plane.continuous_coord 0)
  have hfc0 : ContinuousAt f 0 :=
    (E.continuousAt (hSquare (hgSquare 0 (by simp)))).comp hg.continuousAt
  have hfc1 : ContinuousAt f 1 :=
    (E.continuousAt (hSquare (hgSquare 1 (by simp)))).comp hg.continuousAt
  have h0near : f ⁻¹' O ∈ nhds (0 : ℝ) :=
    hfc0.preimage_mem_nhds (hOopen.mem_nhds (by simpa [O,hf0] using ha))
  have h1near : f ⁻¹' O ∈ nhds (1 : ℝ) :=
    hfc1.preimage_mem_nhds (hOopen.mem_nhds (by simpa [O,hf1] using hb))
  obtain ⟨ε0,hε0,h0ball⟩ := Metric.mem_nhds_iff.mp h0near
  obtain ⟨ε1,hε1,h1ball⟩ := Metric.mem_nhds_iff.mp h1near
  let η : ℝ := min ε0 (min ε1 1) / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hη0 : η < ε0 := by dsimp [η]; linarith [min_le_left ε0 (min ε1 1)]
  have hη1 : η < ε1 := by
    have hh := (min_le_right ε0 (min ε1 1)).trans (min_le_left ε1 1)
    dsimp [η]; linarith
  have hηquarter : η ≤ 1/4 := by
    have hh := (min_le_right ε0 (min ε1 1)).trans (min_le_right ε1 1)
    dsimp [η]; linarith
  have hcollar0 (t : ℝ) (ht : t ∈ Icc 0 η) : f t ∈ O := by
    apply h0ball
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg ht.1]
    exact ht.2.trans_lt hη0
  have hcollar1 (t : ℝ) (ht : t ∈ Icc (1-η) 1) : f t ∈ O := by
    apply h1ball
    rw [Metric.mem_ball,Real.dist_eq,abs_of_nonpos (by linarith [ht.2])]
    linarith [ht.1,hη1]
  have hηI : η ∈ Ioo (0 : ℝ) 1 := ⟨hη,by linarith⟩
  have hη'I : 1-η ∈ Ioo (0 : ℝ) 1 := ⟨by linarith,hη |> sub_lt_self 1⟩
  have hmidne : f η ≠ f (1-η) := by
    intro h
    have hh := hfinj ⟨hηI.1.le,hηI.2.le⟩ ⟨hη'I.1.le,hη'I.2.le⟩ h
    linarith
  obtain ⟨Q,hQD,hQpoly,hQarc⟩ := exists_simple_arc_of_isPreconnected hDopen hDconn
    (hfD η hηI) (hfD (1-η) hη'I) hmidne
  obtain ⟨n,P,hPc,hP0,hPend⟩ := exists_preArc_of_isArcBetween hQarc hQpoly
  have huO : f η ∈ O := hcollar0 η (by simp; exact hη.le)
  have hvO : f (1-η) ∈ O := hcollar1 (1-η) (by simp; linarith)
  obtain ⟨ρ0,hρ0,hρ0sub⟩ := Metric.isOpen_iff.mp (hDopen.inter hOopen)
    (f η) ⟨hfD η hηI,huO⟩
  obtain ⟨ρ1,hρ1,hρ1sub⟩ := Metric.isOpen_iff.mp (hDopen.inter hOopen)
    (f (1-η)) ⟨hfD (1-η) hη'I,hvO⟩
  obtain ⟨t,R,htpos,htsmall,hRv,hRc,hRD,hRf,hRreg⟩ :=
    hgeneralPolygon n P D (hPc.symm ▸ hQarc.isArc.isCompact) hDopen
      (hPc.symm ▸ hQD) (min ρ0 ρ1) (lt_min hρ0 hρ1)
  let shift : Plane := Plane.mk t 0
  have hshiftnorm : ‖shift‖ = t := by
    simp [shift,EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk,htpos.le]
  have hshiftBall (x : Plane) (ρ : ℝ) (hρ : t < ρ) : shift+x ∈ Metric.ball x ρ := by
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_right,hshiftnorm]
    exact hρ
  have hRarc : IsArcBetween R.carrier (shift+f η) (shift+f (1-η)) := by
    rw [hRc,hPc]
    exact hQarc.image_of_injOn (subset_univ _) (continuous_const.add continuous_id).continuousOn
      (fun _ _ _ _ h => add_left_cancel h)
  have hconn0 : segment ℝ (f η) (shift+f η) ⊆ D ∩ O :=
    ((convex_ball (f η) ρ0).segment_subset
      (Metric.mem_ball_self hρ0)
      (hshiftBall (f η) ρ0 (htsmall.trans_le (min_le_left _ _)))).trans hρ0sub
  have hconn1 : segment ℝ (shift+f (1-η)) (f (1-η)) ⊆ D ∩ O :=
    ((convex_ball (f (1-η)) ρ1).segment_subset
      (hshiftBall (f (1-η)) ρ1 (htsmall.trans_le (min_le_right _ _)))
      (Metric.mem_ball_self hρ1)).trans hρ1sub
  have hconn0ne : f η ≠ shift+f η := by
    intro h
    have hh := congrArg (fun z : Plane => z 0) h
    have hh' : f η 0 = t+f η 0 := by simpa [shift,Plane.mk] using hh
    linarith
  have hconn1ne : shift+f (1-η) ≠ f (1-η) := by
    intro h
    have hh := congrArg (fun z : Plane => z 0) h
    have hh' : t+f (1-η) 0 = f (1-η) 0 := by simpa [shift,Plane.mk] using hh
    linarith
  let L : Set Plane := f '' Icc 0 η
  let T : Set Plane := f '' Icc (1-η) 1
  let K0 : Set Plane := segment ℝ (f η) (shift+f η)
  let K1 : Set Plane := segment ℝ (shift+f (1-η)) (f (1-η))
  have hLarc : IsArcBetween L (f 0) (f η) := by
    simpa [L,uIcc_of_le hη.le] using isArcBetween_subarc_of_injOn_I
      hfcont hfinj (show (0 : ℝ) ∈ unitInterval from by simp) ⟨hηI.1.le,hηI.2.le⟩ (ne_of_lt hη)
  have hTarc : IsArcBetween T (f (1-η)) (f 1) := by
    simpa [T,uIcc_of_le (by linarith : 1-η ≤ 1)] using isArcBetween_subarc_of_injOn_I
      hfcont hfinj ⟨hη'I.1.le,hη'I.2.le⟩ (by simp) (ne_of_lt hη'I.2)
  have hMiddle : ∃ M ⊆ (K0 ∪ R.carrier) ∪ K1,
      IsArcBetween M (f η) (f (1-η)) := by
    by_cases hsame : f η = shift+f (1-η)
    · refine ⟨K1,subset_union_right,?_⟩
      rw [hsame]
      exact isArcBetween_segment hconn1ne
    · obtain ⟨M0,hM0sub,hM0arc⟩ := exists_arc_in_union_of_arcs
        (isArcBetween_segment hconn0ne) hRarc hsame
      obtain ⟨M,hMsub,hMarc⟩ := exists_arc_in_union_of_arcs hM0arc
        (isArcBetween_segment hconn1ne) hmidne
      exact ⟨M,hMsub.trans (union_subset_union hM0sub subset_rfl),hMarc⟩
  obtain ⟨M,hMsub,hMarc⟩ := hMiddle
  have h0v : f 0 ≠ f (1-η) := by
    intro h
    have hh := hfinj (by simp) ⟨hη'I.1.le,hη'I.2.le⟩ h
    linarith [hη'I.1]
  have h01 : f 0 ≠ f 1 := fun h => by
    have hh := hfinj (by simp) (by simp) h
    norm_num at hh
  obtain ⟨C0,hC0sub,hC0arc⟩ := exists_arc_in_union_of_arcs hLarc hMarc h0v
  obtain ⟨C,hCsub,hCarc⟩ := exists_arc_in_union_of_arcs hC0arc hTarc h01
  let bad : Set Plane := (L ∪ K0) ∪ (K1 ∪ T)
  have hCcover : C ⊆ bad ∪ R.carrier := by
    intro z hz
    rcases hCsub hz with hz | hz
    · rcases hC0sub hz with hz | hz
      · exact Or.inl (Or.inl (Or.inl hz))
      · rcases hMsub hz with hz | hz
        · rcases hz with hz | hz
          · exact Or.inl (Or.inl (Or.inr hz))
          · exact Or.inr hz
        · exact Or.inl (Or.inr (Or.inl hz))
    · exact Or.inl (Or.inr (Or.inr hz))
  have hbadO : bad ⊆ O := by
    intro z hz
    rcases hz with (hz | hz) | (hz | hz)
    · obtain ⟨s,hs,rfl⟩ := hz
      exact hcollar0 s hs
    · exact (hconn0 hz).2
    · exact (hconn1 hz).2
    · obtain ⟨s,hs,rfl⟩ := hz
      exact hcollar1 s hs
  have hbadClosed : IsClosed bad :=
    (hLarc.isArc.isCompact.union (isCompact_segment _ _)).union
      ((isCompact_segment _ _).union hTarc.isArc.isCompact) |>.isClosed
  have hCfinite : (C ∩ {z : Plane | z 0 = 0}).Finite := by
    apply hRf.subset
    intro z hz
    rcases hCcover hz.1 with hb | hr
    · exact False.elim (hbadO hb hz.2)
    · exact ⟨hr,hz.2⟩
  have hCproper : C \ {f 0,f 1} ⊆ D := by
    intro z hz
    rcases hCsub hz.1 with hzC | hzT
    · rcases hC0sub hzC with hzL | hzM
      · obtain ⟨s,hs,hsz⟩ := hzL
        have hspos : 0 < s := lt_of_le_of_ne hs.1 (fun h =>
          hz.2 (Or.inl (by rw [← hsz,← h])))
        rw [← hsz]
        exact hfD s ⟨hspos,hs.2.trans_lt hηI.2⟩
      · rcases hMsub hzM with (hzK | hzR) | hzK
        · exact (hconn0 hzK).1
        · exact hRD hzR
        · exact (hconn1 hzK).1
    · obtain ⟨s,hs,hsz⟩ := hzT
      have hslt : s < 1 := lt_of_le_of_ne hs.2 (fun h =>
        hz.2 (Or.inr (by simp [← hsz,h])))
      rw [← hsz]
      exact hfD s ⟨hη'I.1.trans_le hs.1,hslt⟩
  have hCtarget : C ⊆ E.target := by
    intro z hz
    by_cases hze : z ∈ ({f 0,f 1} : Set Plane)
    · rcases hze with rfl | hz
      · exact E.map_source (hSquare (hgSquare 0 (by simp)))
      · rw [Set.mem_singleton_iff.mp hz]
        exact E.map_source (hSquare (hgSquare 1 (by simp)))
    · obtain ⟨x,hx,rfl⟩ := hCproper ⟨hz,hze⟩
      exact E.map_source (hOpenSource hx)
  have hCregular : ∀ p ∈ C ∩ {z : Plane | z 0 = 0},
      ∃ W : Set Plane, IsOpen W ∧ p ∈ W ∧ W ⊆ E.target ∧
      ∃ m : ℝ, ∀ z ∈ W, (z ∈ C ↔ z 1 = p 1 + m*z 0) := by
    intro p hp
    have hp0 : p 0 = 0 := hp.2
    have hpbad : p ∉ bad := fun h => hbadO h hp.2
    have hpR : p ∈ R.carrier := (hCcover hp.1).resolve_left hpbad
    obtain ⟨V,hVo,hpV,m,hm⟩ := hRreg p ⟨hpR,hp.2⟩
    let U := (V ∩ badᶜ) ∩ E.target
    have hUo : IsOpen U := (hVo.inter hbadClosed.isOpen_compl).inter E.open_target
    have hpU : p ∈ U := ⟨⟨hpV,hpbad⟩,hCtarget hp.1⟩
    have hpa : p ≠ f 0 := fun h => ha (by simpa [h,hf0] using hp.2)
    have hpb : p ≠ f 1 := fun h => hb (by simpa [h,hf1] using hp.2)
    obtain ⟨W,hWo,hpW,hWU,hWline⟩ := position_arc_local_affine hCarc hp.1 hpa hpb
      hUo hpU m (by
        intro z hz
        have hzR := (hCcover hz.1).resolve_left hz.2.1.2
        simpa [hp0] using hm z ⟨hzR,hz.2.1.1⟩)
    refine ⟨W,hWo,hpW,fun z hz => (hWU hz).2,m,?_⟩
    intro z hz
    simpa [hp0] using hWline z hz
  let B : Set Plane := E.symm '' C
  have hBimage : E '' B = C := by
    ext z
    constructor
    · rintro ⟨x,⟨y,hy,rfl⟩,rfl⟩
      simpa [E.right_inv (hCtarget hy)] using hy
    · intro hz
      exact ⟨E.symm z,⟨z,hz,rfl⟩,E.right_inv (hCtarget hz)⟩
  have hBsource : B ⊆ E.source := by
    rintro z ⟨x,hx,rfl⟩
    exact E.symm.map_source (hCtarget hx)
  have hB0 : E.symm (f 0) = Plane.mk (-1) 0 := by
    rw [hf0]
    exact E.left_inv (by simpa [g] using hSquare (hgSquare 0 (by simp)))
  have hB1 : E.symm (f 1) = Plane.mk 1 0 := by
    rw [hf1]
    exact E.left_inv (by convert hSquare (hgSquare 1 (by simp)) using 1 <;> norm_num [g])
  have hBarc : IsArcBetween B (Plane.mk (-1) 0) (Plane.mk 1 0) := by
    rw [← hB0,← hB1]
    exact hCarc.image_of_injOn hCtarget E.symm.continuousOn E.symm.injOn
  refine ⟨B,hBarc,?_,by simpa [hBimage] using hCfinite,?_⟩
  · intro z hz
    obtain ⟨x,hx,hxz⟩ := hz.1
    have hxe : x ∉ ({f 0,f 1} : Set Plane) := by
      intro he
      rcases he with he | he
      · apply hz.2
        left
        rw [← hxz,he,hB0]
      · apply hz.2
        right
        rw [← hxz,Set.mem_singleton_iff.mp he,hB1]
        exact Set.mem_singleton _
    obtain ⟨y,hy,hyx⟩ := hCproper ⟨hx,hxe⟩
    have he : E.symm x = y := by rw [← hyx,E.left_inv (hOpenSource hy)]
    rwa [← hxz,he]
  · simpa [hBimage] using hCregular
end CurveComplex
