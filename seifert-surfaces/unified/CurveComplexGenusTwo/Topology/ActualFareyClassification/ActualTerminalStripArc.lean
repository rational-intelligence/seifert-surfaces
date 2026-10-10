import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTerminalFiberCrossing

open Set Topology Schoenflies CurveComplex

/-- The actual one-crossing terminal source constructs a fundamental source
arc with its WHOLE open parameter interior strictly in the reference strip.
No strip-containment or fundamental-crosscut certificate is supplied. -/
theorem actual_single_fiber_source_has_strict_fundamental_strip_arc
    (G : C(ℝ,Plane)) (T c r : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hFiber : {t : ℝ | G t 0=c}={r}) :
    G r 0=c ∧ G (r+T)=G r+Plane.mk T 0 ∧
      ∀ t∈Ioo r (r+T), c<G t 0 ∧ G t 0<c+T := by
  have hr : G r 0=c := (show r∈{t : ℝ | G t 0=c} from hFiber.symm ▸ mem_singleton r)
  have hEnd : G (r+T)=G r+Plane.mk T 0 := by simpa using hp 1 r
  have hRight : G (r+T) 0=c+T := by rw [hEnd]; change G r 0+T=c+T; rw [hr]
  have hC (x : ℝ) (hx : G x 0=c) : x=r :=
    (show x∈({r} : Set ℝ) from hFiber ▸ (show x∈{t : ℝ | G t 0=c} from hx))
  have hCT (x : ℝ) (hx : G x 0=c+T) : x=r+T := by
    have hShift := hp (-1) x
    have hu : G (x-T) 0=c := by
      have hh : G (x-T)=G x+Plane.mk (-T) 0 := by simpa [sub_eq_add_neg] using hShift
      rw [hh]
      change G x 0+-T=c
      linarith
    have hh := hC (x-T) hu
    linarith
  have hCont : Continuous (fun x : ℝ => G x 0) := by fun_prop
  refine ⟨hr,hEnd,?_⟩
  intro t ht
  constructor
  · by_contra hn
    have htc : G t 0 ≤ c := le_of_not_gt hn
    obtain ⟨u,hu,huc⟩ := intermediate_value_Icc ht.2.le hCont.continuousOn ⟨htc,hRight ▸ (by linarith : c ≤ c+T)⟩
    have hur := hC u huc
    linarith [hu.1,ht.1]
  · by_contra hn
    have hct : c+T ≤ G t 0 := le_of_not_gt hn
    obtain ⟨u,hu,huc⟩ := intermediate_value_Icc ht.1.le hCont.continuousOn
      ⟨hr ▸ (by linarith : c ≤ c+T),hct⟩
    have hur := hCT u huc
    linarith [hu.2,ht.2]

/-- The actual terminal single-fiber source produces its straight VERTICAL
adjacent-row connector with open interior avoiding the ENTIRE lifted family. -/
theorem actual_single_fiber_source_has_actual_vertical_adjacent_connector
    (G : C(ℝ,Plane)) (T c r : ℝ) (hT : 0<T)
    (hFiber : {t : ℝ | G t 0=c}={r}) :
    ∀ t∈Ioo (0:ℝ) 1, AffineMap.lineMap (G r) (G r+Plane.mk 0 T) t∉
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) := by
  have hr : G r 0=c := (show r∈{t : ℝ | G t 0=c} from hFiber.symm ▸ mem_singleton r)
  intro t ht hz
  obtain ⟨j,x,hx⟩ := mem_iUnion.mp hz
  change G x+Plane.mk 0 ((j:ℝ)*T)=AffineMap.lineMap (G r) (G r+Plane.mk 0 T) t at hx
  have hx0 : G x 0=c := by
    have hh := congrArg (fun z : Plane => z 0) hx
    simp [AffineMap.lineMap_apply,Plane.mk,hr] at hh
    linarith
  have hxr : x=r := (show x∈({r} : Set ℝ) from hFiber ▸ (show x∈{t : ℝ | G t 0=c} from hx0))
  subst x
  have hh := congrArg (fun z : Plane => z 1) hx
  simp [AffineMap.lineMap_apply,Plane.mk] at hh
  have hj : (j:ℝ)=t := by nlinarith
  have hjPos : 0<j := by exact_mod_cast (hj ▸ ht.1)
  have hjLt : j<1 := by exact_mod_cast (hj ▸ ht.2)
  omega

#print axioms actual_single_fiber_source_has_strict_fundamental_strip_arc
#print axioms actual_single_fiber_source_has_actual_vertical_adjacent_connector
