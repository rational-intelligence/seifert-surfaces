import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualMarkedFiniteDescent

open Set Topology Schoenflies CurveComplex

/-- Actual normalized positive period forces every vertical fiber to be met. -/
theorem actual_periodic_source_meets_every_vertical_fiber
    (G : C(ℝ,Plane)) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0) :
    ∃ x : ℝ, G x 0=c := by
  let k := Int.floor ((c-G 0 0)/T)
  have hfloor : (k:ℝ) ≤ (c-G 0 0)/T := Int.floor_le _
  have hceil : (c-G 0 0)/T < (k:ℝ)+1 :=
    Int.floor_le_iff.mp (show Int.floor ((c-G 0 0)/T) ≤ k from le_rfl)
  have ha : G ((k:ℝ)*T) 0 ≤ c := by
    have hh := hp k 0
    simp only [zero_add] at hh
    rw [hh]
    change G 0 0+(k:ℝ)*T ≤ c
    have hbound := (le_div_iff₀ hT).mp hfloor
    linarith
  have hb : c ≤ G (((k+1:ℤ):ℝ)*T) 0 := by
    have hh := hp (k+1) 0
    simp only [zero_add] at hh
    rw [hh]
    change c ≤ G 0 0+((k+1:ℤ):ℝ)*T
    have hbound := (div_lt_iff₀ hT).mp hceil
    push_cast
    linarith
  have hab : (k:ℝ)*T ≤ ((k+1:ℤ):ℝ)*T := by push_cast; nlinarith
  have hCont : Continuous (fun x : ℝ => G x 0) := by fun_prop
  obtain ⟨x,_,hx⟩ := intermediate_value_Icc hab hCont.continuousOn ⟨ha,hb⟩
  exact ⟨x,hx⟩

/-- Actual terminal finite fiber bound is exactly one crossing, and it
identifies EVERY full-grid crossing parameter with its complete period orbit. -/
theorem actual_terminal_source_has_one_crossing_and_exact_grid_parameters
    (G : C(ℝ,Plane)) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (hcount : {t : ℝ | G t 0=c}.ncard ≤ 1) :
    ∃ r : ℝ, {t : ℝ | G t 0=c}={r} ∧
      {t : ℝ | ∃ i : ℤ, G t 0=c+(i:ℝ)*T}=range (fun i : ℤ => r+(i:ℝ)*T) := by
  obtain ⟨x,hx⟩ := actual_periodic_source_meets_every_vertical_fiber G T c hT hp
  have hPositive : 0<{t : ℝ | G t 0=c}.ncard := (ncard_pos hfinite).mpr ⟨x,hx⟩
  have hOne : {t : ℝ | G t 0=c}.ncard=1 := by omega
  obtain ⟨r,hFiber⟩ := ncard_eq_one.mp hOne
  have hr : G r 0=c := by
    have hh : r∈{t : ℝ | G t 0=c} := hFiber.symm ▸ mem_singleton r
    exact hh
  refine ⟨r,hFiber,?_⟩
  ext t
  constructor
  · rintro ⟨i,hi⟩
    let u := t+((-i:ℤ):ℝ)*T
    have hu : G u 0=c := by
      rw [hp]
      change G t 0+((-i:ℤ):ℝ)*T=c
      push_cast
      linarith
    have hur : u=r := (show u∈({r} : Set ℝ) from hFiber ▸ (show u∈{t : ℝ | G t 0=c} from hu))
    refine ⟨i,?_⟩
    dsimp [u] at hur
    push_cast at hur
    linarith
  · rintro ⟨i,rfl⟩
    refine ⟨i,?_⟩
    rw [hp]
    change G r 0+(i:ℝ)*T=c+(i:ℝ)*T
    rw [hr]

#print axioms actual_periodic_source_meets_every_vertical_fiber
#print axioms actual_terminal_source_has_one_crossing_and_exact_grid_parameters
