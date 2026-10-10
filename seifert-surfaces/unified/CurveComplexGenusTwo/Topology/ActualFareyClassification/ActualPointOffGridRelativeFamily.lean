import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSmallPeriodicBump
import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly

open Set Topology Schoenflies CurveComplex Metric

/-- An actual closed lattice-invariant family permits an equivariant move of
an outside point off the whole reference grid, while fixing the ENTIRE family
for all times. This is a concrete periodic infimum-distance bump, not a supplied
point-motion certificate. -/
theorem actual_outside_point_can_avoid_grid_fixing_family
    (L : Set Plane) (hL : IsClosed L) (T c : ℝ) (hT : 0<T)
    (hInv : ∀ (i : ℤ×ℤ) z,
      z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)∈L ↔ z∈L)
    (p : Plane) (hp : p∉L) :
    ∃ J : AmbientIsotopy Plane,
      (∀ t (i : ℤ×ℤ) z,
        J.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
          J.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t z, z∈L → J.map (t,z)=z) ∧
      (∀ i : ℤ, J.finalMap p 0≠c+(i:ℝ)*T) := by
  classical
  by_cases hpGrid : ∃ i : ℤ, p 0=c+(i:ℝ)*T
  swap
  · refine ⟨AmbientIsotopy.identity Plane,?_,?_,?_⟩
    · intro t i z; rfl
    · intro t z hz; rfl
    · intro i hi; exact hpGrid ⟨i,hi⟩
  obtain ⟨k,hk⟩ := hpGrid
  obtain ⟨R0,hR0,hball⟩ := Metric.isOpen_iff.mp hL.isOpen_compl p hp
  let R := min (R0/2) (T/2)
  have hR : 0<R := by dsimp [R]; positivity
  have hRR0 : R<R0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hRT : R ≤ T/2 := min_le_right _ _
  let delta : ℤ×ℤ→Plane := fun i => Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)
  have hdelta (i j : ℤ×ℤ) : delta (i+j)=delta i+delta j := by
    ext n; fin_cases n <;> simp [delta,Plane.mk,Int.cast_add] <;> ring
  let P := range (fun i : ℤ×ℤ => p+delta i)
  have hPn : P.Nonempty := ⟨p+delta 0,mem_range_self _⟩
  have hpP : p∈P := by refine ⟨0,?_⟩; ext n; fin_cases n <;> simp [delta,Plane.mk]
  have hPtranslate (i : ℤ×ℤ) : (fun z : Plane => z+delta i) '' P=P := by
    apply subset_antisymm
    · rintro z ⟨w,⟨j,rfl⟩,rfl⟩
      refine ⟨j+i,?_⟩
      change p+delta (j+i)=(p+delta j)+delta i
      rw [hdelta]
      abel
    · rintro z ⟨j,rfl⟩
      refine ⟨p+delta (j-i),⟨j-i,rfl⟩,?_⟩
      have hh := hdelta (j-i) i
      rw [sub_add_cancel] at hh
      change (p+delta (j-i))+delta i=p+delta j
      rw [hh]
      abel
  have hdist (i : ℤ×ℤ) (z : Plane) : infDist (z+delta i) P=infDist z P := by
    have hh : infDist (z+delta i) ((fun z : Plane => z+delta i) '' P)=infDist z P :=
      infDist_image (IsometryEquiv.addRight (delta i)).isometry
    rw [hPtranslate i] at hh
    exact hh
  have hfar (z : Plane) (hz : z∈L) : R ≤ infDist z P := by
    apply (le_infDist hPn).mpr
    rintro w ⟨i,rfl⟩
    have hzMinus : z-delta i∈L := by
      apply (hInv i (z-delta i)).mp
      simpa [delta] using hz
    have hAway : R0 ≤ dist (z-delta i) p := by
      by_contra hn
      exact hball (mem_ball.mpr (lt_of_not_ge hn)) hzMinus
    have hSame : dist (z-delta i) p=dist z (p+delta i) := by
      rw [dist_eq_norm,dist_eq_norm]
      congr 1
      abel
    rw [hSame] at hAway
    exact hRR0.le.trans hAway
  let v : Plane := Plane.mk (1/2) 0
  have hv : ‖v‖<1 := by norm_num [v,EuclideanSpace.norm_eq]
  let b : Plane→ℝ := fun z => max (R-infDist z P) 0
  have hb0 : LipschitzWith 1 (fun z : Plane => R-infDist z P) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hh := (lipschitz_infDist_pt P).dist_le_mul x y
    simpa only [NNReal.coe_one,one_mul,Real.dist_eq,sub_sub_sub_cancel_left,abs_sub_comm] using hh
  have hb : LipschitzWith 1 b := hb0.max_const 0
  let f : Plane→Plane := fun z => b z • v
  have hf : LipschitzWith ‖v‖₊ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖b x • v-b y • v‖≤‖v‖*dist x y
    rw [←sub_smul,norm_smul,Real.norm_eq_abs]
    have hh := hb.dist_le_mul x y
    simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hh
    calc |b x-b y| * ‖v‖≤dist x y*‖v‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
      _=‖v‖*dist x y := mul_comm _ _
  have hfPeriod (i : ℤ×ℤ) (z : Plane) : f (z+delta i)=f z := by
    dsimp [f,b]
    rw [hdist]
  obtain ⟨J,hJ,hJeq,hJzero⟩ := actual_small_periodic_displacement_isotopy f ‖v‖₊ hv hf T hfPeriod
  have hJp : J.finalMap p=p+Plane.mk (R/2) 0 := by
    change J.map (⟨1,by norm_num⟩,p)=_
    rw [hJ]
    simp only [one_smul]
    have hpDist := infDist_zero_of_mem hpP
    dsimp [f,b]
    rw [hpDist,sub_zero,max_eq_left hR.le]
    ext n; fin_cases n <;> simp [v,Plane.mk]
    all_goals ring
  refine ⟨J,hJeq,?_,?_⟩
  · intro t z hz
    apply hJzero
    dsimp [f,b]
    rw [max_eq_right (sub_nonpos.mpr (hfar z hz)),zero_smul]
  · intro i hi
    rw [hJp] at hi
    change p 0+R/2=c+(i:ℝ)*T at hi
    have hdiff : ((i-k:ℤ):ℝ)*T=R/2 := by push_cast; linarith
    have hik : 0<(i-k:ℤ) := by
      by_contra hn
      have hh : ((i-k:ℤ):ℝ)≤0 := by exact_mod_cast le_of_not_gt hn
      have hh' := mul_nonpos_of_nonpos_of_nonneg hh hT.le
      linarith
    have hone : 1 ≤ ((i-k:ℤ):ℝ) := by exact_mod_cast hik
    have hh := mul_le_mul_of_nonneg_right hone hT.le
    linarith

#print axioms actual_outside_point_can_avoid_grid_fixing_family
