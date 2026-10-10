import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSmallPeriodicBump
import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly

open Set Topology Schoenflies CurveComplex Metric

theorem actual_small_horizontal_grid_slide_relative_puncture
    (T c e : ℝ) (p : Plane) (hT : 0<T)
    (hpc : p 0<c) (hcp : c<p 0+T)
    (he : |e| < min (c-p 0) (p 0+T-c)) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t (i : ℤ×ℤ), H.map (t,p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t (i : ℤ×ℤ) z,
        H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
          H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      H.finalMap '' {z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T}=
        {z : Plane | ∃ i : ℤ, z 0=c+e+(i:ℝ)*T} := by
  let m := min (c-p 0) (p 0+T-c)
  let R := (|e|+m)/2
  have hm : 0< m := by dsimp [m]; positivity
  have hR : 0<R := by dsimp [R]; positivity
  have heR : |e|<R := by dsimp [R]; linarith
  have hRm : R< m := by dsimp [R]; linarith
  let C := range (fun i : ℤ => c+(i:ℝ)*T)
  have hCn : C.Nonempty := ⟨c,0,by simp⟩
  have hCperiod (k : ℤ) : (fun x : ℝ => x+(k:ℝ)*T) '' C=C := by
    apply subset_antisymm
    · rintro z ⟨x,⟨i,rfl⟩,rfl⟩
      refine ⟨i+k,?_⟩
      push_cast
      ring
    · rintro z ⟨i,rfl⟩
      refine ⟨c+((i-k:ℤ):ℝ)*T,⟨i-k,rfl⟩,?_⟩
      push_cast
      ring
  have hPeriod (k : ℤ) (x : ℝ) : infDist (x+(k:ℝ)*T) C=infDist x C := by
    have hh : infDist (x+(k:ℝ)*T) ((fun x : ℝ => x+(k:ℝ)*T) '' C)=infDist x C :=
      infDist_image (IsometryEquiv.addRight ((k:ℝ)*T)).isometry
    rwa [hCperiod] at hh
  have hFar : m ≤ infDist (p 0) C := by
    apply (le_infDist hCn).mpr
    rintro y ⟨i,rfl⟩
    rw [Real.dist_eq]
    by_cases hi : 0 ≤ i
    · have hi' : 0 ≤ (i:ℝ) := by exact_mod_cast hi
      have hh : p 0-(c+(i:ℝ)*T)≤0 := by nlinarith
      rw [abs_of_nonpos hh]
      have hmc : m ≤ c-p 0 := min_le_left _ _
      nlinarith
    · have hi' : (i:ℝ) ≤ -1 := by exact_mod_cast (show i ≤ -1 by omega)
      have hh : 0 ≤ p 0-(c+(i:ℝ)*T) := by nlinarith
      rw [abs_of_nonneg hh]
      have hmc : m ≤ p 0+T-c := min_le_right _ _
      nlinarith
  have hCoord : LipschitzWith 1 (fun z : Plane => z 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [dist_eq_norm] using PiLp.norm_apply_le (x-y) 0
  have hDist : LipschitzWith 1 (fun z : Plane => infDist (z 0) C) := by
    simpa only [Function.comp_def,one_mul] using (lipschitz_infDist_pt C).comp hCoord
  let b : Plane→ℝ := fun z => max (R-infDist (z 0) C) 0
  have hb0 : LipschitzWith 1 (fun z : Plane => R-infDist (z 0) C) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hh := hDist.dist_le_mul x y
    simpa only [NNReal.coe_one,one_mul,Real.dist_eq,sub_sub_sub_cancel_left,abs_sub_comm] using hh
  have hb : LipschitzWith 1 b := hb0.max_const 0
  let v : Plane := Plane.mk (e/R) 0
  have hvNorm : ‖v‖=|e|/R := by
    simp [v,EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk,Real.sqrt_sq_eq_abs,abs_div,abs_of_pos hR]
  have hv : ‖v‖<1 := by rw [hvNorm]; exact (div_lt_iff₀ hR).mpr (by simpa using heR)
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
  have hfPeriod (i : ℤ×ℤ) (z : Plane) :
      f (z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=f z := by
    dsimp [f,b]
    change max (R-infDist (z 0+(i.1:ℝ)*T) C) 0 • v=max (R-infDist (z 0) C) 0 • v
    rw [hPeriod]
  obtain ⟨H,hH,hHeq,hHzero⟩ := actual_small_periodic_displacement_isotopy f ‖v‖₊ hv hf T hfPeriod
  have hpZero : f p=0 := by
    dsimp [f,b]
    rw [max_eq_right (by linarith : R-infDist (p 0) C≤0),zero_smul]
  have hGridPoint (z : Plane) (hz : ∃ i : ℤ, z 0=c+(i:ℝ)*T) :
      H.finalMap z=z+Plane.mk e 0 := by
    have hzC : z 0∈C := by obtain ⟨i,hi⟩ := hz; exact ⟨i,hi.symm⟩
    change H.map (⟨1,by norm_num⟩,z)=_
    rw [hH]
    simp only [one_smul]
    dsimp [f,b]
    rw [infDist_zero_of_mem hzC,sub_zero,max_eq_left hR.le]
    congr 1
    ext n; fin_cases n <;> simp [v,Plane.mk]
    field_simp
  refine ⟨H,?_,hHeq,?_⟩
  · intro t i
    rw [hHeq,hHzero t p hpZero]
  · ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      rw [hGridPoint w hw]
      obtain ⟨i,hi⟩ := hw
      refine ⟨i,?_⟩
      change w 0+e=c+e+(i:ℝ)*T
      linarith
    · rintro ⟨i,hi⟩
      let w := z-Plane.mk e 0
      have hw : ∃ i : ℤ, w 0=c+(i:ℝ)*T := by
        refine ⟨i,?_⟩
        change z 0-e=c+(i:ℝ)*T
        linarith
      refine ⟨w,hw,?_⟩
      rw [hGridPoint w hw]
      exact sub_add_cancel _ _

#print axioms actual_small_horizontal_grid_slide_relative_puncture
