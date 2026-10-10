import CurveComplexGenusTwo.Topology.GeometricPosition.CurveSubdivision
import Schoenflies.Plane
namespace CurveComplex.PositionTrimV2
/-- Trim short off-family endpoint collars from an actual equal-mesh circle
subdivision. The selected central angular subarcs are mutually disjoint, remain
inside their assigned charts, and their complement in the whole actual circle
is disjoint from the fixed finite family. -/
theorem position_trimmed_crosscuts
    (S : Type*) [TopologicalSpace S] [T2Space S]
    (J : Type*) [Fintype J] (r : J → Curve S)
    (c : Curve S) (n : ℕ) (hn : 2 ≤ n)
    (arc : Fin n → C(Interval, S))
    (harc : ∀ k t, arc k t = c.map (Circle.exp
      (-Real.pi + 2 * Real.pi * (((k.val : ℝ) + (t : ℝ)) / n))))
    (hcover : c.image = ⋃ k, Set.range (arc k))
    (e : Fin n → OpenPartialHomeomorph S Schoenflies.Plane)
    (hchart : ∀ k, Set.range (arc k) ⊆ (e k).source)
    (hends : ∀ k j, arc k ⟨0, by norm_num⟩ ∉ (r j).image ∧
      arc k ⟨1, by norm_num⟩ ∉ (r j).image) :
    ∃ a b : Fin n → ℝ,
      (∀ k, a k < b k) ∧
      (∀ k, b k - a k < 2 * Real.pi) ∧
      (∀ k, (fun t => c.map (Circle.exp t)) '' Set.Icc (a k) (b k) ⊆ (e k).source) ∧
      (∀ i j, i ≠ j → Disjoint
        ((fun t => c.map (Circle.exp t)) '' Set.Icc (a i) (b i))
        ((fun t => c.map (Circle.exp t)) '' Set.Icc (a j) (b j))) ∧
      (∀ k j, c.map (Circle.exp (a k)) ∉ (r j).image ∧
        c.map (Circle.exp (b k)) ∉ (r j).image) ∧
      (∀ j, Disjoint
        (c.image \ ⋃ k, (fun t => c.map (Circle.exp t)) '' Set.Icc (a k) (b k))
        (r j).image) := by
  classical
  let zero : Interval := ⟨0,by norm_num⟩
  let one : Interval := ⟨1,by norm_num⟩
  let bad : Set Interval := ⋃ k, ⋃ j, (arc k) ⁻¹' (r j).image
  have hbad : IsClosed bad := isClosed_iUnion_of_finite (fun k =>
    isClosed_iUnion_of_finite (fun j =>
      ((isCompact_range (r j).embedded.continuous).isClosed).preimage (arc k).continuous))
  have hzero : zero ∈ badᶜ := by
    intro h
    obtain ⟨k,j,hkj⟩ := Set.mem_iUnion₂.mp h
    exact (hends k j).1 hkj
  have hone : one ∈ badᶜ := by
    intro h
    obtain ⟨k,j,hkj⟩ := Set.mem_iUnion₂.mp h
    exact (hends k j).2 hkj
  obtain ⟨δ₀,hδ₀,hball₀⟩ := Metric.isOpen_iff.mp hbad.isOpen_compl zero hzero
  obtain ⟨δ₁,hδ₁,hball₁⟩ := Metric.isOpen_iff.mp hbad.isOpen_compl one hone
  let ε : ℝ := min (1/4) (min δ₀ δ₁) / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεhalf : ε < 1/2 := by
    have := min_le_left (1/4:ℝ) (min δ₀ δ₁)
    dsimp [ε]; linarith
  have hεδ₀ : ε < δ₀ := by
    have := (min_le_right (1/4:ℝ) (min δ₀ δ₁)).trans (min_le_left δ₀ δ₁)
    dsimp [ε]; linarith
  have hεδ₁ : ε < δ₁ := by
    have := (min_le_right (1/4:ℝ) (min δ₀ δ₁)).trans (min_le_right δ₀ δ₁)
    dsimp [ε]; linarith
  have hcollar (k : Fin n) (t : Interval) (ht : (t:ℝ) ≤ ε ∨ 1-ε ≤ (t:ℝ)) :
      ∀ j, arc k t ∉ (r j).image := by
    have htgood : t ∈ badᶜ := by
      rcases ht with ht | ht
      · apply hball₀
        rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
        change |(t:ℝ)-0| < δ₀
        rw [sub_zero,abs_of_nonneg t.property.1]
        exact ht.trans_lt hεδ₀
      · apply hball₁
        rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
        change |(t:ℝ)-1| < δ₁
        rw [abs_of_nonpos (by linarith [t.property.2])]
        linarith
    intro j h
    exact htgood (Set.mem_iUnion₂.mpr ⟨k,j,h⟩)
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let d : ℝ := 2*Real.pi/n
  have hd : 0 < d := by dsimp [d]; positivity
  have hdn : d*n = 2*Real.pi := by dsimp [d]; field_simp
  let L : Fin n → ℝ := fun k => -Real.pi+d*k.val
  let a : Fin n → ℝ := fun k => L k+d*ε
  let b : Fin n → ℝ := fun k => L k+d*(1-ε)
  have hparam (k : Fin n) (t : Interval) :
      arc k t = c.map (Circle.exp (L k+d*(t:ℝ))) := by
    rw [harc]
    congr 2
    dsimp [L,d]
    ring
  have hLlow (k : Fin n) : -Real.pi ≤ L k := by
    dsimp [L]
    have := Nat.cast_nonneg (α := ℝ) k.val
    nlinarith
  have hLhigh (k : Fin n) : L k+d ≤ Real.pi := by
    have hk : (k.val:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast Nat.succ_le_of_lt k.isLt
    dsimp [L]
    nlinarith
  have hab (k : Fin n) : a k < b k := by dsimp [a,b]; nlinarith
  have hwidth (k : Fin n) : b k-a k < 2*Real.pi := by
    have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    have hdperiod : d < 2*Real.pi := by nlinarith
    dsimp [a,b]
    nlinarith
  have hinner (k : Fin n) (t : ℝ) (ht : t ∈ Set.Icc (a k) (b k)) :
      L k < t ∧ t < L k+d := by
    dsimp [a,b] at ht
    constructor <;> nlinarith [ht.1,ht.2]
  have hglobal (k : Fin n) (t : ℝ) (ht : t ∈ Set.Icc (a k) (b k)) :
      t ∈ Set.Ico (-Real.pi) Real.pi :=
    ⟨(hLlow k).trans (hinner k t ht).1.le,(hinner k t ht).2.trans_le (hLhigh k)⟩
  have hcentral (k : Fin n) (t : ℝ) (ht : t ∈ Set.Icc (a k) (b k)) :
      ∃ u : Interval, ε ≤ (u:ℝ) ∧ (u:ℝ) ≤ 1-ε ∧
        arc k u = c.map (Circle.exp t) := by
    let v := (t-L k)/d
    have hvlow : ε ≤ v := (le_div_iff₀ hd).mpr (by dsimp [a] at ht; linarith [ht.1])
    have hvhigh : v ≤ 1-ε := (div_le_iff₀ hd).mpr (by dsimp [b] at ht; linarith [ht.2])
    let u : Interval := ⟨v,⟨by linarith,by linarith⟩⟩
    refine ⟨u,hvlow,hvhigh,?_⟩
    rw [hparam]
    congr 2
    change L k+d*((t-L k)/d) = t
    field_simp [hd.ne'] <;> ring
  have hdis (i j : Fin n) (hij : i ≠ j) : Disjoint
      ((fun t => c.map (Circle.exp t)) '' Set.Icc (a i) (b i))
      ((fun t => c.map (Circle.exp t)) '' Set.Icc (a j) (b j)) := by
    rw [Set.disjoint_left]
    rintro x ⟨t,ht,rfl⟩ ⟨u,hu,heu⟩
    have htu : u = t := Circle.exp_injOn_Ico (by linarith : Real.pi-(-Real.pi) ≤ 2*Real.pi)
      (hglobal j u hu) (hglobal i t ht) (c.embedded.injective heu)
    subst u
    have hti := hinner i t ht
    have htj := hinner j t hu
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hk : (i.val:ℝ)+1 ≤ (j.val:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
      dsimp [L] at hti htj
      nlinarith
    · have hk : (j.val:ℝ)+1 ≤ (i.val:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
      dsimp [L] at hti htj
      nlinarith
  refine ⟨a,b,hab,hwidth,?_,hdis,?_,?_⟩
  · intro k x hx
    obtain ⟨t,ht,rfl⟩ := hx
    obtain ⟨u,hu₀,hu₁,he⟩ := hcentral k t ht
    change c.map (Circle.exp t) ∈ (e k).source
    rw [← he]
    exact hchart k (Set.mem_range_self u)
  · intro k j
    let u₀ : Interval := ⟨ε,⟨hε.le,by linarith⟩⟩
    let u₁ : Interval := ⟨1-ε,⟨by linarith,by linarith⟩⟩
    have he₀ : arc k u₀ = c.map (Circle.exp (a k)) := hparam k u₀
    have he₁ : arc k u₁ = c.map (Circle.exp (b k)) := hparam k u₁
    exact ⟨he₀ ▸ hcollar k u₀ (Or.inl le_rfl) j,he₁ ▸ hcollar k u₁ (Or.inr le_rfl) j⟩
  · intro j
    rw [Set.disjoint_left]
    rintro x ⟨hxc,hxnot⟩ hxj
    rw [hcover] at hxc
    obtain ⟨k,u,rfl⟩ := Set.mem_iUnion.mp hxc
    have hout : (u:ℝ) < ε ∨ 1-ε < (u:ℝ) := by
      by_contra hn
      push_neg at hn
      apply hxnot
      apply Set.mem_iUnion.mpr
      refine ⟨k,L k+d*(u:ℝ),?_,(hparam k u).symm⟩
      dsimp [a,b]
      constructor <;> nlinarith [hn.1,hn.2]
    exact hcollar k u (hout.imp le_of_lt le_of_lt) j hxj

end CurveComplex.PositionTrimV2
