import Schoenflies.Plane
import Mathlib
open Set Schoenflies Topology
open scoped Topology

theorem normalized_line_deck_family (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G)
    (T : ℝ) (hT : 0 < T)
    (hp : ∀ (k : ℤ) (x : ℝ),G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ),G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0) :
    let L : ℤ → Set Plane := fun j => range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))
    (∀ j,IsClosed (L j)) ∧ Pairwise (fun i j => Disjoint (L i) (L j)) ∧ LocallyFinite L := by
  dsimp only
  let L : ℤ → Set Plane := fun j => range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))
  have hyper : Function.Periodic (fun x : ℝ => G x 1) T := by
    intro x
    simpa [Plane.mk] using congrArg (fun z : Plane => z 1) (hp 1 x)
  have hcont : Continuous (fun x : ℝ => G x 1) := (EuclideanSpace.proj 1).continuous.comp G.continuous
  have hcompact : IsCompact (range (fun x : ℝ => G x 1)) := by
    rw [← hyper.image_Icc hT 0]
    exact isCompact_Icc.image hcont
  obtain ⟨M,hM⟩ := (hcompact.image continuous_abs).bddAbove
  let B := max M 0+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound (x : ℝ) : |G x 1| < B := by
    have h := hM ⟨G x 1,⟨x,rfl⟩,rfl⟩
    dsimp [B]
    linarith [le_max_left M 0]
  have hLbound (j : ℤ) (z : Plane) (hz : z ∈ L j) : |z 1-(j:ℝ)*T| < B := by
    obtain ⟨x,rfl⟩ := hz
    simpa [Plane.mk] using hbound x
  refine ⟨?_,?_,?_⟩
  · intro j
    exact ((Homeomorph.addRight (Plane.mk 0 ((j:ℝ)*T))).isClosedEmbedding.comp hG).isClosed_range
  · intro i j hij
    apply disjoint_left.mpr
    rintro z ⟨x,hx⟩ ⟨y,hy⟩
    have heq : G x=G y+Plane.mk (((0:ℤ):ℝ)*T) (((j-i:ℤ):ℝ)*T) := by
      have hh := hx.trans hy.symm
      have h0 := congrArg (fun z : Plane => z 0) hh
      have h1 := congrArg (fun z : Plane => z 1) hh
      ext k
      fin_cases k <;> simp [Plane.mk,Int.cast_sub] at * <;> linarith
    have hz := hc x y 0 (j-i) heq
    exact hij (by omega)
  · intro z
    let U : Set Plane := (fun w : Plane => w 1) ⁻¹' Ioo (z 1-1) (z 1+1)
    have hU : U ∈ 𝓝 z := (isOpen_Ioo.preimage (EuclideanSpace.proj 1).continuous).mem_nhds
      (show z 1 ∈ Ioo (z 1-1) (z 1+1) by constructor <;> linarith)
    obtain ⟨N,hN⟩ := exists_nat_gt ((|z 1|+B+1)/T)
    have hNT := (div_lt_iff₀ hT).mp hN
    refine ⟨U,hU,(Set.finite_Icc (-(N:ℤ)) (N:ℤ)).subset ?_⟩
    intro j hj
    obtain ⟨w,hwL,hwU⟩ := hj
    have hb := abs_lt.mp (hLbound j w hwL)
    have hu : z 1-1 < w 1 ∧ w 1 < z 1+1 := hwU
    have hjlo : -(N:ℝ) < (j:ℝ) := by nlinarith [neg_abs_le (z 1)]
    have hjhi : (j:ℝ) < (N:ℝ) := by nlinarith [le_abs_self (z 1)]
    constructor
    · exact_mod_cast hjlo.le
    · exact_mod_cast hjhi.le

#print axioms normalized_line_deck_family
