import B1InteriorCoefficientTube_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
theorem native_interior_coefficient_mean_value_v475 (W : NativeInteriorGraphWindow_v475) (O : Set E2) (hO : IsOpen O) (hU : O ⊆ W.U)
    (hsegments : ∀ x ∈ O, ∀ t ∈ Icc (0 : ℝ) 1,
      jetPoint (W.segmentJet x t) ∈ W.V)
    (hq : ContDiffOn ℝ ∞ W.q O) :
    (∀ x ∈ O, ∀ i j : Fin 2,
      IntervalIntegrable (fun t : ℝ =>
        fderiv ℝ (fun p : E2 => W.flux (x, (W.segmentJet x t).2.1, p) i)
          (W.segmentJet x t).2.2 (coordinateVector 2 j)) volume 0 1) ∧
    (∀ x ∈ O, ∀ i : Fin 2,
      IntervalIntegrable (fun t : ℝ =>
        deriv (fun z : ℝ => W.flux (x, z, (W.segmentJet x t).2.2) i)
          (W.segmentJet x t).2.1) volume 0 1) ∧
    (∀ x ∈ O, ∀ i : Fin 2,
      IntervalIntegrable (fun t : ℝ =>
        fderiv ℝ (fun p : E2 => W.lower (x, (W.segmentJet x t).2.1, p))
          (W.segmentJet x t).2.2 (coordinateVector 2 i)) volume 0 1) ∧
    (∀ x ∈ O,
      IntervalIntegrable (fun t : ℝ =>
        deriv (fun z : ℝ => W.lower (x, z, (W.segmentJet x t).2.2))
          (W.segmentJet x t).2.1) volume 0 1) ∧
    (∀ x ∈ O,
      W.flux (x, W.height x, planarGradient (W.height) x) -
          W.flux (x, 0, 0) =
        matrixAction (W.a x) (planarGradient (W.height) x) +
          W.height x • W.q x) ∧
    (∀ x ∈ O,
      W.lower (x, W.height x, planarGradient (W.height) x) -
          W.lower (x, 0, 0) =
        inner ℝ (W.lowerGradient x) (planarGradient (W.height) x) +
          W.lowerHeight x * W.height x) ∧
    (∀ x ∈ O,
      W.residual (W.height) x - W.residual (fun _ => 0) x =
        classicalL W.a W.b W.c (W.height) x) := by
  have jp_smooth : ContDiff ℝ ∞ jetPoint := by
    unfold jetPoint
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  have p_slice (f : Jet → ℝ) (j : Jet) (hf : DifferentiableAt ℝ f j) (p : E2) :
      fderiv ℝ (fun p : E2 => f (j.1, j.2.1, p)) j.2.2 p =
        fderiv ℝ f j (0, 0, p) := by
    have hs := (hasFDerivAt_const (𝕜 := ℝ) j.1 j.2.2).prodMk
      ((hasFDerivAt_const (𝕜 := ℝ) j.2.1 j.2.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) j.2.2))
    have hh := hf.hasFDerivAt.comp j.2.2 hs
    exact congrArg (fun L : E2 →L[ℝ] ℝ => L p) hh.fderiv
  have z_slice (f : Jet → ℝ) (j : Jet) (hf : DifferentiableAt ℝ f j) :
      deriv (fun z : ℝ => f (j.1, z, j.2.2)) j.2.1 =
        fderiv ℝ f j (0, 1, 0) := by
    have hs := (hasFDerivAt_const (𝕜 := ℝ) j.1 j.2.1).prodMk
      ((hasFDerivAt_id (𝕜 := ℝ) j.2.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) j.2.2 j.2.1))
    have hh := hf.hasFDerivAt.comp j.2.1 hs
    exact congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hh.fderiv
  have partial_p_smooth (A : Set Jet) (hA : IsOpen A) (f : Jet → ℝ)
      (hf : ContDiffOn ℝ ∞ f A) (p : E2) :
      ContDiffOn ℝ ∞ (fun j : Jet =>
        fderiv ℝ (fun p : E2 => f (j.1,j.2.1,p)) j.2.2 p) A := by
    apply ((hf.fderiv_of_isOpen hA (by simp)).clm_apply
      (contDiffOn_const (c := ((0, (0, p)) : Jet)))).congr
    intro j hj
    exact (p_slice f j ((hf.contDiffAt (hA.mem_nhds hj)).differentiableAt (by simp)) p)
  have partial_z_smooth (A : Set Jet) (hA : IsOpen A) (f : Jet → ℝ)
      (hf : ContDiffOn ℝ ∞ f A) :
      ContDiffOn ℝ ∞ (fun j : Jet => deriv (fun z : ℝ => f (j.1,z,j.2.2)) j.2.1) A := by
    apply ((hf.fderiv_of_isOpen hA (by simp)).clm_apply
      (contDiffOn_const (c := ((0, (1, 0)) : Jet)))).congr
    intro j hj
    exact (z_slice f j ((hf.contDiffAt (hA.mem_nhds hj)).differentiableAt (by simp)))
  have flux_lower_smooth (W : NativeInteriorGraphWindow_v475) :
      (∀ i : Fin 2, ContDiffOn ℝ ∞ (fun j => W.flux j i) (jetPoint ⁻¹' W.V)) ∧
      ContDiffOn ℝ ∞ W.lower (jetPoint ⁻¹' W.V) := by
    have hh := native_interior_graph_jet_calculus_v475 W.V W.V_open W.metric
    exact ⟨fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hh.2.1,hh.2.2⟩
  have scalar_mv (A : Set Jet) (hA : IsOpen A) (f : Jet → ℝ)
      (hf : ContDiffOn ℝ ∞ f A) (x p : E2) (u : ℝ)
      (hs : ∀ t ∈ Icc (0 : ℝ) 1, (x,t*u,t • p) ∈ A) :
      (∀ i : Fin 2, IntervalIntegrable (fun t : ℝ =>
        fderiv ℝ (fun p' : E2 => f (x,t*u,p')) (t • p) (coordinateVector 2 i)) volume 0 1) ∧
      IntervalIntegrable (fun t : ℝ => deriv (fun z : ℝ => f (x,z,t • p)) (t*u)) volume 0 1 ∧
      f (x,u,p) - f (x,0,0) =
        (∑ i : Fin 2, (∫ t in (0 : ℝ)..1,
          fderiv ℝ (fun p' : E2 => f (x,t*u,p')) (t • p) (coordinateVector 2 i)) * p i) +
        (∫ t in (0 : ℝ)..1, deriv (fun z : ℝ => f (x,z,t • p)) (t*u)) * u := by
    let S : ℝ → Jet := fun t => (x,t*u,t • p)
    let P : Fin 2 → ℝ → ℝ := fun i t =>
      fderiv ℝ (fun p' : E2 => f (x,t*u,p')) (t • p) (coordinateVector 2 i)
    let Z : ℝ → ℝ := fun t => deriv (fun z : ℝ => f (x,z,t • p)) (t*u)
    have hc : Continuous S := by dsimp [S]; fun_prop
    have hp (i : Fin 2) : IntervalIntegrable (P i) volume 0 1 := by
      have hh := ((partial_p_smooth A hA f hf (coordinateVector 2 i)).continuousOn.comp hc.continuousOn hs)
      exact (show ContinuousOn (P i) (uIcc (0 : ℝ) 1) by simpa [P,S,Function.comp_def] using hh).intervalIntegrable
    have hz : IntervalIntegrable Z volume 0 1 := by
      have hh := ((partial_z_smooth A hA f hf).continuousOn.comp hc.continuousOn hs)
      exact (show ContinuousOn Z (uIcc (0 : ℝ) 1) by simpa [Z,S,Function.comp_def] using hh).intervalIntegrable
    refine ⟨hp,hz,?_⟩
    have hex : p = p 0 • coordinateVector 2 0 + p 1 • coordinateVector 2 1 := by
      ext i
      fin_cases i <;> simp [coordinateVector, EuclideanSpace.single]
    have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => f (S t))
        (P 0 t * p 0 + P 1 t * p 1 + Z t * u) t := by
      intro t ht
      have hft := (hf.contDiffAt (hA.mem_nhds (hs t (by simpa using ht)))).differentiableAt (by simp)
      have hst : HasDerivAt S (0,u,p) t := by
        simpa [S] using (hasDerivAt_const t x).prodMk
          (((hasDerivAt_id t).mul_const u).prodMk ((hasDerivAt_id t).smul_const p))
      have hh := hft.hasFDerivAt.comp_hasDerivAt t hst
      convert hh using 1 <;> try rfl
      rw [show ((0,u,p) : Jet) = (0,0,p) + u • (0,1,0) by ext <;> simp]
      rw [map_add, map_smul, ← p_slice f (S t) hft p, ← z_slice f (S t) hft]
      change _ = fderiv ℝ (fun p' : E2 => f (x,t*u,p')) (t • p) p + u * Z t
      conv_rhs => arg 1; arg 2; rw [hex]
      simp only [map_add,map_smul,smul_eq_mul]
      dsimp [P]
      ring
    have hi := ((hp 0).mul_const (p 0)).add ((hp 1).mul_const (p 1))
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi.add (hz.mul_const u))
    rw [intervalIntegral.integral_add hi (hz.mul_const u),
      intervalIntegral.integral_add ((hp 0).mul_const (p 0)) ((hp 1).mul_const (p 1)),
      intervalIntegral.integral_mul_const,intervalIntegral.integral_mul_const,
      intervalIntegral.integral_mul_const] at heq
    simpa [S,P,Z,Fin.sum_univ_two] using heq.symm
  have grad_smooth (U : Set E2) (hU : IsOpen U) (u : E2 → ℝ)
      (hu : ContDiffOn ℝ ∞ u U) : ContDiffOn ℝ ∞ (planarGradient u) U := by
    unfold planarGradient
    apply ContDiffOn.sum
    intro i hi
    exact ((hu.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const).smul contDiffOn_const
  have smooth_coord (U : Set E2) (f : E2 → E2)
      (hf : ContDiffOn ℝ ∞ f U) (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => f x i) U := by
    exact (show ContDiff ℝ ∞ (fun p : E2 => p i) by fun_prop).comp_contDiffOn hf
  have residual_identity (W : NativeInteriorGraphWindow_v475) (O : Set E2) (hO : IsOpen O) (hU : O ⊆ W.U)
      (hs : ∀ x ∈ O, ∀ t ∈ Icc (0 : ℝ) 1, jetPoint (W.segmentJet x t) ∈ W.V)
      (hq : ContDiffOn ℝ ∞ W.q O)
      (hF : ∀ x ∈ O, W.flux (x, W.height x, planarGradient (W.height) x) -
        W.flux (x, 0, 0) = matrixAction (W.a x) (planarGradient (W.height) x) +
          W.height x • W.q x)
      (hL : ∀ x ∈ O, W.lower (x, W.height x, planarGradient (W.height) x) -
        W.lower (x, 0, 0) = inner ℝ (W.lowerGradient x) (planarGradient (W.height) x) +
          W.lowerHeight x * W.height x) :
      ∀ x ∈ O, W.residual (W.height) x - W.residual (fun _ => 0) x =
        classicalL W.a W.b W.c (W.height) x := by
    let u := W.height
    have hu : ContDiffOn ℝ ∞ u O := W.height_smooth.mono hU
    have hg : ContDiffOn ℝ ∞ (planarGradient u) O := grad_smooth O hO u hu
    have hJ : IsOpen (jetPoint ⁻¹' W.V) := W.V_open.preimage jp_smooth.continuous
    have hf := (flux_lower_smooth W).1
    have hjet : ContDiffOn ℝ ∞ (fun x : E2 => (x,u x,planarGradient u x) : E2 → Jet) O :=
      contDiffOn_id.prodMk (hu.prodMk hg)
    have hzjet : ContDiffOn ℝ ∞ (fun x : E2 => (x,0,0) : E2 → Jet) O :=
      contDiffOn_id.prodMk (contDiffOn_const.prodMk contDiffOn_const)
    have hFi (i : Fin 2) : ContDiffOn ℝ ∞
        (fun x : E2 => W.flux (x,u x,planarGradient u x) i) O := by
      apply (hf i).comp hjet
      intro x hx
      have ht := hs x hx 1 (by norm_num)
      change jetPoint (x, 1 * W.height x, (1 : ℝ) • planarGradient (W.height) x) ∈ W.V at ht
      simpa [u] using ht
    have hZi (i : Fin 2) : ContDiffOn ℝ ∞ (fun x : E2 => W.flux (x,0,0) i) O := by
      apply (hf i).comp hzjet
      intro x hx
      have ht := hs x hx 0 (by norm_num)
      change jetPoint (x, 0 * W.height x, (0 : ℝ) • planarGradient (W.height) x) ∈ W.V at ht
      simpa using ht
    have hqi (i : Fin 2) := smooth_coord O W.q hq i
    have hMi (i : Fin 2) : ContDiffOn ℝ ∞
        (fun x : E2 => matrixAction (W.a x) (planarGradient u x) i) O := by
      apply (((hFi i).sub (hZi i)).sub (hu.mul (hqi i))).congr
      intro x hx
      have he := congrArg (fun p : E2 => p i) (hF x hx)
      change W.flux (x,u x,planarGradient u x) i - W.flux (x,0,0) i =
        matrixAction (W.a x) (planarGradient u x) i + u x * W.q x i at he
      dsimp only
      linarith
    have hgrad (x : E2) (i : Fin 2) : planarGradient u x i =
        fderiv ℝ u x (coordinateVector 2 i) := by
      fin_cases i <;> simp [planarGradient,Fin.sum_univ_two,coordinateVector,EuclideanSpace.single]
    intro x hx
    have hdu := (hu.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hdF (i : Fin 2) := ((hFi i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hdZ (i : Fin 2) := ((hZi i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hdQ (i : Fin 2) := ((hqi i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hdM (i : Fin 2) := ((hMi i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have he (i : Fin 2) :
        fderiv ℝ (fun y : E2 => W.flux (y,u y,planarGradient u y) i) x (coordinateVector 2 i) -
        fderiv ℝ (fun y : E2 => W.flux (y,0,0) i) x (coordinateVector 2 i) =
        fderiv ℝ (fun y : E2 => matrixAction (W.a y) (planarGradient u y) i) x (coordinateVector 2 i) +
        u x * fderiv ℝ (fun y : E2 => W.q y i) x (coordinateVector 2 i) +
          W.q x i * planarGradient u x i := by
      have hev : (fun y : E2 => W.flux (y,u y,planarGradient u y) i - W.flux (y,0,0) i) =ᶠ[𝓝 x]
          (fun y : E2 => matrixAction (W.a y) (planarGradient u y) i + u y * W.q y i) := by
        filter_upwards [hO.mem_nhds hx] with y hy
        exact congrArg (fun p : E2 => p i) (hF y hy)
      have hh := congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i)) hev.fderiv_eq
      have hr := (hdM i).hasFDerivAt.add (hdu.hasFDerivAt.mul (hdQ i).hasFDerivAt)
      have hl := (hdF i).hasFDerivAt.sub (hdZ i).hasFDerivAt
      have hl' : fderiv ℝ (fun y : E2 => W.flux (y,u y,planarGradient u y) i - W.flux (y,0,0) i) x =
        fderiv ℝ (fun y : E2 => W.flux (y,u y,planarGradient u y) i) x -
        fderiv ℝ (fun y : E2 => W.flux (y,0,0) i) x := hl.fderiv
      have hr' : fderiv ℝ (fun y : E2 => matrixAction (W.a y) (planarGradient u y) i + u y * W.q y i) x =
        fderiv ℝ (fun y : E2 => matrixAction (W.a y) (planarGradient u y) i) x +
        (u x • fderiv ℝ (fun y : E2 => W.q y i) x + W.q x i • fderiv ℝ u x) := hr.fderiv
      rw [hl',hr'] at hh
      simpa [hgrad,add_assoc] using hh
    have hzero : planarGradient (fun _ : E2 => (0 : ℝ)) = 0 := by
      funext y
      simp [planarGradient]
    have hl := hL x hx
    have he0 := he 0
    have he1 := he 1
    delta NativeInteriorGraphWindow_v475.residual classicalL NativeInteriorGraphWindow_v475.b NativeInteriorGraphWindow_v475.c
    simp only [hzero,Pi.zero_apply,Fin.sum_univ_two,
      EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
      star_trivial,PiLp.add_apply] at *
    dsimp only [u] at *
    nlinarith
  have hA : IsOpen (jetPoint ⁻¹' W.V) := W.V_open.preimage jp_smooth.continuous
  have hf := flux_lower_smooth W
  have hMVF (x : E2) (hx : x ∈ O) (i : Fin 2) :=
    scalar_mv _ hA (fun j => W.flux j i) (hf.1 i) x
      (planarGradient (W.height) x) (W.height x) (hsegments x hx)
  have hMVL (x : E2) (hx : x ∈ O) :=
    scalar_mv _ hA W.lower hf.2 x
      (planarGradient (W.height) x) (W.height x) (hsegments x hx)
  have hF : ∀ x ∈ O,
      W.flux (x,W.height x,planarGradient (W.height) x) - W.flux (x,0,0) =
        matrixAction (W.a x) (planarGradient (W.height) x) + W.height x • W.q x := by
    intro x hx
    ext i
    delta matrixAction NativeInteriorGraphWindow_v475.a NativeInteriorGraphWindow_v475.q NativeInteriorGraphWindow_v475.segmentJet
    simpa [mul_comm]
      using (hMVF x hx i).2.2
  have hL : ∀ x ∈ O,
      W.lower (x,W.height x,planarGradient (W.height) x) - W.lower (x,0,0) =
        inner ℝ (W.lowerGradient x) (planarGradient (W.height) x) +
          W.lowerHeight x * W.height x := by
    intro x hx
    delta NativeInteriorGraphWindow_v475.lowerGradient NativeInteriorGraphWindow_v475.lowerHeight NativeInteriorGraphWindow_v475.segmentJet
    simpa [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm]
      using (hMVL x hx).2.2
  exact ⟨(fun x hx i j => (hMVF x hx i).1 j),
    (fun x hx i => (hMVF x hx i).2.1),
    (fun x hx i => (hMVL x hx).1 i),
    (fun x hx => (hMVL x hx).2.1),hF,hL,
    residual_identity W O hO hU hsegments hq hF hL⟩


#print axioms native_interior_coefficient_mean_value_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
