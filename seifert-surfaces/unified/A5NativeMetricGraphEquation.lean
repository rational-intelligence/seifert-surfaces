import A5NativeMetricGraphOperator

set_option autoImplicit false
set_option maxHeartbeats 0
-- Style-linter settings are local to the literal paid A3 proof reuse.
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N] {h : AmbientMetric N}

/-- The literal metric area-density Euler equation follows from actual
coordinate minimality on any open smooth part of the same graph. -/
theorem native_graph_classical_equation
    (G : NativeMetricGraph h) (Ω : Set E2) (hΩ : IsOpen Ω)
    (hΩdisc : Ω ⊆ G.disc) (hsmooth : ContDiffOn ℝ ∞ G.height Ω)
    (hminimal : IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) Ω) :
    ∀ x ∈ Ω, G.classicalResidual x = 0 := by
  classical
  open Matrix in
  have hfirst
      (G : NativeMetricGraph h) (Ω : Set E2) (hΩ : IsOpen Ω)
      (hΩdisc : Ω ⊆ G.disc) (hsmooth : ContDiffOn ℝ ∞ G.height Ω) :
      let g := actualChartTensor h G.coordinates
      let Φ := graphMap (G.origin)
        G.plane G.normal G.height
      ∀ x ∈ Ω,
        G.classicalResidual x = G.areaDensity (G.attainedJet x) *
          (coordinateInner g (Φ x) (tracedAcceleration g Φ x) G.normal -
            ∑ i : Fin 2, ∑ j : Fin 2, (inducedMetric g Φ x)⁻¹ i j *
              coordinateInner g (Φ x) (tracedAcceleration g Φ x) (graphTangent Φ x i) *
              coordinateInner g (Φ x) (graphTangent Φ x j) G.normal) := by
    classical
    dsimp only
    let f := graphMap (G.origin)
      G.plane G.normal G.height
    have hf : ContDiffOn ℝ ∞ f Ω :=
      (contDiffOn_const.add G.plane.contDiff.contDiffOn).add (hsmooth.smul_const G.normal)
    have hprops
        (h : AmbientMetric N) (c : SmoothAmbientChart N) :
        (∀ a b, ContDiffOn ℝ ∞ (fun y => actualChartTensor h c y a b) c.chart.target) ∧
        (∀ y ∈ c.chart.target, ∀ a b,
          actualChartTensor h c y a b = actualChartTensor h c y b a) ∧
        (∀ y ∈ c.chart.target, ∀ v : E3, v ≠ 0 →
          0 < coordinateInner (actualChartTensor h c) y v v) := by
      classical
      have hchartMD : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
        ⟨c.smooth.mdifferentiableOn (by simp),
          c.inverse_smooth.mdifferentiableOn (by simp)⟩
      have hvector (v : E3) :
          ContMDiffOn 𝓘(ℝ, E3) (𝓘(ℝ, E3).tangent) ∞
            (fun y => Bundle.TotalSpace.mk' E3 (c.chart.symm y)
              (inverseChartDifferential c y v)) c.chart.target := by
        have hconst : ContMDiff 𝓘(ℝ, E3) (𝓘(ℝ, E3).tangent) ∞
            (fun y : E3 => Bundle.TotalSpace.mk' E3 y
              ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v)) := by
          apply (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (E := E3)
            (V := fun y => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v)).mpr
          change ContDiff ℝ ∞ (fun _ : E3 => v)
          exact contDiff_const
        have htm := c.inverse_smooth.contMDiffOn_tangentMapWithin
          (m := ∞) (by simp) c.chart.open_target.uniqueMDiffOn
        have hv := htm.comp (f := fun y : E3 => Bundle.TotalSpace.mk' E3 y
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v))
          hconst.contMDiffOn (s := c.chart.target) (by
          intro y hy
          exact hy)
        apply hv.congr
        intro y hy
        have hd := mfderivWithin_eq_mfderiv
          (c.chart.open_target.uniqueMDiffOn y hy)
          ((c.inverse_smooth.contMDiffAt (c.chart.open_target.mem_nhds hy)).mdifferentiableAt
            (by simp))
        change Bundle.TotalSpace.mk' E3 (c.chart.symm y)
            ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm y)
              ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v)) =
          Bundle.TotalSpace.mk' E3 (c.chart.symm y)
            ((mfderivWithin 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm c.chart.target y)
              ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v))
        rw [hd]
      refine ⟨?_, ?_, ?_⟩
      · intro a b y hy
        have hh : ContMDiffWithinAt 𝓘(ℝ, E3) (𝓘(ℝ, E3).prod 𝓘(ℝ)) ∞
            (fun y => Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial N ℝ) (c.chart.symm y)
              (actualChartTensor h c y a b)) c.chart.target y := by
          apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := E3) (F₂ := E3)
          · exact h.contMDiff.contMDiffAt.comp_contMDiffWithinAt y (c.inverse_smooth y hy)
          · exact hvector (coordinateVector 3 a) y hy
          · exact hvector (coordinateVector 3 b) y hy
        exact (Bundle.contMDiffWithinAt_totalSpace.mp hh).2.contDiffWithinAt
      · intro y hy a b
        exact h.symm _ _ _
      · intro y hy v hv
        have hInner : coordinateInner (actualChartTensor h c) y v v =
            h.inner (c.chart.symm y) (inverseChartDifferential c y v)
              (inverseChartDifferential c y v) := by
          have hsum (v : E3) : (∑ i : Fin 3, v i • coordinateVector 3 i) = v := by
            ext j
            simp [coordinateVector, EuclideanSpace.single, Pi.single_apply]
          have hdiff (v : E3) : inverseChartDifferential c y v =
              ∑ i : Fin 3, v i • inverseChartDifferential c y (coordinateVector 3 i) := by
            simpa only [map_sum, map_smul] using
              congrArg (inverseChartDifferential c y) (hsum v).symm
          unfold coordinateInner actualChartTensor
          rw [hdiff v, map_sum]
          simp only [map_smul, _root_.sum_apply, _root_.smul_apply, map_sum, smul_eq_mul]
          simp only [Finset.mul_sum]
          conv_rhs => rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          ring
        rw [hInner]
        have hinj : Function.Injective (inverseChartDifferential c y) :=
          ((hchartMD.symm.mfderiv_bijective hy).comp
            (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm.bijective).injective
        exact h.pos _ _ (fun hz => hv (hinj (hz.trans (map_zero _).symm)))
    have hGram (x₀ : E2) (hx₀ : x₀ ∈ Ω) :
        (G.jetMetric (G.attainedJet x₀)).PosDef := by
      let g := actualChartTensor h G.coordinates
      let y := f x₀
      let v : Fin 2 → E3 := fun i => G.jetTangent (planarGradient G.height x₀) i
      have hy : y ∈ G.coordinates.chart.target := by
        apply G.graph_in_chart
        have hd : dist x₀ 0 < G.radius := hΩdisc hx₀
        change dist x₀ 0 ≤ 2 * G.radius
        linarith [G.radius_pos]
      have hB : (g y).PosDef := by
        apply Matrix.PosDef.of_dotProduct_mulVec_pos
        · ext i j
          exact h.symm _ _ _
        · intro ξ hξ
          have hp := (hprops h G.coordinates).2.2 y hy (WithLp.toLp 2 ξ)
            (fun hz => hξ (WithLp.toLp_injective 2 hz))
          convert hp using 1
          simp only [coordinateInner,dotProduct,Matrix.mulVec,Fin.sum_univ_three,
            Pi.star_apply,star_trivial]
          dsimp [g]
          ring
      have hli : LinearIndependent ℝ v := by
        apply Fintype.linearIndependent_iff.mpr
        intro a ha
        have hs : G.plane (∑ i : Fin 2, a i • coordinateVector 2 i) +
            (∑ i : Fin 2, a i * planarGradient G.height x₀ i) • G.normal = 0 := by
          try dsimp only [v,NativeMetricGraph.jetTangent] at ha ⊢
          simpa only [smul_add,Finset.sum_add_distrib,map_sum,map_smul,mul_smul,Finset.sum_smul] using ha
        have he : ((∑ i : Fin 2, a i • coordinateVector 2 i),
            ∑ i : Fin 2, a i * planarGradient G.height x₀ i) = ((0 : E2),(0 : ℝ)) := by
          apply G.splitting.injective
          simpa only [map_zero,zero_smul,add_zero] using hs
        have hz := congrArg Prod.fst he
        intro i
        have heval := congrArg (fun z : E2 => z i) hz
        fin_cases i <;> simpa [coordinateVector,EuclideanSpace.single,Pi.single_apply] using heval
      let W : Matrix (Fin 3) (Fin 2) ℝ := fun a i => v i a
      have hW : Function.Injective W.mulVec := by
        intro x y hxy
        have hsum : ∑ i, (x i-y i) • v i = 0 := by
          ext a
          have hh := congrFun hxy a
          simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two] at hh
          simpa only [Fin.sum_univ_two,PiLp.add_apply,PiLp.smul_apply,
            smul_eq_mul,sub_mul,PiLp.zero_apply] using (by
              dsimp [W] at hh
              nlinarith [hh] : (x 0-y 0)*v 0 a+(x 1-y 1)*v 1 a=0)
        have he := Fintype.linearIndependent_iff.mp hli _ hsum
        funext i
        exact sub_eq_zero.mp (he i)
      have heq : G.jetMetric (G.attainedJet x₀) = W.conjTranspose * g y * W := by
        ext i j
        change (∑ a : Fin 3,∑ b : Fin 3,g y a b * v i a * v j b) =
          ∑ b : Fin 3,(∑ a : Fin 3,v i a * g y a b)*v j b
        simp only [Fin.sum_univ_three]
        ring
      rw [heq]
      exact hB.conjTranspose_mul_mul_same hW
    intro x hx
    have hw : DifferentiableAt ℝ G.height x :=
      (hsmooth.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
    have hfd : HasFDerivAt f (G.plane + (fderiv ℝ G.height x).smulRight G.normal) x := by
      convert ((hasFDerivAt_const _ x).add G.plane.hasFDerivAt).add
        (hw.hasFDerivAt.smul_const G.normal) using 1 <;> first | rfl | simp only [zero_add]
    have htangent (i : Fin 2) : graphTangent f x i =
        G.jetTangent (planarGradient G.height x) i := by
      try dsimp only [graphTangent,NativeMetricGraph.jetTangent,NativeMetricGraph.attainedJet]
      simp only [hfd.fderiv,_root_.add_apply,ContinuousLinearMap.smulRight_apply]
      have hgrad : planarGradient G.height x i = fderiv ℝ G.height x (coordinateVector 2 i) := by
        fin_cases i <;> simp [planarGradient, coordinateVector, PiLp.single_apply]
      rw [hgrad]
    have hmetric : inducedMetric (actualChartTensor h G.coordinates) f x =
        G.jetMetric (G.attainedJet x) := by
      ext i j
      try dsimp only [inducedMetric,NativeMetricGraph.jetMetric,NativeMetricGraph.attainedJet,NativeMetricGraph.jetPoint]
      simp only [htangent]
      rfl
    let p := planarGradient G.height x
    let y := f x
    let B : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
      ∑ a : Fin 3, ∑ b : Fin 3,
        actualChartTensor h G.coordinates y a b •
          (PiLp.proj 2 (fun _ : Fin 3 => ℝ) a).smulRight
            (PiLp.proj 2 (fun _ : Fin 3 => ℝ) b)
    have hinner (v w : E3) :
        coordinateInner (actualChartTensor h G.coordinates) y v w = B v w := by
      simp only [B, coordinateInner, _root_.sum_apply, _root_.smul_apply,
        ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, smul_eq_mul, mul_assoc]
    let A : Matrix (Fin 2) (Fin 2) ℝ := G.jetMetric (G.attainedJet x)
    let V : Fin 2 → E3 := fun i => graphTangent f x i
    have hpos : 0 < A.det := (hGram x hx).det_pos
    have hBsym (v w : E3) : B v w = B w v := by
      rw [← hinner, ← hinner]
      unfold coordinateInner
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [show actualChartTensor h G.coordinates y b a =
        actualChartTensor h G.coordinates y a b from h.symm _ _ _]
      ring
    have hAsym : A 0 1 = A 1 0 := by
      change coordinateInner (actualChartTensor h G.coordinates) y (G.jetTangent p 0)
        (G.jetTangent p 1) = coordinateInner (actualChartTensor h G.coordinates) y
          (G.jetTangent p 1) (G.jetTangent p 0)
      rw [hinner, hinner, hBsym]
    have hgraph : y ∈ G.coordinates.chart.target := by
      apply G.graph_in_chart
      have hd : dist x 0 < G.radius := hΩdisc hx
      change dist x 0 ≤ 2 * G.radius
      linarith [G.radius_pos]
    have hVarAlg (A : Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ) (b : Fin 2 → ℝ)
        (K : Fin 2 → Fin 2 → Fin 2 → ℝ) (Kn E Z : Matrix (Fin 2) (Fin 2) ℝ)
        (hA : A 1 0 = A 0 1) (hK : ∀ i j k,K i j k = K j i k)
        (hKn : ∀ i j,Kn i j = Kn j i) (hZ : Z 1 0 = Z 0 1)
        (hs : s ≠ 0) (hsquare : s ^ 2 = A.det) :
        let dA := fun k i j => K k i j + K k j i
        let db := fun k i => Kn k i + (1 / 2 : ℝ) * (E k i - E i k + Z k i)
        let ds := fun k => (A 1 1 * dA k 0 0 + A 0 0 * dA k 1 1 -
          2 * A 0 1 * dA k 0 1) / (2 * s)
        ((dA 0 1 1 * b 0 + A 1 1 * db 0 0 -
            (dA 0 0 1 * b 1 + A 0 1 * db 0 1)) * s -
            (A 1 1 * b 0 - A 0 1 * b 1) * ds 0) / s ^ 2 +
        ((dA 1 0 0 * b 1 + A 0 0 * db 1 1 -
            (dA 1 0 1 * b 0 + A 0 1 * db 1 0)) * s -
            (A 0 0 * b 1 - A 0 1 * b 0) * ds 1) / s ^ 2 -
          (A 1 1 * Z 0 0 + A 0 0 * Z 1 1 - 2 * A 0 1 * Z 0 1) / (2 * s) =
          s * ((∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j * Kn i j) -
            ∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j *
              (∑ k : Fin 2, ∑ l : Fin 2, A⁻¹ k l * K k l i) * b j) := by
      classical
      dsimp only
      have hi : A⁻¹ = (s ^ 2)⁻¹ • !![A 1 1,-A 0 1;-A 1 0,A 0 0] := by
        rw [Matrix.inv_def,Matrix.adjugate_fin_two,← hsquare]
        simp only [Ring.inverse_eq_inv]
      rw [hi]
      simp only [Fin.sum_univ_two,Matrix.smul_apply,smul_eq_mul,Matrix.of_apply,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.head_fin_const,
        hA,hK,hKn,hZ]
      have hdet : A 0 0 * A 1 1 - A 0 1 * A 0 1 = s ^ 2 := by
        rw [hsquare,Matrix.det_fin_two,hA]
      field_simp (discharger := first | assumption | positivity | norm_num | simp only [hs])
      have hs4 : s ^ 4 = (A 0 0 * A 1 1 - A 0 1 * A 0 1) ^ 2 := by
        calc
          s ^ 4 = (s ^ 2) ^ 2 := by ring
          _ = _ := by rw [← hdet]
      ring_nf
      simp only [hs4,← hdet]
      ring
    have hConnLower (g : MetricTensor) (y : E3) (hg : IsUnit (g y).det)
        (hsym : ∀ z a b, g z a b = g z b a) (u v w : E3) :
        coordinateInner g y
          (∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3,
            christoffel g y a b k * u a * v b) • coordinateVector 3 k) w =
          (1 / 2 : ℝ) *
            ((∑ a : Fin 3, ∑ b : Fin 3,fderiv ℝ (fun z => g z a b) y u * v a * w b) +
             (∑ a : Fin 3, ∑ b : Fin 3,fderiv ℝ (fun z => g z a b) y v * u a * w b) -
             (∑ a : Fin 3, ∑ b : Fin 3,fderiv ℝ (fun z => g z a b) y w * u a * v b)) := by
      classical
      have hLower (g : MetricTensor) (y : E3) (hg : IsUnit (g y).det)
          (hsym : ∀ a b, g y a b = g y b a) (u v w : E3) :
          coordinateInner g y
            (∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3,
              christoffel g y a b k * u a * v b) • coordinateVector 3 k) w =
            (1 / 2 : ℝ) * (∑ a : Fin 3, ∑ b : Fin 3, ∑ l : Fin 3,
              (partial3 (fun z => g z l b) y a + partial3 (fun z => g z l a) y b -
                partial3 (fun z => g z a b) y l) * u a * v b * w l) := by
        classical
        have hlower (a b l : Fin 3) :
            (∑ k : Fin 3, g y l k * christoffel g y a b k) =
              (1 / 2 : ℝ) * (partial3 (fun z => g z l b) y a +
                partial3 (fun z => g z l a) y b - partial3 (fun z => g z a b) y l) := by
          let R : Fin 3 → ℝ := fun m => partial3 (fun z => g z m b) y a +
            partial3 (fun z => g z m a) y b - partial3 (fun z => g z a b) y m
          change (∑ k : Fin 3, g y l k * ((1 / 2 : ℝ) * ∑ m : Fin 3, (g y)⁻¹ k m * R m)) =
            (1 / 2 : ℝ) * R l
          calc
            _ = (1 / 2 : ℝ) * ∑ m : Fin 3, (g y * (g y)⁻¹) l m * R m := by
              simp only [Matrix.mul_apply,Fin.sum_univ_three]
              ring
            _ = _ := by
              rw [Matrix.mul_nonsing_inv _ hg]
              change (1 / 2 : ℝ) * (∑ m : Fin 3, (if l = m then 1 else 0) * R m) = _
              simp
        have hcoord (s : Fin 3 → ℝ) (k : Fin 3) :
            (∑ i : Fin 3,s i • coordinateVector 3 i) k = s k := by
          simp [coordinateVector,EuclideanSpace.single,Pi.single_apply]
        simp only [coordinateInner,hcoord]
        calc
          _ = ∑ a : Fin 3, ∑ b : Fin 3, ∑ l : Fin 3,
              (∑ k : Fin 3,g y l k * christoffel g y a b k) * u a * v b * w l := by
            simp only [Fin.sum_univ_three,hsym]
            ring
          _ = _ := by
            simp only [hlower,Fin.sum_univ_three]
            ring
      rw [hLower g y hg (hsym y)]
      have hsum (v : E3) : (∑ i : Fin 3,v i • coordinateVector 3 i) = v := by
        ext j
        simp [coordinateVector,EuclideanSpace.single,Pi.single_apply]
      have hexpand (F : E3 → ℝ) (d : E3) : fderiv ℝ F y d =
          ∑ i : Fin 3,partial3 F y i * d i := by
        conv_lhs => rw [← hsum d]
        try dsimp only [partial3]
        simp only [map_sum,map_smul,smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have hdsym (a i j : Fin 3) : partial3 (fun z => g z i j) y a =
          partial3 (fun z => g z j i) y a := by
        have he : (fun z => g z i j) = (fun z => g z j i) := funext (fun z => hsym z i j)
        rw [he]
      simp only [hexpand,Fin.sum_univ_three,hdsym]
      ring
    have hInnerDeriv (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
        (g : MetricTensor) (f U V : X → E3) (x d : X)
        (hg : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) (f x))
        (hf : DifferentiableAt ℝ f x) (hU : DifferentiableAt ℝ U x)
        (hV : DifferentiableAt ℝ V x) :
        fderiv ℝ (fun z => coordinateInner g (f z) (U z) (V z)) x d =
          (∑ a : Fin 3, ∑ b : Fin 3,
            fderiv ℝ (fun z => g z a b) (f x) (fderiv ℝ f x d) * U x a * V x b) +
          coordinateInner g (f x) (fderiv ℝ U x d) (V x) +
          coordinateInner g (f x) (U x) (fderiv ℝ V x d) := by
      classical
      have hterm (a b : Fin 3) :
          fderiv ℝ (fun z => g (f z) a b * U z a * V z b) x d =
            fderiv ℝ (fun z => g z a b) (f x) (fderiv ℝ f x d) * U x a * V x b +
            g (f x) a b * (fderiv ℝ U x d) a * V x b +
            g (f x) a b * U x a * (fderiv ℝ V x d) b := by
        have hp := ((((hg a b).hasFDerivAt.comp x hf.hasFDerivAt).mul
          ((EuclideanSpace.proj (𝕜 := ℝ) a).hasFDerivAt.comp x hU.hasFDerivAt)).mul
          ((EuclideanSpace.proj (𝕜 := ℝ) b).hasFDerivAt.comp x hV.hasFDerivAt))
        change HasFDerivAt (fun z => g (f z) a b * U z a * V z b) _ x at hp
        have he := congrArg (fun L : X →L[ℝ] ℝ => L d) hp.fderiv
        simp only [Function.comp_def,Pi.mul_apply,EuclideanSpace.coe_proj,_root_.add_apply,_root_.smul_apply,
          smul_eq_mul,ContinuousLinearMap.comp_apply] at he
        rw [he]
        ring
      have hdiff (a b : Fin 3) : DifferentiableAt ℝ
          (fun z => g (f z) a b * U z a * V z b) x :=
        (((hg a b).comp x hf).mul
          ((EuclideanSpace.proj (𝕜 := ℝ) a).differentiableAt.comp x hU)).mul
          ((EuclideanSpace.proj (𝕜 := ℝ) b).differentiableAt.comp x hV)
      unfold coordinateInner
      rw [fderiv_fun_sum (fun a _ => DifferentiableAt.fun_sum (fun b _ => hdiff a b))]
      simp only [_root_.sum_apply]
      simp_rw [fderiv_fun_sum (fun b _ => hdiff _ b),_root_.sum_apply,hterm]
      simp only [Fin.sum_univ_three]
      ring
    let g := actualChartTensor h G.coordinates
    let Af : E2 → Matrix (Fin 2) (Fin 2) ℝ := inducedMetric g f
    let bf : E2 → Fin 2 → ℝ := fun z i => coordinateInner g (f z) (graphTangent f z i) G.normal
    let sf : E2 → ℝ := fun z => Real.sqrt (Af z).det
    let md (u v w : E3) := ∑ a : Fin 3,∑ b : Fin 3,
      fderiv ℝ (fun z => g z a b) y u * v a * w b
    let acc (i j : Fin 2) := covariantAcceleration g f x i j
    let K (i j k : Fin 2) := B (acc i j) (V k)
    let Kn (i j : Fin 2) := B (acc i j) G.normal
    let E (i j : Fin 2) := md (V i) (V j) G.normal
    let Z (i j : Fin 2) := md G.normal (V i) (V j)
    have hgdiff (a b : Fin 3) : DifferentiableAt ℝ (fun z => g z a b) y :=
      (((hprops h G.coordinates).1 a b).contDiffAt
        (G.coordinates.chart.open_target.mem_nhds hgraph)).differentiableAt (by simp)
    have hgsym (z : E3) (a b : Fin 3) : g z a b = g z b a := h.symm _ _ _
    have hmdsym (u v w : E3) : md u v w = md u w v := by
      have hd (a b : Fin 3) : fderiv ℝ (fun z => g z a b) y =
          fderiv ℝ (fun z => g z b a) y := by
        congr 1
        exact funext (fun z => hgsym z a b)
      simp only [md,Fin.sum_univ_three,hd]
      ring
    have hZsym : Z 1 0 = Z 0 1 := hmdsym _ _ _
    have hgfpos : (g y).PosDef := by
      apply Matrix.PosDef.of_dotProduct_mulVec_pos
      · ext i j
        simpa only [Matrix.conjTranspose_apply,star_trivial] using hgsym y j i
      · intro ξ hξ
        have hp := (hprops h G.coordinates).2.2 y hgraph (WithLp.toLp 2 ξ)
          (fun hz => hξ (WithLp.toLp_injective 2 hz))
        change 0 < ∑ a : Fin 3,∑ b : Fin 3,g y a b * ξ a * ξ b at hp
        convert hp using 1
        simp only [dotProduct,Matrix.mulVec,coordinateInner,Fin.sum_univ_three,
          Pi.star_apply,star_trivial]
        ring
    have hgg : IsUnit (g y).det := isUnit_iff_ne_zero.mpr hgfpos.det_pos.ne'
    let gam (u v : E3) := ∑ k : Fin 3,(∑ a : Fin 3,∑ b : Fin 3,
      christoffel g y a b k * u a * v b) • coordinateVector 3 k
    have hgam (u v w : E3) : B (gam u v) w =
        (1/2 : ℝ) * (md u v w + md v u w - md w u v) := by
      rw [← hinner]
      exact hConnLower g y hgg hgsym u v w
    have hfAt : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hΩ.mem_nhds hx)
    have hVD (i : Fin 2) : DifferentiableAt ℝ (fun z => graphTangent f z i) x :=
      (hfAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp) |>.clm_apply (differentiableAt_const _)
    have hsecond (i j : Fin 2) :
        fderiv ℝ (fun z => graphTangent f z j) x (coordinateVector 2 i) =
          fderiv ℝ (fderiv ℝ f) x (coordinateVector 2 i) (coordinateVector 2 j) := by
      have hp := ((hfAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.clm_apply
        (hasFDerivAt_const (coordinateVector 2 j) x)
      try dsimp only [graphTangent]
      simpa only [ContinuousLinearMap.comp_apply,_root_.zero_apply,map_zero,_root_.add_apply,zero_add,ContinuousLinearMap.flip_apply] using
        congrArg (fun L : E2 →L[ℝ] E3 => L (coordinateVector 2 i)) hp.fderiv
    have haccsym (i j : Fin 2) : acc i j = acc j i := by
      have hc (a b k : Fin 3) : christoffel g y a b k = christoffel g y b a k := by
        have he : (fun z => g z a b) = (fun z => g z b a) := funext (fun z => hgsym z a b)
        try dsimp only [christoffel]
        simp only [he,add_comm]
      try dsimp only [acc,covariantAcceleration]
      simp only [hsecond]
      change fderiv ℝ (fderiv ℝ f) x (coordinateVector 2 i) (coordinateVector 2 j) + gam (V i) (V j) =
        fderiv ℝ (fderiv ℝ f) x (coordinateVector 2 j) (coordinateVector 2 i) + gam (V j) (V i)
      rw [(hfAt.isSymmSndFDerivAt (by norm_num)).eq]
      congr 1
      unfold gam
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      simp only [Fin.sum_univ_three,hc]
      ring
    have hKsym (i j k : Fin 2) : K i j k = K j i k := by
      change B (acc i j) (V k) = B (acc j i) (V k)
      rw [haccsym]
    have hKnsym (i j : Fin 2) : Kn i j = Kn j i := by
      change B (acc i j) G.normal = B (acc j i) G.normal
      rw [haccsym]
    have hAdiff (i j : Fin 2) : DifferentiableAt ℝ (fun z => Af z i j) x := by
      change DifferentiableAt ℝ (fun z => ∑ a : Fin 3,∑ b : Fin 3,
        g (f z) a b * graphTangent f z i a * graphTangent f z j b) x
      apply DifferentiableAt.fun_sum
      intro a ha
      apply DifferentiableAt.fun_sum
      intro b hb
      exact (((hgdiff a b).comp x hfd.differentiableAt).mul
        ((EuclideanSpace.proj (𝕜 := ℝ) a).differentiableAt.comp x (hVD i))).mul
        ((EuclideanSpace.proj (𝕜 := ℝ) b).differentiableAt.comp x (hVD j))
    have hbDiff (i : Fin 2) : DifferentiableAt ℝ (fun z => bf z i) x := by
      apply DifferentiableAt.fun_sum
      intro a ha
      apply DifferentiableAt.fun_sum
      intro b hb
      exact (((hgdiff a b).comp x hfd.differentiableAt).mul
        ((EuclideanSpace.proj (𝕜 := ℝ) a).differentiableAt.comp x (hVD i))).mul_const _
    have hAD (k i j : Fin 2) : fderiv ℝ (fun z => Af z i j) x (coordinateVector 2 k) =
        K k i j + K k j i := by
      have hd := hInnerDeriv E2 g f (fun z => graphTangent f z i)
        (fun z => graphTangent f z j) x (coordinateVector 2 k) hgdiff
        hfd.differentiableAt (hVD i) (hVD j)
      change fderiv ℝ (fun z => Af z i j) x (coordinateVector 2 k) = _ at hd
      rw [hd]
      try dsimp only [acc,K,covariantAcceleration]
      simp only [map_add,_root_.add_apply]
      change md (V k) (V i) (V j) +
        coordinateInner g y (fderiv ℝ (fun z => graphTangent f z i) x (coordinateVector 2 k)) (V j) +
        coordinateInner g y (V i) (fderiv ℝ (fun z => graphTangent f z j) x (coordinateVector 2 k)) =
        B (fderiv ℝ (fun z => graphTangent f z i) x (coordinateVector 2 k)) (V j) +
        B (gam (V k) (V i)) (V j) +
        (B (fderiv ℝ (fun z => graphTangent f z j) x (coordinateVector 2 k)) (V i) +
        B (gam (V k) (V j)) (V i))
      rw [hinner,hinner,hBsym (V i),hgam,hgam]
      simp only [hmdsym]
      ring
    have hbD (k i : Fin 2) : fderiv ℝ (fun z => bf z i) x (coordinateVector 2 k) =
        Kn k i + (1/2 : ℝ) * (E k i - E i k + Z k i) := by
      have hd := hInnerDeriv E2 g f (fun z => graphTangent f z i)
        (fun _ => G.normal) x (coordinateVector 2 k) hgdiff
        hfd.differentiableAt (hVD i) (differentiableAt_const _)
      change fderiv ℝ (fun z => bf z i) x (coordinateVector 2 k) = _ at hd
      rw [hd]
      simp only [fderiv_const_apply,_root_.zero_apply,PiLp.zero_apply,coordinateInner,mul_zero,Finset.sum_const_zero,add_zero]
      change md (V k) (V i) G.normal +
        coordinateInner g y (fderiv ℝ (fun z => graphTangent f z i) x (coordinateVector 2 k)) G.normal = _
      rw [hinner]
      try dsimp only [acc,Kn,covariantAcceleration]
      simp only [map_add,_root_.add_apply]
      change md (V k) (V i) G.normal + B _ G.normal =
        B _ G.normal + B (gam (V k) (V i)) G.normal + _
      rw [hgam]
      simp only [E,Z]
      ring
    have hFluxFormula (x₀ : E2) (hx₀ : x₀ ∈ Ω) :
        G.attainedFlux x₀ 0 = (Af x₀ 1 1 * bf x₀ 0 - Af x₀ 0 1 * bf x₀ 1) / sf x₀ ∧
        G.attainedFlux x₀ 1 = (Af x₀ 0 0 * bf x₀ 1 - Af x₀ 0 1 * bf x₀ 0) / sf x₀ := by
      have hw : DifferentiableAt ℝ G.height x₀ :=
        (hsmooth.contDiffAt (hΩ.mem_nhds hx₀)).differentiableAt (by simp)
      have hfd : HasFDerivAt f (G.plane + (fderiv ℝ G.height x₀).smulRight G.normal) x₀ := by
        convert ((hasFDerivAt_const _ x₀).add G.plane.hasFDerivAt).add
          (hw.hasFDerivAt.smul_const G.normal) using 1 <;> first | rfl | simp only [zero_add]
      have htangent (i : Fin 2) : graphTangent f x₀ i =
          G.jetTangent (planarGradient G.height x₀) i := by
        try dsimp only [graphTangent,NativeMetricGraph.jetTangent,NativeMetricGraph.attainedJet]
        simp only [hfd.fderiv,_root_.add_apply,ContinuousLinearMap.smulRight_apply]
        have hgrad : planarGradient G.height x₀ i = fderiv ℝ G.height x₀ (coordinateVector 2 i) := by
          fin_cases i <;> simp [planarGradient, coordinateVector, PiLp.single_apply]
        rw [hgrad]
      have hmetric : inducedMetric (actualChartTensor h G.coordinates) f x₀ =
          G.jetMetric (G.attainedJet x₀) := by
        ext i j
        try dsimp only [inducedMetric,NativeMetricGraph.jetMetric,NativeMetricGraph.attainedJet,NativeMetricGraph.jetPoint]
        simp only [htangent]
        rfl
      have hdet : 0 < Matrix.det (inducedMetric (actualChartTensor h G.coordinates) f x₀) := by
        rw [hmetric]
        exact (hGram x₀ hx₀).det_pos
      let p := planarGradient G.height x₀
      let y := f x₀
      let B : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
        ∑ a : Fin 3, ∑ b : Fin 3,
          actualChartTensor h G.coordinates y a b •
            (PiLp.proj 2 (fun _ : Fin 3 => ℝ) a).smulRight
              (PiLp.proj 2 (fun _ : Fin 3 => ℝ) b)
      have hinner (v w : E3) :
          coordinateInner (actualChartTensor h G.coordinates) y v w = B v w := by
        simp only [B, coordinateInner, _root_.sum_apply, _root_.smul_apply,
          ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, smul_eq_mul, mul_assoc]
      let P (i : Fin 2) : E2 →L[ℝ] E3 :=
        (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i).smulRight G.normal
      have hTi (i : Fin 2) : HasFDerivAt (fun z => G.jetTangent z i) (P i) p := by
        convert (hasFDerivAt_const (G.plane (coordinateVector 2 i)) p).add (P i).hasFDerivAt using 1
        · rfl
        · simp only [zero_add]
      have hA (i k : Fin 2) : HasFDerivAt
          (fun z => G.jetMetric (x₀, G.height x₀, z) i k)
          ((B (G.jetTangent p i)).comp (P k) +
            (B.comp (P i)).flip (G.jetTangent p k)) p := by
        convert (B.hasFDerivAt.comp p (hTi i)).clm_apply (hTi k) using 1
        · funext z
          exact hinner _ _
        · rfl
      let A : Matrix (Fin 2) (Fin 2) ℝ := G.jetMetric (G.attainedJet x₀)
      have hAdet : HasFDerivAt (fun z => Matrix.det (G.jetMetric (x₀, G.height x₀, z)))
          (G.jetMetric (x₀, G.height x₀, p) 0 0 •
            ((B (G.jetTangent p 1)).comp (P 1) + (B.comp (P 1)).flip (G.jetTangent p 1)) +
          G.jetMetric (x₀, G.height x₀, p) 1 1 •
            ((B (G.jetTangent p 0)).comp (P 0) + (B.comp (P 0)).flip (G.jetTangent p 0)) -
          (G.jetMetric (x₀, G.height x₀, p) 0 1 •
            ((B (G.jetTangent p 1)).comp (P 0) + (B.comp (P 1)).flip (G.jetTangent p 0)) +
          G.jetMetric (x₀, G.height x₀, p) 1 0 •
            ((B (G.jetTangent p 0)).comp (P 1) + (B.comp (P 0)).flip (G.jetTangent p 1)))) p := by
        convert ((hA 0 0).mul (hA 1 1)).sub ((hA 0 1).mul (hA 1 0)) using 1
        funext z
        exact Matrix.det_fin_two _
      have hpos : 0 < Matrix.det (G.jetMetric (x₀, G.height x₀, p)) :=
        (hGram x₀ hx₀).det_pos
      have hF := hAdet.sqrt hpos.ne'
      have hBsym (v w : E3) : B v w = B w v := by
        rw [← hinner, ← hinner]
        unfold coordinateInner
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        rw [show actualChartTensor h G.coordinates y b a =
          actualChartTensor h G.coordinates y a b from h.symm _ _ _]
        ring
      have hAsym : A 0 1 = A 1 0 := by
        change coordinateInner (actualChartTensor h G.coordinates) y (G.jetTangent p 0)
          (G.jetTangent p 1) = coordinateInner (actualChartTensor h G.coordinates) y
            (G.jetTangent p 1) (G.jetTangent p 0)
        rw [hinner, hinner, hBsym]
      have hflux0 : G.metricFlux (G.attainedJet x₀) 0 =
          (A 1 1 * B G.normal (G.jetTangent p 0) -
            A 0 1 * B G.normal (G.jetTangent p 1)) / Real.sqrt A.det := by
        change planarGradient (fun z => G.areaDensity (x₀, G.height x₀, z)) p 0 = _
        have hgradient : planarGradient (fun z => G.areaDensity (x₀, G.height x₀, z)) p 0 =
            fderiv ℝ (fun z => G.areaDensity (x₀, G.height x₀, z)) p (coordinateVector 2 0) := by
          simp [planarGradient, coordinateVector]
        rw [hgradient]
        try dsimp only [NativeMetricGraph.areaDensity]
        rw [hF.fderiv]
        simp only [_root_.smul_apply, smul_eq_mul, _root_.add_apply,
          _root_.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
        simp only [P, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply,
          coordinateVector, EuclideanSpace.single, PiLp.single_apply]
        norm_num only [Fin.reduceEq, ite_true, ite_false, zero_smul, one_smul, map_zero,
          mul_zero, zero_add, add_zero, _root_.zero_apply]
        change 1 / (2 * Real.sqrt A.det) *
          (A 1 1 * (B (G.jetTangent p 0) G.normal + B G.normal (G.jetTangent p 0)) -
            (A 0 1 * B (G.jetTangent p 1) G.normal +
              A 1 0 * B G.normal (G.jetTangent p 1))) = _
        rw [hBsym (G.jetTangent p 0) G.normal, hBsym (G.jetTangent p 1) G.normal, ← hAsym]
        have hroot : Real.sqrt A.det ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
        field_simp (discharger := first | assumption | positivity | norm_num | simp only [hroot])
        <;> ring
      have hflux1 : G.metricFlux (G.attainedJet x₀) 1 =
          (A 0 0 * B G.normal (G.jetTangent p 1) -
            A 0 1 * B G.normal (G.jetTangent p 0)) / Real.sqrt A.det := by
        change planarGradient (fun z => G.areaDensity (x₀, G.height x₀, z)) p 1 = _
        have hgradient : planarGradient (fun z => G.areaDensity (x₀, G.height x₀, z)) p 1 =
            fderiv ℝ (fun z => G.areaDensity (x₀, G.height x₀, z)) p (coordinateVector 2 1) := by
          simp [planarGradient, coordinateVector]
        rw [hgradient]
        try dsimp only [NativeMetricGraph.areaDensity]
        rw [hF.fderiv]
        simp only [_root_.smul_apply, smul_eq_mul, _root_.add_apply,
          _root_.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
        simp only [P, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply,
          coordinateVector, EuclideanSpace.single, PiLp.single_apply]
        norm_num only [Fin.reduceEq, ite_true, ite_false, zero_smul, one_smul, map_zero,
          mul_zero, zero_add, add_zero, _root_.zero_apply]
        change 1 / (2 * Real.sqrt A.det) *
          (A 0 0 * (B (G.jetTangent p 1) G.normal + B G.normal (G.jetTangent p 1)) -
            (A 0 1 * B G.normal (G.jetTangent p 0) +
              A 1 0 * B (G.jetTangent p 0) G.normal)) = _
        rw [hBsym (G.jetTangent p 1) G.normal, hBsym (G.jetTangent p 0) G.normal, ← hAsym]
        have hroot : Real.sqrt A.det ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
        field_simp (discharger := first | assumption | positivity | norm_num | simp only [hroot])
        <;> ring
      have hAF : Af x₀ = A := hmetric
      have hBF (i : Fin 2) : bf x₀ i = B (G.jetTangent p i) G.normal := by
        change coordinateInner (actualChartTensor h G.coordinates) (f x₀) (graphTangent f x₀ i) G.normal = _
        rw [htangent]
        exact hinner _ _
      constructor
      · change G.metricFlux (G.attainedJet x₀) 0 = _
        rw [hflux0]
        simp only [sf,hAF,hBF,hBsym]
      · change G.metricFlux (G.attainedJet x₀) 1 = _
        rw [hflux1]
        simp only [sf,hAF,hBF,hBsym]
    have hAx : Af x = A := hmetric
    have hbx (i : Fin 2) : bf x i = B (V i) G.normal := hinner _ _
    have hsx : sf x ≠ 0 := by
      change Real.sqrt (Af x).det ≠ 0
      rw [hAx]
      exact (Real.sqrt_pos.mpr hpos).ne'
    have hsquare : (sf x) ^ 2 = A.det := by
      change (Real.sqrt (Af x).det) ^ 2 = _
      rw [hAx]
      exact Real.sq_sqrt hpos.le
    have hsf : HasFDerivAt sf
        ((1 / (2 * sf x)) •
          (Af x 0 0 • fderiv ℝ (fun z => Af z 1 1) x +
           Af x 1 1 • fderiv ℝ (fun z => Af z 0 0) x -
          (Af x 0 1 • fderiv ℝ (fun z => Af z 1 0) x +
           Af x 1 0 • fderiv ℝ (fun z => Af z 0 1) x))) x := by
      have hd := (((hAdiff 0 0).hasFDerivAt.mul (hAdiff 1 1).hasFDerivAt).sub
        ((hAdiff 0 1).hasFDerivAt.mul (hAdiff 1 0).hasFDerivAt)).sqrt
        (show Af x 0 0 * Af x 1 1 - Af x 0 1 * Af x 1 0 ≠ 0 by
          rw [← Matrix.det_fin_two,hAx];exact hpos.ne')
      change HasFDerivAt (fun z => Real.sqrt
        (Af z 0 0 * Af z 1 1 - Af z 0 1 * Af z 1 0)) _ x at hd
      simpa only [sf,Matrix.det_fin_two,Pi.sub_apply,Pi.mul_apply] using hd
    have hsD (k : Fin 2) : fderiv ℝ sf x (coordinateVector 2 k) =
        (A 1 1 * (K k 0 0 + K k 0 0) + A 0 0 * (K k 1 1 + K k 1 1) -
          2 * A 0 1 * (K k 0 1 + K k 1 0)) / (2 * sf x) := by
      rw [hsf.fderiv]
      simp only [_root_.smul_apply,smul_eq_mul,_root_.add_apply,_root_.sub_apply,hAD,hAx,← hAsym]
      ring
    let cH : ℝ → E3 := fun t => G.origin + G.plane x + t • G.normal
    have hcH : HasFDerivAt cH (ContinuousLinearMap.toSpanSingleton ℝ G.normal)
        (G.height x) := by
      exact (ContinuousLinearMap.toSpanSingleton ℝ G.normal).hasFDerivAt.const_add
        (G.origin + G.plane x)
    have hcHy : cH (G.height x) = y := rfl
    have hZD (i j : Fin 2) : HasDerivAt
        (fun t => G.jetMetric (x,t,p) i j) (Z i j) (G.height x) := by
      have ht (i : Fin 2) : G.jetTangent p i = V i := (htangent i).symm
      have hd : DifferentiableAt ℝ (fun t => G.jetMetric (x,t,p) i j) (G.height x) := by
        change DifferentiableAt ℝ (fun t => ∑ a : Fin 3,∑ b : Fin 3,
          g (cH t) a b * G.jetTangent p i a * G.jetTangent p j b) (G.height x)
        apply DifferentiableAt.fun_sum
        intro a ha
        apply DifferentiableAt.fun_sum
        intro b hb
        have hg' : DifferentiableAt ℝ (fun z : E3 => g z a b) (cH (G.height x)) := by
          rw [hcHy]
          exact hgdiff a b
        have hh : DifferentiableAt ℝ (fun t => g (cH t) a b) (G.height x) :=
          DifferentiableAt.comp (f := cH) (g := fun z : E3 => g z a b)
            (G.height x) hg' hcH.differentiableAt
        exact (hh.mul_const _).mul_const _
      convert hd.hasDerivAt using 1
      change Z i j = fderiv ℝ (fun t => coordinateInner g (cH t)
        (G.jetTangent p i) (G.jetTangent p j)) (G.height x) 1
      rw [ht,ht]
      rw [hInnerDeriv ℝ g cH (fun _ => V i) (fun _ => V j) (G.height x) 1
        hgdiff hcH.differentiableAt (differentiableAt_const _) (differentiableAt_const _)]
      simp only [hcH.fderiv,ContinuousLinearMap.toSpanSingleton_apply,ContinuousLinearMap.smulRight_apply,
        one_apply_eq_self,one_smul,fderiv_const_apply,_root_.zero_apply,PiLp.zero_apply,hcHy,
        coordinateInner,mul_zero,zero_mul,Finset.sum_const_zero,add_zero]
      rfl
    have hlower : G.attainedLowerOrder x =
        -(A 1 1 * Z 0 0 + A 0 0 * Z 1 1 - 2 * A 0 1 * Z 0 1) / (2 * sf x) := by
      have hd := (((hZD 0 0).mul (hZD 1 1)).sub ((hZD 0 1).mul (hZD 1 0))).sqrt
        (show G.jetMetric (x,G.height x,p) 0 0 * G.jetMetric (x,G.height x,p) 1 1 -
          G.jetMetric (x,G.height x,p) 0 1 * G.jetMetric (x,G.height x,p) 1 0 ≠ 0 by
          rw [← Matrix.det_fin_two];exact hpos.ne')
      change -deriv (fun t => Real.sqrt (Matrix.det (G.jetMetric (x,t,p)))) (G.height x) = _
      simp only [Matrix.det_fin_two]
      change HasDerivAt (fun t => Real.sqrt (G.jetMetric (x,t,p) 0 0 * G.jetMetric (x,t,p) 1 1 -
        G.jetMetric (x,t,p) 0 1 * G.jetMetric (x,t,p) 1 0)) _ (G.height x) at hd
      rw [hd.deriv]
      change -((Z 0 0 * A 1 1 + A 0 0 * Z 1 1 -
        (Z 0 1 * A 1 0 + A 0 1 * Z 1 0)) / (2 * Real.sqrt
          (A 0 0 * A 1 1 - A 0 1 * A 1 0))) = _
      rw [← Matrix.det_fin_two]
      change -((Z 0 0 * A 1 1 + A 0 0 * Z 1 1 -
        (Z 0 1 * A 1 0 + A 0 1 * Z 1 0)) / (2 * Real.sqrt A.det)) = _
      simp only [sf,hAx,← hAsym,hZsym]
      ring
    have hQuot (a b c d e l k : Fin 2) :
        fderiv ℝ (fun z => (Af z a b * bf z c - Af z d e * bf z l) / sf z) x
          (coordinateVector 2 k) =
        (((K k a b + K k b a) * bf x c + A a b *
            (Kn k c + (1/2 : ℝ) * (E k c - E c k + Z k c)) -
          ((K k d e + K k e d) * bf x l + A d e *
            (Kn k l + (1/2 : ℝ) * (E k l - E l k + Z k l)))) * sf x -
          (A a b * bf x c - A d e * bf x l) *
            ((A 1 1 * (K k 0 0 + K k 0 0) + A 0 0 * (K k 1 1 + K k 1 1) -
              2 * A 0 1 * (K k 0 1 + K k 1 0)) / (2 * sf x))) / (sf x)^2 := by
      have hn := (((hAdiff a b).hasFDerivAt.mul (hbDiff c).hasFDerivAt).sub
        ((hAdiff d e).hasFDerivAt.mul (hbDiff l).hasFDerivAt))
      have hi := (hasFDerivAt_inv hsx).comp x hsf
      have hd := hn.mul hi
      change HasFDerivAt (fun z => (Af z a b * bf z c - Af z d e * bf z l) * (sf z)⁻¹) _ x at hd
      simp only [div_eq_mul_inv]
      have he := congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 k)) hd.fderiv
      simp only [_root_.smul_apply,_root_.add_apply,_root_.sub_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply,hAD,hbD,hAx] at he
      rw [he]
      have heSF := hsD k
      rw [hsf.fderiv] at heSF
      simp only [_root_.smul_apply,smul_eq_mul,_root_.add_apply,_root_.sub_apply,hAD,hAx,← hAsym] at heSF
      simp only [_root_.smul_apply,smul_eq_mul,_root_.add_apply,_root_.sub_apply,hAD,hAx,← hAsym,
        Pi.sub_apply,Pi.mul_apply,Function.comp_apply]
      field_simp (discharger := first | assumption | positivity | norm_num | simp only [hsx])
      <;> ring
    have hflux0germ : (fun z => G.attainedFlux z 0) =ᶠ[𝓝 x]
        (fun z => (Af z 1 1 * bf z 0 - Af z 0 1 * bf z 1) / sf z) :=
      Filter.Eventually.mono (hΩ.mem_nhds hx) (fun z hz => (hFluxFormula z hz).1)
    have hflux1germ : (fun z => G.attainedFlux z 1) =ᶠ[𝓝 x]
        (fun z => (Af z 0 0 * bf z 1 - Af z 0 1 * bf z 0) / sf z) :=
      Filter.Eventually.mono (hΩ.mem_nhds hx) (fun z hz => (hFluxFormula z hz).2)
    have htracePair (w : E3) : B (tracedAcceleration g f x) w =
        ∑ i : Fin 2, ∑ j : Fin 2,A⁻¹ i j * B (acc i j) w := by
      change B (∑ i : Fin 2,∑ j : Fin 2,(Af x)⁻¹ i j • acc i j) w = _
      rw [hAx]
      simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
    have halg := hVarAlg A (sf x) (bf x) K Kn E Z hAsym.symm hKsym hKnsym hZsym hsx hsquare
    change G.classicalResidual x = Real.sqrt A.det *
      (coordinateInner g y (tracedAcceleration g f x) G.normal -
        ∑ i : Fin 2, ∑ j : Fin 2,(Af x)⁻¹ i j *
          coordinateInner g y (tracedAcceleration g f x) (V i) *
          coordinateInner g y (V j) G.normal)
    rw [hAx]
    dsimp only [g]
    simp only [hinner]
    change G.classicalResidual x = Real.sqrt A.det *
      (B (tracedAcceleration g f x) G.normal -
        ∑ i : Fin 2, ∑ j : Fin 2,A⁻¹ i j * B (tracedAcceleration g f x) (V i) * B (V j) G.normal)
    simp only [htracePair]
    unfold NativeMetricGraph.classicalResidual
    simp only [Fin.sum_univ_two]
    rw [hflux0germ.fderiv_eq,hflux1germ.fderiv_eq,hQuot,hQuot,hlower]
    simpa only [sf,hAx,hbx,K,Kn,Fin.sum_univ_two,sub_eq_add_neg,neg_div] using halg
  let slopeGram (B : Matrix (Fin 3) (Fin 3) ℝ) (L : E2 →L[ℝ] E3)
      (n : E3) (p : E2) : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => coordinateInner (fun _ => B) 0
      (L (coordinateVector 2 i) + p i • n)
      (L (coordinateVector 2 j) + p j • n)
  have hresidual
      (G : NativeMetricGraph h) (Ω : Set E2) (hΩ : IsOpen Ω)
      (hΩdisc : Ω ⊆ G.disc)
      (hsmooth : ContDiffOn ℝ ∞ G.height Ω)
      (htrace : ∀ x ∈ Ω,
        tracedAcceleration (actualChartTensor h G.coordinates)
          (graphMap (G.origin)
            G.plane G.normal G.height) x ∈
        LinearMap.range
          (fderiv ℝ (graphMap (G.origin)
            G.plane G.normal G.height) x).toLinearMap) :
      ∀ x ∈ Ω, G.classicalResidual x = 0 := by
    classical
    have hmetric :
        (∀ i j, ContDiffOn ℝ ∞ (fun y => actualChartTensor h G.coordinates y i j)
          G.coordinates.chart.target) ∧
        (∀ y ∈ G.coordinates.chart.target, ∀ i j,
          actualChartTensor h G.coordinates y i j = actualChartTensor h G.coordinates y j i) ∧
        (∀ y ∈ G.coordinates.chart.target, ∀ w : E3, w ≠ 0 →
          0 < coordinateInner (actualChartTensor h G.coordinates) y w w) := by
      let c := G.coordinates
      refine ⟨?_, ?_, ?_⟩
      · intro i j
        let : Bundle.RiemannianBundle (fun p : N => TangentSpace 𝓘(ℝ, E3) p) :=
          ⟨h.toRiemannianMetric⟩
        have hv (k : Fin 3) : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, E3).tangent ∞
            (fun y => (⟨c.chart.symm y, inverseChartDifferential c y (coordinateVector 3 k)⟩ :
              TangentBundle 𝓘(ℝ, E3) N)) c.chart.target := by
          have hs : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3).tangent ∞
              (fun y => (⟨y, (NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k)⟩ :
                TangentBundle 𝓘(ℝ, E3) E3)) :=
            contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
          have ht := c.inverse_smooth.contMDiffOn_tangentMapWithin
            (m := ∞) (by simp) c.chart.open_target.uniqueMDiffOn
          have hc := ht.comp hs.contMDiffOn (by intro y hy; exact hy)
          apply hc.congr
          intro y hy
          change (⟨c.chart.symm y, (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm y)
            ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k))⟩ : TangentBundle 𝓘(ℝ, E3) N) =
              ⟨c.chart.symm y, (mfderivWithin 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm c.chart.target y)
                ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k))⟩
          rw [mfderivWithin_eq_mfderiv (c.chart.open_target.uniqueMDiffOn y hy)
            (((c.inverse_smooth y hy).mdifferentiableWithinAt (by simp)).mdifferentiableAt
              (c.chart.open_target.mem_nhds hy))]
        exact (open scoped Bundle in (hv i |>.inner_bundle (hv j)).contDiffOn)
      · intro y hy i j
        exact h.symm _ _ _
      · intro y hy w hw
        have he : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
          ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
        have hinj : Function.Injective (inverseChartDifferential c y) :=
          (he.symm.mfderiv_injective hy).comp (NormedSpace.fromTangentSpace y).symm.injective
        have hn : inverseChartDifferential c y w ≠ 0 := by
          intro hh
          apply hw
          apply hinj
          simpa only [map_zero] using hh
        have hid (v w : E3) : coordinateInner (actualChartTensor h c) y v w =
            h.inner (c.chart.symm y) (inverseChartDifferential c y v)
              (inverseChartDifferential c y w) := by
          have hsum (v : E3) : (∑ i : Fin 3, v i • coordinateVector 3 i) = v := by
            ext j
            simp [coordinateVector, EuclideanSpace.single, Pi.single_apply]
          have hdiff (v : E3) : inverseChartDifferential c y v =
              ∑ i : Fin 3, v i • inverseChartDifferential c y (coordinateVector 3 i) := by
            simpa only [map_sum, map_smul] using congrArg (inverseChartDifferential c y) (hsum v).symm
          unfold coordinateInner actualChartTensor
          rw [hdiff v, hdiff w, map_sum]
          simp only [map_smul, _root_.sum_apply, _root_.smul_apply, map_sum, smul_eq_mul]
          simp only [Finset.mul_sum]
          conv_rhs => rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          ring
        rw [hid]
        exact h.pos _ _ hn
    have hann (B : Matrix (Fin 3) (Fin 3) ℝ) (T : E2 →L[ℝ] E3)
      (n : E3) (v : E2)
      (hG : Matrix.PosDef (fun i j : Fin 2 => coordinateInner (fun _ => B) 0
        (T (coordinateVector 2 i)) (T (coordinateVector 2 j)))) :
      coordinateInner (fun _ => B) 0 (T v) n -
        ∑ i : Fin 2, ∑ j : Fin 2,
          (@Inv.inv (Matrix (Fin 2) (Fin 2) ℝ) Matrix.inv (fun i j : Fin 2 => coordinateInner (fun _ => B) 0
            (T (coordinateVector 2 i)) (T (coordinateVector 2 j)))) i j *
          coordinateInner (fun _ => B) 0 (T v) (T (coordinateVector 2 i)) *
          coordinateInner (fun _ => B) 0 (T (coordinateVector 2 j)) n = 0 := by
      classical
      let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j => coordinateInner (fun _ => B) 0
        (T (coordinateVector 2 i)) (T (coordinateVector 2 j))
      have hv : v = v 0 • coordinateVector 2 0 + v 1 • coordinateVector 2 1 := by
        ext i
        fin_cases i <;> simp [coordinateVector,EuclideanSpace.single]
      have hlin (w : E3) : coordinateInner (fun _ => B) 0 (T v) w =
          ∑ k : Fin 2, v k * coordinateInner (fun _ => B) 0 (T (coordinateVector 2 k)) w := by
        conv_lhs => rw [hv,map_add,map_smul,map_smul]
        simp only [coordinateInner,Fin.sum_univ_two,Fin.sum_univ_three,PiLp.add_apply,
          PiLp.smul_apply,smul_eq_mul]
        ring
      rw [hlin]
      simp_rw [hlin]
      change (∑ k : Fin 2, v k * coordinateInner (fun _ => B) 0 (T (coordinateVector 2 k)) n) -
        (∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j * (∑ k : Fin 2, v k * A k i) *
          coordinateInner (fun _ => B) 0 (T (coordinateVector 2 j)) n) = 0
      have heq : (∑ i : Fin 2, ∑ j : Fin 2, A⁻¹ i j * (∑ k : Fin 2, v k * A k i) *
          coordinateInner (fun _ => B) 0 (T (coordinateVector 2 j)) n) =
          ∑ k : Fin 2, ∑ j : Fin 2, v k * (A*A⁻¹) k j *
            coordinateInner (fun _ => B) 0 (T (coordinateVector 2 j)) n := by
        simp only [Matrix.mul_apply,Fin.sum_univ_two]
        ring
      rw [heq, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hG.det_pos.ne')]
      simp
    let g := actualChartTensor h G.coordinates
    let Φ := graphMap (G.origin) G.plane G.normal G.height
    have hvariation (x : E2) (hx : x ∈ Ω) :
        G.classicalResidual x = G.areaDensity (G.attainedJet x) *
          (coordinateInner g (Φ x) (tracedAcceleration g Φ x) G.normal -
            ∑ i : Fin 2, ∑ j : Fin 2, (inducedMetric g Φ x)⁻¹ i j *
              coordinateInner g (Φ x) (tracedAcceleration g Φ x) (graphTangent Φ x i) *
              coordinateInner g (Φ x) (graphTangent Φ x j) G.normal) := by
      exact hfirst G Ω hΩ hΩdisc hsmooth x hx
    intro x hx
    have hu : DifferentiableAt ℝ G.height x :=
      ((hsmooth x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
    have hΦ : HasFDerivAt Φ (G.plane + (fderiv ℝ G.height x).smulRight G.normal) x := by
      exact (G.plane.hasFDerivAt.const_add _).add (hu.hasFDerivAt.smul_const G.normal)
    have hpg (i : Fin 2) : planarGradient G.height x i =
        fderiv ℝ G.height x (coordinateVector 2 i) := by
      unfold planarGradient
      fin_cases i <;> simp [coordinateVector,EuclideanSpace.single]
    have ht (i : Fin 2) : graphTangent Φ x i =
        G.plane (coordinateVector 2 i) + planarGradient G.height x i • G.normal := by
      unfold graphTangent
      rw [hΦ.fderiv,hpg]
      rfl
    have hchartx : Φ x ∈ G.coordinates.chart.target := by
      apply G.graph_in_chart
      have hxdisc := hΩdisc hx
      change dist x 0 < G.radius at hxdisc
      change dist x 0 ≤ 2*G.radius
      linarith [G.radius_pos]
    have hB : (g (Φ x)).PosDef := by
      apply Matrix.PosDef.of_dotProduct_mulVec_pos
      · ext i j
        exact hmetric.2.1 (Φ x) hchartx j i
      · intro w hw
        have hp := hmetric.2.2 (Φ x) hchartx (WithLp.toLp 2 w) (by
          intro he;apply hw;exact congrArg WithLp.ofLp he)
        convert hp using 1
        simp only [coordinateInner,dotProduct,Matrix.mulVec,Fin.sum_univ_three,
          Pi.star_apply,star_trivial]
        dsimp [g]
        ring
    have hgram : (inducedMetric g Φ x).PosDef := by
      let B := g (Φ x)
      let L := G.plane
      let n := G.normal
      have hsplit := G.splitting
      have hgram (q : E2) : (slopeGram B L n q).PosDef := by
        let v : Fin 2 → E3 := fun i => L (coordinateVector 2 i) + q i • n
        have hli : LinearIndependent ℝ v := by
          apply Fintype.linearIndependent_iff.mpr
          intro a ha
          have hs : L (∑ i : Fin 2, a i • coordinateVector 2 i) +
              (∑ i : Fin 2, a i * q i) • n = 0 := by
            simpa only [v, smul_add, Finset.sum_add_distrib,
              map_sum, map_smul, mul_smul, Finset.sum_smul] using ha
          have he : ((∑ i : Fin 2, a i • coordinateVector 2 i), ∑ i : Fin 2, a i * q i) =
              ((0 : E2), (0 : ℝ)) := by
            apply hsplit.injective
            simpa only [map_zero, zero_smul, add_zero] using hs
          have hz := congrArg Prod.fst he
          intro i
          have heval := congrArg (fun z : E2 => z i) hz
          fin_cases i <;> simpa [coordinateVector, EuclideanSpace.single, Pi.single_apply] using heval
        let V : Matrix (Fin 3) (Fin 2) ℝ := fun a i => v i a
        have hV : Function.Injective V.mulVec := by
          intro x y hxy
          have hsum : ∑ i, (x i - y i) • v i = 0 := by
            ext a
            have hh := congrFun hxy a
            simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh
            simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply,
              smul_eq_mul, sub_mul, PiLp.zero_apply] using (by
                dsimp [V] at hh
                nlinarith [hh] : (x 0 - y 0) * v 0 a + (x 1 - y 1) * v 1 a = 0)
          have he := Fintype.linearIndependent_iff.mp hli _ hsum
          funext i
          exact sub_eq_zero.mp (he i)
        have heq : slopeGram B L n q = V.conjTranspose * B * V := by
          ext i j
          change (∑ a : Fin 3, ∑ b : Fin 3, B a b * v i a * v j b) =
            ∑ b : Fin 3, (∑ a : Fin 3, v i a * B a b) * v j b
          simp only [Fin.sum_univ_three]
          ring
        rw [heq]
        exact hB.conjTranspose_mul_mul_same hV
      have heq : inducedMetric g Φ x = slopeGram B L n (planarGradient G.height x) := by
        ext i j
        unfold inducedMetric
        rw [ht i, ht j]
        rfl
      rw [heq]
      exact hgram _
    obtain ⟨v,hv⟩ := htrace x hx
    rw [hvariation x hx]
    have hh := hann (g (Φ x)) (fderiv ℝ Φ x) G.normal v hgram
    change (fderiv ℝ Φ x) v = tracedAcceleration g Φ x at hv
    rw [← hv]
    change G.areaDensity (G.attainedJet x) * _ = 0
    exact mul_eq_zero_of_right _ hh
  
  exact hresidual G Ω hΩ hΩdisc hsmooth hminimal.2

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
