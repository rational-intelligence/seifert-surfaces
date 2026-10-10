import VM03OwedRequests import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff import Mathlib.Analysis.Calculus.ImplicitContDiff import Mathlib.Analysis.Calculus.ContDiff.RCLike import Mathlib.Topology.MetricSpace.Thickening import Mathlib.Topology.Maps.Proper.Basic import Mathlib.Topology.LocallyFinite import Mathlib.Topology.Instances.AddCircle.Defs import Mathlib.Analysis.SpecialFunctions.Complex.Arg import DifferentialGeometry.External.Schoenflies.Realization import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies import Mathlib.Analysis.Convex.GaugeRescale import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology import DifferentialGeometry.Topology.PlanarJordan.Regions import DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffineSimplicial import DifferentialGeometry.Topology.PiecewiseLinear.PLPath import Mathlib.Data.Finset.Sort import Mathlib.Analysis.Calculus.AddTorsor.AffineMap import Mathlib.Analysis.Normed.Affine.Convex import Mathlib.Analysis.Convex.Topology import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension import Mathlib.Topology.Separation.Hausdorff import Mathlib.Analysis.Normed.Module.Connected import Mathlib.Geometry.Euclidean.Inversion.Calculus import Mathlib.MeasureTheory.Function.Jacobian import Mathlib.Analysis.SpecialFunctions.PolarCoord import Mathlib.MeasureTheory.Integral.DivergenceTheorem import DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial import Mathlib.Analysis.LocallyConvex.SeparatingDual import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundary import DifferentialGeometry.Topology.PiecewiseLinear.LinkDimension import Mathlib.Topology.MetricSpace.HausdorffDistance import DifferentialGeometry.Topology.PiecewiseLinear.ConeComplex import Mathlib.Topology.MetricSpace.Contracting import Mathlib.Analysis.SpecialFunctions.SmoothTransition import Mathlib.Analysis.Calculus.Deriv.Support import Mathlib.Analysis.Calculus.MeanValue import DifferentialGeometry.Topology.PiecewiseLinear.Subdivision import Mathlib.Analysis.Calculus.FDeriv.Norm import Mathlib.Analysis.Asymptotics.Lemmas import Mathlib.Analysis.Calculus.ContDiff.Deriv import Mathlib.Analysis.InnerProductSpace.Calculus import Mathlib.Topology.Algebra.MetricSpace.Lipschitz import Mathlib.Analysis.Calculus.TangentCone.Real
import VM03WeakJets
import Mathlib.MeasureTheory.Measure.Count

noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CountGeometry
open SeifertSurfaces.AppendixACoordinates

                                                      
                                                                
                                                                              
                                                                 
                                                                          
                                                                        
                                                                         
                                       
                                                 
                                                               
                                                  
                                       
                                                                                               
                                                                               
                                                                               
                                              
                         
                                                                                                             

                                                   
                                                             
                                                                              
                                                                 
                                                                          
                                                                        
                                                                         
                                       
                                                 
                                                               
                                                  
                                       
                                                                                               
                 
                                                  
                                                                 


end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CountGeometry
set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- Paid source: OriginalPolarOnlyConsumer
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
namespace VM03CapV437

private theorem uniform_tangent_neighborhood
    (γ : ℝ → E2) (hγ : ContDiff ℝ ∞ γ) (T : ℝ)
    (U : Set E2) (hU : IsOpen U) (hγU : ∀ t ∈ Icc (0:ℝ) T, γ t∈U)
    (L : ℝ×E2 → E2 →L[ℝ] ℝ)
    (hL : ∀ t y, y∈U → ContinuousAt L (t,y))
    (hpos : ∀ t ∈ Icc (0:ℝ) T, 0<L (t,γ t) (deriv γ t))
    (Q : ℝ×E2 → ℝ) (hQ : ∀ t y, y∈U → ContinuousAt Q (t,y))
    (hQpos : ∀ t ∈ Icc (0:ℝ) T, 0<Q (t,γ t)) :
    ∃ ε : ℝ, 0<ε ∧ ∀ t ∈ Icc (0:ℝ) T, ∀ y d : E2,
      dist y (γ t)<ε → dist d (deriv γ t)<ε → y∈U ∧ 0<L (t,y) d ∧ 0<Q (t,y) := by
  let O : Set (ℝ×(E2×E2)) := {z | z.2.1∈U ∧ 0<L (z.1,z.2.1) z.2.2 ∧ 0<Q (z.1,z.2.1)}
  have hO : IsOpen O := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hLL : ContinuousAt (fun z : ℝ×(E2×E2) => L (z.1,z.2.1)) z :=
      (hL z.1 z.2.1 hz.1).comp (f:=fun z : ℝ×(E2×E2) => (z.1,z.2.1)) (by fun_prop)
    have hLc : ContinuousAt (fun z : ℝ×(E2×E2) => (L (z.1,z.2.1)) z.2.2) z := hLL.clm_apply (by fun_prop)
    have h1 : ∀ᶠ z' : ℝ×(E2×E2) in 𝓝 z, z'.2.1∈U :=
      (show ContinuousAt (fun z : ℝ×(E2×E2) => z.2.1) z by fun_prop).eventually (hU.mem_nhds hz.1)
    have hQc : ContinuousAt (fun z : ℝ×(E2×E2) => Q (z.1,z.2.1)) z :=
      (hQ z.1 z.2.1 hz.1).comp (f:=fun z : ℝ×(E2×E2) => (z.1,z.2.1)) (by fun_prop)
    exact h1.and ((hLc.eventually (lt_mem_nhds hz.2.1)).and (hQc.eventually (lt_mem_nhds hz.2.2)))
  let K := (fun t : ℝ => (t,γ t,deriv γ t)) '' Icc (0:ℝ) T
  have hK : IsCompact K := isCompact_Icc.image
    (continuous_id.prodMk (hγ.continuous.prodMk (hγ.continuous_deriv (by simp))))
  have hKO : K⊆O := by
    rintro _ ⟨t,ht,rfl⟩
    exact ⟨hγU t ht,hpos t ht,hQpos t ht⟩
  obtain ⟨ε,hε,hthick⟩ := hK.exists_thickening_subset_open hO hKO
  refine ⟨ε,hε,?_⟩
  intro t ht y d hy hd
  change (t,y,d)∈O
  apply hthick
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(t,γ t,deriv γ t),mem_image_of_mem _ ht,?_⟩
  simp only [Prod.dist_eq,dist_self]
  exact max_lt hε (max_lt hy hd)

/- The diagonal angular derivative is exactly the collar radius.  It is
   computed from the original angular parameter, with no reparameterization. -/
private theorem angular_diagonal_identity (γ : ℝ → E2) (hγ : ContDiff ℝ ∞ γ) (v : E2 → E2)
    (U : Set E2) (hv : ∀ y∈U, ContDiffAt ℝ ∞ v y)
    (hγU : ∀ t, γ t∈U) (r : ℝ)
    (hcomp : ∀ t, v (γ t)=r • unitCircleParameter t) :
    ∀ t : ℝ, Real.cos t * (fderiv ℝ v (γ t) (deriv γ t)) 1 -
      Real.sin t * (fderiv ℝ v (γ t) (deriv γ t)) 0 = r := by
  intro t
  let u' : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-Real.sin t,Real.cos t]
  have hu : HasDerivAt unitCircleParameter u' t := by
    have hd : HasDerivAt (fun t : ℝ => ![Real.cos t,Real.sin t]) ![-Real.sin t,Real.cos t] t := by
      apply hasDerivAt_pi.mpr
      intro i
      fin_cases i
      · exact Real.hasDerivAt_cos t
      · exact Real.hasDerivAt_sin t
    exact ((EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hd
  have hvγ := ((hv (γ t) (hγU t)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    (hγ.differentiable (by simp) t).hasDerivAt
  have heq : (fun t => v (γ t))=(fun t => r • unitCircleParameter t) := funext hcomp
  have hleft : HasDerivAt (fun t => r • unitCircleParameter t)
      (fderiv ℝ v (γ t) (deriv γ t)) t := by
    rw [← heq]
    exact hvγ
  have hd := hleft.unique (hu.const_smul r)
  rw [hd]
  change Real.cos t*(r*Real.cos t)-Real.sin t*(r*(-Real.sin t))=r
  linear_combination r*(Real.cos_sq_add_sin_sq t)

/- Uniform positive angular derivative in a neighborhood of the actual
   collar tangent field.  This is the missing stability margin for secants. -/
private theorem actual_uniform_tangent_neighborhood (γ : ℝ → E2) (hγ : ContDiff ℝ ∞ γ) (v : E2 → E2)
    (U : Set E2) (hU : IsOpen U) (hv : ∀ y∈U, ContDiffAt ℝ ∞ v y)
    (hγU : ∀ t, γ t∈U) (r T : ℝ) (hr : 0<r)
    (hcomp : ∀ t, v (γ t)=r • unitCircleParameter t) :
    ∃ ε : ℝ, 0<ε ∧ ∀ t ∈ Icc (0:ℝ) T, ∀ y d : E2,
      dist y (γ t)<ε → dist d (deriv γ t)<ε → y∈U ∧
        0<Real.cos t*(fderiv ℝ v y d) 1-Real.sin t*(fderiv ℝ v y d) 0 ∧
        0<Real.cos t*(v y) 0+Real.sin t*(v y) 1 := by
  let p₀ : E2 →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p₁ : E2 →L[ℝ] ℝ := EuclideanSpace.proj 1
  let L : ℝ×E2 → E2 →L[ℝ] ℝ := fun z =>
    Real.cos z.1 • (p₁.comp (fderiv ℝ v z.2)) - Real.sin z.1 • (p₀.comp (fderiv ℝ v z.2))
  have hL : ∀ t y, y∈U → ContinuousAt L (t,y) := by
    intro t y hy
    have hD : ContinuousAt (fun z : ℝ×E2 => fderiv ℝ v z.2) (t,y) :=
      ((hv y hy).continuousAt_fderiv (by simp)).comp (f:=Prod.snd) continuousAt_snd
    have h0 : ContinuousAt (fun z : ℝ×E2 => p₀.comp (fderiv ℝ v z.2)) (t,y) := continuousAt_const.clm_comp hD
    have h1 : ContinuousAt (fun z : ℝ×E2 => p₁.comp (fderiv ℝ v z.2)) (t,y) := continuousAt_const.clm_comp hD
    exact ((Real.continuous_cos.continuousAt.comp continuousAt_fst).smul h1).sub ((Real.continuous_sin.continuousAt.comp continuousAt_fst).smul h0)
  have hdiag : ∀ t∈Icc (0:ℝ) T, 0<L (t,γ t) (deriv γ t) := by
    intro t ht
    have hd := angular_diagonal_identity γ hγ v U hv hγU r hcomp t
    change 0<Real.cos t*(fderiv ℝ v (γ t) (deriv γ t)) 1-Real.sin t*(fderiv ℝ v (γ t) (deriv γ t)) 0
    rwa [hd]
  let Q : ℝ×E2 → ℝ := fun z => Real.cos z.1*(v z.2) 0+Real.sin z.1*(v z.2) 1
  have hQ : ∀ t y, y∈U → ContinuousAt Q (t,y) := by
    intro t y hy
    have hV : ContinuousAt (fun z : ℝ×E2 => v z.2) (t,y) :=
      (hv y hy).continuousAt.comp (f:=Prod.snd) continuousAt_snd
    exact ((Real.continuous_cos.continuousAt.comp continuousAt_fst).mul
      ((EuclideanSpace.proj (𝕜:=ℝ) 0).continuous.continuousAt.comp hV)).add
      ((Real.continuous_sin.continuousAt.comp continuousAt_fst).mul
      ((EuclideanSpace.proj (𝕜:=ℝ) 1).continuous.continuousAt.comp hV))
  have hQpos : ∀ t∈Icc (0:ℝ) T, 0<Q (t,γ t) := by
    intro t ht
    change 0<Real.cos t*(v (γ t)) 0+Real.sin t*(v (γ t)) 1
    rw [hcomp]
    change 0<Real.cos t*(r*Real.cos t)+Real.sin t*(r*Real.sin t)
    have he : Real.cos t*(r*Real.cos t)+Real.sin t*(r*Real.sin t)=r := by
      linear_combination r*(Real.cos_sq_add_sin_sq t)
    rwa [he]
  exact uniform_tangent_neighborhood γ hγ T U hU (fun t _ => hγU t) L hL hdiag Q hQ hQpos
private theorem secant_estimate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (γ : ℝ → V) (hγ : Differentiable ℝ γ)
    {a b t ε : ℝ} (hab : a < b)
    (hd : ∀ u ∈ Icc a b, ‖deriv γ u - deriv γ t‖ ≤ ε) :
    ‖(b-a)⁻¹ • (γ b - γ a) - deriv γ t‖ ≤ ε := by
  have hm := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u => γ u - u • deriv γ t)
    (f' := fun u => deriv γ u - deriv γ t)
    (fun u _ => by
      convert ((hγ u).hasDerivAt.sub ((hasDerivAt_id u).smul_const (deriv γ t))).hasDerivWithinAt using 1
      · funext z; simp
      · simp)
    hd (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le)
  have hid : (γ b - b • deriv γ t) - (γ a - a • deriv γ t) =
      (γ b - γ a) - (b-a) • deriv γ t := by module
  rw [hid, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)] at hm
  have he : (b-a)⁻¹ • (γ b - γ a) - deriv γ t =
      (b-a)⁻¹ • ((γ b - γ a) - (b-a) • deriv γ t) := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab.ne'), one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (sub_pos.mpr hab))]
  calc
    _ ≤ (b-a)⁻¹ * (ε * (b-a)) := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
    _ = ε := by field_simp [sub_ne_zero.mpr hab.ne']


/- Every sufficiently short chord inherits strict angular monotonicity from
   the original collar inverse.  The paid secant estimate is consumed above. -/
private theorem short_chord_angular_control (γ : ℝ → E2) (hγ : ContDiff ℝ ∞ γ) (v : E2 → E2)
    (U : Set E2) (hU : IsOpen U) (hv : ∀ y∈U, ContDiffAt ℝ ∞ v y)
    (hγU : ∀ t, γ t∈U) (r T : ℝ) (hr : 0<r)
    (hcomp : ∀ t, v (γ t)=r • unitCircleParameter t) :
    ∃ δ : ℝ, 0<δ ∧ ∀ a∈Icc (0:ℝ) T, ∀ b∈Icc (0:ℝ) T,
      a<b → b-a<δ → ∀ t∈Icc a b,
      (∀ s∈Icc (0:ℝ) 1, AffineMap.lineMap (γ a) (γ b) s∈U) ∧
      (∀ s∈Icc (0:ℝ) 1, 0<Real.cos t*(v (AffineMap.lineMap (γ a) (γ b) s)) 0+
        Real.sin t*(v (AffineMap.lineMap (γ a) (γ b) s)) 1) ∧
      StrictMonoOn (fun s =>
        Real.cos t*(v (AffineMap.lineMap (γ a) (γ b) s)) 1-
        Real.sin t*(v (AffineMap.lineMap (γ a) (γ b) s)) 0) (Icc (0:ℝ) 1) ∧
      ∀ s ∈ Icc (0:ℝ) 1,
        0 < Real.cos t * (fderiv ℝ v (AffineMap.lineMap (γ a) (γ b) s) (γ b-γ a)) 1 -
          Real.sin t * (fderiv ℝ v (AffineMap.lineMap (γ a) (γ b) s) (γ b-γ a)) 0 := by
  obtain ⟨ε,hε,hnear⟩ := actual_uniform_tangent_neighborhood γ hγ v U hU hv hγU r T hr hcomp
  obtain ⟨δ₀,hδ₀,hmod₀⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc : IsCompact (Icc (0:ℝ) T)).uniformContinuousOn_of_continuous hγ.continuous.continuousOn) ε hε
  obtain ⟨δ₁,hδ₁,hmod₁⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc : IsCompact (Icc (0:ℝ) T)).uniformContinuousOn_of_continuous
      (hγ.continuous_deriv (by simp)).continuousOn) (ε/2) (by positivity)
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro a ha b hb hab hsmall t ht
  have htT : t∈Icc (0:ℝ) T := ⟨ha.1.trans ht.1,ht.2.trans hb.2⟩
  have hdist (u : ℝ) (hu : u∈Icc a b) : dist u t < b-a+min δ₀ δ₁-(b-a) := by
    rw [Real.dist_eq]
    have hh : |u-t|≤b-a := abs_le.mpr ⟨by linarith [hu.1,ht.2],by linarith [hu.2,ht.1]⟩
    linarith
  have hdist' (u : ℝ) (hu : u∈Icc a b) : dist u t< min δ₀ δ₁ := by simpa using hdist u hu
  let d : E2 := (b-a)⁻¹ • (γ b-γ a)
  have hd : dist d (deriv γ t)<ε := by
    rw [dist_eq_norm]
    have he := secant_estimate γ (hγ.differentiable (by simp)) hab (t:=t) (ε:=ε/2) (by
      intro u hu
      have huT : u∈Icc (0:ℝ) T := ⟨ha.1.trans hu.1,hu.2.trans hb.2⟩
      have hh := hmod₁ u huT t htT ((hdist' u hu).trans_le (min_le_right _ _))
      exact (show ‖deriv γ u-deriv γ t‖<ε/2 by simpa only [dist_eq_norm] using hh).le)
    exact he.trans_lt (by linarith)
  let c : ℝ → E2 := AffineMap.lineMap (γ a) (γ b)
  have hcnear (s : ℝ) (hs : s∈Icc (0:ℝ) 1) : dist (c s) (γ t)<ε := by
    have hA : γ a∈ball (γ t) ε := hmod₀ a ha t htT ((hdist' a (left_mem_Icc.mpr hab.le)).trans_le (min_le_left _ _))
    have hB : γ b∈ball (γ t) ε := hmod₀ b hb t htT ((hdist' b (right_mem_Icc.mpr hab.le)).trans_le (min_le_left _ _))
    exact (convex_ball (γ t) ε).segment_subset hA hB (lineMap_mem_segment ℝ (γ a) (γ b) hs)
  have hctrl (s : ℝ) (hs : s∈Icc (0:ℝ) 1) := hnear t htT (c s) d (hcnear s hs) hd
  refine ⟨fun s hs => (hctrl s hs).1,fun s hs => (hctrl s hs).2.2,?_,?_⟩
  swap
  · intro s hs
    have hdiff : γ b-γ a=(b-a) • d := by
      simp [d,smul_smul,mul_inv_cancel₀ (sub_ne_zero.mpr hab.ne')]
    have he : Real.cos t * (fderiv ℝ v (c s) (γ b-γ a)) 1 -
        Real.sin t * (fderiv ℝ v (c s) (γ b-γ a)) 0 =
        (b-a) * (Real.cos t * (fderiv ℝ v (c s) d) 1 -
          Real.sin t * (fderiv ℝ v (c s) d) 0) := by
      rw [hdiff, map_smul]
      simp only [PiLp.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    change 0 < Real.cos t * (fderiv ℝ v (c s) (γ b-γ a)) 1 -
      Real.sin t * (fderiv ℝ v (c s) (γ b-γ a)) 0
    rw [he]
    exact mul_pos (sub_pos.mpr hab) (hctrl s hs).2.1
  let H : ℝ → ℝ := fun s => Real.cos t*(v (c s)) 1-Real.sin t*(v (c s)) 0
  have hc : Continuous c := by
    have hh : Continuous (fun s : ℝ => (1-s) • γ a+s • γ b) := by fun_prop
    convert! hh using 1
    funext s
    exact AffineMap.lineMap_apply_module (γ a) (γ b) s
  have hvon : ContinuousOn v U := fun y hy => (hv y hy).continuousAt.continuousWithinAt
  have hvc : ContinuousOn (fun s => v (c s)) (Icc (0:ℝ) 1) := hvon.comp hc.continuousOn (fun s hs => (hctrl s hs).1)
  apply strictMonoOn_of_deriv_pos (convex_Icc (0:ℝ) 1)
  · exact (continuousOn_const.mul ((EuclideanSpace.proj (𝕜:=ℝ) 1).continuous.comp_continuousOn hvc)).sub
      (continuousOn_const.mul ((EuclideanSpace.proj (𝕜:=ℝ) 0).continuous.comp_continuousOn hvc))
  · intro s hs
    have hs' : s∈Icc (0:ℝ) 1 := interior_subset hs
    let L : E2 →L[ℝ] ℝ := Real.cos t • EuclideanSpace.proj 1-Real.sin t • EuclideanSpace.proj 0
    have hcv : HasDerivAt (fun s => v (c s)) (fderiv ℝ v (c s) (γ b-γ a)) s :=
      ((hv (c s) (hctrl s hs').1).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s AffineMap.hasDerivAt_lineMap
    have hh := L.hasFDerivAt.comp_hasDerivAt s hcv
    change HasDerivAt H (L (fderiv ℝ v (c s) (γ b-γ a))) s at hh
    rw [hh.deriv]
    have hdiff : γ b-γ a=(b-a) • d := by simp [d,smul_smul,mul_inv_cancel₀ (sub_ne_zero.mpr hab.ne')]
    rw [hdiff,map_smul,map_smul]
    exact mul_pos (sub_pos.mpr hab) (hctrl s hs').2.1
end VM03CapV437
noncomputable section
open Set Function
open scoped Topology ContDiff
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
namespace VM03CapV437

/- Continuous choice of the unique zero on every chord.  The target interval
   is compact, so the zero set supplies the closed graph of the choice. -/
private theorem continuous_unique_zero {X : Type*} [TopologicalSpace X]
    (F : X → ℝ → ℝ) (hF : Continuous (fun z : X × Icc (0:ℝ) 1 => F z.1 z.2))
    (hmono : ∀ x, StrictMonoOn (F x) (Icc (0:ℝ) 1))
    (hend : ∀ x, F x 0≤0 ∧ 0≤F x 1) :
    ∃ τ : X → Icc (0:ℝ) 1, Continuous τ ∧ ∀ x, F x (τ x)=0 := by
  have he (x : X) : ∃ t : Icc (0:ℝ) 1, F x t=0 := by
    have hc : ContinuousOn (F x) (Icc (0:ℝ) 1) := by
      apply continuousOn_iff_continuous_restrict.mpr
      exact hF.comp (continuous_const.prodMk continuous_id)
    obtain ⟨t,ht,hzero⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hc (hend x)
    exact ⟨⟨t,ht⟩,hzero⟩
  choose τ hτ using he
  refine ⟨τ,?_,hτ⟩
  apply continuous_of_isClosed_graph
  have heq : τ.graph={z : X × Icc (0:ℝ) 1 | F z.1 z.2=0} := by
    ext z
    constructor
    · intro hz
      have hz' : τ z.1=z.2 := hz
      change F z.1 z.2=0
      rw [← hz']
      exact hτ z.1
    · intro hz
      change τ z.1=z.2
      apply Subtype.ext
      exact (hmono z.1).injOn (τ z.1).2 z.2.2 ((hτ z.1).trans hz.symm)
  rw [heq]
  exact isClosed_eq hF continuous_const

private theorem scalar_nonzero_isInvertible (L : ℝ →L[ℝ] ℝ) (hL : L 1≠0) : L.IsInvertible := by
  have hlin (t : ℝ) : L t=t*L 1 := by
    calc
      L t=L (t • (1:ℝ)) := by simp
      _=t • L 1 := L.map_smul t 1
      _=t*L 1 := rfl
  have hi : Injective L := by
    intro x y hxy
    have hh : x * L 1 = y * L 1 := (hlin x).symm.trans (hxy.trans (hlin y))
    exact mul_right_cancel₀ hL hh
  let e := LinearEquiv.ofInjectiveEndo L.toLinearMap hi
  exact ⟨e.toContinuousLinearEquiv,rfl⟩


private theorem smooth_continuous_root_within (F : (ℝ × ℝ) → ℝ) (τ : ℝ → ℝ)
    (s : Set ℝ) (x : ℝ) (hx : x ∈ s)
    (hF : ContDiffAt ℝ ∞ F (x,τ x)) (hτ : ContinuousWithinAt τ s x)
    (hz : ∀ᶠ t in 𝓝[s] x, F (t,τ t)=F (x,τ x))
    (hd : fderiv ℝ F (x,τ x) (0,1) ≠ 0) : ContDiffWithinAt ℝ ∞ τ s x := by
  have hinv : (fderiv ℝ F (x,τ x) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible :=
    scalar_nonzero_isInvertible _ hd
  have ht : Tendsto (fun t => (t,τ t)) (𝓝[s] x) (𝓝 (x,τ x)) :=
    continuousWithinAt_id.prodMk hτ
  have he := ht.eventually (hF.eventually_apply_eq_iff_implicitFunction (by simp) hinv)
  apply (hF.contDiffAt_implicitFunction (by simp) hinv).contDiffWithinAt.congr_of_eventuallyEq
  · filter_upwards [he,hz] with t ht hz
    exact ((ht.mp hz)).symm
  · exact (hF.implicitFunction_apply_self (by simp) hinv).symm


private theorem closed_interval_root (a b : ℝ) (hab : a ≤ b)
    (F : ℝ × ℝ → ℝ)
    (hF : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, ContDiffAt ℝ ∞ F (t,s))
    (hmono : ∀ t ∈ Icc a b, StrictMonoOn (fun s => F (t,s)) (Icc (0:ℝ) 1))
    (hend : ∀ t ∈ Icc a b, F (t,0) ≤ 0 ∧ 0 ≤ F (t,1))
    (ha : F (a,0)=0) (hb : F (b,1)=0)
    (hd : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1,
      fderiv ℝ F (t,s) (0,1) ≠ 0) :
    ∃ τ : ℝ → ℝ, ContDiffOn ℝ ∞ τ (Icc a b) ∧
      (∃ K, LipschitzOnWith K τ (Icc a b)) ∧
      MapsTo τ (Icc a b) (Icc (0:ℝ) 1) ∧
      (∀ t ∈ Icc a b, F (t,τ t)=0) ∧ τ a=0 ∧ τ b=1 ∧
      τ '' Icc a b=Icc (0:ℝ) 1 := by
  classical
  have hFc : Continuous (fun z : Icc a b × Icc (0:ℝ) 1 => F (z.1,z.2)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (hF z.1 z.1.2 z.2 z.2.2).continuousAt.comp (f:=fun z : Icc a b × Icc (0:ℝ) 1 => ((z.1:ℝ),(z.2:ℝ))) (by fun_prop)
  obtain ⟨τ₀,hτ₀,hzero⟩ := continuous_unique_zero
    (fun t : Icc a b => fun s => F (t,s)) hFc (fun t => hmono t t.2) (fun t => hend t t.2)
  let τ : ℝ → ℝ := fun t => if ht : t ∈ Icc a b then τ₀ ⟨t,ht⟩ else 0
  have hτeq (t : ℝ) (ht : t ∈ Icc a b) : τ t=τ₀ ⟨t,ht⟩ := by simp only [τ,dif_pos ht]
  have hτc : ContinuousOn τ (Icc a b) := by
    apply continuousOn_iff_continuous_restrict.mpr
    convert continuous_subtype_val.comp hτ₀ using 1
    funext t
    exact hτeq t t.2
  have hm : MapsTo τ (Icc a b) (Icc (0:ℝ) 1) := by
    intro t ht
    rw [hτeq t ht]
    exact (τ₀ ⟨t,ht⟩).2
  have hz : ∀ t ∈ Icc a b, F (t,τ t)=0 := by
    intro t ht
    rw [hτeq t ht]
    exact hzero ⟨t,ht⟩
  have hτs : ContDiffOn ℝ ∞ τ (Icc a b) := by
    intro t ht
    apply smooth_continuous_root_within F τ (Icc a b) t ht (hF t ht (τ t) (hm ht)) (hτc t ht)
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact (hz u hu).trans (hz t ht).symm
    · exact hd t ht (τ t) (hm ht)
  have hea : τ a=0 := (hmono a (left_mem_Icc.mpr hab)).injOn
    (hm (left_mem_Icc.mpr hab)) (by norm_num)
    ((hz a (left_mem_Icc.mpr hab)).trans ha.symm)
  have heb : τ b=1 := (hmono b (right_mem_Icc.mpr hab)).injOn
    (hm (right_mem_Icc.mpr hab)) (by norm_num)
    ((hz b (right_mem_Icc.mpr hab)).trans hb.symm)
  refine ⟨τ,hτs,hτs.exists_lipschitzOnWith (by simp) (convex_Icc a b) isCompact_Icc,hm,hz,hea,heb,?_⟩
  apply Subset.antisymm hm.image_subset
  intro y hy
  have hv := intermediate_value_Icc hab hτc
  rw [hea,heb] at hv
  exact hv hy

private theorem positive_ray_of_cross_zero (x : E2) (t : ℝ)
    (hcross : Real.cos t*x 1-Real.sin t*x 0=0)
    (hpos : 0≤Real.cos t*x 0+Real.sin t*x 1) :
    x=‖x‖ • unitCircleParameter t := by
  let k := Real.cos t*x 0+Real.sin t*x 1
  have hk : 0≤k := hpos
  have he : x=k • unitCircleParameter t := by
    ext i
    fin_cases i
    · change x 0=(Real.cos t*x 0+Real.sin t*x 1)*Real.cos t
      linear_combination -(Real.sin t)*hcross - x 0*(Real.cos_sq_add_sin_sq t)
    · change x 1=(Real.cos t*x 0+Real.sin t*x 1)*Real.sin t
      linear_combination (Real.cos t)*hcross - x 1*(Real.cos_sq_add_sin_sq t)
  have hu : ‖unitCircleParameter t‖=1 := by
    have hh : ‖unitCircleParameter t‖^2=1 := by
      rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
      exact Real.cos_sq_add_sin_sq t
    nlinarith [norm_nonneg (unitCircleParameter t)]
  have hn : ‖x‖=k := by
    have hh := congrArg norm he
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hk,hu,mul_one] at hh
    exact hh
  rw [hn]
  exact he


private theorem angular_chord_equation (v : E2 → E2) (c : ℝ → E2)
    (t s : ℝ) (hv : ContDiffAt ℝ ∞ v (c s)) (hc : ContDiff ℝ ∞ c) :
    let F : ℝ × ℝ → ℝ := fun z =>
      Real.cos z.1 * v (c z.2) 1 - Real.sin z.1 * v (c z.2) 0
    ContDiffAt ℝ ∞ F (t,s) ∧
      fderiv ℝ F (t,s) (0,1) =
        Real.cos t * (fderiv ℝ v (c s) (deriv c s)) 1 -
          Real.sin t * (fderiv ℝ v (c s) (deriv c s)) 0 := by
  dsimp only
  let F : ℝ × ℝ → ℝ := fun z =>
    Real.cos z.1 * v (c z.2) 1 - Real.sin z.1 * v (c z.2) 0
  have hvc : ContDiffAt ℝ ∞ (v ∘ c) s := hv.comp s hc.contDiffAt
  have hcv : ContDiffAt ℝ ∞ (fun z : ℝ×ℝ => v (c z.2)) (t,s) := by fun_prop
  have hF : ContDiffAt ℝ ∞ F (t,s) := by
    dsimp [F]
    exact ((Real.contDiff_cos.contDiffAt.comp _ contDiffAt_fst).mul ((EuclideanSpace.proj (𝕜:=ℝ) 1).contDiff.contDiffAt.comp _ hcv)).sub
      ((Real.contDiff_sin.contDiffAt.comp _ contDiffAt_fst).mul ((EuclideanSpace.proj (𝕜:=ℝ) 0).contDiff.contDiffAt.comp _ hcv))
  refine ⟨hF,?_⟩
  have hvd := hv.differentiableAt (by simp) |>.hasFDerivAt
  have hcd := hc.differentiable (by simp) s |>.hasDerivAt
  have hprod : HasDerivAt (fun u : ℝ => (t,u)) (0,1) s := by
    simpa using (hasDerivAt_const s t).prodMk (hasDerivAt_id s)
  have hd₁ := (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s hprod
  have hd₂ := hvd.comp_hasDerivAt s hcd
  have hd₃ := ((EuclideanSpace.proj (𝕜:=ℝ) 1).hasFDerivAt.comp_hasDerivAt s hd₂).const_mul (Real.cos t)
  have hd₄ := ((EuclideanSpace.proj (𝕜:=ℝ) 0).hasFDerivAt.comp_hasDerivAt s hd₂).const_mul (Real.sin t)
  exact hd₁.unique (hd₃.sub hd₄)

private theorem local_boundary_reparameterization
    (γ : ℝ → E2) (hγ : ContDiff ℝ ∞ γ) (v w : E2 → E2)
    (U : Set E2) (hU : IsOpen U) (hv : ∀ y ∈ U, ContDiffAt ℝ ∞ v y)
    (hγU : ∀ t, γ t ∈ U) (r T : ℝ) (hr : 0 < r)
    (hcomp : ∀ t, v (γ t)=r • unitCircleParameter t)
    (hright : ∀ y ∈ U, w (v y)=y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ Icc (0:ℝ) T, ∀ b ∈ Icc (0:ℝ) T,
      a < b → b-a < δ →
      ∃ τ ρ : ℝ → ℝ,
        ContDiffOn ℝ ∞ τ (Icc a b) ∧ ContDiffOn ℝ ∞ ρ (Icc a b) ∧
        (∃ K, LipschitzOnWith K τ (Icc a b)) ∧
        (∃ K, LipschitzOnWith K ρ (Icc a b)) ∧
        τ '' Icc a b=Icc (0:ℝ) 1 ∧ τ a=0 ∧ τ b=1 ∧ ρ a=r ∧ ρ b=r ∧
        (∀ t ∈ Icc a b, v (AffineMap.lineMap (γ a) (γ b) (τ t))=ρ t • unitCircleParameter t) ∧
        (∀ t ∈ Icc a b, w (ρ t • unitCircleParameter t)=AffineMap.lineMap (γ a) (γ b) (τ t)) ∧
        (fun t => w (ρ t • unitCircleParameter t)) '' Icc a b=segment ℝ (γ a) (γ b) ∧
        ∀ t ∈ Icc a b, ρ t ∈ (fun y => ‖v y‖) '' U := by
  obtain ⟨δ,hδ,hchord⟩ := short_chord_angular_control γ hγ v U hU hv hγU r T hr hcomp
  refine ⟨min δ Real.pi,lt_min hδ Real.pi_pos,?_⟩
  intro a ha b hb hab hsmall
  let c : ℝ → E2 := AffineMap.lineMap (γ a) (γ b)
  have hcs : ContDiff ℝ ∞ c := by
    have hh : ContDiff ℝ ∞ (fun s : ℝ => (1-s) • γ a+s • γ b) := by fun_prop
    convert! hh using 1
    funext s
    exact AffineMap.lineMap_apply_module (γ a) (γ b) s
  have hctrl := hchord a ha b hb hab (hsmall.trans_le (min_le_left _ _))
  have hstep : b-a < Real.pi := hsmall.trans_le (min_le_right _ _)
  have hmap (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : c s ∈ U :=
    (hctrl a (left_mem_Icc.mpr hab.le)).1 s hs
  have hc0 : c 0=γ a := AffineMap.lineMap_apply_zero _ _
  have hc1 : c 1=γ b := AffineMap.lineMap_apply_one _ _
  have hra : v (c 0)=r • unitCircleParameter a := by rw [hc0,hcomp]
  have hrb : v (c 1)=r • unitCircleParameter b := by rw [hc1,hcomp]
  let F : ℝ × ℝ → ℝ := fun z => Real.cos z.1 * v (c z.2) 1-Real.sin z.1 * v (c z.2) 0
  have hend : ∀ t ∈ Icc a b, F (t,0) ≤ 0 ∧ 0 ≤ F (t,1) := by
    intro t ht
    dsimp only [F]
    rw [hra,hrb]
    constructor
    · change Real.cos t*(r*Real.sin a)-Real.sin t*(r*Real.cos a) ≤ 0
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr ht.1) (by linarith [ht.2])
      have he : Real.cos t*(r*Real.sin a)-Real.sin t*(r*Real.cos a)=-(r*Real.sin (t-a)) := by
        rw [Real.sin_sub]; ring
      rw [he]
      exact neg_nonpos.mpr (mul_nonneg hr.le hs)
    · change 0 ≤ Real.cos t*(r*Real.sin b)-Real.sin t*(r*Real.cos b)
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr ht.2) (by linarith [ht.1])
      have he : Real.cos t*(r*Real.sin b)-Real.sin t*(r*Real.cos b)=r*Real.sin (b-t) := by
        rw [Real.sin_sub]; ring
      rw [he]
      exact mul_nonneg hr.le hs
  have hFa : F (a,0)=0 := by
    dsimp only [F]; rw [hra]
    change Real.cos a*(r*Real.sin a)-Real.sin a*(r*Real.cos a)=0
    ring
  have hFb : F (b,1)=0 := by
    dsimp only [F]; rw [hrb]
    change Real.cos b*(r*Real.sin b)-Real.sin b*(r*Real.cos b)=0
    ring
  have hFs (t : ℝ) (ht : t ∈ Icc a b) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :=
    angular_chord_equation v c t s (hv (c s) (hmap s hs)) hcs
  obtain ⟨τ,hτs,hτL,hτm,hτzero,hτa,hτb,hτimage⟩ := closed_interval_root a b hab.le F
    (fun t ht s hs => (hFs t ht s hs).1)
    (fun t ht => (hctrl t ht).2.2.1) hend hFa hFb (by
      intro t ht s hs
      rw [(hFs t ht s hs).2]
      have hder : deriv c s=γ b-γ a := AffineMap.hasDerivAt_lineMap.deriv
      rw [hder]
      exact ((hctrl t ht).2.2.2 s hs).ne')
  let ρ : ℝ → ℝ := fun t => ‖v (c (τ t))‖
  have hn (t : ℝ) (ht : t ∈ Icc a b) : v (c (τ t)) ≠ 0 := by
    have hh := (hctrl t ht).2.1 (τ t) (hτm ht)
    intro he
    rw [he] at hh
    norm_num at hh
  have hρs : ContDiffOn ℝ ∞ ρ (Icc a b) := by
    intro t ht
    exact ((hv (c (τ t)) (hmap (τ t) (hτm ht))).comp_contDiffWithinAt t
      (hcs.contDiffAt.comp_contDiffWithinAt t (hτs t ht))).norm ℝ (hn t ht)
  have hvcomp (t : ℝ) (ht : t ∈ Icc a b) : v (c (τ t))=ρ t • unitCircleParameter t :=
    positive_ray_of_cross_zero _ t (hτzero t ht) ((hctrl t ht).2.1 (τ t) (hτm ht)).le
  have hwcomp (t : ℝ) (ht : t ∈ Icc a b) : w (ρ t • unitCircleParameter t)=c (τ t) := by
    rw [← hvcomp t ht]
    exact hright (c (τ t)) (hmap (τ t) (hτm ht))
  have hnorm (t : ℝ) : ‖r • unitCircleParameter t‖=r := by
    have hu : ‖unitCircleParameter t‖=1 := by
      have hh : ‖unitCircleParameter t‖^2=1 := by
        rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
        exact Real.cos_sq_add_sin_sq t
      nlinarith [norm_nonneg (unitCircleParameter t)]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hu,mul_one]
  refine ⟨τ,ρ,hτs,hρs,hτL,hρs.exists_lipschitzOnWith (by simp) (convex_Icc a b) isCompact_Icc,
    hτimage,hτa,hτb,?_,?_,hvcomp,hwcomp,?_,?_⟩
  · dsimp only [ρ]; rw [hτa,hra,hnorm]
  · dsimp only [ρ]; rw [hτb,hrb,hnorm]
  · rw [image_congr hwcomp,← image_image,hτimage]
    exact (segment_eq_image_lineMap ℝ (γ a) (γ b)).symm
  · intro t ht
    exact ⟨c (τ t),hmap (τ t) (hτm ht),rfl⟩

private theorem finite_closed_gluing {ι : Type*} [Fintype ι]
    (S : ι → Set ℝ) (hS : ∀ i, IsClosed (S i))
    (f : ∀ i, S i → ℝ) (hf : ∀ i, Continuous (f i))
    (hagree : ∀ i j (x : ℝ) (hi : x∈S i) (hj : x∈S j), f i ⟨x,hi⟩=f j ⟨x,hj⟩) :
    ∃ g : ℝ → ℝ, ContinuousOn g (⋃ i, S i) ∧
      ∀ i (x : ℝ) (hx : x∈S i), g x=f i ⟨x,hx⟩ := by
  classical
  let g : ℝ → ℝ := fun x => if h : ∃ i, x∈S i then f h.choose ⟨x,h.choose_spec⟩ else 0
  have hg (i : ι) (x : ℝ) (hx : x∈S i) : g x=f i ⟨x,hx⟩ := by
    have h : ∃ i, x∈S i := ⟨i,hx⟩
    dsimp only [g]
    rw [dif_pos h]
    exact hagree _ i x _ hx
  refine ⟨g,?_,hg⟩
  apply LocallyFinite.continuousOn_iUnion (locallyFinite_of_finite S) hS
  intro i
  apply continuousOn_iff_continuous_restrict.mpr
  have he : (fun x : S i => g x)=f i := funext (fun x => hg i x x.2)
  change Continuous (fun x : S i => g x)
  rw [he]
  exact hf i

/- Adjacent interval profiles with a common endpoint value produce a
   continuous periodic profile.  The original real parameter is retained. -/
private theorem finite_periodic_profile (N : ℕ) (hN : 0<N) (h : ℝ) (hh : 0<h) (r : ℝ)
    (ρ : ∀ i : Fin N, Icc ((i:ℝ)*h) (((i.1+1:ℕ):ℝ)*h) → ℝ)
    (hρ : ∀ i, Continuous (ρ i))
    (hends : ∀ (i : Fin N) (t : ℝ) (ht : t∈Icc ((i:ℝ)*h) (((i.1+1:ℕ):ℝ)*h)),
      t=(i:ℝ)*h ∨ t=(((i.1+1:ℕ):ℝ)*h) → ρ i ⟨t,ht⟩=r) :
    ∃ R : ℝ → ℝ, Continuous R ∧ Periodic R ((N:ℝ)*h) ∧
      ∀ (i : Fin N) (t : ℝ) (ht : t∈Icc ((i:ℝ)*h) (((i.1+1:ℕ):ℝ)*h)),
        R t=ρ i ⟨t,ht⟩ := by
  classical
  let S : Fin N → Set ℝ := fun i => Icc ((i:ℝ)*h) (((i.1+1:ℕ):ℝ)*h)
  have hstep (i : Fin N) : ((i.1+1:ℕ):ℝ)*h=(i:ℝ)*h+h := by push_cast; ring
  have hagree : ∀ i j (x : ℝ) (hi : x∈S i) (hj : x∈S j), ρ i ⟨x,hi⟩=ρ j ⟨x,hj⟩ := by
    intro i j x hi hj
    by_cases hij : i=j
    · subst j
      rfl
    · have hne : i.1≠j.1 := fun h => hij (Fin.ext h)
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hle : (i.1+1:ℝ)≤j.1 := by exact_mod_cast (show i.1+1≤j.1 by omega)
        have hbnd := mul_le_mul_of_nonneg_right hle hh.le
        have hx1 : x=((i.1+1:ℕ):ℝ)*h := by
          change (i:ℝ)*h≤x ∧ x≤((i.1+1:ℕ):ℝ)*h at hi
          change (j:ℝ)*h≤x ∧ x≤((j.1+1:ℕ):ℝ)*h at hj
          push_cast at *
          linarith [hi.2,hj.1]
        have hx2 : x=(j:ℝ)*h := by
          change (i:ℝ)*h≤x ∧ x≤((i.1+1:ℕ):ℝ)*h at hi
          change (j:ℝ)*h≤x ∧ x≤((j.1+1:ℕ):ℝ)*h at hj
          push_cast at *
          linarith [hi.2,hj.1]
        exact (hends i x hi (Or.inr hx1)).trans (hends j x hj (Or.inl hx2)).symm
      · have hle : (j.1+1:ℝ)≤ i.1 := by exact_mod_cast (show j.1+1≤ i.1 by omega)
        have hbnd := mul_le_mul_of_nonneg_right hle hh.le
        have hx1 : x=((j.1+1:ℕ):ℝ)*h := by
          change (i:ℝ)*h≤x ∧ x≤((i.1+1:ℕ):ℝ)*h at hi
          change (j:ℝ)*h≤x ∧ x≤((j.1+1:ℕ):ℝ)*h at hj
          push_cast at *
          linarith [hj.2,hi.1]
        have hx2 : x=(i:ℝ)*h := by
          change (i:ℝ)*h≤x ∧ x≤((i.1+1:ℕ):ℝ)*h at hi
          change (j:ℝ)*h≤x ∧ x≤((j.1+1:ℕ):ℝ)*h at hj
          push_cast at *
          linarith [hj.2,hi.1]
        exact (hends i x hi (Or.inl hx2)).trans (hends j x hj (Or.inr hx1)).symm
  obtain ⟨g,hg,hgρ⟩ := finite_closed_gluing S (fun _ => isClosed_Icc) ρ hρ hagree
  have hcover : (⋃ i, S i)=Icc (0:ℝ) ((N:ℝ)*h) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      refine ⟨(mul_nonneg (Nat.cast_nonneg _) hh.le).trans hi.1,hi.2.trans ?_⟩
      apply mul_le_mul_of_nonneg_right _ hh.le
      exact_mod_cast (show i.1+1≤ N by omega)
    · intro x hx
      by_cases hxend : x=(N:ℝ)*h
      · refine mem_iUnion.mpr ⟨⟨N-1,by omega⟩,?_⟩
        change (N-1:ℕ)*h≤x ∧ x≤(((N-1)+1:ℕ):ℝ)*h
        rw [hxend,show N-1+1=N by omega]
        exact ⟨mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N 1) hh.le,le_rfl⟩
      · have hxlt : x<(N:ℝ)*h := lt_of_le_of_ne hx.2 hxend
        let i := Nat.floor (x/h)
        have hxh : 0≤x/h := div_nonneg hx.1 hh.le
        have hi0 : (i:ℝ)≤x/h := Nat.floor_le hxh
        have hi1 : x/h<(i:ℝ)+1 := Nat.lt_floor_add_one _
        have hiN : i<N := by
          have hquot : x/h<(N:ℝ) := (div_lt_iff₀ hh).mpr hxlt
          exact_mod_cast hi0.trans_lt hquot
        refine mem_iUnion.mpr ⟨⟨i,hiN⟩,?_⟩
        constructor
        · exact (le_div_iff₀ hh).mp hi0
        · have hh' := (div_lt_iff₀ hh).mp hi1
          push_cast
          exact hh'.le
  have hgcont : ContinuousOn g (Icc (0:ℝ) ((N:ℝ)*h)) := hcover ▸ hg
  let T : ℝ := (N:ℝ)*h
  have hT : 0<T := mul_pos (by exact_mod_cast hN) hh
  letI : Fact (0<T) := ⟨hT⟩
  have hg0 : g 0=r := by
    have hz : (0:ℝ)∈S ⟨0,hN⟩ := by dsimp [S]; simp; linarith
    exact (hgρ ⟨0,hN⟩ 0 hz).trans (hends ⟨0,hN⟩ 0 hz (Or.inl (by simp)))
  have hgT : g T=r := by
    have hn : N-1+1=N := by omega
    have hz : T∈S ⟨N-1,by omega⟩ := by
      dsimp [S,T]
      rw [hn]
      exact ⟨mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N 1) hh.le,le_rfl⟩
    exact (hgρ ⟨N-1,by omega⟩ T hz).trans (hends ⟨N-1,by omega⟩ T hz (Or.inr (by dsimp [T]; rw [hn])))
  let R : ℝ → ℝ := fun t => AddCircle.liftIco T 0 g (t : AddCircle T)
  have hR : Continuous R := (AddCircle.liftIco_zero_continuous (hg0.trans hgT.symm) hgcont).comp continuous_quotient_mk'
  have hper : Periodic R T := by
    intro t
    dsimp [R]
    simp only [AddCircle.coe_period,add_zero]
  refine ⟨R,hR,hper,?_⟩
  intro i t ht
  have htbig : t∈Icc (0:ℝ) T := hcover ▸ (mem_iUnion.mpr ⟨i,ht⟩)
  by_cases hend : t=T
  · subst t
    have hR0 : R 0=g 0 := AddCircle.liftIco_zero_coe_apply ⟨le_rfl,hT⟩
    have hRT : R T=R 0 := by simpa using hper 0
    rw [hRT,hR0,hg0]
    exact ((hgρ i T ht).symm.trans hgT).symm
  · have ht' : t∈Ico (0:ℝ) T := ⟨htbig.1,lt_of_le_of_ne htbig.2 hend⟩
    exact (AddCircle.liftIco_zero_coe_apply ht').trans (hgρ i t ht)
private theorem global_boundary_reparameterization (γ : ℝ → E2) (hγ : ContDiff ℝ ∞ γ) (v w : E2 → E2)
    (U : Set E2) (hU : IsOpen U) (hv : ∀ y∈U, ContDiffAt ℝ ∞ v y)
    (hγU : ∀ t, γ t∈U) (r : ℝ) (hr : 0<r)
    (hcomp : ∀ t, v (γ t)=r • unitCircleParameter t)
    (hright : ∀ y∈U, w (v y)=y) :
    ∃ (N : ℕ) (ρ : ℝ → ℝ), 3≤N ∧ Continuous ρ ∧ Periodic ρ (2*Real.pi) ∧
      (∀ t, ρ t∈(fun y => ‖v y‖) '' U) ∧
      (∀ i : Fin N, ρ ((i:ℝ)*(2*Real.pi/N))=r) ∧
      range (fun t => w (ρ t • unitCircleParameter t)) =
        ⋃ i : Fin N, segment ℝ (γ ((i:ℝ)*(2*Real.pi/N)))
          (γ (((i.1+1:ℕ):ℝ)*(2*Real.pi/N))) ∧
      ∀ i : Fin N, let a := (i:ℝ)*(2*Real.pi/N); let b := ((i.1+1:ℕ):ℝ)*(2*Real.pi/N)
        ContDiffOn ℝ ∞ ρ (Icc a b) ∧
        (∃ K, LipschitzOnWith K ρ (Icc a b)) ∧
        ∃ τ : ℝ → ℝ, ContDiffOn ℝ ∞ τ (Icc a b) ∧
          (∃ K, LipschitzOnWith K τ (Icc a b)) ∧
          τ '' Icc a b=Icc (0:ℝ) 1 ∧ τ a=0 ∧ τ b=1 ∧
          (∀ t ∈ Icc a b, v (AffineMap.lineMap (γ a) (γ b) (τ t))=ρ t • unitCircleParameter t) ∧
          (∀ t ∈ Icc a b, w (ρ t • unitCircleParameter t)=AffineMap.lineMap (γ a) (γ b) (τ t)) := by
  let T := 2*Real.pi
  have hT : 0<T := by dsimp [T]; positivity
  obtain ⟨δ,hδ,hlocal⟩  := local_boundary_reparameterization γ hγ v w U hU hv hγU r T hr hcomp hright
  obtain ⟨N,hN⟩ := exists_nat_gt (max 3 (T/δ))
  have hN3 : 3≤N := by exact_mod_cast (le_of_lt ((le_max_left _ _).trans_lt hN))
  have hN0 : 0<N := by omega
  have hNR : (0:ℝ)<N := by exact_mod_cast hN0
  let h := T/N
  have hh : 0<h := div_pos hT hNR
  have hNh : (N:ℝ)*h=T := by dsimp [h]; field_simp
  have hsmall : h<δ := by
    apply (div_lt_iff₀ hNR).mpr
    have hh' := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hN)
    linarith
  let a : Fin N → ℝ := fun i => (i:ℝ)*h
  let b : Fin N → ℝ := fun i => (((i.1+1:ℕ):ℝ)*h)
  have hdiff (i : Fin N) : b i-a i=h := by dsimp [a,b]; push_cast; ring
  have hab (i : Fin N) : a i<b i := by linarith [hdiff i]
  have ha (i : Fin N) : a i∈Icc (0:ℝ) T := by
    refine ⟨mul_nonneg (Nat.cast_nonneg _) hh.le,?_⟩
    rw [← hNh]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast i.isLt.le) hh.le
  have hb (i : Fin N) : b i∈Icc (0:ℝ) T := by
    refine ⟨mul_nonneg (Nat.cast_nonneg _) hh.le,?_⟩
    rw [← hNh]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show i.1+1≤N by omega)) hh.le
  have hex (i : Fin N) := hlocal (a i) (ha i) (b i) (hb i) (hab i) (by rw [hdiff]; exact hsmall)
  choose τ ρ₀ hτs hρs hτL hρL hτim hτa hτb hρa₀ hρb₀ hvcomp hwcomp hρimage hρval₀ using hex
  let ρ : ∀ i : Fin N, Icc (a i) (b i) → ℝ := fun i t => ρ₀ i t
  have hρ (i : Fin N) : Continuous (ρ i) := (hρs i).continuousOn.restrict
  have hρa (i : Fin N) : ρ i ⟨a i,left_mem_Icc.mpr (hab i).le⟩=r := hρa₀ i
  have hρb (i : Fin N) : ρ i ⟨b i,right_mem_Icc.mpr (hab i).le⟩=r := hρb₀ i
  have hρval (i : Fin N) (t : Icc (a i) (b i)) : ρ i t ∈ (fun y => ‖v y‖) '' U := hρval₀ i t t.2
  have hρrange (i : Fin N) : range (fun t : Icc (a i) (b i) => w (ρ i t • unitCircleParameter t))=
      segment ℝ (γ (a i)) (γ (b i)) := by
    rw [← hρimage i]
    exact Set.range_restrict (fun t => w (ρ₀ i t • unitCircleParameter t)) (Icc (a i) (b i))
  have hends : ∀ (i : Fin N) (t : ℝ) (ht : t∈Icc (a i) (b i)),
      t=a i ∨ t=b i → ρ i ⟨t,ht⟩=r := by
    intro i t ht he
    rcases he with rfl | rfl
    · exact hρa i
    · exact hρb i
  obtain ⟨R,hR,hRp,hmatch⟩ := finite_periodic_profile N hN0 h hh r ρ hρ hends
  have hper : Periodic R T := by rwa [hNh] at hRp
  have hcover : ∀ t∈Ico (0:ℝ) T, ∃ i : Fin N, t∈Icc (a i) (b i) := by
    intro t ht
    let i := Nat.floor (t/h)
    have hq : 0≤t/h := div_nonneg ht.1 hh.le
    have hilow : (i:ℝ)≤t/h := Nat.floor_le hq
    have hihigh : t/h<(i:ℝ)+1 := Nat.lt_floor_add_one _
    have hiN : i<N := by
      have hqN : t/h<(N:ℝ) := (div_lt_iff₀ hh).mpr (by rw [hNh]; exact ht.2)
      exact_mod_cast hilow.trans_lt hqN
    refine ⟨⟨i,hiN⟩,(le_div_iff₀ hh).mp hilow,?_⟩
    have hbound := (div_lt_iff₀ hh).mp hihigh
    dsimp [b]
    push_cast
    exact hbound.le
  have hvalues : ∀ t, R t∈(fun y => ‖v y‖) '' U := by
    intro t
    obtain ⟨s,hs,he⟩ := hper.exists_mem_Ico hT t 0
    have hs' : s∈Ico (0:ℝ) T := by simpa using hs
    obtain ⟨i,hi⟩ := hcover s hs'
    rw [he,hmatch i s hi]
    exact hρval i ⟨s,hi⟩
  have hunit : Periodic unitCircleParameter T := by
    intro t
    ext i
    fin_cases i
    · exact Real.cos_periodic t
    · exact Real.sin_periodic t
  let H : ℝ → E2 := fun t => w (R t • unitCircleParameter t)
  have hHper : Periodic H T := by
    intro t
    dsimp [H]
    rw [hper t,hunit t]
  refine ⟨N,R,hN3,hR,hper,hvalues,?_,?_,?_⟩
  · intro i
    exact (hmatch i (a i) (left_mem_Icc.mpr (hab i).le)).trans (hρa i)
  · apply Subset.antisymm
    · rintro _ ⟨t,rfl⟩
      obtain ⟨s,hs,he⟩ := hHper.exists_mem_Ico hT t 0
      obtain ⟨i,hi⟩ := hcover s (by simpa using hs)
      apply mem_iUnion.mpr
      refine ⟨i,?_⟩
      change H t∈segment ℝ (γ (a i)) (γ (b i))
      rw [he]
      change w (R s • unitCircleParameter s)∈_
      rw [hmatch i s hi,← hρrange i]
      exact ⟨⟨s,hi⟩,rfl⟩
    · intro y hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      change y∈segment ℝ (γ (a i)) (γ (b i)) at hi
      rw [← hρrange i] at hi
      obtain ⟨t,ht⟩ := hi
      refine ⟨t,?_⟩
      change w (R t • unitCircleParameter t)=y
      rw [hmatch i t t.2]
      exact ht
  · intro i
    change ContDiffOn ℝ ∞ R (Icc (a i) (b i)) ∧ _
    have he : EqOn R (ρ₀ i) (Icc (a i) (b i)) := fun t ht => hmatch i t ht
    refine ⟨(hρs i).congr he,?_,τ i,hτs i,hτL i,hτim i,hτa i,hτb i,?_,?_⟩
    · obtain ⟨K,hK⟩ := hρL i
      refine ⟨K,?_⟩
      intro x hx y hy
      rw [he hx,he hy]
      exact hK hx hy
    · intro t ht
      rw [he ht]
      exact hvcomp i t ht
    · intro t ht
      rw [he ht]
      exact hwcomp i t ht

end VM03CapV437

namespace VM03CapV437
private theorem smooth_inverse_on_image
    (w : E2 → E2) (hw : ContDiff ℝ ∞ w) (U : Set E2) (hU : IsOpen U)
    (hinj : InjOn w U) (hdet : ∀ x ∈ U, (fderiv ℝ w x).det ≠ 0) :
    ∀ y ∈ w '' U, ContDiffAt ℝ ∞ (invFunOn w U) y := by
  rintro y ⟨x,hx,rfl⟩
  let L := (fderiv ℝ w x).toLinearMap.equivOfDetNeZero (hdet x hx)
  let e := L.toContinuousLinearEquiv
  have he : (e:E2 →L[ℝ] E2)=fderiv ℝ w x := by ext z; rfl
  have hd : HasFDerivAt w (e:E2 →L[ℝ] E2) x := by
    rw [he]
    exact (hw.differentiable (by simp) x).hasFDerivAt
  let H := hw.contDiffAt.toOpenPartialHomeomorph w hd (by simp)
  have hxH : x ∈ H.source := hw.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hV : IsOpen (w '' (H.source ∩ U)) :=
    H.isOpen_image_of_subset_source (H.open_source.inter hU) inter_subset_left
  have hlocal : ContDiffAt ℝ ∞ H.symm (w x) :=
    hw.contDiffAt.to_localInverse hd (by simp)
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds ⟨x,⟨hxH,hx⟩,rfl⟩] with z hz
  obtain ⟨a,ha,rfl⟩ := hz
  rw [hinj.leftInvOn_invFunOn ha.2]
  exact (H.left_inv ha.1).symm


private theorem isOpen_image_of_det_ne_zero (w : E2 → E2) (hw : ContDiff ℝ ∞ w)
    (U : Set E2) (hU : IsOpen U)
    (hdet : ∀ x ∈ U, (fderiv ℝ w x).det ≠ 0) : IsOpen (w '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x,hx,rfl⟩
  let L := (fderiv ℝ w x).toLinearMap.equivOfDetNeZero (hdet x hx)
  let e := L.toContinuousLinearEquiv
  have he : (e : E2 →L[ℝ] E2) = fderiv ℝ w x := by ext z; rfl
  have hd : HasFDerivAt w (e : E2 →L[ℝ] E2) x := by
    rw [he]
    exact (hw.differentiable (by simp) x).hasFDerivAt
  let H := hw.contDiffAt.toOpenPartialHomeomorph w hd (by simp)
  have hxH : x ∈ H.source := hw.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hopen : IsOpen (w '' (H.source ∩ U)) :=
    H.isOpen_image_of_subset_source (H.open_source.inter hU) inter_subset_left
  exact Filter.mem_of_superset (hopen.mem_nhds ⟨x,⟨hxH,hx⟩,rfl⟩)
    (image_mono inter_subset_right)



end VM03CapV437

namespace VM03CapV437
private theorem support_BoundaryReparameterization_1 (w : E2 → E2) (η r : ℝ)
    (hw : ContDiff ℝ ∞ w) (hη0 : 0<η) (hη1 : η<1) (hr : 1-η<r) (hr1 : r<1)
    (hi : InjOn w {x : E2 | |‖x‖-1|<η})
    (hdet : ∀ x : E2, |‖x‖-1|<η → (fderiv ℝ w x).det≠0) :
    ∃ (N : ℕ) (ρ : ℝ → ℝ), 3≤N ∧ Continuous ρ ∧ Periodic ρ (2*Real.pi) ∧
      (∀ t, 1-η<ρ t ∧ ρ t<1) ∧
      (∀ i : ℕ, i<N → ρ ((i:ℝ)*(2*Real.pi/N))=r) ∧
      range (fun t => w (ρ t • unitCircleParameter t)) =
        ⋃ i : Fin N, segment ℝ
          (w (r • unitCircleParameter ((i:ℝ)*(2*Real.pi/N))))
          (w (r • unitCircleParameter (((i.1+1:ℕ):ℝ)*(2*Real.pi/N)))) ∧
      ∀ i : Fin N, let a := (i:ℝ)*(2*Real.pi/N); let b := ((i.1+1:ℕ):ℝ)*(2*Real.pi/N)
        ContDiffOn ℝ ∞ ρ (Icc a b) ∧ (∃ K, LipschitzOnWith K ρ (Icc a b)) ∧
        ∃ τ : ℝ → ℝ, ContDiffOn ℝ ∞ τ (Icc a b) ∧
          (∃ K, LipschitzOnWith K τ (Icc a b)) ∧
          τ '' Icc a b=Icc (0:ℝ) 1 ∧ τ a=0 ∧ τ b=1 ∧
          (∀ t ∈ Icc a b, w (ρ t • unitCircleParameter t)=
            AffineMap.lineMap (w (r • unitCircleParameter a)) (w (r • unitCircleParameter b)) (τ t)) := by
  let A : Set E2 := {x | 1-η<‖x‖ ∧ ‖x‖<1}
  let U := w '' A
  let v := invFunOn w A
  let γ : ℝ → E2 := fun t => w (r • unitCircleParameter t)
  have hr0 : 0<r := by linarith
  have hA : IsOpen A := (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hsub : A⊆{x : E2 | |‖x‖-1|<η} := by
    intro x hx
    change |‖x‖-1|<η
    change 1-η<‖x‖ ∧ ‖x‖<1 at hx
    rw [abs_lt]
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hiA : InjOn w A := hi.mono hsub
  have hdetA : ∀ x∈A, (fderiv ℝ w x).det≠0 := fun x hx => hdet x (hsub hx)
  have hU : IsOpen U := isOpen_image_of_det_ne_zero w hw A hA hdetA
  have hv : ∀ y∈U, ContDiffAt ℝ ∞ v y := smooth_inverse_on_image w hw A hA hiA hdetA
  have hu : ContDiff ℝ ∞ unitCircleParameter := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp [unitCircleParameter] <;> fun_prop
  have hγ : ContDiff ℝ ∞ γ := by
    exact hw.comp ((contDiff_const_smul (𝕜:=ℝ) r).comp hu)
  have hun (t : ℝ) : ‖unitCircleParameter t‖=1 := by
    have hh : ‖unitCircleParameter t‖^2=1 := by
      rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
      exact Real.cos_sq_add_sin_sq t
    nlinarith [norm_nonneg (unitCircleParameter t)]
  have hparam (t : ℝ) : r • unitCircleParameter t∈A := by
    have hn : ‖r • unitCircleParameter t‖=r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr0,hun,mul_one]
    change 1-η<‖r • unitCircleParameter t‖ ∧ ‖r • unitCircleParameter t‖<1
    rw [hn]
    exact ⟨hr,hr1⟩
  have hγU : ∀ t, γ t∈U := fun t => mem_image_of_mem w (hparam t)
  have hcomp : ∀ t, v (γ t)=r • unitCircleParameter t := fun t => hiA.leftInvOn_invFunOn (hparam t)
  have hright : ∀ y∈U, w (v y)=y := fun y hy => invFunOn_eq hy
  obtain ⟨N,ρ,hN,hρ,hper,hvalue,hvertices,hcarrier,hpieces⟩ :=
    global_boundary_reparameterization γ hγ v w U hU hv hγU r hr0 hcomp hright
  refine ⟨N,ρ,hN,hρ,hper,?_,?_,hcarrier,?_⟩
  · intro t
    obtain ⟨y,hy,he⟩ := hvalue t
    have hmem : v y∈A := invFunOn_mem hy
    change 1-η<‖v y‖ ∧ ‖v y‖<1 at hmem
    change ‖v y‖=ρ t at he
    rwa [he] at hmem
  · intro i hi
    exact hvertices ⟨i,hi⟩
  · intro i
    obtain ⟨hρs,hρL,τ,hτs,hτL,him,ha,hb,hv,hw⟩ := hpieces i
    exact ⟨hρs,hρL,τ,hτs,hτL,him,ha,hb,hw⟩
end VM03CapV437
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
namespace VM03CapV437

private theorem angular_profile (ρ : ℝ → ℝ) (hρ : Continuous ρ)
    (hper : Periodic ρ (2*Real.pi)) :
    ∃ A : E2 → ℝ,
      (∀ x, x ≠ 0 → ContinuousAt A x) ∧
      (∀ x (r : ℝ), 0 < r → A (r • x)=A x) ∧
      (∀ t, A (unitCircleParameter t)=ρ t) ∧
      ∀ x, ∃ t, A x=ρ t := by
  let e : E2 → ℂ := fun x => ⟨x 0,x 1⟩
  have hec : Continuous e := by
    exact Complex.equivRealProdCLM.symm.continuous.comp
      ((EuclideanSpace.proj (𝕜:=ℝ) 0).continuous.prodMk (EuclideanSpace.proj (𝕜:=ℝ) 1).continuous)
  have he0 (x : E2) (hx : x ≠ 0) : e x ≠ 0 := by
    intro he
    apply hx
    ext i
    fin_cases i
    · exact congrArg Complex.re he
    · exact congrArg Complex.im he
  let f : AddCircle (2*Real.pi) → ℝ := hper.lift
  have hfc : Continuous f := continuous_coinduced_dom.mpr hρ
  have hf (t : ℝ) : f (t : AddCircle (2*Real.pi))=ρ t := rfl
  let A : E2 → ℝ := fun x => f (Complex.arg (e x) : Real.Angle)
  refine ⟨A,?_,?_,?_,?_⟩
  · intro x hx
    exact hfc.continuousAt.comp ((Complex.continuousAt_arg_coe_angle (he0 x hx)).comp hec.continuousAt)
  · intro x r hr
    have he : e (r • x)=(r:ℂ)*e x := by
      apply Complex.ext <;> simp [e,PiLp.smul_apply,smul_eq_mul]
    dsimp only [A]
    rw [he,Complex.arg_real_mul _ hr]
  · intro t
    have he : e (unitCircleParameter t)=(Real.cos t:ℂ)+(Real.sin t:ℂ)*Complex.I := by
      apply Complex.ext <;> simp only [e,unitCircleParameter,Complex.add_re,Complex.add_im,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,zero_add,add_zero]
      all_goals rfl
    dsimp only [A]
    rw [he]
    have ha := Complex.arg_cos_add_sin_mul_I_coe_angle (t : Real.Angle)
    rw [show (Complex.arg ((Real.cos t:ℂ)+(Real.sin t:ℂ)*Complex.I) : Real.Angle)=(t:Real.Angle) by simpa using ha]
    exact hf t
  · intro x
    exact ⟨Complex.arg (e x),hf _⟩

private theorem radial_segment (a b p : ℝ) (hab : a < b) (hp : p < b) :
    let f : ℝ → ℝ := fun r => p+(r-a)*(b-p)/(b-a)
    StrictMono f ∧ f a=p ∧ f b=b ∧ f '' Icc a b=Icc p b := by
  dsimp only
  let f : ℝ → ℝ := fun r => p+(r-a)*(b-p)/(b-a)
  have hm : StrictMono f := by
    intro x y hxy
    apply add_lt_add_right
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (sub_lt_sub_right hxy a)
      (sub_pos.mpr hp)) (sub_pos.mpr hab)
  have ha : f a=p := by simp [f]
  have hb : f b=b := by dsimp [f]; field_simp [(sub_pos.mpr hab).ne']; ring
  refine ⟨hm,ha,hb,?_⟩
  have hc : Continuous f := by dsimp [f]; fun_prop
  apply Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨by simpa only [ha] using hm.monotone hx.1,by simpa only [hb] using hm.monotone hx.2⟩
  · have hh := intermediate_value_Icc hab.le hc.continuousOn
    rwa [ha,hb] at hh

private theorem radial_annulus (A : E2 → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hA : ∀ x, 0 < A x ∧ A x < b)
    (hAh : ∀ x (r : ℝ), 0 < r → A (r • x)=A x)
    (hAc : ∀ x, x ≠ 0 → ContinuousAt A x) :
    ∃ T : E2 → E2,
      ContinuousOn T {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} ∧
      BijOn T {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} {y | A y ≤ ‖y‖ ∧ ‖y‖ ≤ b} ∧
      (∀ x, ‖x‖=a → T x=(A x/a) • x) ∧
      (∀ x, ‖x‖=b → T x=x) ∧
      (∀ x, a ≤ ‖x‖ → ‖x‖ ≤ b → A (T x)=A x) ∧
      ∀ x, a ≤ ‖x‖ → ‖x‖ ≤ b →
        ‖T x‖=A x+(‖x‖-a)*(b-A x)/(b-a) := by
  let D : Set E2 := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}
  let E : Set E2 := {y | A y ≤ ‖y‖ ∧ ‖y‖ ≤ b}
  let f : E2 → ℝ → ℝ := fun x r => A x+(r-a)*(b-A x)/(b-a)
  have hf (x : E2) : StrictMono (f x) ∧ f x a=A x ∧ f x b=b ∧ f x '' Icc a b=Icc (A x) b :=
    radial_segment a b (A x) hab (hA x).2
  have hn (x : E2) (hx : x ∈ D) : 0 < ‖x‖ := ha.trans_le hx.1
  have hfn (x : E2) (hx : x ∈ D) : 0 < f x ‖x‖ :=
    (hA x).1.trans_le (by
      have hh := (hf x).1.monotone hx.1
      rwa [(hf x).2.1] at hh)
  let T : E2 → E2 := fun x => (f x ‖x‖/‖x‖) • x
  have hnorm (x : E2) (hx : x ∈ D) : ‖T x‖=f x ‖x‖ := by
    rw [show T x=(f x ‖x‖/‖x‖) • x from rfl,norm_smul,Real.norm_eq_abs,
      abs_of_pos (div_pos (hfn x hx) (hn x hx)),div_mul_cancel₀ _ (hn x hx).ne']
  have hprofile (x : E2) (hx : x ∈ D) : A (T x)=A x :=
    hAh x _ (div_pos (hfn x hx) (hn x hx))
  have hTc : ContinuousOn T D := by
    intro x hx
    have hax := hAc x (norm_pos_iff.mp (hn x hx))
    have hfcd : ContinuousAt (fun y => f y ‖y‖) x := by
      dsimp [f]
      fun_prop
    exact ((hfcd.div continuous_norm.continuousAt (hn x hx).ne').smul continuousAt_id).continuousWithinAt
  have hm : MapsTo T D E := by
    intro x hx
    change A (T x) ≤ ‖T x‖ ∧ ‖T x‖ ≤ b
    rw [hprofile x hx,hnorm x hx]
    exact ⟨by simpa only [(hf x).2.1] using (hf x).1.monotone hx.1,
      by simpa only [(hf x).2.2.1] using (hf x).1.monotone hx.2⟩
  have hi : InjOn T D := by
    intro x hx y hy he
    have hAeq : A x=A y := (hprofile x hx).symm.trans ((congrArg A he).trans (hprofile y hy))
    have hfeq : f x ‖x‖=f x ‖y‖ := by
      have hh := congrArg norm he
      rw [hnorm x hx,hnorm y hy] at hh
      simpa only [f,hAeq] using hh
    have hnormeq : ‖x‖=‖y‖ := (hf x).1.injective hfeq
    have hscale : f x ‖x‖/‖x‖=f y ‖y‖/‖y‖ := by rw [hnormeq]; simp only [f,hAeq]
    have he' : (f x ‖x‖/‖x‖) • x=(f x ‖x‖/‖x‖) • y := by
      change (f x ‖x‖/‖x‖) • x=(f y ‖y‖/‖y‖) • y at he
      rwa [← hscale] at he
    exact (smul_right_injective _ (div_pos (hfn x hx) (hn x hx)).ne') he'
  have hs : SurjOn T D E := by
    intro y hy
    have hypos : 0 < ‖y‖ := (hA y).1.trans_le hy.1
    have hym : ‖y‖ ∈ f y '' Icc a b := (hf y).2.2.2.symm ▸ hy
    obtain ⟨r,hr,he⟩ := hym
    have hrpos : 0 < r := ha.trans_le hr.1
    let x : E2 := (r/‖y‖) • y
    have hnx : ‖x‖=r := by
      rw [show x=(r/‖y‖) • y from rfl,norm_smul,Real.norm_eq_abs,
        abs_of_pos (div_pos hrpos hypos),div_mul_cancel₀ _ hypos.ne']
    have hAx : A x=A y := hAh y _ (div_pos hrpos hypos)
    have hx : x ∈ D := by change a ≤ ‖x‖ ∧ ‖x‖ ≤ b; rwa [hnx]
    refine ⟨x,hx,?_⟩
    change (f x ‖x‖/‖x‖) • ((r/‖y‖) • y)=y
    rw [hnx,show f x r=f y r by simp only [f,hAx],he,smul_smul]
    have hh : (‖y‖/r)*(r/‖y‖)=1 := by field_simp
    rw [hh,one_smul]
  refine ⟨T,hTc,⟨hm,hi,hs⟩,?_,?_,fun x h1 h2 => hprofile x ⟨h1,h2⟩,
    fun x h1 h2 => hnorm x ⟨h1,h2⟩⟩
  · intro x hx
    dsimp only [T]
    rw [hx,(hf x).2.1]
  · intro x hx
    dsimp only [T]
    rw [hx,(hf x).2.2.1,div_self (ha.trans hab).ne',one_smul]


private theorem relative_radial_annulus (A : E2 → ℝ) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hA : ∀ x, 0 < A x ∧ A x < b)
    (hAh : ∀ x (r : ℝ), 0 < r → A (r • x)=A x)
    (hAc : ∀ x, x ≠ 0 → ContinuousAt A x) :
    ∃ T : E2 → E2,
      ContinuousOn T {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} ∧
      BijOn T {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} {y | A y ≤ ‖y‖ ∧ ‖y‖ ≤ 1} ∧
      (∀ x, ‖x‖=a → T x=(A x/a) • x) ∧
      EqOn T id {x | b ≤ ‖x‖} := by
  classical
  obtain ⟨T₀,hTc,hTb,hTa,hTend,hTA,hTnorm⟩ := radial_annulus A a b ha hab hA hAh hAc
  let T : E2 → E2 := fun x => if ‖x‖ ≤ b then T₀ x else x
  have hsmall (x : E2) (hx : ‖x‖ ≤ b) : T x=T₀ x := by simp only [T,if_pos hx]
  have hlarge (x : E2) (hx : b ≤ ‖x‖) : T x=x := by
    by_cases hh : ‖x‖ ≤ b
    · rw [hsmall x hh,hTend x (le_antisymm hh hx)]
    · exact if_neg hh
  have hTC : ContinuousOn T {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} := by
    apply ContinuousOn.if
    · intro x hx
      exact hTend x (frontier_le_subset_eq continuous_norm continuous_const hx.2)
    · apply hTc.mono
      intro x hx
      have hh := hx.2
      rw [(show IsClosed {y : E2 | ‖y‖ ≤ b} from isClosed_le continuous_norm continuous_const).closure_eq] at hh
      exact ⟨hx.1.1,hh⟩
    · exact continuous_id.continuousOn
  have hmap : MapsTo T {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} {y | A y ≤ ‖y‖ ∧ ‖y‖ ≤ 1} := by
    intro x hx
    by_cases hh : ‖x‖ ≤ b
    · rw [hsmall x hh]
      have hz := hTb.mapsTo ⟨hx.1,hh⟩
      exact ⟨hz.1,hz.2.trans hb.le⟩
    · rw [hlarge x (le_of_not_ge hh)]
      exact ⟨(hA x).2.le.trans (le_of_not_ge hh),hx.2⟩
  have hinj : InjOn T {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} := by
    intro x hx y hy he
    by_cases hxb : ‖x‖ ≤ b
    · by_cases hyb : ‖y‖ ≤ b
      · exact hTb.injOn ⟨hx.1,hxb⟩ ⟨hy.1,hyb⟩ (by simpa only [hsmall x hxb,hsmall y hyb] using he)
      · have hn := (hTb.mapsTo ⟨hx.1,hxb⟩).2
        rw [← hsmall x hxb,he,hlarge y (le_of_not_ge hyb)] at hn
        exact (hyb hn).elim
    · by_cases hyb : ‖y‖ ≤ b
      · have hn := (hTb.mapsTo ⟨hy.1,hyb⟩).2
        rw [← hsmall y hyb,← he,hlarge x (le_of_not_ge hxb)] at hn
        exact (hxb hn).elim
      · simpa only [hlarge x (le_of_not_ge hxb),hlarge y (le_of_not_ge hyb)] using he
  have hsurj : SurjOn T {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} {y | A y ≤ ‖y‖ ∧ ‖y‖ ≤ 1} := by
    intro y hy
    by_cases hh : ‖y‖ ≤ b
    · obtain ⟨x,hx,he⟩ := hTb.surjOn ⟨hy.1,hh⟩
      exact ⟨x,⟨hx.1,hx.2.trans hb.le⟩,(hsmall x hx.2).trans he⟩
    · exact ⟨y,⟨hab.le.trans (le_of_not_ge hh),hy.2⟩,hlarge y (le_of_not_ge hh)⟩
  refine ⟨T,hTC,⟨hmap,hinj,hsurj⟩,?_,fun x hx => hlarge x hx⟩
  intro x hx
  rw [hsmall x (hx ▸ hab.le)]
  exact hTa x hx

private theorem periodic_upper_margin (ρ : ℝ → ℝ) (hρ : Continuous ρ)
    (hper : Periodic ρ (2*Real.pi)) (hbound : ∀ t, ρ t < 1) :
    ∃ b : ℝ, b < 1 ∧ ∀ t, ρ t < b := by
  have hT : 0 < 2*Real.pi := by positivity
  obtain ⟨s,hs,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) (2*Real.pi)).Nonempty from ⟨0,by simp [hT.le]⟩) hρ.continuousOn
  refine ⟨(ρ s+1)/2,by linarith [hbound s],?_⟩
  intro t
  obtain ⟨u,hu,he⟩ := hper.exists_mem_Ico hT t 0
  have hu' : u ∈ Icc (0:ℝ) (2*Real.pi) := ⟨hu.1,by simpa using hu.2.le⟩
  rw [he]
  have hm : ρ u ≤ ρ s := hmax hu'
  linarith [hbound s]

private theorem support_AnnularConnection_1 (w : E2 → E2) (η : ℝ) (ρ : ℝ → ℝ)
    (hw : Continuous w) (hη0 : 0 < η) (hη1 : η < 1)
    (hi : InjOn w {x : E2 | |‖x‖-1| < η})
    (hρ : Continuous ρ) (hper : Periodic ρ (2*Real.pi))
    (hr : ∀ t, 1-η < ρ t ∧ ρ t < 1) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
      ∃ (A : E2 → ℝ) (F : E2 → E2),
        (∀ t, A (unitCircleParameter t)=ρ t) ∧
        (∀ x, 1-η < A x ∧ A x < b) ∧
        (∀ x, x ≠ 0 → ContinuousAt A x) ∧
        (∀ x (r : ℝ), 0 < r → A (r • x)=A x) ∧
        ContinuousOn F {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} ∧
        BijOn F {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1}
          (w '' {y | A y ≤ ‖y‖ ∧ ‖y‖ ≤ 1}) ∧
        (∀ t, F (a • unitCircleParameter t)=w (ρ t • unitCircleParameter t)) ∧
        EqOn F w {x | b ≤ ‖x‖} := by
  obtain ⟨A,hAc,hAh,hAu,hAr⟩ := angular_profile ρ hρ hper
  obtain ⟨b,hb,hρb⟩ := periodic_upper_margin ρ hρ hper (fun t => (hr t).2)
  have hA (x : E2) : 1-η < A x ∧ A x < b := by
    obtain ⟨t,he⟩ := hAr x
    rw [he]
    exact ⟨(hr t).1,hρb t⟩
  let a := (1-η)/2
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a < b := by have h := hA 0; dsimp [a]; linarith [h.1,h.2]
  have hA0 (x : E2) : 0 < A x ∧ A x < b := ⟨by linarith [(hA x).1],(hA x).2⟩
  obtain ⟨T,hTc,hTb,hTa,hTout⟩ := relative_radial_annulus A a b ha hab hb hA0 hAh hAc
  let E : Set E2 := {y | A y ≤ ‖y‖ ∧ ‖y‖ ≤ 1}
  have hE : E ⊆ {x : E2 | |‖x‖-1| < η} := by
    intro x hx
    change |‖x‖-1| < η
    rw [abs_lt]
    exact ⟨by linarith [(hA x).1,hx.1],by linarith [hx.2]⟩
  have hwE : BijOn w E (w '' E) := ⟨mapsTo_image _ _,hi.mono hE,surjOn_image _ _⟩
  refine ⟨a,b,ha,hab,hb,A,w ∘ T,hAu,hA,hAc,hAh,hw.comp_continuousOn hTc,hwE.comp hTb,?_,?_⟩
  · intro t
    have hu : ‖unitCircleParameter t‖=1 := by
      have hh : ‖unitCircleParameter t‖^2=1 := by
        rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
        exact Real.cos_sq_add_sin_sq t
      nlinarith [norm_nonneg (unitCircleParameter t)]
    have hn : ‖a • unitCircleParameter t‖=a := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha,hu,mul_one]
    change w (T (a • unitCircleParameter t))=_
    rw [hTa _ hn,hAh _ a ha,hAu,smul_smul,div_mul_cancel₀ _ ha.ne']
  · intro x hx
    change w (T x)=w x
    rw [hTout hx,id_eq]

end VM03CapV437
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open Schoenflies DifferentialGeometry.Topology.PiecewiseLinear
namespace VM03CapV437

private theorem polygonal_chain (v : ℕ → E2) :
    ∀ N : ℕ, 0 < N → IsPolygonal (⋃ i : Fin N, segment ℝ (v i) (v (i.1+1))) := by
  intro N hN
  induction N with
  | zero => omega
  | succ n ih =>
    by_cases hn : n=0
    · subst n
      have he : (⋃ i : Fin 1, segment ℝ (v i) (v (i.1+1)))=segment ℝ (v 0) (v 1) := by
        ext x
        constructor
        · intro hx
          obtain ⟨i,hi⟩ := mem_iUnion.mp hx
          have hh : i.1=0 := by omega
          simpa only [hh,zero_add] using hi
        · intro hx
          exact mem_iUnion.mpr ⟨0,hx⟩
      rw [he]
      exact isPolygonal_segment (v 0) (v 1)
    · have hpn : 0 < n := Nat.pos_of_ne_zero hn
      have he : (⋃ i : Fin (n+1), segment ℝ (v i) (v (i.1+1))) =
          (⋃ i : Fin n, segment ℝ (v i) (v (i.1+1))) ∪ segment ℝ (v n) (v (n+1)) := by
        ext x
        constructor
        · intro hx
          obtain ⟨i,hi⟩ := mem_iUnion.mp hx
          by_cases hh : i.1 < n
          · exact Or.inl (mem_iUnion.mpr ⟨⟨i.1,hh⟩,hi⟩)
          · have hn : i.1=n := by omega
            exact Or.inr (hn ▸ hi)
        · rintro (hx | hx)
          · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
            exact mem_iUnion.mpr ⟨i.castSucc,hi⟩
          · exact mem_iUnion.mpr ⟨Fin.last n,hx⟩
      rw [he]
      apply (ih hpn).union (isPolygonal_segment (v n) (v (n+1)))
      refine ⟨v n,?_,left_mem_segment ℝ _ _⟩
      apply mem_iUnion.mpr
      refine ⟨⟨n-1,by omega⟩,?_⟩
      have hh : n-1+1=n := by omega
      rw [hh]
      exact right_mem_segment ℝ _ _

private theorem periodic_jordan (γ : ℝ → E2) (hγ : Continuous γ)
    (hp : Periodic γ (2*Real.pi))
    (hi : ∀ t u, γ t=γ u → ∃ k : ℤ, t-u=(k:ℝ)*(2*Real.pi)) :
    IsJordanCurve (range γ) := by
  let T := 2*Real.pi
  have hT : 0 < T := by dsimp [T]; positivity
  let f : ℝ → E2 := fun s => γ (s*T)
  have hfc : Continuous f := hγ.comp (continuous_id.mul continuous_const)
  refine ⟨f,⟨hfc.continuousOn,?_,?_⟩,?_⟩
  · change γ (0*T)=γ (1*T)
    simpa using (hp 0).symm
  · intro x hx y hy he
    obtain ⟨k,hk⟩ := hi (x*T) (y*T) he
    have hd : x-y=(k:ℝ) := by
      apply (mul_right_cancel₀ hT.ne')
      nlinarith [hk]
    have hklt : (-1:ℝ)<(k:ℝ) ∧ (k:ℝ)<1 := by
      rw [← hd]
      exact ⟨by linarith [hx.1,hy.2],by linarith [hx.2,hy.1]⟩
    have hk0 : k=0 := by
      have h1 : (-1:ℤ)<k := by exact_mod_cast hklt.1
      have h2 : k<1 := by exact_mod_cast hklt.2
      omega
    simp only [hk0,Int.cast_zero] at hd
    linarith
  · apply Subset.antisymm
    · rintro _ ⟨t,ht,rfl⟩
      exact mem_range_self _
    · rintro _ ⟨t,rfl⟩
      obtain ⟨s,hs,he⟩ := hp.exists_mem_Ico hT t 0
      refine ⟨s/T,?_,?_⟩
      · exact ⟨div_nonneg hs.1 hT.le,(div_le_iff₀ hT).mpr (by simpa using hs.2.le)⟩
      · change γ ((s/T)*T)=γ t
        rw [div_mul_cancel₀ _ hT.ne']
        exact he.symm

private theorem closedPolygon_chain_isPLBall {m : ℕ} (P : ClosedPolygon m) :
    ∀ k : ℕ, k + 1 < m + 3 → IsPLBall 1 (P.chain k) := by
  intro k
  induction k with
  | zero =>
    intro _
    change IsPLBall 1 (P.edge 0)
    exact isPLBall_segment (P.vertex_ne 0)
  | succ k ih =>
    intro hk
    have hA := P.isArcBetween_chain k (by omega)
    have hB : IsArcBetween (P.edge ((k+1:ℕ) : ZMod (m+3)))
        (P.vertex ((k+1:ℕ) : ZMod (m+3)))
        (P.vertex ((k+1+1:ℕ) : ZMod (m+3))) := by
      rw [ClosedPolygon.natCast_succ (k+1)]
      exact isArcBetween_segment (P.vertex_ne _)
    have hmeet : ∀ z ∈ P.chain k, z ∈ P.edge ((k+1:ℕ) : ZMod (m+3)) →
        z=P.vertex ((k+1:ℕ) : ZMod (m+3)) := by
      intro z hz hze
      obtain ⟨j,hj,hzj⟩ := ClosedPolygon.mem_chain_iff.mp hz
      exact ClosedPolygon.edge_meet_earlier (by omega) (by omega) hzj hze
    exact isPLBall_union_of_isArcBetween (ih (by omega))
      (isPLBall_segment (P.vertex_ne _)) hA hB hmeet

private theorem closedPolygon_isPLSphere {m : ℕ} (P : ClosedPolygon m) :
    IsPLSphere 1 P.carrier := by
  have hlast : ((m+2:ℕ) : ZMod (m+3))+1=0 := by
    rw [← ClosedPolygon.natCast_succ]
    exact ZMod.natCast_self (m+3)
  have hA := P.isArcBetween_chain (m+1) (by omega)
  have hB : IsArcBetween (P.edge ((m+2:ℕ) : ZMod (m+3)))
      (P.vertex 0) (P.vertex ((m+2:ℕ) : ZMod (m+3))) := by
    have h := isArcBetween_segment (P.vertex_ne ((m+2:ℕ) : ZMod (m+3)))
    rw [hlast] at h
    simpa only [ClosedPolygon.edge, hlast] using h.reverse
  have hmeet : P.chain (m+1) ∩ P.edge ((m+2:ℕ) : ZMod (m+3)) =
      {P.vertex 0,P.vertex ((m+2:ℕ) : ZMod (m+3))} := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨j,hj,hzj⟩ := ClosedPolygon.mem_chain_iff.mp hz.1
      simpa only [mem_insert_iff,mem_singleton_iff] using
        ClosedPolygon.edge_meet_last (by omega) hzj hz.2
    · exact pair_subset ⟨hA.left_mem,hB.left_mem⟩ ⟨hA.right_mem,hB.right_mem⟩
  have hcut : IsCutPair P.carrier (P.vertex 0)
      (P.vertex ((m+2:ℕ) : ZMod (m+3)))
      (P.chain (m+1)) (P.edge ((m+2:ℕ) : ZMod (m+3))) := by
    refine ⟨hA,hB,?_,hmeet⟩
    exact P.chain_eq_carrier
  exact isPLSphere_one_of_isCutPair hcut
    (closedPolygon_chain_isPLBall P (m+1) (by omega))
    (isPLBall_segment (P.vertex_ne _))

open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider

/- The literal supplied boundary now produces an actual finite PL disk, with an
   explicit simplex-to-disk PL homeomorphism and a finite boundary-compatible complex. -/

private theorem support_SamePolygon_1 (R : ℝ) (Ω : SmoothFlatJordanDomain R) (w : E2 → E2) (η : ℝ)
    (hw : Continuous w) (hb : ∀ t, w (unitCircleParameter t)=Ω.boundary.gamma t)
    (hη : η < 1) (hinj : InjOn w {x : E2 | |‖x‖-1| < η})
    (ρ : ℝ → ℝ) (hρ : Continuous ρ) (hp : Periodic ρ (2*Real.pi))
    (hr : ∀ t, 1-η < ρ t ∧ ρ t < 1)
    (N : ℕ) (hN : 0 < N) (v : ℕ → E2)
    (hcar : range (fun t => w (ρ t • unitCircleParameter t)) =
      ⋃ i : Fin N, segment ℝ (v i) (v (i.1+1))) :
    ∃ m : ℕ, ∃ P : ClosedPolygon m,
      P.carrier=range (fun t => w (ρ t • unitCircleParameter t)) ∧
      IsPLBall 2 (closure (inside P.carrier)) := by
  have hu : Continuous unitCircleParameter := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.continuous_cos
    · exact Real.continuous_sin
  have hn (t : ℝ) : ‖unitCircleParameter t‖=1 := by
    have hh : ‖unitCircleParameter t‖^2=1 := by
      rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
      exact Real.cos_sq_add_sin_sq t
    nlinarith [norm_nonneg (unitCircleParameter t)]
  have hr0 (t : ℝ) : 0 < ρ t := by linarith [(hr t).1]
  have hnorm (t : ℝ) : ‖ρ t • unitCircleParameter t‖=ρ t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hr0 t),hn,mul_one]
  have hm (t : ℝ) : ρ t • unitCircleParameter t ∈ {x : E2 | |‖x‖-1| < η} := by
    change |‖ρ t • unitCircleParameter t‖-1| < η
    rw [hnorm,abs_lt]
    exact ⟨by linarith [(hr t).1],by linarith [(hr t).1,(hr t).2]⟩
  have hγc : Continuous (fun t => w (ρ t • unitCircleParameter t)) := hw.comp (hρ.smul hu)
  have hγp : Periodic (fun t => w (ρ t • unitCircleParameter t)) (2*Real.pi) := by
    intro t
    change w (ρ (t+2*Real.pi) • unitCircleParameter (t+2*Real.pi))=w (ρ t • unitCircleParameter t)
    rw [hp t]
    congr 2
    ext i
    fin_cases i
    · exact Real.cos_periodic t
    · exact Real.sin_periodic t
  have hγi : ∀ t u, w (ρ t • unitCircleParameter t)=w (ρ u • unitCircleParameter u) →
      ∃ k : ℤ, t-u=(k:ℝ)*(2*Real.pi) := by
    intro t u he
    have he' := hinj (hm t) (hm u) he
    have hrho : ρ t=ρ u := by
      have hh := congrArg norm he'
      rwa [hnorm,hnorm] at hh
    rw [← hrho] at he'
    have hcircle := smul_right_injective E2 (hr0 t).ne' he'
    exact (Ω.boundary.simple t u).mp (by rw [← hb t,← hb u,hcircle])
  have hpoly : IsPolygonal (range (fun t => w (ρ t • unitCircleParameter t))) := by
    rw [hcar]
    exact polygonal_chain v N hN
  obtain ⟨m,P,hP⟩ := exists_closedPolygon (periodic_jordan _ hγc hγp hγi) hpoly
  exact ⟨m,P,hP,isPLBall_closure_inside_of_isPLSphere_one (closedPolygon_isPLSphere P)⟩
end VM03CapV437
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
namespace VM03CapV437
private theorem circle_norm (t : ℝ) : ‖unitCircleParameter t‖=1 := by
  have hh : ‖unitCircleParameter t‖^2=1 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
    exact Real.cos_sq_add_sin_sq t
  nlinarith [norm_nonneg (unitCircleParameter t)]

private theorem circle_surjective (x : E2) (hx : x ∈ sphere 0 1) :
    ∃ t : ℝ, unitCircleParameter t=x := by
  let z : ℂ := ⟨x 0,x 1⟩
  have hnx : ‖x‖=1 := mem_sphere_zero_iff_norm.mp hx
  have hnz : ‖z‖=1 := by
    have hn : ‖z‖^2=‖x‖^2 := by
      rw [Complex.sq_norm,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
      simp [Complex.normSq_apply,z,pow_two]
    rw [hnx] at hn
    nlinarith [norm_nonneg z]
  have hz : z ≠ 0 := by intro he; simp [he] at hnz
  refine ⟨z.arg,?_⟩
  ext i
  fin_cases i
  · change Real.cos z.arg=x 0
    rw [Complex.cos_arg hz,hnz,div_one]
  · change Real.sin z.arg=x 1
    rw [Complex.sin_arg,hnz,div_one]

private theorem sphere_boundary_bijection
    (w : E2 → E2) (η : ℝ) (A : E2 → ℝ) (ρ : ℝ → ℝ)
    (hw : Continuous w) (hη : η < 1)
    (hi : InjOn w {x : E2 | |‖x‖-1| < η})
    (hAc : ∀ x, x ≠ 0 → ContinuousAt A x)
    (hA : ∀ x, 1-η < A x ∧ A x < 1)
    (hAu : ∀ t, A (unitCircleParameter t)=ρ t) :
    ∃ B : E2 → E2, ContinuousOn B (sphere 0 1) ∧
      BijOn B (sphere 0 1) (range (fun t => w (ρ t • unitCircleParameter t))) ∧
      (∀ t, B (unitCircleParameter t)=w (ρ t • unitCircleParameter t)) := by
  let B : E2 → E2 := fun x => w (A x • x)
  have hpos (x : E2) : 0 < A x := by linarith [(hA x).1]
  have hnorm (x : E2) (hx : x ∈ sphere 0 1) : ‖A x • x‖=A x := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hpos x),mem_sphere_zero_iff_norm.mp hx,mul_one]
  have hmem (x : E2) (hx : x ∈ sphere 0 1) : |‖A x • x‖-1| < η := by
    rw [hnorm x hx,abs_lt]
    exact ⟨by linarith [(hA x).1],by linarith [(hA x).1,(hA x).2]⟩
  have hBu (t : ℝ) : B (unitCircleParameter t)=w (ρ t • unitCircleParameter t) := by
    dsimp [B]
    rw [hAu]
  refine ⟨B,?_,⟨?_,?_,?_⟩,hBu⟩
  · intro x hx
    exact (hw.continuousAt.comp ((hAc x (ne_of_mem_sphere hx one_ne_zero)).smul continuousAt_id)).continuousWithinAt
  · intro x hx
    obtain ⟨t,rfl⟩ := circle_surjective x hx
    rw [hBu]
    exact mem_range_self t
  · intro x hx y hy he
    have hh : A x • x=A y • y := hi (hmem x hx) (hmem y hy) he
    have hval : A x=A y := by
      have hn := congrArg norm hh
      rwa [hnorm x hx,hnorm y hy] at hn
    rw [← hval] at hh
    exact smul_right_injective E2 (hpos x).ne' hh
  · rintro _ ⟨t,rfl⟩
    exact ⟨unitCircleParameter t,mem_sphere_zero_iff_norm.mpr (circle_norm t),hBu t⟩


private theorem circle_injOn_short_interval (a b : ℝ) (hab : b-a < 2*Real.pi) :
    InjOn unitCircleParameter (Icc a b) := by
  letI : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
  intro x hx y hy he
  have hcos : Real.cos x=Real.cos y := congrArg (fun z : E2 => z 0) he
  have hsin : Real.sin x=Real.sin y := congrArg (fun z : E2 => z 1) he
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show x ∈ Ico a (a+2*Real.pi) from ⟨hx.1,by linarith [hx.2]⟩)
    (show y ∈ Ico a (a+2*Real.pi) from ⟨hy.1,by linarith [hy.2]⟩)).mp
    (Real.Angle.cos_sin_inj hcos hsin)

private theorem chord_parameter_strictMono
    (B : E2 → E2) (hB : InjOn B (sphere 0 1))
    (a b : ℝ) (hab : a ≤ b) (hshort : b-a < 2*Real.pi)
    (p q : E2) (τ : ℝ → ℝ) (hc : ContinuousOn τ (Icc a b))
    (ha : τ a=0) (hb : τ b=1)
    (he : ∀ t ∈ Icc a b, B (unitCircleParameter t)=AffineMap.lineMap p q (τ t)) :
    StrictMonoOn τ (Icc a b) := by
  apply ContinuousOn.strictMonoOn_of_injOn_Icc hab (by rw [ha,hb]; norm_num) hc
  intro t ht u hu htu
  apply circle_injOn_short_interval a b hshort ht hu
  apply hB (mem_sphere_zero_iff_norm.mpr (circle_norm t))
    (mem_sphere_zero_iff_norm.mpr (circle_norm u))
  rw [he t ht,he u hu,htu]


private theorem radial_boundary_level (w : E2 → E2) (A : E2 → ℝ) (ρ : ℝ → ℝ)
    (hA : ∀ x, 0 < A x) (hAh : ∀ x (r : ℝ), 0 < r → A (r • x)=A x)
    (hAu : ∀ t, A (unitCircleParameter t)=ρ t) :
    range (fun t => w (ρ t • unitCircleParameter t))=w '' {x : E2 | ‖x‖=A x} := by
  apply Subset.antisymm
  · rintro y ⟨t,rfl⟩
    have hρ : 0 < ρ t := by rw [← hAu]; exact hA _
    refine ⟨ρ t • unitCircleParameter t,?_,rfl⟩
    change ‖ρ t • unitCircleParameter t‖=A (ρ t • unitCircleParameter t)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hρ,circle_norm,mul_one,hAh _ _ hρ,hAu]
  · rintro y ⟨x,hx,rfl⟩
    have hnorm : ‖x‖=A x := hx
    have hxpos : 0 < ‖x‖ := hnorm ▸ hA x
    let u := ‖x‖⁻¹ • x
    have hnu : u ∈ sphere 0 1 := by simp [u,norm_smul,hxpos.ne']
    obtain ⟨t,ht⟩ := circle_surjective u hnu
    refine ⟨t,?_⟩
    have hρ : ρ t=‖x‖ := by
      rw [← hAu,ht,hAh x _ (inv_pos.mpr hxpos),hnorm]
    change w (ρ t • unitCircleParameter t)=w x
    rw [hρ,ht]
    simp [u,smul_smul,hxpos.ne']
end VM03CapV437
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
namespace VM03CapV437

private theorem radial_boundary_extension
    (Q : Set E2) (hQc : Convex ℝ Q) (hQ0 : Q ∈ 𝓝 (0:E2))
    (hQclosed : IsClosed Q) (hQb : Bornology.IsBounded Q)
    (β : E2 → E2) (hβc : ContinuousOn β (sphere 0 1))
    (hβ : BijOn β (sphere 0 1) (frontier Q)) :
    ∃ C : E2 → E2, Continuous C ∧ Bijective C ∧
      BijOn C (closedBall 0 1) Q ∧ BijOn C (ball 0 1) (interior Q) ∧
      EqOn C β (sphere 0 1) ∧ C 0=0 ∧
      (∀ x (r : ℝ), 0 ≤ r → C (r • x)=r • C x) ∧
      ∀ x, x ≠ 0 → C x=‖x‖ • β (‖x‖⁻¹ • x) := by
  classical
  let n : E2 → E2 := fun x => ‖x‖⁻¹ • x
  have hn (x : E2) (hx : x ≠ 0) : n x ∈ sphere 0 1 := by
    simp [n,mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx)),hx]
  have hnn (x : E2) (hx : x ∈ sphere 0 1) : n x=x := by
    have hh := mem_sphere_zero_iff_norm.mp hx
    simp [n,hh]
  have hns (x : E2) (r : ℝ) (hr : 0 < r) : n (r • x)=n x := by
    dsimp [n]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,smul_smul]
    congr 1
    field_simp
  let C : E2 → E2 := fun x => ‖x‖ • β (n x)
  have hC0 : C 0=0 := by simp [C]
  have hQg : ∀ x, 0 < gauge Q x ↔ x ≠ 0 := fun x =>
    gauge_pos (absorbent_nhds_zero hQ0) (NormedSpace.isVonNBounded_of_isBounded ℝ hQb)
  have hCg (x : E2) : gauge Q (C x)=‖x‖ := by
    by_cases hx : x=0
    · simp [hx,hC0]
    · rw [show C x=‖x‖ • β (n x) from rfl,gauge_smul_of_nonneg (norm_nonneg x)]
      have hh := (gauge_eq_one_iff_mem_frontier hQc hQ0).mpr (hβ.mapsTo (hn x hx))
      simp [hh,smul_eq_mul]
  have hCh (x : E2) (r : ℝ) (hr : 0 ≤ r) : C (r • x)=r • C x := by
    rcases hr.eq_or_lt with hr | hr
    · simp [← hr,hC0]
    · dsimp only [C]
      rw [hns x r hr,norm_smul,Real.norm_eq_abs,abs_of_pos hr,smul_smul]
  have hCi : Injective C := by
    intro x y he
    have hnorm : ‖x‖=‖y‖ := by simpa only [hCg] using congrArg (gauge Q) he
    by_cases hx : x=0
    · subst x
      exact (norm_eq_zero.mp (by simpa using hnorm.symm)).symm
    · have hy : y ≠ 0 := by intro hy; exact hx (norm_eq_zero.mp (by simpa [hy] using hnorm))
      have heβ : β (n x)=β (n y) := by
        apply smul_right_injective E2 (norm_pos_iff.mpr hx).ne'
        change ‖x‖ • β (n x)=‖x‖ • β (n y)
        simpa only [C,hnorm] using he
      have hen : n x=n y := hβ.injOn (hn x hx) (hn y hy) heβ
      have hxnorm : ‖x‖ • n x=x := by simp [n,smul_smul,hx]
      have hynorm : ‖y‖ • n y=y := by simp [n,smul_smul,hy]
      calc x = ‖x‖ • n x := hxnorm.symm
           _ = ‖y‖ • n y := by rw [hnorm,hen]
           _ = y := hynorm
  have hCs : Surjective C := by
    intro y
    by_cases hy : y=0
    · exact ⟨0,hy ▸ hC0⟩
    · let r := gauge Q y
      have hr : 0 < r := (hQg y).mpr hy
      have hg : gauge Q (r⁻¹ • y)=1 := by
        rw [gauge_smul_of_nonneg (inv_nonneg.mpr hr.le),smul_eq_mul]
        exact inv_mul_cancel₀ hr.ne'
      obtain ⟨u,hu,heu⟩ := hβ.surjOn ((gauge_eq_one_iff_mem_frontier hQc hQ0).mp hg)
      refine ⟨r • u,?_⟩
      have hnu : ‖u‖=1 := mem_sphere_zero_iff_norm.mp hu
      rw [hCh u r hr.le]
      change r • (‖u‖ • β (n u))=y
      rw [hnu,one_smul,hnn u hu,heu,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hCcont : Continuous C := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x=0
    · subst x
      obtain ⟨B,hB⟩ := (isCompact_sphere (0:E2) 1).image_of_continuousOn hβc |>.isBounded.exists_norm_le
      have hbound (y : E2) : ‖C y‖ ≤ ‖y‖*B := by
        by_cases hy : y=0
        · simp [hy,hC0]
        · rw [show C y=‖y‖ • β (n y) from rfl,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg y)]
          exact mul_le_mul_of_nonneg_left (hB _ (mem_image_of_mem β (hn y hy))) (norm_nonneg y)
      apply Metric.continuousAt_iff.mpr
      intro ε hε
      refine ⟨ε/(|B|+1),by positivity,?_⟩
      intro y hy
      rw [hC0,dist_zero_right]
      rw [dist_zero_right] at hy
      calc ‖C y‖ ≤ ‖y‖*B := hbound y
           _ ≤ ‖y‖*|B| := mul_le_mul_of_nonneg_left (le_abs_self B) (norm_nonneg y)
           _ < ε := by
             have hh : ‖y‖*(|B|+1) < ε := (lt_div_iff₀ (by positivity)).mp hy
             nlinarith [norm_nonneg y,abs_nonneg B]
    · have hnc : ContinuousAt n x := continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx) |>.smul continuousAt_id
      have hbn : ContinuousAt (β ∘ n) x := by
        apply (hβc (n x) (hn x hx)).tendsto.comp
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within n hnc
        filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
        exact hn y hy
      exact continuous_norm.continuousAt.smul hbn
  have hclosed (x : E2) : C x ∈ Q ↔ x ∈ closedBall 0 1 := by
    rw [← hQclosed.closure_eq,← gauge_le_one_iff_mem_closure hQc hQ0,hCg,mem_closedBall_zero_iff]
  have hopen (x : E2) : C x ∈ interior Q ↔ x ∈ ball 0 1 := by
    rw [← gauge_lt_one_iff_mem_interior hQc hQ0,hCg,mem_ball_zero_iff]
  refine ⟨C,hCcont,⟨hCi,hCs⟩,?_,?_,?_,hC0,hCh,fun _ _ => rfl⟩
  · refine ⟨fun x hx => (hclosed x).mpr hx,hCi.injOn,?_⟩
    intro y hy
    obtain ⟨x,rfl⟩ := hCs y
    exact ⟨x,(hclosed x).mp hy,rfl⟩
  · refine ⟨fun x hx => (hopen x).mpr hx,hCi.injOn,?_⟩
    intro y hy
    obtain ⟨x,rfl⟩ := hCs y
    exact ⟨x,(hopen x).mp hy,rfl⟩
  · intro x hx
    change ‖x‖ • β (n x)=β x
    rw [mem_sphere_zero_iff_norm.mp hx,one_smul,hnn x hx]


open DifferentialGeometry.Topology.PiecewiseLinear

private theorem inner_pl_disk_with_prescribed_boundary
    (D : Set E2) (hD : IsPLBall 2 D) (hDc : IsClosed D)
    (B : E2 → E2) (hBc : ContinuousOn B (sphere 0 1))
    (hB : BijOn B (sphere 0 1) (frontier D)) :
    ∃ (K : Geometry.SimplicialComplex ℝ E2) (F C G : E2 → E2),
      K.faces.Finite ∧ Convex ℝ K.space ∧ IsCompact K.space ∧ K.space ∈ 𝓝 (0:E2) ∧
      IsPLBall 2 K.space ∧ IsPLHomeomorphOn F K.space D ∧
      Continuous C ∧ Bijective C ∧ BijOn C (closedBall 0 1) K.space ∧
      BijOn C (ball 0 1) (interior K.space) ∧
      (∀ x, G x=F (C x)) ∧ ContinuousOn G (closedBall 0 1) ∧
      BijOn G (closedBall 0 1) D ∧ BijOn G (ball 0 1) (interior D) ∧
      EqOn G B (sphere 0 1) := by
  classical
  obtain ⟨T,hT,hcard,h0,hsub,hT0⟩ := exists_affineIndependent_openSimplex_subset
    (n:=1) (E:=E2) (by simp) (0:E2) (Filter.univ_mem : (univ : Set E2) ∈ 𝓝 0)
  let K := simplexComplex T hT
  have hKspace : K.space=convexHull ℝ (T:Set E2) := simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKc : IsCompact K.space := by rw [hKspace]; exact T.finite_toSet.isCompact_convexHull ℝ
  have hKconv : Convex ℝ K.space := by rw [hKspace]; exact convex_convexHull ℝ _
  have hK0 : K.space ∈ 𝓝 (0:E2) := hKspace.symm ▸ hT0
  have hK : IsPLBall 2 K.space := by
    rw [hKspace]
    exact isPLBall_convexHull_of_affineIndependent T hT hcard
  obtain ⟨f,hf⟩ := hK
  obtain ⟨g,hg⟩ := hD
  let F : E2 → E2 := g ∘ invFunOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hF : IsPLHomeomorphOn F K.space D := hf.symm.trans hg
  let V := invFunOn F K.space
  have hV : IsPLHomeomorphOn V D K.space := hF.symm
  have hfront : F '' frontier K.space=frontier D := hF.image_frontier rfl hKc.isClosed hDc
  have hVfront : V '' frontier D=frontier K.space := hV.image_frontier rfl hDc hKc.isClosed
  have hVb : BijOn V (frontier D) (frontier K.space) :=
    ⟨by intro y hy; exact hVfront ▸ mem_image_of_mem V hy,
      hV.bijOn.injOn.mono (frontier_subset_closure.trans hDc.closure_eq.subset),
      by intro y hy; exact hVfront.symm ▸ hy⟩
  let β := V ∘ B
  have hβ : BijOn β (sphere 0 1) (frontier K.space) := hVb.comp hB
  have hβc : ContinuousOn β (sphere 0 1) := hV.isPiecewiseAffineOn.continuousOn.comp hBc
    (hB.mapsTo.mono_right (frontier_subset_closure.trans hDc.closure_eq.subset))
  obtain ⟨C,hCc,hCi,hCclosed,hCopen,hCboundary,hC0,hCh,hCformula⟩ :=
    radial_boundary_extension K.space hKconv hK0 hKc.isClosed hKc.isBounded β hβc hβ
  let G := F ∘ C
  have hFI : BijOn F (interior K.space) (interior D) :=
    ⟨by intro x hx; exact hF.image_interior rfl ▸ mem_image_of_mem F hx,
      hF.bijOn.injOn.mono interior_subset,
      by intro y hy; exact (hF.image_interior rfl).symm ▸ hy⟩
  refine ⟨K,F,C,G,simplexComplex_faces_finite T hT,hKconv,hKc,hK0,⟨f,hf⟩,hF,
    hCc,hCi,hCclosed,hCopen,fun _ => rfl,
    hF.isPiecewiseAffineOn.continuousOn.comp hCc.continuousOn hCclosed.mapsTo,
    hF.bijOn.comp hCclosed,hFI.comp hCopen,?_⟩
  intro x hx
  change F (C x)=B x
  rw [hCboundary hx]
  exact hF.bijOn.invOn_invFunOn.2
    ((frontier_subset_closure.trans hDc.closure_eq.subset) (hB.mapsTo hx))
end VM03CapV437
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
namespace VM03CapV437
private theorem disk_annulus_glue
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (G F : E2 → E2)
    (hG : ContinuousOn G (closedBall 0 1))
    (hF : ContinuousOn F {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1})
    (hseam : ∀ x : E2, ‖x‖=a → G (a⁻¹ • x)=F x) :
    ∃ H : E2 → E2, ContinuousOn H (closedBall 0 1) ∧
      EqOn H (fun x => G (a⁻¹ • x)) (closedBall 0 a) ∧
      EqOn H F {x | a ≤ ‖x‖} ∧
      H '' closedBall 0 1=G '' closedBall 0 1 ∪ F '' {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} ∧
      H '' ball 0 1=G '' ball 0 1 ∪ F '' {x | a ≤ ‖x‖ ∧ ‖x‖ < 1} := by
  classical
  let H : E2 → E2 := fun x => if ‖x‖ ≤ a then G (a⁻¹ • x) else F x
  have hsmall (x : E2) (hx : ‖x‖ ≤ a) : H x=G (a⁻¹ • x) := if_pos hx
  have hlarge (x : E2) (hx : a ≤ ‖x‖) : H x=F x := by
    by_cases hh : ‖x‖ ≤ a
    · exact (hsmall x hh).trans (hseam x (le_antisymm hh hx))
    · exact if_neg hh
  have hscale (x : E2) : ‖a⁻¹ • x‖=‖x‖/a := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha),div_eq_inv_mul]
  have hposscale (x : E2) : ‖a • x‖=a*‖x‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha]
  have hscaled (x : E2) (hx : ‖x‖ ≤ a) : a⁻¹ • x ∈ closedBall 0 1 := by
    rw [mem_closedBall_zero_iff,hscale]
    exact (div_le_one ha).mpr hx
  have hHC : ContinuousOn H (closedBall 0 1) := by
    apply ContinuousOn.if
    · intro x hx
      exact hseam x (frontier_le_subset_eq continuous_norm continuous_const hx.2)
    · exact hG.comp (by fun_prop) (by
        intro x hx
        have hh := hx.2
        rw [(show IsClosed {y : E2 | ‖y‖ ≤ a} from isClosed_le continuous_norm continuous_const).closure_eq] at hh
        exact hscaled x hh)
    · apply hF.mono
      intro x hx
      refine ⟨?_,mem_closedBall_zero_iff.mp hx.1⟩
      have hcl : closure {y : E2 | ¬‖y‖ ≤ a} ⊆ {y : E2 | a ≤ ‖y‖} := by
        apply closure_minimal
        · intro y hy
          exact (lt_of_not_ge hy).le
        · exact isClosed_le continuous_const continuous_norm
      exact hcl hx.2
  refine ⟨H,hHC,fun x hx => hsmall x (mem_closedBall_zero_iff.mp hx),hlarge,?_,?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      by_cases hxa : ‖x‖ ≤ a
      · exact Or.inl ⟨a⁻¹ • x,hscaled x hxa,(hsmall x hxa).symm⟩
      · exact Or.inr ⟨x,⟨(lt_of_not_ge hxa).le,mem_closedBall_zero_iff.mp hx⟩,
          (hlarge x (lt_of_not_ge hxa).le).symm⟩
    · rintro y (⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩)
      · have hxnorm : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
        have hax : ‖a • x‖ ≤ a := by rw [hposscale]; nlinarith
        refine ⟨a • x,mem_closedBall_zero_iff.mpr (hax.trans ha1.le),?_⟩
        rw [hsmall _ hax,smul_smul,inv_mul_cancel₀ ha.ne',one_smul]
      · exact ⟨x,mem_closedBall_zero_iff.mpr hx.2,hlarge x hx.1⟩
  · apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      by_cases hxa : ‖x‖ < a
      · refine Or.inl ⟨a⁻¹ • x,?_,(hsmall x hxa.le).symm⟩
        rw [mem_ball_zero_iff,hscale]
        exact (div_lt_one ha).mpr hxa
      · exact Or.inr ⟨x,⟨le_of_not_gt hxa,mem_ball_zero_iff.mp hx⟩,
          (hlarge x (le_of_not_gt hxa)).symm⟩
    · rintro y (⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩)
      · have hxnorm : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
        have hax : ‖a • x‖ < a := by rw [hposscale]; nlinarith
        refine ⟨a • x,mem_ball_zero_iff.mpr (hax.trans ha1),?_⟩
        rw [hsmall _ hax.le,smul_smul,inv_mul_cancel₀ ha.ne',one_smul]
      · exact ⟨x,mem_ball_zero_iff.mpr hx.2,hlarge x hx.1⟩
end VM03CapV437
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
namespace VM03CapV437
private theorem disk_annulus_glue_injective
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (G F H : E2 → E2)
    (hGi : InjOn G (closedBall 0 1))
    (hFi : InjOn F {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1})
    (hsmall : EqOn H (fun x => G (a⁻¹ • x)) (closedBall 0 a))
    (hlarge : EqOn H F {x | a ≤ ‖x‖})
    (hdis : Disjoint (G '' ball 0 1) (F '' {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1})) :
    InjOn H (closedBall 0 1) := by
  have hscale (x : E2) : ‖a⁻¹ • x‖=‖x‖/a := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha),div_eq_inv_mul]
  have hgs (x : E2) (hx : ‖x‖ < a) : a⁻¹ • x ∈ ball 0 1 := by
    rw [mem_ball_zero_iff,hscale]
    exact (div_lt_one ha).mpr hx
  intro x hx y hy he
  have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  have hy1 : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
  by_cases hxa : ‖x‖ < a
  · by_cases hya : ‖y‖ < a
    · have he' := hGi (ball_subset_closedBall (hgs x hxa)) (ball_subset_closedBall (hgs y hya))
        (by simpa only [hsmall (mem_closedBall_zero_iff.mpr hxa.le),
          hsmall (mem_closedBall_zero_iff.mpr hya.le)] using he)
      exact smul_right_injective E2 (inv_pos.mpr ha).ne' he'
    · have him : H x ∈ G '' ball 0 1 := ⟨a⁻¹ • x,hgs x hxa,
        (hsmall (mem_closedBall_zero_iff.mpr hxa.le)).symm⟩
      have him' : H y ∈ F '' {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} :=
        ⟨y,⟨le_of_not_gt hya,hy1⟩,(hlarge (le_of_not_gt hya)).symm⟩
      exact ((disjoint_left.mp hdis) him (he ▸ him')).elim
  · by_cases hya : ‖y‖ < a
    · have him : H y ∈ G '' ball 0 1 := ⟨a⁻¹ • y,hgs y hya,
        (hsmall (mem_closedBall_zero_iff.mpr hya.le)).symm⟩
      have him' : H x ∈ F '' {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} :=
        ⟨x,⟨le_of_not_gt hxa,hx1⟩,(hlarge (le_of_not_gt hxa)).symm⟩
      exact ((disjoint_left.mp hdis) him (he.symm ▸ him')).elim
    · exact hFi ⟨le_of_not_gt hxa,hx1⟩ ⟨le_of_not_gt hya,hy1⟩
        (by simpa only [hlarge (le_of_not_gt hxa),hlarge (le_of_not_gt hya)] using he)

private theorem embedded_disk_frontier
    (H : E2 → E2) (hH : ContinuousOn H (closedBall 0 1))
    (hi : InjOn H (closedBall 0 1)) :
    IsOpen (H '' ball 0 1) ∧ IsConnected (H '' ball 0 1) ∧
      Bornology.IsBounded (H '' ball 0 1) ∧ frontier (H '' ball 0 1)=H '' sphere 0 1 := by
  have hc : IsCompact (H '' closedBall 0 1) := (isCompact_closedBall (0:E2) 1).image_of_continuousOn hH
  have ho : IsOpen (H '' ball 0 1) :=
    DifferentialGeometry.Topology.invariance_of_domain_isOpen_image_of_finrank_eq
      rfl isOpen_ball (hH.mono ball_subset_closedBall) (hi.mono ball_subset_closedBall)
  have hcl : closure (H '' ball 0 1)=H '' closedBall 0 1 := by
    have hh := image_closure_of_isCompact
      (show IsCompact (closure (ball (0:E2) 1)) from by rw [closure_ball (0:E2) (by norm_num)]; exact isCompact_closedBall _ _)
      (show ContinuousOn H (closure (ball (0:E2) 1)) from by rwa [closure_ball (0:E2) (by norm_num)])
    simpa only [closure_ball (0:E2) (show (1:ℝ) ≠ 0 by norm_num)] using hh.symm
  refine ⟨ho,(isConnected_ball (show (0:ℝ)<1 by norm_num)).image H (hH.mono ball_subset_closedBall),
    hc.isBounded.subset (image_mono ball_subset_closedBall),?_⟩
  rw [ho.frontier_eq,hcl,← hi.image_sdiff_subset ball_subset_closedBall]
  congr 1
  ext x
  simp only [mem_diff,mem_closedBall_zero_iff,mem_ball_zero_iff,not_lt,mem_sphere_zero_iff_norm]
  exact le_antisymm_iff.symm
end VM03CapV437
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open Schoenflies
namespace VM03CapV437
private theorem bounded_region_eq_inside
    (V J : Set E2) (hV : IsOpen V) (hVc : IsConnected V)
    (hVb : Bornology.IsBounded V) (hJ : IsJordanCurve J) (hfront : frontier V=J) :
    V=inside J := by
  obtain ⟨x,hx⟩ := hVc.nonempty
  have hsub : V ⊆ Jᶜ := by
    intro y hy hJy
    have hh : y ∈ frontier V := hfront.symm ▸ hJy
    rw [hV.frontier_eq] at hh
    exact hh.2 hy
  have he := Plane.connectedComponentIn_eq_of_frontier_disjoint hV hVc.isPreconnected hsub
    (by rw [hfront]; exact inter_compl_self J) hx
  have hreg := (jordan_curve_theorem hJ).isRegionOf_connectedComponentIn (hsub hx)
  rw [he] at hreg
  rcases hreg with hi | ho
  · exact hi
  · exact ((jordan_curve_theorem hJ).not_isBounded_outside (ho ▸ hVb)).elim

private theorem nested_jordan_closure
    (J Γ : Set E2) (hJ : IsJordanCurve J) (hΓ : IsJordanCurve Γ)
    (hsub : J ⊆ inside Γ) : closure (inside J) ⊆ inside Γ := by
  have hJs := jordan_curve_theorem hJ
  have hΓs := jordan_curve_theorem hΓ
  let S := closure (outside Γ)
  have hSc : IsConnected S := hΓs.isConnected_outside.closure
  have hSJ : Disjoint S J := by
    apply disjoint_left.mpr
    intro x hx hxJ
    have hh := hsub hxJ
    rw [hΓs.inside_eq_compl_closure_outside] at hh
    exact hh hx
  obtain ⟨W,V,hWV,hSW⟩ := hJs.exists_isRegionPair_subset hSc.isPreconnected hSc.nonempty hSJ
  have hSout : S ⊆ outside J := by
    rcases hWV with ⟨hW,hV⟩ | ⟨hW,hV⟩
    · rw [hW] at hSW
      exact (hΓs.not_isBounded_outside (hJs.isBounded_inside.subset (subset_closure.trans hSW))).elim
    · rwa [hW] at hSW
  intro x hx
  rw [hΓs.inside_eq_compl_closure_outside]
  intro hxS
  have hh := hSout hxS
  rw [hJs.outside_eq_compl_closure_inside] at hh
  exact hh hx

private theorem inner_polygon_subset_domain
    (V J : Set E2) (hV : IsOpen V) (hVc : IsConnected V)
    (hVb : Bornology.IsBounded V) (hfront : IsJordanCurve (frontier V))
    (hJ : IsJordanCurve J) (hJV : J ⊆ V) : closure (inside J) ⊆ V := by
  have hVeq := bounded_region_eq_inside V (frontier V) hV hVc hVb hfront rfl
  rw [hVeq]
  apply nested_jordan_closure J (frontier V) hJ hfront
  rwa [← hVeq]

private theorem radial_annular_image_outside
    (w : E2 → E2) (η : ℝ) (A : E2 → ℝ) (J V : Set E2)
    (hw : Continuous w) (hη : η < 1)
    (hi : InjOn w {x : E2 | |‖x‖-1| < η})
    (hA : ∀ x, 1-η < A x ∧ A x < 1)
    (hAh : ∀ x (r : ℝ), 0 < r → A (r • x)=A x)
    (hJ : IsJordanCurve J)
    (hJdata : J=w '' {x : E2 | ‖x‖=A x})
    (hinside : closure (inside J) ⊆ V)
    (houter : ∀ x : E2, ‖x‖=1 → w x ∉ V) :
    ∀ x : E2, A x < ‖x‖ → ‖x‖ ≤ 1 → w x ∈ outside J := by
  have hJs := jordan_curve_theorem hJ
  have hpos (x : E2) : 0 < A x := by linarith [(hA x).1]
  have hmem (x : E2) (h1 : A x ≤ ‖x‖) (h2 : ‖x‖ ≤ 1) : |‖x‖-1| < η := by
    rw [abs_lt]
    exact ⟨by linarith [(hA x).1],by linarith [(hA x).1,(hA x).2,h2]⟩
  have hav (x : E2) (hx : A x < ‖x‖) (hx1 : ‖x‖ ≤ 1) : w x ∉ J := by
    intro hj
    rw [hJdata] at hj
    obtain ⟨y,hy,he⟩ := hj
    have hy' : ‖y‖=A y := hy
    have heq : y=x := hi (hmem y (by rw [hy']) (by rw [hy']; exact (hA y).2.le))
      (hmem x hx.le hx1) he
    subst y
    exact hx.ne' hy'
  intro x hx hx1
  have hx0 : 0 < ‖x‖ := (hpos x).trans hx
  let u := ‖x‖⁻¹ • x
  have hnu : ‖u‖=1 := by simp [u,norm_smul,hx0.ne']
  have hux : ‖x‖ • u=x := by simp [u,smul_smul,hx0.ne']
  have hAu : A u=A x := hAh x _ (inv_pos.mpr hx0)
  let p : ℝ → E2 := fun r => w (r • u)
  have hpc : Continuous p := hw.comp (continuous_id.smul continuous_const)
  let S := p '' Icc ‖x‖ 1
  have hSc : IsPreconnected S := isPreconnected_Icc.image _ hpc.continuousOn
  have hScompl : S ⊆ Jᶜ := by
    rintro _ ⟨r,hr,rfl⟩
    have hr0 : 0 < r := hx0.trans_le hr.1
    have hnr : ‖r • u‖=r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr0,hnu,mul_one]
    apply hav
    · rw [hAh u r hr0,hAu,hnr]
      exact hx.trans_le hr.1
    · rw [hnr]; exact hr.2
  have h1out : p 1 ∈ outside J := by
    rw [hJs.outside_eq_compl_closure_inside]
    intro hh
    apply houter u hnu
    exact hinside (by simpa [p] using hh)
  have hSout : S ⊆ outside J := by
    apply hSc.subset_left_of_subset_union hJs.isOpen_outside hJs.isOpen_inside
      disjoint_inside_outside.symm
    · rw [union_comm,inside_union_outside]
      exact hScompl
    · exact ⟨p 1,⟨1,⟨hx1,le_rfl⟩,rfl⟩,h1out⟩
  apply hSout
  refine ⟨‖x‖,⟨le_rfl,hx1⟩,?_⟩
  change w (‖x‖ • u)=w x
  rw [hux]
end VM03CapV437
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open Schoenflies DifferentialGeometry.Topology.PiecewiseLinear
namespace VM03CapV437
private theorem support_ActualContinuousCap (R : ℝ) (Ω : SmoothFlatJordanDomain R) (w : E2 → E2) (η : ℝ)
    (hw : ContDiff ℝ ∞ w) (hb : ∀ t, w (unitCircleParameter t)=Ω.boundary.gamma t)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hi : InjOn w {x : E2 | |‖x‖-1| < η})
    (hdet : ∀ x : E2, |‖x‖-1| < η → (fderiv ℝ w x).det ≠ 0)
    (hinward : ∀ x : E2, 1-η < ‖x‖ → ‖x‖ < 1 → w x ∈ Ω.domain) :
    ∃ (H : E2 → E2) (b : ℝ), 1-η < b ∧ b < 1 ∧
      ContinuousOn H (closedBall 0 1) ∧ InjOn H (closedBall 0 1) ∧
      H '' ball 0 1=Ω.domain ∧
      (∀ t, H (unitCircleParameter t)=Ω.boundary.gamma t) ∧
      EqOn H w {x | b ≤ ‖x‖} := by
  classical
  let r := 1-η/2
  have hr : 1-η < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  obtain ⟨N,ρ,hN,hρ,hρp,hρb,hρv,hcar,hpieces⟩ :=
    support_BoundaryReparameterization_1 w η r hw hη0 hη1 hr hr1 hi hdet
  obtain ⟨m,P,hPcar,hPball⟩ := support_SamePolygon_1 R Ω w η hw.continuous hb hη1 hi
    ρ hρ hρp hρb N (by omega)
    (fun i => w (r • unitCircleParameter ((i:ℝ)*(2*Real.pi/N)))) hcar
  have hPJ : IsJordanCurve P.carrier := isJordanCurve_of_isPLSphere_one (closedPolygon_isPLSphere P)
  have hΓ : IsJordanCurve (frontier Ω.domain) := by
    rw [← Ω.boundary.image]
    exact periodic_jordan Ω.boundary.gamma Ω.boundary.smooth.continuous Ω.boundary.periodic
      (fun t u he => (Ω.boundary.simple t u).mp he)
  have hPV : P.carrier ⊆ Ω.domain := by
    rw [hPcar]
    rintro y ⟨t,rfl⟩
    have hρpos : 0 < ρ t := by linarith [(hρb t).1]
    have hn : ‖ρ t • unitCircleParameter t‖=ρ t := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hρpos,circle_norm,mul_one]
    apply hinward
    · rw [hn]; exact (hρb t).1
    · rw [hn]; exact (hρb t).2
  have hinside : closure (inside P.carrier) ⊆ Ω.domain :=
    inner_polygon_subset_domain Ω.domain P.carrier Ω.open_domain Ω.connected_domain Ω.bounded_domain
      hΓ hPJ hPV
  obtain ⟨a,b,ha,hab,hb1,A,F,hAu,hA,hAc,hAh,hFc,hFb,hFtrace,hFout⟩ :=
    support_AnnularConnection_1 w η ρ hw.continuous hη0 hη1 hi hρ hρp hρb
  have hbη : 1-η < b := (hA 0).1.trans (hA 0).2
  have ha1 : a < 1 := hab.trans hb1
  have hAb (x : E2) : 1-η < A x ∧ A x < 1 := ⟨(hA x).1,(hA x).2.trans hb1⟩
  have hApos (x : E2) : 0 < A x := by linarith [(hA x).1]
  obtain ⟨B,hBc,hBb,hBtrace⟩ := sphere_boundary_bijection w η A ρ hw.continuous hη1 hi hAc hAb hAu
  have hB : BijOn B (sphere 0 1) (frontier (closure (inside P.carrier))) := by
    rw [frontier_closure_inside_of_isPLSphere_one (closedPolygon_isPLSphere P),hPcar]
    exact hBb
  obtain ⟨K,L,C,G,hKfin,hKconv,hKcomp,hK0,hKball,hL,hCc,hCb,hCclosed,hCopen,
    hGformula,hGc,hGclosed,hGopen,hGtrace⟩ := inner_pl_disk_with_prescribed_boundary
      (closure (inside P.carrier)) hPball isClosed_closure B hBc hB
  have hI : interior (closure (inside P.carrier))=inside P.carrier := by
    apply Subset.antisymm
    · intro x hx
      have hm := interior_subset hx
      rw [(IsRegionOf.inside P.carrier).closure_eq (jordan_curve_theorem hPJ)] at hm
      apply hm.resolve_right
      intro hxP
      have hf : x ∈ frontier (closure (inside P.carrier)) := by
        rwa [frontier_closure_inside_of_isPLSphere_one (closedPolygon_isPLSphere P)]
      exact hf.2 hx
    · have hh := interior_mono (subset_closure (s:=inside P.carrier))
      rwa [(jordan_curve_theorem hPJ).isOpen_inside.interior_eq] at hh
  have hGim : G '' ball 0 1=inside P.carrier := hGopen.image_eq.trans hI
  have hseam : ∀ x : E2, ‖x‖=a → G (a⁻¹ • x)=F x := by
    intro x hx
    have hn : a⁻¹ • x ∈ sphere 0 1 := by simp [norm_smul,Real.norm_eq_abs,abs_of_pos ha,hx,ha.ne']
    obtain ⟨t,ht⟩ := circle_surjective (a⁻¹ • x) hn
    have he : a • unitCircleParameter t=x := by rw [ht,smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
    rw [← ht,hGtrace (mem_sphere_zero_iff_norm.mpr (circle_norm t)),hBtrace,← hFtrace,he]
  obtain ⟨H,hHc,hHsmall,hHlarge,hHclosed,hHopen⟩ := disk_annulus_glue a ha ha1 G F hGc hFc hseam
  have hJdata : P.carrier=w '' {x : E2 | ‖x‖=A x} :=
    hPcar.trans (radial_boundary_level w A ρ hApos hAh hAu)
  have hout : ∀ x : E2, A x < ‖x‖ → ‖x‖ ≤ 1 → w x ∈ outside P.carrier :=
    radial_annular_image_outside w η A P.carrier Ω.domain hw.continuous hη1 hi hAb hAh
      hPJ hJdata hinside (by
        intro x hx
        obtain ⟨t,rfl⟩ := circle_surjective x (mem_sphere_zero_iff_norm.mpr hx)
        rw [hb]
        have hf : Ω.boundary.gamma t ∈ frontier Ω.domain := Ω.boundary.image ▸ mem_range_self t
        rw [Ω.open_domain.frontier_eq] at hf
        exact hf.2)
  have hdis : Disjoint (G '' ball 0 1) (F '' {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1}) := by
    rw [hGim,hFb.image_eq]
    apply disjoint_left.mpr
    rintro y hy ⟨x,hx,rfl⟩
    rcases hx.1.eq_or_lt with he | he
    · exact inside_subset_compl hy (hJdata.symm ▸ mem_image_of_mem w (show x ∈ {x | ‖x‖=A x} from he.symm))
    · exact disjoint_left.mp disjoint_inside_outside hy (hout x he hx.2)
  have hHi : InjOn H (closedBall 0 1) := disk_annulus_glue_injective a ha ha1 G F H
    hGclosed.injOn hFb.injOn hHsmall hHlarge hdis
  have hHout : EqOn H w {x | b ≤ ‖x‖} := by
    intro x hx
    exact (hHlarge (hab.le.trans hx)).trans (hFout hx)
  have hHtrace (t : ℝ) : H (unitCircleParameter t)=Ω.boundary.gamma t := by
    apply (hHout (by change b ≤ ‖unitCircleParameter t‖; rw [circle_norm]; exact hb1.le)).trans
    exact hb t
  have hboundary : H '' sphere 0 1=frontier Ω.domain := by
    rw [← Ω.boundary.image]
    apply Subset.antisymm
    · rintro y ⟨x,hx,rfl⟩
      obtain ⟨t,rfl⟩ := circle_surjective x hx
      exact ⟨t,(hHtrace t).symm⟩
    · rintro y ⟨t,rfl⟩
      exact ⟨unitCircleParameter t,mem_sphere_zero_iff_norm.mpr (circle_norm t),hHtrace t⟩
  obtain ⟨hHo,hHconn,hHbounded,hHfront⟩ := embedded_disk_frontier H hHc hHi
  have hHV : H '' ball 0 1=Ω.domain := by
    exact (bounded_region_eq_inside _ _ hHo hHconn hHbounded hΓ (hHfront.trans hboundary)).trans
      (bounded_region_eq_inside Ω.domain (frontier Ω.domain) Ω.open_domain Ω.connected_domain
        Ω.bounded_domain hΓ rfl).symm
  exact ⟨H,b,hbη,hb1,hHc,hHi,hHV,hHtrace,hHout⟩
end VM03CapV437
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
namespace VM03CapV437RawRegular
private theorem circle_norm (t : ℝ) : ‖unitCircleParameter t‖=1 := by
  have hh : ‖unitCircleParameter t‖^2=1 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
    exact Real.cos_sq_add_sin_sq t
  nlinarith [norm_nonneg (unitCircleParameter t)]

private theorem circle_surjective (x : E2) (hx : x ∈ sphere 0 1) :
    ∃ t : ℝ, unitCircleParameter t=x := by
  let z : ℂ := ⟨x 0,x 1⟩
  have hnx : ‖x‖=1 := mem_sphere_zero_iff_norm.mp hx
  have hnz : ‖z‖=1 := by
    have hn : ‖z‖^2=‖x‖^2 := by
      rw [Complex.sq_norm,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
      simp [Complex.normSq_apply,z,pow_two]
    rw [hnx] at hn
    nlinarith [norm_nonneg z]
  have hz : z ≠ 0 := by intro he; simp [he] at hnz
  refine ⟨z.arg,?_⟩
  ext i
  fin_cases i
  · change Real.cos z.arg=x 0
    rw [Complex.cos_arg hz,hnz,div_one]
  · change Real.sin z.arg=x 1
    rw [Complex.sin_arg,hnz,div_one]

private theorem sphere_boundary_bijection
    (w : E2 → E2) (η : ℝ) (A : E2 → ℝ) (ρ : ℝ → ℝ)
    (hw : Continuous w) (hη : η < 1)
    (hi : InjOn w {x : E2 | |‖x‖-1| < η})
    (hAc : ∀ x, x ≠ 0 → ContinuousAt A x)
    (hA : ∀ x, 1-η < A x ∧ A x < 1)
    (hAu : ∀ t, A (unitCircleParameter t)=ρ t) :
    ∃ B : E2 → E2, ContinuousOn B (sphere 0 1) ∧
      BijOn B (sphere 0 1) (range (fun t => w (ρ t • unitCircleParameter t))) ∧
      (∀ t, B (unitCircleParameter t)=w (ρ t • unitCircleParameter t)) := by
  let B : E2 → E2 := fun x => w (A x • x)
  have hpos (x : E2) : 0 < A x := by linarith [(hA x).1]
  have hnorm (x : E2) (hx : x ∈ sphere 0 1) : ‖A x • x‖=A x := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hpos x),mem_sphere_zero_iff_norm.mp hx,mul_one]
  have hmem (x : E2) (hx : x ∈ sphere 0 1) : |‖A x • x‖-1| < η := by
    rw [hnorm x hx,abs_lt]
    exact ⟨by linarith [(hA x).1],by linarith [(hA x).1,(hA x).2]⟩
  have hBu (t : ℝ) : B (unitCircleParameter t)=w (ρ t • unitCircleParameter t) := by
    dsimp [B]
    rw [hAu]
  refine ⟨B,?_,⟨?_,?_,?_⟩,hBu⟩
  · intro x hx
    exact (hw.continuousAt.comp ((hAc x (ne_of_mem_sphere hx one_ne_zero)).smul continuousAt_id)).continuousWithinAt
  · intro x hx
    obtain ⟨t,rfl⟩ := circle_surjective x hx
    rw [hBu]
    exact mem_range_self t
  · intro x hx y hy he
    have hh : A x • x=A y • y := hi (hmem x hx) (hmem y hy) he
    have hval : A x=A y := by
      have hn := congrArg norm hh
      rwa [hnorm x hx,hnorm y hy] at hn
    rw [← hval] at hh
    exact smul_right_injective E2 (hpos x).ne' hh
  · rintro _ ⟨t,rfl⟩
    exact ⟨unitCircleParameter t,mem_sphere_zero_iff_norm.mpr (circle_norm t),hBu t⟩


private theorem circle_injOn_short_interval (a b : ℝ) (hab : b-a < 2*Real.pi) :
    InjOn unitCircleParameter (Icc a b) := by
  letI : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
  intro x hx y hy he
  have hcos : Real.cos x=Real.cos y := congrArg (fun z : E2 => z 0) he
  have hsin : Real.sin x=Real.sin y := congrArg (fun z : E2 => z 1) he
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show x ∈ Ico a (a+2*Real.pi) from ⟨hx.1,by linarith [hx.2]⟩)
    (show y ∈ Ico a (a+2*Real.pi) from ⟨hy.1,by linarith [hy.2]⟩)).mp
    (Real.Angle.cos_sin_inj hcos hsin)

private theorem chord_parameter_strictMono
    (B : E2 → E2) (hB : InjOn B (sphere 0 1))
    (a b : ℝ) (hab : a ≤ b) (hshort : b-a < 2*Real.pi)
    (p q : E2) (τ : ℝ → ℝ) (hc : ContinuousOn τ (Icc a b))
    (ha : τ a=0) (hb : τ b=1)
    (he : ∀ t ∈ Icc a b, B (unitCircleParameter t)=AffineMap.lineMap p q (τ t)) :
    StrictMonoOn τ (Icc a b) := by
  apply ContinuousOn.strictMonoOn_of_injOn_Icc hab (by rw [ha,hb]; norm_num) hc
  intro t ht u hu htu
  apply circle_injOn_short_interval a b hshort ht hu
  apply hB (mem_sphere_zero_iff_norm.mpr (circle_norm t))
    (mem_sphere_zero_iff_norm.mpr (circle_norm u))
  rw [he t ht,he u hu,htu]


private theorem radial_boundary_level (w : E2 → E2) (A : E2 → ℝ) (ρ : ℝ → ℝ)
    (hA : ∀ x, 0 < A x) (hAh : ∀ x (r : ℝ), 0 < r → A (r • x)=A x)
    (hAu : ∀ t, A (unitCircleParameter t)=ρ t) :
    range (fun t => w (ρ t • unitCircleParameter t))=w '' {x : E2 | ‖x‖=A x} := by
  apply Subset.antisymm
  · rintro y ⟨t,rfl⟩
    have hρ : 0 < ρ t := by rw [← hAu]; exact hA _
    refine ⟨ρ t • unitCircleParameter t,?_,rfl⟩
    change ‖ρ t • unitCircleParameter t‖=A (ρ t • unitCircleParameter t)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hρ,circle_norm,mul_one,hAh _ _ hρ,hAu]
  · rintro y ⟨x,hx,rfl⟩
    have hnorm : ‖x‖=A x := hx
    have hxpos : 0 < ‖x‖ := hnorm ▸ hA x
    let u := ‖x‖⁻¹ • x
    have hnu : u ∈ sphere 0 1 := by simp [u,norm_smul,hxpos.ne']
    obtain ⟨t,ht⟩ := circle_surjective u hnu
    refine ⟨t,?_⟩
    have hρ : ρ t=‖x‖ := by
      rw [← hAu,ht,hAh x _ (inv_pos.mpr hxpos),hnorm]
    change w (ρ t • unitCircleParameter t)=w x
    rw [hρ,ht]
    simp [u,smul_smul,hxpos.ne']
end VM03CapV437RawRegular
noncomputable section
open Set Function Filter Metric
open scoped Topology ContDiff
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Topology.PiecewiseLinear
namespace VM03CapV437RawRegular
private theorem real_finite_convexHull (s : Finset ℝ) (hs : s.Nonempty) :
    convexHull ℝ (s:Set ℝ)=Icc (s.min' hs) (s.max' hs) := by
  apply Subset.antisymm
  · apply convexHull_min
    · intro x hx
      exact ⟨Finset.min'_le s x hx,Finset.le_max' s x hx⟩
    · exact convex_Icc _ _
  · have hmin : s.min' hs ∈ convexHull ℝ (s:Set ℝ) :=
      subset_convexHull ℝ _ (Finset.min'_mem s hs)
    have hmax : s.max' hs ∈ convexHull ℝ (s:Set ℝ) :=
      subset_convexHull ℝ _ (Finset.max'_mem s hs)
    have hh := (convex_convexHull ℝ (s:Set ℝ)).segment_subset hmin hmax
    simpa only [segment_eq_Icc (Finset.min'_le_max' s hs)] using hh

private theorem pl_interval_affine_cover (f : ℝ → E2) (a b : ℝ)
    (hf : IsPiecewiseAffineOn f (Icc a b)) :
    ∃ (ι : Type) (_ : Finite ι) (l u : ι → ℝ) (A : ι → ℝ →ᵃ[ℝ] E2),
      (∀ i, a≤l i ∧ l i≤u i ∧ u i≤b ∧ EqOn f (A i) (Icc (l i) (u i))) ∧
      ∀ x∈Icc a b, ∃ i, x∈Icc (l i) (u i) := by
  classical
  obtain ⟨K,hfin,hspace⟩ := (isHPolytope_Icc (a:=a) (b:=b)).isPolyhedron.exists_simplicialComplex
  letI : Finite K.faces := hfin.to_subtype
  have hfK : IsPiecewiseAffineOn f K.space := hspace ▸ hf
  obtain ⟨J,hsub,hJfin,hfaces⟩ := hfK.exists_isSubdivision_affineOn_faces K
  letI : Finite J.faces := hJfin.to_subtype
  have hJspace : J.space=Icc a b := hsub.space_eq.trans hspace
  let l : J.faces → ℝ := fun s => s.1.min' (J.nonempty_of_mem_faces s.2)
  let u : J.faces → ℝ := fun s => s.1.max' (J.nonempty_of_mem_faces s.2)
  have hHull (s : J.faces) : convexHull ℝ (s.1:Set ℝ)=Icc (l s) (u s) :=
    real_finite_convexHull s.1 (J.nonempty_of_mem_faces s.2)
  choose A hA using fun s : J.faces => hfaces s.1 s.2
  refine ⟨J.faces,inferInstance,l,u,A,?_,?_⟩
  · intro s
    have hlu : l s≤u s := Finset.min'_le_max' s.1 (J.nonempty_of_mem_faces s.2)
    have hsub : Icc (l s) (u s) ⊆ Icc a b := by
      rw [← hHull s,← hJspace]
      exact J.convexHull_subset_space s.2
    exact ⟨(hsub ⟨le_rfl,hlu⟩).1,hlu,(hsub ⟨hlu,le_rfl⟩).2,by
      rw [← hHull s]; exact hA s⟩
  · intro x hx
    have hxJ : x∈J.space := hJspace.symm ▸ hx
    obtain ⟨s,hs,hxs⟩ := J.mem_space_iff.mp hxJ
    exact ⟨⟨s,hs⟩,(hHull ⟨s,hs⟩) ▸ hxs⟩
end VM03CapV437RawRegular
namespace VM03CapV437RawRegular
private theorem finite_knots_order (S : Finset ℝ) (a b : ℝ) (hab : a<b)
    (ha : a∈S) (hb : b∈S) (hS : (S:Set ℝ) ⊆ Icc a b) :
    ∃ (m : ℕ) (_ : 0 < m) (r : Fin (m + 1) → ℝ), StrictMono r ∧ r 0=a ∧
      r (Fin.last m)=b ∧ range r=(S:Set ℝ) ∧
      ∀ (i : Fin m) z, z∈S → ¬ (r i.castSucc<z ∧ z<r i.succ) := by
  classical
  have hcard : 2≤S.card := by
    have hp : ({a,b}:Finset ℝ) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl
      · exact ha
      · exact hb
    have hh := Finset.card_le_card hp
    simpa [Finset.card_pair hab.ne] using hh
  let m := S.card-1
  have hm : 0 < m := by dsimp [m]; omega
  have heq : S.card=m + 1 := by dsimp [m]; omega
  let r : Fin (m + 1) ↪o ℝ := S.orderEmbOfFin heq
  have hrange : range r=(S:Set ℝ) := Finset.range_orderEmbOfFin S heq
  have hrS (i : Fin (m + 1)) : r i∈S := S.orderEmbOfFin_mem heq i
  have hr0 : r 0=a := by
    obtain ⟨i,hi⟩ : a∈range r := by rw [hrange]; exact ha
    exact le_antisymm (by rw [← hi]; exact r.monotone (Fin.zero_le _)) (hS (hrS 0)).1
  have hrm : r (Fin.last m)=b := by
    obtain ⟨i,hi⟩ : b∈range r := by rw [hrange]; exact hb
    exact le_antisymm (hS (hrS _)).2 (by rw [← hi]; exact r.monotone (Fin.le_last _))
  refine ⟨m,hm,r,r.strictMono,hr0,hrm,hrange,?_⟩
  intro i z hz hzbetween
  obtain ⟨j,hj⟩ : z∈range r := by rw [hrange]; exact hz
  rw [← hj] at hzbetween
  have hi : i.castSucc < j := r.lt_iff_lt.mp hzbetween.1
  have hj' : j < i.succ := r.lt_iff_lt.mp hzbetween.2
  have h1 : i.1 < j.1 := hi
  have h2 : j.1 < i.1+1 := hj'
  omega

private theorem interval_cover_partition {ι : Type*} [Finite ι]
    (a b : ℝ) (hab : a<b) (l u : ι → ℝ)
    (hbound : ∀ i, a≤l i ∧ l i≤u i ∧ u i≤b)
    (hcover : ∀ x∈Icc a b, ∃ i, x∈Icc (l i) (u i)) :
    ∃ (m : ℕ) (_ : 0 < m) (r : Fin (m + 1) → ℝ), StrictMono r ∧ r 0=a ∧
      r (Fin.last m)=b ∧ ∀ i : Fin m, ∃ j, Icc (r i.castSucc) (r i.succ) ⊆ Icc (l j) (u j) := by
  classical
  letI : Fintype ι := Fintype.ofFinite _
  let S : Finset ℝ := {a,b} ∪ Finset.univ.image l ∪ Finset.univ.image u
  have ha : a∈S := by simp [S]
  have hb : b∈S := by simp [S]
  have hl (i : ι) : l i∈S := by simp [S]
  have hu (i : ι) : u i∈S := by simp [S]
  have hS : (S:Set ℝ) ⊆ Icc a b := by
    intro x hx
    simp only [S,Finset.mem_coe,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_image,Finset.mem_univ,true_and] at hx
    rcases hx with ((rfl|rfl)|⟨i,rfl⟩)|⟨i,rfl⟩
    · exact ⟨le_rfl,hab.le⟩
    · exact ⟨hab.le,le_rfl⟩
    · exact ⟨(hbound i).1,(hbound i).2.1.trans (hbound i).2.2⟩
    · exact ⟨(hbound i).1.trans (hbound i).2.1,(hbound i).2.2⟩
  obtain ⟨m,hm,r,hr,hr0,hrm,hrange,hgap⟩ := finite_knots_order S a b hab ha hb hS
  refine ⟨m,hm,r,hr,hr0,hrm,?_⟩
  intro i
  have hi : r i.castSucc<r i.succ := hr (by exact_mod_cast Nat.lt_succ_self i.1)
  have hlow : a≤r i.castSucc := by rw [← hr0]; exact hr.monotone (Fin.zero_le _)
  have hupp : r i.succ≤b := by rw [← hrm]; exact hr.monotone (Fin.le_last _)
  let x := (r i.castSucc+r i.succ)/2
  obtain ⟨j,hj⟩ := hcover x ⟨by dsimp [x]; linarith,by dsimp [x]; linarith⟩
  have hlj : l j≤r i.castSucc := by
    by_contra hh
    exact hgap i (l j) (hl j) ⟨lt_of_not_ge hh,by dsimp [x] at hj; linarith [hj.1]⟩
  have huj : r i.succ≤u j := by
    by_contra hh
    exact hgap i (u j) (hu j) ⟨by dsimp [x] at hj; linarith [hj.2],lt_of_not_ge hh⟩
  exact ⟨j,fun _ hx => ⟨hlj.trans hx.1,hx.2.trans huj⟩⟩

private theorem pl_interval_partition (f : ℝ → E2) (a b : ℝ) (hab : a<b)
    (hf : IsPiecewiseAffineOn f (Icc a b)) :
    ∃ (m : ℕ) (_ : 0 < m) (r : Fin (m + 1) → ℝ), StrictMono r ∧ r 0=a ∧
      r (Fin.last m)=b ∧ ∀ i : Fin m, ∃ A : ℝ →ᵃ[ℝ] E2,
        EqOn f A (Icc (r i.castSucc) (r i.succ)) := by
  obtain ⟨ι,hfin,l,u,A,hbound,hcover⟩ := pl_interval_affine_cover f a b hf
  letI : Finite ι := hfin
  obtain ⟨m,hm,r,hr,hr0,hrm,hsub⟩ := interval_cover_partition a b hab l u
    (fun i => ⟨(hbound i).1,(hbound i).2.1,(hbound i).2.2.1⟩) hcover
  refine ⟨m,hm,r,hr,hr0,hrm,?_⟩
  intro i
  obtain ⟨j,hj⟩ := hsub i
  exact ⟨A j,(hbound j).2.2.2.mono hj⟩
end VM03CapV437RawRegular
namespace VM03CapV437RawRegular
private theorem smooth_reparameterized_pl_interval
    (f : ℝ → E2) (hf : IsPiecewiseAffineOn f (Icc (0:ℝ) 1))
    (τ : ℝ → ℝ) (a b : ℝ) (hab : a<b)
    (hτ : ContDiffOn ℝ ∞ τ (Icc a b)) (hm : StrictMonoOn τ (Icc a b))
    (him : τ '' Icc a b=Icc (0:ℝ) 1) (ha : τ a=0) (hb : τ b=1) :
    ∃ (m : ℕ) (_ : 0 < m) (r : Fin (m+1) → ℝ), StrictMono r ∧ r 0=a ∧
      r (Fin.last m)=b ∧ ∀ i : Fin m,
        ContDiffOn ℝ ∞ (f ∘ τ) (Icc (r i.castSucc) (r i.succ)) := by
  classical
  obtain ⟨m,hm0,s,hs,hs0,hsm,hfaces⟩ := pl_interval_partition f 0 1 (by norm_num) hf
  have hsI (i : Fin (m+1)) : s i∈Icc (0:ℝ) 1 :=
    ⟨by rw [← hs0]; exact hs.monotone (Fin.zero_le _),by rw [← hsm]; exact hs.monotone (Fin.le_last _)⟩
  have hr_ex (i : Fin (m+1)) : ∃ x∈Icc a b,τ x=s i := by
    have hi : s i∈τ '' Icc a b := him.symm ▸ hsI i
    exact hi
  choose r hr hτr using hr_ex
  have hrm : StrictMono r := by
    intro i j hij
    by_contra hh
    have hh' : τ (r j)≤τ (r i) := hm.monotoneOn (hr j) (hr i) (le_of_not_gt hh)
    rw [hτr,hτr] at hh'
    exact (not_le_of_gt (hs hij)) hh'
  have hr0 : r 0=a := hm.injOn (hr 0) ⟨le_rfl,hab.le⟩ (by rw [hτr,hs0,ha])
  have hrend : r (Fin.last m)=b := hm.injOn (hr _) ⟨hab.le,le_rfl⟩ (by rw [hτr,hsm,hb])
  refine ⟨m,hm0,r,hrm,hr0,hrend,?_⟩
  intro i
  obtain ⟨A,hA⟩ := hfaces i
  have hsub : Icc (r i.castSucc) (r i.succ) ⊆ Icc a b :=
    fun x hx => ⟨(hr i.castSucc).1.trans hx.1,hx.2.trans (hr i.succ).2⟩
  have hmap : MapsTo τ (Icc (r i.castSucc) (r i.succ))
      (Icc (s i.castSucc) (s i.succ)) := by
    intro x hx
    exact ⟨by rw [← hτr]; exact hm.monotoneOn (hr _) (hsub hx) hx.1,
      by rw [← hτr]; exact hm.monotoneOn (hsub hx) (hr _) hx.2⟩
  have hAcd : ContDiff ℝ ∞ A :=
    (show ContinuousAffineMap ℝ ℝ E2 from ⟨A,A.continuous_of_finiteDimensional⟩).contDiff
  exact (hAcd.comp_contDiffOn (hτ.mono hsub)).congr fun x hx => hA (hmap hx)
end VM03CapV437RawRegular
namespace VM03CapV437RawRegular
private theorem fin_partition_cover (m : ℕ) (hm : 0 < m)
    (r : Fin (m+1) → ℝ) (hr : Monotone r) :
    ∀ x∈Icc (r 0) (r (Fin.last m)), ∃ i : Fin m,
      x∈Icc (r i.castSucc) (r i.succ) := by
  classical
  intro x hx
  by_cases hxend : x=r (Fin.last m)
  · let i : Fin m := ⟨m-1,Nat.sub_lt hm (by omega)⟩
    have hi : i.succ=Fin.last m := Fin.ext (by dsimp [i]; omega)
    exact ⟨i,by rw [hi,hxend]; exact ⟨hr (Fin.le_last _),le_rfl⟩⟩
  let S : Finset (Fin (m+1)) := Finset.univ.filter fun j => r j≤x
  have hS : S.Nonempty := ⟨0,by simp [S,hx.1]⟩
  let j := S.max' hS
  have hj : r j≤x := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  have hjm : j.1 < m := by
    by_contra hh
    have he : j=Fin.last m := by
      apply Fin.ext
      change j.1=m
      have := j.2
      omega
    exact hxend (le_antisymm hx.2 (he ▸ hj))
  let i : Fin m := ⟨j.1,hjm⟩
  have hi : i.castSucc=j := Fin.ext rfl
  have hnext : x≤r i.succ := by
    by_contra hh
    have hmem : i.succ∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(lt_of_not_ge hh).le⟩
    have hle := Finset.le_max' S i.succ hmem
    have hval : j.1+1≤j.1 := hle
    omega
  exact ⟨i,by rw [hi]; exact hj,hnext⟩

private theorem pl_trace_partition
    (V : E2 → E2) (D : Set E2) (hV : IsPiecewiseAffineOn V D)
    (γ : ℝ → E2) (p q : E2) (hpq : segment ℝ p q ⊆ D)
    (τ : ℝ → ℝ) (a b : ℝ) (hab : a<b)
    (hτ : ContDiffOn ℝ ∞ τ (Icc a b)) (hm : StrictMonoOn τ (Icc a b))
    (him : τ '' Icc a b=Icc (0:ℝ) 1) (ha : τ a=0) (hb : τ b=1)
    (htrace : ∀ t∈Icc a b, γ t=AffineMap.lineMap p q (τ t)) :
    ∃ (m : ℕ) (_ : 0 < m) (r : Fin (m+1) → ℝ), StrictMono r ∧ r 0=a ∧
      r (Fin.last m)=b ∧ ∀ i : Fin m,
        ContDiffOn ℝ ∞ (V ∘ γ) (Icc (r i.castSucc) (r i.succ)) := by
  let c : ℝ →ᵃ[ℝ] E2 := AffineMap.lineMap p q
  have hc : IsPiecewiseAffineOn c (Icc (0:ℝ) 1) :=
    isPiecewiseAffineOn_of_affine_of_isHPolytope c isHPolytope_Icc
  have hmap : Icc (0:ℝ) 1 ⊆ c ⁻¹' D := by
    intro s hs
    apply hpq
    rw [segment_eq_image_lineMap]
    exact ⟨s,hs,rfl⟩
  have hf : IsPiecewiseAffineOn (V ∘ c) (Icc (0:ℝ) 1) := by
    have hh := hV.comp hc
    rwa [inter_eq_left.mpr hmap] at hh
  obtain ⟨m,hm0,r,hr,hr0,hrm,hpieces⟩ := smooth_reparameterized_pl_interval
    (V ∘ c) hf τ a b hab hτ hm him ha hb
  refine ⟨m,hm0,r,hr,hr0,hrm,?_⟩
  intro i
  have hsub : Icc (r i.castSucc) (r i.succ) ⊆ Icc a b := by
    intro t ht
    have hl : a≤r i.castSucc := by rw [← hr0]; exact hr.monotone (Fin.zero_le _)
    have hu : r i.succ≤b := by rw [← hrm]; exact hr.monotone (Fin.le_last _)
    exact ⟨hl.trans ht.1,ht.2.trans hu⟩
  exact (hpieces i).congr fun t ht => congrArg V (htrace t (hsub ht))
end VM03CapV437RawRegular
noncomputable section
open Set Function Metric
open SeifertSurfaces.AppendixACoordinates
namespace VM03CapV437RawRegular
private theorem lipschitzOn_Icc_join {Y : Type*} [PseudoMetricSpace Y]
    (f : ℝ → Y) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (K : NNReal)
    (hleft : LipschitzOnWith K f (Icc a b)) (hright : LipschitzOnWith K f (Icc b c)) :
    LipschitzOnWith K f (Icc a c) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  wlog hxy : x ≤ y generalizing x y
  · simpa only [dist_comm (f y) (f x),dist_comm y x] using this y hy x hx (le_of_not_ge hxy)
  by_cases hyb : y ≤ b
  · exact hleft.dist_le_mul x ⟨hx.1,hxy.trans hyb⟩ y ⟨hy.1,hyb⟩
  by_cases hbx : b ≤ x
  · exact hright.dist_le_mul x ⟨hbx,hx.2⟩ y ⟨hbx.trans hxy,hy.2⟩
  have hxb : x ≤ b := (lt_of_not_ge hbx).le
  have hby : b ≤ y := (lt_of_not_ge hyb).le
  have h1 := hleft.dist_le_mul x ⟨hx.1,hxb⟩ b ⟨hab,le_rfl⟩
  have h2 := hright.dist_le_mul b ⟨le_rfl,hbc⟩ y ⟨hby,hy.2⟩
  have ht := dist_triangle (f x) (f b) (f y)
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxb)] at h1
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hby)] at h2
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy)]
  nlinarith

private theorem lipschitzOn_finite_partition {Y : Type*} [PseudoMetricSpace Y]
    (f : ℝ → Y) (r : ℕ → ℝ) (hr : Monotone r) (K : NNReal) :
    ∀ N : ℕ, (∀ i < N, LipschitzOnWith K f (Icc (r i) (r (i+1)))) →
      LipschitzOnWith K f (Icc (r 0) (r N)) := by
  intro N
  induction N with
  | zero =>
    intro _
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hx' : x=r 0 := le_antisymm hx.2 hx.1
    have hy' : y=r 0 := le_antisymm hy.2 hy.1
    simp [hx',hy']
  | succ n ih =>
    intro hpieces
    exact lipschitzOn_Icc_join f (r 0) (r n) (r (n+1)) (hr (Nat.zero_le _))
      (hr (Nat.le_succ _)) K (ih fun i hi => hpieces i (Nat.lt.step hi))
      (hpieces n (Nat.lt_succ_self n))

private theorem finite_partition_lipschitz {Y : Type*} [PseudoMetricSpace Y]
    (f : ℝ → Y) (r : ℕ → ℝ) (hr : Monotone r) (N : ℕ)
    (hpieces : ∀ i : Fin N, ∃ K : NNReal, LipschitzOnWith K f (Icc (r i) (r (i.1+1)))) :
    ∃ K : NNReal, LipschitzOnWith K f (Icc (r 0) (r N)) := by
  classical
  choose k hk using hpieces
  let K := Finset.univ.sup k
  refine ⟨K,lipschitzOn_finite_partition f r hr K N ?_⟩
  intro i hi
  exact (hk ⟨i,hi⟩).weaken (by
    simpa only [K] using
      (Finset.le_sup (s := (Finset.univ : Finset (Fin N)))
        (f := k) (Finset.mem_univ ⟨i,hi⟩)))
end VM03CapV437RawRegular
namespace VM03CapV437RawRegular
private theorem periodic_lipschitz {Y : Type*} [PseudoMetricSpace Y]
    (f : ℝ → Y) (T : ℝ) (hT : 0<T) (hper : Periodic f T) (K : NNReal)
    (hK : LipschitzOnWith K f (Icc 0 T)) : LipschitzWith K f := by
  have hshift : LipschitzOnWith K f (Icc T (2*T)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hh := hK.dist_le_mul (x-T) ⟨by linarith [hx.1],by linarith [hx.2]⟩
      (y-T) ⟨by linarith [hy.1],by linarith [hy.2]⟩
    have hfx : f (x-T)=f x := by simpa using (hper (x-T)).symm
    have hfy : f (y-T)=f y := by simpa using (hper (y-T)).symm
    simpa only [hfx,hfy,dist_sub_right] using hh
  have h2 := lipschitzOn_Icc_join f 0 T (2*T) hT.le (by linarith) K hK hshift
  have hrepr (x : ℝ) : ∃ x' ∈ Ico (0:ℝ) T, ∃ k : ℤ, x=x'+k•T := by
    obtain ⟨hx,k,hk⟩ := (toIcoMod_eq_iff hT).mp (rfl : toIcoMod hT 0 x=toIcoMod hT 0 x)
    exact ⟨_,by simpa using hx,k,hk⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  wlog hxy : x≤y generalizing x y
  · simpa only [dist_comm (f y) (f x),dist_comm y x] using this y x (le_of_not_ge hxy)
  obtain ⟨x',hx',k,hx⟩ := hrepr x
  have hfx : f x=f x' := by rw [hx]; exact hper.zsmul k x'
  by_cases hnear : y-x≤T
  · let y' := x'+(y-x)
    have hy' : y' ∈ Icc (0:ℝ) (2*T) := ⟨by dsimp [y']; linarith [hx'.1],by dsimp [y']; linarith [hx'.2]⟩
    have hfy : f y=f y' := by
      have he : y=y'+k•T := by dsimp [y']; linarith [hx]
      rw [he]; exact hper.zsmul k y'
    have hd : dist x' y'=dist x y := by
      rw [Real.dist_eq,Real.dist_eq]
      congr 1
      dsimp [y']
      ring
    simpa only [hfx,hfy,hd] using h2.dist_le_mul x' ⟨hx'.1,by linarith [hx'.2]⟩ y' hy'
  · obtain ⟨y',hy',l,hy⟩ := hrepr y
    have hfy : f y=f y' := by rw [hy]; exact hper.zsmul l y'
    have hd : dist x' y'≤T := by
      rw [Real.dist_eq,abs_le]
      constructor <;> linarith [hx'.1,hx'.2,hy'.1,hy'.2]
    calc dist (f x) (f y)
      _ = dist (f x') (f y') := by rw [hfx,hfy]
      _ ≤ K*dist x' y' := hK.dist_le_mul x' ⟨hx'.1,hx'.2.le⟩ y' ⟨hy'.1,hy'.2.le⟩
      _ ≤ K*T := mul_le_mul_of_nonneg_left hd K.2
      _ ≤ K*dist x y := by
        apply mul_le_mul_of_nonneg_left _ K.2
        rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy)]
        linarith
end VM03CapV437RawRegular
namespace VM03CapV437RawRegular
private theorem fin_partition_lipschitz {Y : Type*} [PseudoMetricSpace Y]
    (f : ℝ → Y) (m : ℕ) (r : Fin (m+1) → ℝ) (hr : Monotone r)
    (hpieces : ∀ i : Fin m, ∃ K : NNReal,
      LipschitzOnWith K f (Icc (r i.castSucc) (r i.succ))) :
    ∃ K : NNReal, LipschitzOnWith K f (Icc (r 0) (r (Fin.last m))) := by
  let r' : ℕ → ℝ := fun n => r ⟨min n m,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  have hr' : Monotone r' := by
    intro i j hij
    apply hr
    exact min_le_min_right m hij
  have hpiece (i : Fin m) : ∃ K : NNReal,
      LipschitzOnWith K f (Icc (r' i) (r' (i.1+1))) := by
    have h0 : r' i=r i.castSucc := congrArg r (Fin.ext (Nat.min_eq_left i.2.le))
    have h1 : r' (i.1+1)=r i.succ :=
      congrArg r (Fin.ext (Nat.min_eq_left (Nat.succ_le_of_lt i.2)))
    rw [h0,h1]
    exact hpieces i
  obtain ⟨K,hK⟩ := finite_partition_lipschitz f r' hr' m hpiece
  have h0 : r' 0=r 0 := congrArg r (Fin.ext (Nat.zero_min _))
  have h1 : r' m=r (Fin.last m) := congrArg r (Fin.ext (Nat.min_self _))
  exact ⟨K,by rwa [h0,h1] at hK⟩
end VM03CapV437RawRegular
noncomputable section
open Set Function Filter Metric
open scoped Topology ContDiff
open SeifertSurfaces.AppendixACoordinates
namespace VM03CapV437RawRegular
private theorem angular_lipschitz_compact {Y : Type*} [PseudoMetricSpace Y]
    (γ : ℝ → Y) (hper : Periodic γ (2*Real.pi)) (K : NNReal)
    (hγ : LipschitzWith K γ) (S : Set E2) (hS : IsCompact S) (hS0 : 0 ∉ S) :
    ∃ L : NNReal, LipschitzOnWith L
      (fun x : E2 => γ (Complex.arg ⟨x 0,x 1⟩)) S := by
  let e : E2 ≃L[ℝ] ℂ :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).trans Complex.equivRealProdCLM.symm
  have he (x : E2) : e x=(⟨x 0,x 1⟩ : ℂ) := by
    apply Complex.ext <;> simp [e]
  have hmod (a d : ℝ) (heq : (a : Real.Angle)=(d : Real.Angle)) : γ a=γ d := by
    obtain ⟨k,hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp heq
    have hp := hper.zsmul k d
    rw [zsmul_eq_mul] at hp
    have ha : a=d+(k:ℝ)*(2*Real.pi) := by nlinarith [hk]
    rw [ha]
    exact hp
  have hneg (z : ℂ) (hz : z≠0) : γ (Complex.arg (-z)+Real.pi)=γ (Complex.arg z) := by
    apply hmod
    rw [Real.Angle.coe_add,Complex.arg_neg_coe_angle hz,add_assoc,
      ← Real.Angle.coe_add,← two_mul,Real.Angle.coe_two_pi,add_zero]
  have harg (z : ℂ) (hz : z∈Complex.slitPlane) : ContDiffAt ℝ 1 Complex.arg z := by
    have hl : ContDiffAt ℝ ∞ Complex.log z := (Complex.contDiffAt_log hz).restrict_scalars ℝ
    have hi : ContDiffAt ℝ ∞ (fun z : ℂ => (Complex.log z).im) z :=
      Complex.imCLM.contDiff.contDiffAt.comp z hl
    have hfull : ContDiffAt ℝ ∞ Complex.arg z := by simpa only [Complex.log_im] using hi
    exact hfull.of_le (by simp)
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS
  intro x hx
  have hx0 : x≠0 := fun hh => hS0 (hh ▸ hx)
  have he0 : e x≠0 := fun hh => hx0 (e.injective (by simpa using hh))
  obtain ⟨θ,hθ,heq⟩ : ∃ θ : E2 → ℝ, ContDiffAt ℝ 1 θ x ∧
      ∀ᶠ y in 𝓝 x, γ (Complex.arg (e y))=γ (θ y) := by
    by_cases hs : e x∈Complex.slitPlane
    · exact ⟨fun y => Complex.arg (e y),
        (harg (e x) hs).comp x e.contDiff.contDiffAt,Filter.Eventually.of_forall fun _ => rfl⟩
    · have hns : -e x∈Complex.slitPlane := by
        change 0<(-e x).re ∨ (-e x).im≠0
        change ¬(0<(e x).re ∨ (e x).im≠0) at hs
        push_neg at hs
        have hn : (e x).re≠0 := fun hh => he0 (Complex.ext hh hs.2)
        exact Or.inl (by simpa using neg_pos.mpr (lt_of_le_of_ne hs.1 hn))
      refine ⟨fun y => Complex.arg (-e y)+Real.pi,
        ((harg (-e x) hns).comp x e.contDiff.contDiffAt.neg).add contDiffAt_const,?_⟩
      filter_upwards [isOpen_compl_singleton.mem_nhds hx0] with y hy
      exact (hneg (e y) (fun hh => hy (e.injective (by simpa using hh)))).symm
  obtain ⟨L,U,hU,hL⟩ := hθ.exists_lipschitzOnWith
  let V := U ∩ {y | γ (Complex.arg (e y))=γ (θ y)}
  refine ⟨K*L,V,mem_nhdsWithin_of_mem_nhds (inter_mem hU heq),?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  rw [← he y,← he z,hy.2,hz.2]
  exact (hγ.comp_lipschitzOnWith hL).dist_le_mul y hy.1 z hz.1
end VM03CapV437RawRegular
noncomputable section
open Set Function Metric
open SeifertSurfaces.AppendixACoordinates
namespace VM03CapV437RawRegular
private theorem normalized_dist_mul_le (x y : E2) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x‖*dist (‖x‖⁻¹ • x) (‖y‖⁻¹ • y) ≤ 2*dist x y := by
  let u := ‖x‖⁻¹ • x
  let v := ‖y‖⁻¹ • y
  have hv : ‖v‖=1 := by simp [v,norm_smul,hy]
  have hxu : ‖x‖ • u=x := by simp [u,smul_smul,hx]
  have hyv : ‖y‖ • v=y := by simp [v,smul_smul,hy]
  have hdist : dist y (‖x‖ • v)=|‖y‖-‖x‖| := by
    nth_rw 1 [← hyv]
    rw [dist_eq_norm,← sub_smul,norm_smul,Real.norm_eq_abs,hv,mul_one]
  calc ‖x‖*dist u v = dist (‖x‖ • u) (‖x‖ • v) := by
         simp only [dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg x)]
       _ ≤ dist x y+dist y (‖x‖ • v) := by rw [hxu]; exact dist_triangle _ _ _
       _ ≤ 2*dist x y := by
         rw [hdist]
         have hh := abs_norm_sub_norm_le y x
         rw [← dist_eq_norm,dist_comm] at hh
         linarith

private theorem radial_extension_lipschitz (β : E2 → E2) (K B : NNReal)
    (hβ : LipschitzOnWith K β (sphere 0 1))
    (hB : ∀ x ∈ sphere 0 1, ‖β x‖ ≤ B) :
    LipschitzWith (2*K+B) (fun x : E2 => ‖x‖ • β (‖x‖⁻¹ • x)) := by
  let C : E2 → E2 := fun x => ‖x‖ • β (‖x‖⁻¹ • x)
  have hn (x : E2) (hx : x ≠ 0) : ‖x‖⁻¹ • x ∈ sphere 0 1 := by simp [norm_smul,hx]
  have hC0 : C 0=0 := by simp [C]
  have hbound (x : E2) : ‖C x‖ ≤ (B:ℝ)*‖x‖ := by
    by_cases hx : x=0
    · simp [hx,hC0]
    · rw [show C x=‖x‖ • β (‖x‖⁻¹ • x) from rfl,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg x),mul_comm]
      exact mul_le_mul_of_nonneg_right (hB _ (hn x hx)) (norm_nonneg x)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (C x) (C y) ≤ ((2*K+B:NNReal):ℝ)*dist x y
  have hBK : (B:ℝ) ≤ ((2*K+B:NNReal):ℝ) := by
    simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat]
    exact le_add_of_nonneg_left (mul_nonneg (by norm_num) K.coe_nonneg)
  by_cases hx : x=0
  · subst x
    simpa only [hC0,dist_zero_left] using (hbound y).trans
      (mul_le_mul_of_nonneg_right hBK (norm_nonneg y))
  by_cases hy : y=0
  · subst y
    simpa only [hC0,dist_zero_right] using (hbound x).trans
      (mul_le_mul_of_nonneg_right hBK (norm_nonneg x))
  let u := ‖x‖⁻¹ • x
  let v := ‖y‖⁻¹ • y
  have hfirst : dist (C x) (‖x‖ • β v) ≤ (K:ℝ)*(2*dist x y) := by
    change dist (‖x‖ • β u) (‖x‖ • β v) ≤ _
    rw [dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg x),← dist_eq_norm]
    calc ‖x‖*dist (β u) (β v) ≤ ‖x‖*((K:ℝ)*dist u v) :=
           mul_le_mul_of_nonneg_left (hβ.dist_le_mul u (hn x hx) v (hn y hy)) (norm_nonneg x)
         _ = (K:ℝ)*(‖x‖*dist u v) := by ring
         _ ≤ (K:ℝ)*(2*dist x y) := mul_le_mul_of_nonneg_left (normalized_dist_mul_le x y hx hy) K.coe_nonneg
  have hsecond : dist (‖x‖ • β v) (C y) ≤ (B:ℝ)*dist x y := by
    change dist (‖x‖ • β v) (‖y‖ • β v) ≤ _
    rw [dist_eq_norm,← sub_smul,norm_smul,Real.norm_eq_abs]
    have hnorm := abs_norm_sub_norm_le x y
    rw [← dist_eq_norm] at hnorm
    calc |‖x‖-‖y‖| * ‖β v‖ ≤ dist x y*(B:ℝ) :=
           mul_le_mul hnorm (hB v (hn y hy)) (norm_nonneg _) (dist_nonneg)
         _ = (B:ℝ)*dist x y := by ring
  have hh := (dist_triangle (C x) (‖x‖ • β v) (C y)).trans (add_le_add hfirst hsecond)
  simpa only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat] using
    (show dist (C x) (C y) ≤ (2*(K:ℝ)+(B:ℝ))*dist x y by nlinarith [hh])
end VM03CapV437RawRegular
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
namespace VM03CapV437RawRegular
private theorem smooth_pl_trace_on_finite_chords
    (V : E2 → E2) (D : Set E2) (hV : IsPiecewiseAffineOn V D)
    (γ : ℝ → E2) (ρ : ℝ → ℝ) (N : ℕ) (hN : 0 < N)
    (t : Fin (N+1) → ℝ) (ht : StrictMono t) (h0 : t 0=0) (hT : t (Fin.last N)=2*Real.pi)
    (hpieces : ∀ i : Fin N,
      ContDiffOn ℝ ∞ ρ (Icc (t i.castSucc) (t i.succ)) ∧
      ∃ (p q : E2) (τ : ℝ → ℝ), segment ℝ p q ⊆ D ∧
        ContDiffOn ℝ ∞ τ (Icc (t i.castSucc) (t i.succ)) ∧
        StrictMonoOn τ (Icc (t i.castSucc) (t i.succ)) ∧
        τ '' Icc (t i.castSucc) (t i.succ)=Icc (0:ℝ) 1 ∧
        τ (t i.castSucc)=0 ∧ τ (t i.succ)=1 ∧
        ∀ z∈Icc (t i.castSucc) (t i.succ), γ z=AffineMap.lineMap p q (τ z)) :
    ∃ (m : ℕ) (_ : 0 < m) (r : Fin (m+1) → ℝ), StrictMono r ∧ r 0=0 ∧
      r (Fin.last m)=2*Real.pi ∧ ∀ i : Fin m,
        ContDiffOn ℝ ∞ (V ∘ γ) (Icc (r i.castSucc) (r i.succ)) ∧
        ContDiffOn ℝ ∞ ρ (Icc (r i.castSucc) (r i.succ)) := by
  classical
  have hlocal (i : Fin N) :
      ∃ (m : ℕ) (_ : 0 < m) (r : Fin (m+1) → ℝ), StrictMono r ∧ r 0=t i.castSucc ∧
        r (Fin.last m)=t i.succ ∧ ∀ j : Fin m,
          ContDiffOn ℝ ∞ (V ∘ γ) (Icc (r j.castSucc) (r j.succ)) ∧
          ContDiffOn ℝ ∞ ρ (Icc (r j.castSucc) (r j.succ)) := by
    obtain ⟨hρ,p,q,τ,hpq,hτ,hm,himage,ha,hb,htrace⟩ := hpieces i
    obtain ⟨m,hm0,r,hr,hr0,hrm,hparts⟩ := pl_trace_partition V D hV γ p q hpq τ
      (t i.castSucc) (t i.succ) (ht (by exact_mod_cast Nat.lt_succ_self i.1))
      hτ hm himage ha hb htrace
    refine ⟨m,hm0,r,hr,hr0,hrm,?_⟩
    intro j
    refine ⟨hparts j,hρ.mono ?_⟩
    intro z hz
    have hl : t i.castSucc ≤ r j.castSucc := by rw [← hr0]; exact hr.monotone (Fin.zero_le _)
    have hu : r j.succ ≤ t i.succ := by rw [← hrm]; exact hr.monotone (Fin.le_last _)
    exact ⟨hl.trans hz.1,hz.2.trans hu⟩
  choose m hm r hr hr0 hrm hparts using hlocal
  let ι := Σ i : Fin N, Fin (m i)
  let l : ι → ℝ := fun j => r j.1 j.2.castSucc
  let u : ι → ℝ := fun j => r j.1 j.2.succ
  have hbound (j : ι) : 0 ≤ l j ∧ l j ≤ u j ∧ u j ≤ 2*Real.pi := by
    have hlow : 0 ≤ t j.1.castSucc := by rw [← h0]; exact ht.monotone (Fin.zero_le _)
    have hupp : t j.1.succ ≤ 2*Real.pi := by rw [← hT]; exact ht.monotone (Fin.le_last _)
    have hlow' : t j.1.castSucc ≤ l j := by
      dsimp [l]; rw [← hr0]; exact (hr j.1).monotone (Fin.zero_le _)
    have hupp' : u j ≤ t j.1.succ := by
      dsimp [u]; rw [← hrm]; exact (hr j.1).monotone (Fin.le_last _)
    exact ⟨hlow.trans hlow',(hr j.1).monotone (by exact_mod_cast Nat.le_succ j.2.1),hupp'.trans hupp⟩
  have hcover : ∀ x∈Icc (0:ℝ) (2*Real.pi), ∃ j : ι, x∈Icc (l j) (u j) := by
    intro x hx
    have hx' : x∈Icc (t 0) (t (Fin.last N)) := by rwa [h0,hT]
    obtain ⟨i,hi⟩ := fin_partition_cover N hN t ht.monotone x hx'
    have hi' : x∈Icc (r i 0) (r i (Fin.last (m i))) := by rwa [hr0,hrm]
    obtain ⟨j,hj⟩ := fin_partition_cover (m i) (hm i) (r i) (hr i).monotone x hi'
    exact ⟨⟨i,j⟩,hj⟩
  obtain ⟨M,hM,s,hs,hs0,hsT,hsub⟩ := interval_cover_partition 0 (2*Real.pi)
    (by positivity) l u hbound hcover
  refine ⟨M,hM,s,hs,hs0,hsT,?_⟩
  intro i
  obtain ⟨j,hj⟩ := hsub i
  exact ⟨((hparts j.1 j.2).1).mono hj,((hparts j.1 j.2).2).mono hj⟩

private theorem periodic_smooth_pieces_lipschitz {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (γ : ℝ → Y) (hper : Periodic γ (2*Real.pi)) (m : ℕ)
    (r : Fin (m+1) → ℝ) (hr : StrictMono r) (h0 : r 0=0) (hT : r (Fin.last m)=2*Real.pi)
    (hs : ∀ i : Fin m, ContDiffOn ℝ ∞ γ (Icc (r i.castSucc) (r i.succ))) :
    ∃ K : NNReal, LipschitzWith K γ := by
  obtain ⟨K,hK⟩ := fin_partition_lipschitz γ m r hr.monotone
    (fun i => (hs i).exists_lipschitzOnWith (by simp) (convex_Icc _ _) isCompact_Icc)
  rw [h0,hT] at hK
  exact ⟨K,periodic_lipschitz γ (2*Real.pi) (by positivity) hper K hK⟩
end VM03CapV437RawRegular
namespace VM03CapV437RawRegular
private theorem sphere_lipschitz_of_periodic_trace {Y : Type*} [PseudoMetricSpace Y]
    (B : E2 → Y) (γ : ℝ → Y)
    (hper : Periodic γ (2*Real.pi)) (K : NNReal) (hγ : LipschitzWith K γ)
    (htrace : ∀ t, B (unitCircleParameter t)=γ t) :
    ∃ L : NNReal, LipschitzOnWith L B (sphere 0 1) := by
  have harg (x : E2) (hx : x∈sphere 0 1) : unitCircleParameter (Complex.arg ⟨x 0,x 1⟩)=x := by
    let z : ℂ := ⟨x 0,x 1⟩
    have hnx : ‖x‖=1 := mem_sphere_zero_iff_norm.mp hx
    have hnz : ‖z‖=1 := by
      have hn : ‖z‖^2=‖x‖^2 := by
        rw [Complex.sq_norm,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
        simp [Complex.normSq_apply,z,pow_two]
      rw [hnx] at hn
      nlinarith [norm_nonneg z]
    have hz : z≠0 := by intro he; simp [he] at hnz
    ext i
    fin_cases i
    · change Real.cos z.arg=x 0
      rw [Complex.cos_arg hz,hnz,div_one]
    · change Real.sin z.arg=x 1
      rw [Complex.sin_arg,hnz,div_one]
  obtain ⟨L,hL⟩ := angular_lipschitz_compact γ hper K hγ (sphere 0 1)
    (isCompact_sphere _ _) (by simp)
  refine ⟨L,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have he (z : E2) (hz : z∈sphere 0 1) : B z=γ (Complex.arg ⟨z 0,z 1⟩) := by
    rw [← htrace, harg z hz]
  simpa only [he x hx,he y hy] using hL.dist_le_mul x hx y hy

private theorem radial_extension_lipschitz_of_periodic_smooth_pieces
    (B : E2 → E2) (γ : ℝ → E2) (hper : Periodic γ (2*Real.pi))
    (htrace : ∀ t, B (unitCircleParameter t)=γ t)
    (m : ℕ) (r : Fin (m+1) → ℝ) (hr : StrictMono r)
    (h0 : r 0=0) (hT : r (Fin.last m)=2*Real.pi)
    (hs : ∀ i : Fin m, ContDiffOn ℝ ∞ γ (Icc (r i.castSucc) (r i.succ))) :
    ∃ L : NNReal, LipschitzWith L (fun x : E2 => ‖x‖ • B (‖x‖⁻¹ • x)) := by
  obtain ⟨K,hK⟩ := periodic_smooth_pieces_lipschitz γ hper m r hr h0 hT hs
  obtain ⟨L,hL⟩ := sphere_lipschitz_of_periodic_trace B γ hper K hK htrace
  obtain ⟨C,hC⟩ := (isCompact_sphere (0:E2) 1).exists_bound_of_continuousOn hL.continuousOn
  let C' : NNReal := ⟨max C 0,le_max_right _ _⟩
  have hC' : ∀ x∈sphere (0:E2) 1, ‖B x‖ ≤ C' := fun x hx => (hC x hx).trans (le_max_left _ _)
  exact ⟨2*L+C',radial_extension_lipschitz B L C' hL hC'⟩
end VM03CapV437RawRegular
namespace VM03CapV437RawRegular
private theorem actual_boundary_regular_grid
    (w : E2 → E2) (r : ℝ) (ρ : ℝ → ℝ) (N : ℕ) (hN : 3 ≤ N)
    (B : E2 → E2) (hB : InjOn B (sphere 0 1))
    (hBu : ∀ t, B (unitCircleParameter t)=w (ρ t • unitCircleParameter t))
    (hpieces : ∀ i : Fin N, let a := (i:ℝ)*(2*Real.pi/N); let b := ((i.1+1:ℕ):ℝ)*(2*Real.pi/N)
      ContDiffOn ℝ ∞ ρ (Icc a b) ∧
      ∃ τ : ℝ → ℝ, ContDiffOn ℝ ∞ τ (Icc a b) ∧
        τ '' Icc a b=Icc (0:ℝ) 1 ∧ τ a=0 ∧ τ b=1 ∧
        ∀ z∈Icc a b, w (ρ z • unitCircleParameter z)=
          AffineMap.lineMap (w (r • unitCircleParameter a)) (w (r • unitCircleParameter b)) (τ z))
    (V : E2 → E2) (D : Set E2) (hV : IsPiecewiseAffineOn V D)
    (hγD : range (fun t => w (ρ t • unitCircleParameter t)) ⊆ D) :
    ∃ (m : ℕ) (_ : 0 < m) (s : Fin (m+1) → ℝ), StrictMono s ∧ s 0=0 ∧
      s (Fin.last m)=2*Real.pi ∧
      (∀ i : Fin m,
        ContDiffOn ℝ ∞ (fun t => V (w (ρ t • unitCircleParameter t)))
          (Icc (s i.castSucc) (s i.succ)) ∧
        ContDiffOn ℝ ∞ ρ (Icc (s i.castSucc) (s i.succ))) ∧
      ∃ L : NNReal, LipschitzWith L (fun x : E2 => ‖x‖ • V (B (‖x‖⁻¹ • x))) := by
  have hNR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  let h := 2*Real.pi/N
  have hh : 0<h := div_pos (by positivity) hNR
  have hshort : h<2*Real.pi := by
    apply (div_lt_iff₀ hNR).mpr
    nlinarith [Real.pi_pos,show (3:ℝ) ≤ N by exact_mod_cast hN]
  let t : Fin (N+1) → ℝ := fun i => (i:ℝ)*h
  have ht : StrictMono t := by
    intro i j hij
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) hh
  have ht0 : t 0=0 := by simp [t]
  have htT : t (Fin.last N)=2*Real.pi := by dsimp [t,h]; field_simp
  let γ : ℝ → E2 := fun t => w (ρ t • unitCircleParameter t)
  have hγper : Periodic γ (2*Real.pi) := by
    intro z
    change w (ρ (z+2*Real.pi) • unitCircleParameter (z+2*Real.pi))=w (ρ z • unitCircleParameter z)
    rw [← hBu,← hBu]
    congr 1
    ext i
    fin_cases i <;> simp [unitCircleParameter,Real.cos_add,Real.sin_add]
  have hdata (i : Fin N) :
      ContDiffOn ℝ ∞ ρ (Icc (t i.castSucc) (t i.succ)) ∧
      ∃ (p q : E2) (τ : ℝ → ℝ), segment ℝ p q ⊆ D ∧
        ContDiffOn ℝ ∞ τ (Icc (t i.castSucc) (t i.succ)) ∧
        StrictMonoOn τ (Icc (t i.castSucc) (t i.succ)) ∧
        τ '' Icc (t i.castSucc) (t i.succ)=Icc (0:ℝ) 1 ∧
        τ (t i.castSucc)=0 ∧ τ (t i.succ)=1 ∧
        ∀ z∈Icc (t i.castSucc) (t i.succ), γ z=AffineMap.lineMap p q (τ z) := by
    obtain ⟨hρ,τ,hτ,him,ha,hb,he⟩ := hpieces i
    have he' : ∀ z∈Icc (t i.castSucc) (t i.succ), B (unitCircleParameter z)=
        AffineMap.lineMap (w (r • unitCircleParameter (t i.castSucc)))
          (w (r • unitCircleParameter (t i.succ))) (τ z) := by
      intro z hz
      rw [hBu]
      exact he z hz
    have hab : t i.castSucc<t i.succ := ht (by exact_mod_cast Nat.lt_succ_self i.1)
    have hwidth : t i.succ-t i.castSucc<2*Real.pi := by
      change ((i.1+1:ℕ):ℝ)*h-(i.1:ℝ)*h<2*Real.pi
      push_cast
      nlinarith [hshort]
    have hm := chord_parameter_strictMono B hB (t i.castSucc) (t i.succ) hab.le hwidth
      (w (r • unitCircleParameter (t i.castSucc))) (w (r • unitCircleParameter (t i.succ)))
      τ hτ.continuousOn ha hb he'
    refine ⟨hρ,_,_,τ,?_,hτ,hm,him,ha,hb,he⟩
    intro y hy
    rw [segment_eq_image_lineMap] at hy
    obtain ⟨z,hz,rfl⟩ := hy
    obtain ⟨u,hu,heu⟩ : z∈τ '' Icc (t i.castSucc) (t i.succ) := him.symm ▸ hz
    apply hγD
    exact ⟨u,(he u hu).trans (congrArg _ heu)⟩
  obtain ⟨m,hm,s,hs,hs0,hsT,hgrid⟩ := smooth_pl_trace_on_finite_chords V D hV γ ρ N
    (by omega) t ht ht0 htT hdata
  refine ⟨m,hm,s,hs,hs0,hsT,hgrid,?_⟩
  exact radial_extension_lipschitz_of_periodic_smooth_pieces (V ∘ B) (V ∘ γ)
    (hγper.comp V) (fun z => congrArg V (hBu z)) m s hs hs0 hsT (fun i => (hgrid i).1)
end VM03CapV437RawRegular
namespace VM03CapV437RawRegular
private theorem finite_partition_refine_avoiding
    (m : ℕ) (hm : 0 < m) (r : Fin (m+1) → ℝ) (hr : StrictMono r)
    (a b : ℝ) (hab : a<b) (hr0 : r 0=a) (hrm : r (Fin.last m)=b)
    (Δ : Finset ℝ) (hΔ : (Δ:Set ℝ) ⊆ Icc a b) :
    ∃ (n : ℕ) (_ : 0 < n) (s : Fin (n+1) → ℝ), StrictMono s ∧ s 0=a ∧
      s (Fin.last n)=b ∧ ∀ i : Fin n,
        (∃ j : Fin m, Icc (s i.castSucc) (s i.succ) ⊆ Icc (r j.castSucc) (r j.succ)) ∧
        Disjoint (Ioo (s i.castSucc) (s i.succ)) (Δ:Set ℝ) := by
  classical
  let S := Finset.univ.image r ∪ Δ
  have hri (i : Fin (m+1)) : r i∈S := by simp [S]
  have hS : (S:Set ℝ) ⊆ Icc a b := by
    intro x hx
    simp only [S,Finset.mem_coe,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and] at hx
    rcases hx with ⟨i,rfl⟩|hx
    · exact ⟨by rw [← hr0]; exact hr.monotone (Fin.zero_le _),
        by rw [← hrm]; exact hr.monotone (Fin.le_last _)⟩
    · exact hΔ hx
  obtain ⟨n,hn,s,hs,hs0,hsn,hsrange,hgap⟩ := finite_knots_order S a b hab
    (hr0 ▸ hri 0) (hrm ▸ hri (Fin.last m)) hS
  refine ⟨n,hn,s,hs,hs0,hsn,?_⟩
  intro i
  have hi : s i.castSucc<s i.succ := hs (by exact_mod_cast Nat.lt_succ_self i.1)
  have hlo : a ≤ s i.castSucc := by rw [← hs0]; exact hs.monotone (Fin.zero_le _)
  have hhi : s i.succ ≤ b := by rw [← hsn]; exact hs.monotone (Fin.le_last _)
  let x := (s i.castSucc+s i.succ)/2
  have hx : x∈Icc (r 0) (r (Fin.last m)) := by
    rw [hr0,hrm]
    exact ⟨by dsimp [x]; linarith,by dsimp [x]; linarith⟩
  obtain ⟨j,hj⟩ := fin_partition_cover m hm r hr.monotone x hx
  have hleft : r j.castSucc ≤ s i.castSucc := by
    by_contra hh
    exact hgap i _ (hri _) ⟨lt_of_not_ge hh,by dsimp [x] at hj; linarith [hj.1]⟩
  have hright : s i.succ ≤ r j.succ := by
    by_contra hh
    exact hgap i _ (hri _) ⟨by dsimp [x] at hj; linarith [hj.2],lt_of_not_ge hh⟩
  refine ⟨⟨j,fun _ hz => ⟨hleft.trans hz.1,hz.2.trans hright⟩⟩,Set.disjoint_left.mpr ?_⟩
  intro z hz hzΔ
  exact hgap i z (Finset.mem_union_right _ hzΔ) hz

private theorem finite_bad_angles
    (B : E2 → E2) (hB : InjOn B (sphere 0 1)) (S : Finset E2) :
    ∃ Δ : Finset ℝ, (Δ:Set ℝ) ⊆ Icc (0:ℝ) (2*Real.pi) ∧
      ∀ t∈Icc (0:ℝ) (2*Real.pi), B (unitCircleParameter t)∈(S:Set E2) ↔ t∈Δ := by
  classical
  let γ := fun t => B (unitCircleParameter t)
  have hγ : InjOn γ (Ico (0:ℝ) (2*Real.pi)) := by
    intro x hx y hy he
    have hu := hB (mem_sphere_zero_iff_norm.mpr (circle_norm x))
      (mem_sphere_zero_iff_norm.mpr (circle_norm y)) he
    have hcos : Real.cos x=Real.cos y := congrArg (fun z : E2 => z 0) hu
    have hsin : Real.sin x=Real.sin y := congrArg (fun z : E2 => z 1) hu
    letI : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0:ℝ)) (by simpa using hx) (by simpa using hy)).mp
      (Real.Angle.cos_sin_inj hcos hsin)
  let D := {t | t∈Icc (0:ℝ) (2*Real.pi) ∧ γ t∈(S:Set E2)}
  have hfin0 : (Ico (0:ℝ) (2*Real.pi) ∩ γ ⁻¹' (S:Set E2)).Finite :=
    S.finite_toSet.of_injOn (f := γ) (fun _ hx => hx.2) (hγ.mono inter_subset_left)
  have hfin : D.Finite := (hfin0.union (finite_singleton (2*Real.pi))).subset (by
    intro t ht
    by_cases he : t=2*Real.pi
    · exact Or.inr he
    · exact Or.inl ⟨⟨ht.1.1,lt_of_le_of_ne ht.1.2 he⟩,ht.2⟩)
  refine ⟨hfin.toFinset,?_,?_⟩
  · intro t ht
    exact (hfin.mem_toFinset.mp ht).1
  · intro t ht
    rw [hfin.mem_toFinset]
    exact ⟨fun h => ⟨ht,h⟩,fun h => h.2⟩
end VM03CapV437RawRegular
namespace VM03CapV437RawRegular
private theorem regular_grid_avoid_boundary_vertices
    (B : E2 → E2) (hB : InjOn B (sphere 0 1))
    (γ : ℝ → E2) (ρ : ℝ → ℝ) (htrace : ∀ t,B (unitCircleParameter t)=γ t)
    (m : ℕ) (hm : 0 < m) (r : Fin (m+1) → ℝ) (hr : StrictMono r)
    (hr0 : r 0=0) (hrm : r (Fin.last m)=2*Real.pi)
    (hpieces : ∀ i : Fin m,
      ContDiffOn ℝ ∞ γ (Icc (r i.castSucc) (r i.succ)) ∧
      ContDiffOn ℝ ∞ ρ (Icc (r i.castSucc) (r i.succ))) (S : Finset E2) :
    ∃ (n : ℕ) (_ : 0 < n) (s : Fin (n+1) → ℝ), StrictMono s ∧ s 0=0 ∧
      s (Fin.last n)=2*Real.pi ∧ ∀ i : Fin n,
        ContDiffOn ℝ ∞ γ (Icc (s i.castSucc) (s i.succ)) ∧
        ContDiffOn ℝ ∞ ρ (Icc (s i.castSucc) (s i.succ)) ∧
        ∀ t∈Ioo (s i.castSucc) (s i.succ),γ t∉(S:Set E2) := by
  obtain ⟨Δ,hΔ,hbad⟩ := finite_bad_angles B hB S
  obtain ⟨n,hn,s,hs,hs0,hsn,hsub⟩ := finite_partition_refine_avoiding m hm r hr
    0 (2*Real.pi) (by positivity) hr0 hrm Δ hΔ
  refine ⟨n,hn,s,hs,hs0,hsn,?_⟩
  intro i
  obtain ⟨⟨j,hj⟩,hdis⟩ := hsub i
  refine ⟨(hpieces j).1.mono hj,(hpieces j).2.mono hj,?_⟩
  intro t ht hS
  have ht0 : 0 ≤ t := by
    have hh : s 0 ≤ s i.castSucc := hs.monotone (Fin.zero_le _)
    rw [hs0] at hh
    exact hh.trans ht.1.le
  have htT : t ≤ 2*Real.pi := by
    have hh : s i.succ ≤ s (Fin.last n) := hs.monotone (Fin.le_last _)
    rw [hsn] at hh
    exact ht.2.le.trans hh
  have htΔ : t∈Δ := (hbad t ⟨ht0,htT⟩).mp (by rwa [htrace])
  exact Set.disjoint_left.mp hdis ht htΔ
end VM03CapV437RawRegular
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
namespace VM03CapV437RawFormula

private theorem angular_profile (ρ : ℝ → ℝ) (hρ : Continuous ρ)
    (hper : Periodic ρ (2*Real.pi)) :
    ∃ A : E2 → ℝ,
      (∀ x, x ≠ 0 → ContinuousAt A x) ∧
      (∀ x (r : ℝ), 0 < r → A (r • x)=A x) ∧
      (∀ t, A (unitCircleParameter t)=ρ t) ∧
      ∀ x, ∃ t, A x=ρ t := by
  let e : E2 → ℂ := fun x => ⟨x 0,x 1⟩
  have hec : Continuous e := by
    exact Complex.equivRealProdCLM.symm.continuous.comp
      ((EuclideanSpace.proj (𝕜:=ℝ) 0).continuous.prodMk (EuclideanSpace.proj (𝕜:=ℝ) 1).continuous)
  have he0 (x : E2) (hx : x ≠ 0) : e x ≠ 0 := by
    intro he
    apply hx
    ext i
    fin_cases i
    · exact congrArg Complex.re he
    · exact congrArg Complex.im he
  let f : AddCircle (2*Real.pi) → ℝ := hper.lift
  have hfc : Continuous f := continuous_coinduced_dom.mpr hρ
  have hf (t : ℝ) : f (t : AddCircle (2*Real.pi))=ρ t := rfl
  let A : E2 → ℝ := fun x => f (Complex.arg (e x) : Real.Angle)
  refine ⟨A,?_,?_,?_,?_⟩
  · intro x hx
    exact hfc.continuousAt.comp ((Complex.continuousAt_arg_coe_angle (he0 x hx)).comp hec.continuousAt)
  · intro x r hr
    have he : e (r • x)=(r:ℂ)*e x := by
      apply Complex.ext <;> simp [e,PiLp.smul_apply,smul_eq_mul]
    dsimp only [A]
    rw [he,Complex.arg_real_mul _ hr]
  · intro t
    have he : e (unitCircleParameter t)=(Real.cos t:ℂ)+(Real.sin t:ℂ)*Complex.I := by
      apply Complex.ext <;> simp only [e,unitCircleParameter,Complex.add_re,Complex.add_im,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,zero_add,add_zero]
      all_goals rfl
    dsimp only [A]
    rw [he]
    have ha := Complex.arg_cos_add_sin_mul_I_coe_angle (t : Real.Angle)
    rw [show (Complex.arg ((Real.cos t:ℂ)+(Real.sin t:ℂ)*Complex.I) : Real.Angle)=(t:Real.Angle) by simpa using ha]
    exact hf t
  · intro x
    exact ⟨Complex.arg (e x),hf _⟩

private theorem radial_segment (a b p : ℝ) (hab : a < b) (hp : p < b) :
    let f : ℝ → ℝ := fun r => p+(r-a)*(b-p)/(b-a)
    StrictMono f ∧ f a=p ∧ f b=b ∧ f '' Icc a b=Icc p b := by
  dsimp only
  let f : ℝ → ℝ := fun r => p+(r-a)*(b-p)/(b-a)
  have hm : StrictMono f := by
    intro x y hxy
    apply add_lt_add_right
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (sub_lt_sub_right hxy a)
      (sub_pos.mpr hp)) (sub_pos.mpr hab)
  have ha : f a=p := by simp [f]
  have hb : f b=b := by dsimp [f]; field_simp [(sub_pos.mpr hab).ne']; ring
  refine ⟨hm,ha,hb,?_⟩
  have hc : Continuous f := by dsimp [f]; fun_prop
  apply Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨by simpa only [ha] using hm.monotone hx.1,by simpa only [hb] using hm.monotone hx.2⟩
  · have hh := intermediate_value_Icc hab.le hc.continuousOn
    rwa [ha,hb] at hh

private theorem radial_annulus (A : E2 → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hA : ∀ x, 0 < A x ∧ A x < b)
    (hAh : ∀ x (r : ℝ), 0 < r → A (r • x)=A x)
    (hAc : ∀ x, x ≠ 0 → ContinuousAt A x) :
    ∃ T : E2 → E2,
      ContinuousOn T {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} ∧
      BijOn T {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} {y | A y ≤ ‖y‖ ∧ ‖y‖ ≤ b} ∧
      (∀ x, ‖x‖=a → T x=(A x/a) • x) ∧
      (∀ x, ‖x‖=b → T x=x) ∧
      (∀ x, a ≤ ‖x‖ → ‖x‖ ≤ b → A (T x)=A x) ∧
      ∀ x, a ≤ ‖x‖ → ‖x‖ ≤ b →
        ‖T x‖=A x+(‖x‖-a)*(b-A x)/(b-a) ∧
        T x=((A x+(‖x‖-a)*(b-A x)/(b-a))/‖x‖) • x := by
  let D : Set E2 := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}
  let E : Set E2 := {y | A y ≤ ‖y‖ ∧ ‖y‖ ≤ b}
  let f : E2 → ℝ → ℝ := fun x r => A x+(r-a)*(b-A x)/(b-a)
  have hf (x : E2) : StrictMono (f x) ∧ f x a=A x ∧ f x b=b ∧ f x '' Icc a b=Icc (A x) b :=
    radial_segment a b (A x) hab (hA x).2
  have hn (x : E2) (hx : x ∈ D) : 0 < ‖x‖ := ha.trans_le hx.1
  have hfn (x : E2) (hx : x ∈ D) : 0 < f x ‖x‖ :=
    (hA x).1.trans_le (by
      have hh := (hf x).1.monotone hx.1
      rwa [(hf x).2.1] at hh)
  let T : E2 → E2 := fun x => (f x ‖x‖/‖x‖) • x
  have hnorm (x : E2) (hx : x ∈ D) : ‖T x‖=f x ‖x‖ := by
    rw [show T x=(f x ‖x‖/‖x‖) • x from rfl,norm_smul,Real.norm_eq_abs,
      abs_of_pos (div_pos (hfn x hx) (hn x hx)),div_mul_cancel₀ _ (hn x hx).ne']
  have hprofile (x : E2) (hx : x ∈ D) : A (T x)=A x :=
    hAh x _ (div_pos (hfn x hx) (hn x hx))
  have hTc : ContinuousOn T D := by
    intro x hx
    have hax := hAc x (norm_pos_iff.mp (hn x hx))
    have hfcd : ContinuousAt (fun y => f y ‖y‖) x := by
      dsimp [f]
      fun_prop
    exact ((hfcd.div continuous_norm.continuousAt (hn x hx).ne').smul continuousAt_id).continuousWithinAt
  have hm : MapsTo T D E := by
    intro x hx
    change A (T x) ≤ ‖T x‖ ∧ ‖T x‖ ≤ b
    rw [hprofile x hx,hnorm x hx]
    exact ⟨by simpa only [(hf x).2.1] using (hf x).1.monotone hx.1,
      by simpa only [(hf x).2.2.1] using (hf x).1.monotone hx.2⟩
  have hi : InjOn T D := by
    intro x hx y hy he
    have hAeq : A x=A y := (hprofile x hx).symm.trans ((congrArg A he).trans (hprofile y hy))
    have hfeq : f x ‖x‖=f x ‖y‖ := by
      have hh := congrArg norm he
      rw [hnorm x hx,hnorm y hy] at hh
      simpa only [f,hAeq] using hh
    have hnormeq : ‖x‖=‖y‖ := (hf x).1.injective hfeq
    have hscale : f x ‖x‖/‖x‖=f y ‖y‖/‖y‖ := by rw [hnormeq]; simp only [f,hAeq]
    have he' : (f x ‖x‖/‖x‖) • x=(f x ‖x‖/‖x‖) • y := by
      change (f x ‖x‖/‖x‖) • x=(f y ‖y‖/‖y‖) • y at he
      rwa [← hscale] at he
    exact (smul_right_injective _ (div_pos (hfn x hx) (hn x hx)).ne') he'
  have hs : SurjOn T D E := by
    intro y hy
    have hypos : 0 < ‖y‖ := (hA y).1.trans_le hy.1
    have hym : ‖y‖ ∈ f y '' Icc a b := (hf y).2.2.2.symm ▸ hy
    obtain ⟨r,hr,he⟩ := hym
    have hrpos : 0 < r := ha.trans_le hr.1
    let x : E2 := (r/‖y‖) • y
    have hnx : ‖x‖=r := by
      rw [show x=(r/‖y‖) • y from rfl,norm_smul,Real.norm_eq_abs,
        abs_of_pos (div_pos hrpos hypos),div_mul_cancel₀ _ hypos.ne']
    have hAx : A x=A y := hAh y _ (div_pos hrpos hypos)
    have hx : x ∈ D := by change a ≤ ‖x‖ ∧ ‖x‖ ≤ b; rwa [hnx]
    refine ⟨x,hx,?_⟩
    change (f x ‖x‖/‖x‖) • ((r/‖y‖) • y)=y
    rw [hnx,show f x r=f y r by simp only [f,hAx],he,smul_smul]
    have hh : (‖y‖/r)*(r/‖y‖)=1 := by field_simp
    rw [hh,one_smul]
  refine ⟨T,hTc,⟨hm,hi,hs⟩,?_,?_,fun x h1 h2 => hprofile x ⟨h1,h2⟩,
    fun x h1 h2 => ⟨hnorm x ⟨h1,h2⟩,rfl⟩⟩
  · intro x hx
    dsimp only [T]
    rw [hx,(hf x).2.1]
  · intro x hx
    dsimp only [T]
    rw [hx,(hf x).2.2.1,div_self (ha.trans hab).ne',one_smul]


private theorem relative_radial_annulus (A : E2 → ℝ) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hA : ∀ x, 0 < A x ∧ A x < b)
    (hAh : ∀ x (r : ℝ), 0 < r → A (r • x)=A x)
    (hAc : ∀ x, x ≠ 0 → ContinuousAt A x) :
    ∃ T : E2 → E2,
      ContinuousOn T {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} ∧
      BijOn T {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} {y | A y ≤ ‖y‖ ∧ ‖y‖ ≤ 1} ∧
      (∀ x, ‖x‖=a → T x=(A x/a) • x) ∧
      EqOn T id {x | b ≤ ‖x‖} ∧
      ∀ x, a ≤ ‖x‖ → ‖x‖ ≤ b →
        T x=((A x+(‖x‖-a)*(b-A x)/(b-a))/‖x‖) • x := by
  classical
  obtain ⟨T₀,hTc,hTb,hTa,hTend,hTA,hTnorm⟩ := radial_annulus A a b ha hab hA hAh hAc
  let T : E2 → E2 := fun x => if ‖x‖ ≤ b then T₀ x else x
  have hsmall (x : E2) (hx : ‖x‖ ≤ b) : T x=T₀ x := by simp only [T,if_pos hx]
  have hlarge (x : E2) (hx : b ≤ ‖x‖) : T x=x := by
    by_cases hh : ‖x‖ ≤ b
    · rw [hsmall x hh,hTend x (le_antisymm hh hx)]
    · exact if_neg hh
  have hTC : ContinuousOn T {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} := by
    apply ContinuousOn.if
    · intro x hx
      exact hTend x (frontier_le_subset_eq continuous_norm continuous_const hx.2)
    · apply hTc.mono
      intro x hx
      have hh := hx.2
      rw [(show IsClosed {y : E2 | ‖y‖ ≤ b} from isClosed_le continuous_norm continuous_const).closure_eq] at hh
      exact ⟨hx.1.1,hh⟩
    · exact continuous_id.continuousOn
  have hmap : MapsTo T {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} {y | A y ≤ ‖y‖ ∧ ‖y‖ ≤ 1} := by
    intro x hx
    by_cases hh : ‖x‖ ≤ b
    · rw [hsmall x hh]
      have hz := hTb.mapsTo ⟨hx.1,hh⟩
      exact ⟨hz.1,hz.2.trans hb.le⟩
    · rw [hlarge x (le_of_not_ge hh)]
      exact ⟨(hA x).2.le.trans (le_of_not_ge hh),hx.2⟩
  have hinj : InjOn T {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} := by
    intro x hx y hy he
    by_cases hxb : ‖x‖ ≤ b
    · by_cases hyb : ‖y‖ ≤ b
      · exact hTb.injOn ⟨hx.1,hxb⟩ ⟨hy.1,hyb⟩ (by simpa only [hsmall x hxb,hsmall y hyb] using he)
      · have hn := (hTb.mapsTo ⟨hx.1,hxb⟩).2
        rw [← hsmall x hxb,he,hlarge y (le_of_not_ge hyb)] at hn
        exact (hyb hn).elim
    · by_cases hyb : ‖y‖ ≤ b
      · have hn := (hTb.mapsTo ⟨hy.1,hyb⟩).2
        rw [← hsmall y hyb,← he,hlarge x (le_of_not_ge hxb)] at hn
        exact (hxb hn).elim
      · simpa only [hlarge x (le_of_not_ge hxb),hlarge y (le_of_not_ge hyb)] using he
  have hsurj : SurjOn T {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} {y | A y ≤ ‖y‖ ∧ ‖y‖ ≤ 1} := by
    intro y hy
    by_cases hh : ‖y‖ ≤ b
    · obtain ⟨x,hx,he⟩ := hTb.surjOn ⟨hy.1,hh⟩
      exact ⟨x,⟨hx.1,hx.2.trans hb.le⟩,(hsmall x hx.2).trans he⟩
    · exact ⟨y,⟨hab.le.trans (le_of_not_ge hh),hy.2⟩,hlarge y (le_of_not_ge hh)⟩
  refine ⟨T,hTC,⟨hmap,hinj,hsurj⟩,?_,fun x hx => hlarge x hx,?_⟩
  · intro x hx
    rw [hsmall x (hx ▸ hab.le)]
    exact hTa x hx
  · intro x hx hxb
    rw [hsmall x hxb]
    exact (hTnorm x hx hxb).2

private theorem periodic_upper_margin (ρ : ℝ → ℝ) (hρ : Continuous ρ)
    (hper : Periodic ρ (2*Real.pi)) (hbound : ∀ t, ρ t < 1) :
    ∃ b : ℝ, b < 1 ∧ ∀ t, ρ t < b := by
  have hT : 0 < 2*Real.pi := by positivity
  obtain ⟨s,hs,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) (2*Real.pi)).Nonempty from ⟨0,by simp [hT.le]⟩) hρ.continuousOn
  refine ⟨(ρ s+1)/2,by linarith [hbound s],?_⟩
  intro t
  obtain ⟨u,hu,he⟩ := hper.exists_mem_Ico hT t 0
  have hu' : u ∈ Icc (0:ℝ) (2*Real.pi) := ⟨hu.1,by simpa using hu.2.le⟩
  rw [he]
  have hm : ρ u ≤ ρ s := hmax hu'
  linarith [hbound s]

private theorem support_AnnularWithFormula (w : E2 → E2) (η : ℝ) (ρ : ℝ → ℝ)
    (hw : Continuous w) (hη0 : 0 < η) (hη1 : η < 1)
    (hi : InjOn w {x : E2 | |‖x‖-1| < η})
    (hρ : Continuous ρ) (hper : Periodic ρ (2*Real.pi))
    (hr : ∀ t, 1-η < ρ t ∧ ρ t < 1) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
      ∃ (A : E2 → ℝ) (F : E2 → E2),
        (∀ t, A (unitCircleParameter t)=ρ t) ∧
        (∀ x, 1-η < A x ∧ A x < b) ∧
        (∀ x, x ≠ 0 → ContinuousAt A x) ∧
        (∀ x (r : ℝ), 0 < r → A (r • x)=A x) ∧
        ContinuousOn F {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} ∧
        BijOn F {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1}
          (w '' {y | A y ≤ ‖y‖ ∧ ‖y‖ ≤ 1}) ∧
        (∀ t, F (a • unitCircleParameter t)=w (ρ t • unitCircleParameter t)) ∧
        EqOn F w {x | b ≤ ‖x‖} ∧
        (∀ x, a ≤ ‖x‖ → ‖x‖ ≤ b →
          F x=w ((A x+(‖x‖-a)*(b-A x)/(b-a)) • (‖x‖⁻¹ • x))) ∧
        ∀ s t, a ≤ s → s ≤ b → F (s • unitCircleParameter t)=
          w ((ρ t+(s-a)*(b-ρ t)/(b-a)) • unitCircleParameter t) := by
  obtain ⟨A,hAc,hAh,hAu,hAr⟩ := angular_profile ρ hρ hper
  obtain ⟨b,hb,hρb⟩ := periodic_upper_margin ρ hρ hper (fun t => (hr t).2)
  have hA (x : E2) : 1-η < A x ∧ A x < b := by
    obtain ⟨t,he⟩ := hAr x
    rw [he]
    exact ⟨(hr t).1,hρb t⟩
  let a := (1-η)/2
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a < b := by have h := hA 0; dsimp [a]; linarith [h.1,h.2]
  have hA0 (x : E2) : 0 < A x ∧ A x < b := ⟨by linarith [(hA x).1],(hA x).2⟩
  obtain ⟨T,hTc,hTb,hTa,hTout,hTformula⟩ := relative_radial_annulus A a b ha hab hb hA0 hAh hAc
  let E : Set E2 := {y | A y ≤ ‖y‖ ∧ ‖y‖ ≤ 1}
  have hE : E ⊆ {x : E2 | |‖x‖-1| < η} := by
    intro x hx
    change |‖x‖-1| < η
    rw [abs_lt]
    exact ⟨by linarith [(hA x).1,hx.1],by linarith [hx.2]⟩
  have hwE : BijOn w E (w '' E) := ⟨mapsTo_image _ _,hi.mono hE,surjOn_image _ _⟩
  refine ⟨a,b,ha,hab,hb,A,w ∘ T,hAu,hA,hAc,hAh,hw.comp_continuousOn hTc,hwE.comp hTb,?_,?_,?_,?_⟩
  · intro t
    have hu : ‖unitCircleParameter t‖=1 := by
      have hh : ‖unitCircleParameter t‖^2=1 := by
        rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
        exact Real.cos_sq_add_sin_sq t
      nlinarith [norm_nonneg (unitCircleParameter t)]
    have hn : ‖a • unitCircleParameter t‖=a := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha,hu,mul_one]
    change w (T (a • unitCircleParameter t))=_
    rw [hTa _ hn,hAh _ a ha,hAu,smul_smul,div_mul_cancel₀ _ ha.ne']
  · intro x hx
    change w (T x)=w x
    rw [hTout hx,id_eq]
  · intro x hx hxb
    change w (T x)=_
    rw [hTformula x hx hxb,smul_smul,div_eq_mul_inv]
  · intro s t hs hsb
    have hs0 : 0<s := ha.trans_le hs
    have hu : ‖unitCircleParameter t‖=1 := by
      have hh : ‖unitCircleParameter t‖^2=1 := by
        rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
        exact Real.cos_sq_add_sin_sq t
      nlinarith [norm_nonneg (unitCircleParameter t)]
    have hn : ‖s • unitCircleParameter t‖=s := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs0,hu,mul_one]
    change w (T (s • unitCircleParameter t))=_
    rw [hTformula _ (by rw [hn]; exact hs) (by rw [hn]; exact hsb),hn,hAh _ s hs0,hAu,smul_smul,
      div_mul_cancel₀ _ hs0.ne']

end VM03CapV437RawFormula
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
namespace VM03CapV437RawRegular
set_option maxHeartbeats 800000
private theorem circle_smooth : ContDiff ℝ ∞ unitCircleParameter := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact Real.contDiff_cos
  · exact Real.contDiff_sin

private theorem annular_polar_tile (w : E2 → E2) (hw : ContDiff ℝ ∞ w)
    (ρ : ℝ → ℝ) (l u a b : ℝ) (hρ : ContDiffOn ℝ ∞ ρ (Icc l u)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ×ℝ => w ((ρ z.2+(z.1-a)*(b-ρ z.2)/(b-a)) • unitCircleParameter z.2))
      (Icc a b ×ˢ Icc l u) := by
  have hρ' : ContDiffOn ℝ ∞ (fun z : ℝ×ℝ => ρ z.2) (Icc a b ×ˢ Icc l u) :=
    hρ.comp contDiffOn_snd (fun _ hz => hz.2)
  have hr : ContDiffOn ℝ ∞
      (fun z : ℝ×ℝ => ρ z.2+(z.1-a)*(b-ρ z.2)/(b-a)) (Icc a b ×ˢ Icc l u) := by
    exact hρ'.add (((contDiffOn_fst.sub contDiffOn_const).mul (contDiffOn_const.sub hρ')).div_const _)
  exact hw.comp_contDiffOn (hr.smul (circle_smooth.comp contDiff_snd).contDiffOn)

private theorem normalized_lipschitz_away
    (a : ℝ) (ha : 0<a)
    (hest : ∀ x y : E2, x≠0 → y≠0 →
      ‖x‖*dist (‖x‖⁻¹ • x) (‖y‖⁻¹ • y) ≤ 2*dist x y) :
    ∃ L : NNReal, LipschitzOnWith L (fun x : E2 => ‖x‖⁻¹ • x) {x | a≤‖x‖} := by
  let L : NNReal := ⟨2/a,by positivity⟩
  refine ⟨L,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hx0 : x≠0 := norm_pos_iff.mp (ha.trans_le hx)
  have hy0 : y≠0 := norm_pos_iff.mp (ha.trans_le hy)
  have hh := hest x y hx0 hy0
  have hl : a*dist (‖x‖⁻¹ • x) (‖y‖⁻¹ • y) ≤ 2*dist x y :=
    (mul_le_mul_of_nonneg_right hx dist_nonneg).trans hh
  change dist (‖x‖⁻¹ • x) (‖y‖⁻¹ • y) ≤ (2/a)*dist x y
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hl)

private theorem homogeneous_lipschitz_away {Y : Type*} [PseudoMetricSpace Y]
    (A : E2 → Y) (a : ℝ) (ha : 0<a)
    (hAh : ∀ x (r : ℝ), 0<r → A (r • x)=A x)
    (K L : NNReal) (hA : LipschitzOnWith K A (sphere 0 1))
    (hL : LipschitzOnWith L (fun x : E2 => ‖x‖⁻¹ • x) {x | a≤‖x‖}) :
    LipschitzOnWith (K*L) A {x | a≤‖x‖} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hx0 : 0<‖x‖ := ha.trans_le hx
  have hy0 : 0<‖y‖ := ha.trans_le hy
  have hnx : ‖x‖⁻¹ • x∈sphere 0 1 := by simp [norm_smul,hx0.ne']
  have hny : ‖y‖⁻¹ • y∈sphere 0 1 := by simp [norm_smul,hy0.ne']
  have hh := hA.dist_le_mul (‖x‖⁻¹ • x) hnx (‖y‖⁻¹ • y) hny
  rw [hAh x _ (inv_pos.mpr hx0),hAh y _ (inv_pos.mpr hy0)] at hh
  have hl := hL.dist_le_mul x hx y hy
  calc dist (A x) (A y)
    _ ≤ (K:ℝ)*dist (‖x‖⁻¹ • x) (‖y‖⁻¹ • y) := hh
    _ ≤ (K:ℝ)*((L:ℝ)*dist x y) := mul_le_mul_of_nonneg_left hl K.2
    _ = ((K*L:NNReal):ℝ)*dist x y := by rw [NNReal.coe_mul]; ring

private theorem polynomial_chart_lipschitz (a b : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K
      (fun z : ℝ×ℝ×E2 => (z.1+(z.2.1-a)*(b-z.1)/(b-a)) • z.2.2)
      (Icc (0:ℝ) b ×ˢ (Icc a b ×ˢ closedBall (0:E2) 1)) := by
  have hΦ : ContDiff ℝ ∞ (fun z : ℝ×ℝ×E2 => (z.1+(z.2.1-a)*(b-z.1)/(b-a)) • z.2.2) := by fun_prop
  exact hΦ.contDiffOn.exists_lipschitzOnWith (by simp)
    ((convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_closedBall _ _)))
    (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_closedBall _ _)))

private theorem polynomial_annulus_lipschitz
    (A : E2 → ℝ) (a b : ℝ) (ha : 0<a) (hab : a≤b)
    (KA KN : NNReal)
    (hA : LipschitzOnWith KA A {x | a≤‖x‖})
    (hN : LipschitzOnWith KN (fun x : E2 => ‖x‖⁻¹ • x) {x | a≤‖x‖})
    (hAb : ∀ x,0≤A x ∧ A x≤b) :
    ∃ K : NNReal, LipschitzOnWith K
      (fun x : E2 => (A x+(‖x‖-a)*(b-A x)/(b-a)) • (‖x‖⁻¹ • x))
      {x | a≤‖x‖ ∧ ‖x‖≤b} := by
  let Q : Set (ℝ×ℝ×E2) := Icc (0:ℝ) b ×ˢ (Icc a b ×ˢ closedBall (0:E2) 1)
  let Φ : (ℝ×ℝ×E2) → E2 := fun z => (z.1+(z.2.1-a)*(b-z.1)/(b-a)) • z.2.2
  obtain ⟨K,hK⟩ := polynomial_chart_lipschitz a b
  let D : Set E2 := {x | a≤‖x‖ ∧ ‖x‖≤b}
  let f : E2 → ℝ×ℝ×E2 := fun x => (A x,‖x‖,‖x‖⁻¹ • x)
  have hnorm : LipschitzOnWith 1 (norm : E2 → ℝ) D := lipschitzWith_one_norm.lipschitzOnWith
  have hf : LipschitzOnWith (max KA (max 1 KN)) f D :=
    (hA.mono fun _ hx => hx.1).prodMk
      (hnorm.prodMk (hN.mono fun _ hx => hx.1))
  have hmap : MapsTo f D Q := by
    intro x hx
    refine ⟨hAb x,hx,?_⟩
    have hx0 : 0<‖x‖ := ha.trans_le hx.1
    rw [mem_closedBall_zero_iff]
    change ‖‖x‖⁻¹ • x‖≤1
    simp [norm_smul,hx0.ne']
  refine ⟨K*max KA (max 1 KN),LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hxy := hK.dist_le_mul (f x) (hmap hx) (f y) (hmap hy)
  have hfxy := hf.dist_le_mul x hx y hy
  change dist (Φ (f x)) (Φ (f y)) ≤ _
  calc dist (Φ (f x)) (Φ (f y))
    _ ≤ (K:ℝ)*dist (f x) (f y) := hxy
    _ ≤ (K:ℝ)*(((max KA (max 1 KN):NNReal):ℝ)*dist x y) :=
      mul_le_mul_of_nonneg_left hfxy K.2
    _ = _ := by rw [NNReal.coe_mul,mul_assoc]
end VM03CapV437RawRegular
noncomputable section
open Set Function Filter Metric
open SeifertSurfaces.AppendixACoordinates
namespace VM03CapV437RawRegular
private theorem radial_lipschitz_glue (H : E2 → E2) (a : ℝ) (K : NNReal)
    (hsmall : LipschitzOnWith K H {x | ‖x‖≤a})
    (hlarge : LipschitzOnWith K H {x | a≤‖x‖}) : LipschitzWith K H := by
  have hcross (x y : E2) (hx : ‖x‖≤a) (hy : a≤‖y‖) :
      dist (H x) (H y)≤K*dist x y := by
    let c : ℝ → E2 := fun t => AffineMap.lineMap x y t
    have hc : Continuous (fun t => ‖c t‖) := by dsimp [c,AffineMap.lineMap_apply_module]; fun_prop
    have ha : a∈Icc (‖c 0‖) (‖c 1‖) := by simpa [c] using And.intro hx hy
    obtain ⟨t,ht,hta⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hc.continuousOn ha
    have hseg : c t∈segment ℝ x y := by
      rw [segment_eq_image_lineMap]
      exact ⟨t,ht,rfl⟩
    have hd := dist_add_dist_of_mem_segment hseg
    have h1 := hsmall.dist_le_mul x hx (c t) (le_of_eq hta)
    have h2 := hlarge.dist_le_mul (c t) (le_of_eq hta.symm) y hy
    have htri := dist_triangle (H x) (H (c t)) (H y)
    nlinarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : ‖x‖≤a
  · by_cases hy : ‖y‖≤a
    · exact hsmall.dist_le_mul x hx y hy
    · exact hcross x y hx (le_of_not_ge hy)
  · by_cases hy : ‖y‖≤a
    · simpa only [dist_comm (H y) (H x),dist_comm y x] using hcross y x hy (le_of_not_ge hx)
    · exact hlarge.dist_le_mul x (le_of_not_ge hx) y (le_of_not_ge hy)
end VM03CapV437RawRegular
namespace VM03CapV437RawRegular
private theorem radial_lipschitz_glue_away (H : E2 → E2) (a b : ℝ) (hab : a≤b) (K : NNReal)
    (hsmall : LipschitzOnWith K H {x | a≤‖x‖ ∧ ‖x‖≤b})
    (hlarge : LipschitzOnWith K H {x | b≤‖x‖}) :
    LipschitzOnWith K H {x | a≤‖x‖} := by
  have hcross (x y : E2) (hx : a≤‖x‖ ∧ ‖x‖≤b) (hy : b≤‖y‖) :
      dist (H x) (H y)≤K*dist x y := by
    let c : ℝ → E2 := fun t => AffineMap.lineMap x y t
    have hc : Continuous (fun t => ‖c t‖) := by dsimp [c,AffineMap.lineMap_apply_module]; fun_prop
    have ha : b∈Icc (‖c 0‖) (‖c 1‖) := by simpa [c] using And.intro hx.2 hy
    obtain ⟨t,ht,hta⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hc.continuousOn ha
    change ‖c t‖=b at hta
    have hseg : c t∈segment ℝ x y := by
      rw [segment_eq_image_lineMap]
      exact ⟨t,ht,rfl⟩
    have hd := dist_add_dist_of_mem_segment hseg
    have h1 := hsmall.dist_le_mul x hx (c t) ⟨by rw [hta]; exact hab,le_of_eq hta⟩
    have h2 := hlarge.dist_le_mul (c t) (le_of_eq hta.symm) y hy
    have htri := dist_triangle (H x) (H (c t)) (H y)
    nlinarith
  apply LipschitzOnWith.of_dist_le_mul
  intro x hxa y hya
  by_cases hx : ‖x‖≤b
  · by_cases hy : ‖y‖≤b
    · exact hsmall.dist_le_mul x ⟨hxa,hx⟩ y ⟨hya,hy⟩
    · exact hcross x y ⟨hxa,hx⟩ (le_of_not_ge hy)
  · by_cases hy : ‖y‖≤b
    · simpa only [dist_comm (H y) (H x),dist_comm y x] using hcross y x ⟨hya,hy⟩ (le_of_not_ge hx)
    · exact hlarge.dist_le_mul x (le_of_not_ge hx) y (le_of_not_ge hy)
end VM03CapV437RawRegular
namespace VM03CapV437RawRegular
private theorem support_RegularAnnular (w : E2 → E2) (η : ℝ) (ρ : ℝ → ℝ)
    (hw : ContDiff ℝ ∞ w) (hwL : ∃ K : NNReal,LipschitzWith K w)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hi : InjOn w {x : E2 | |‖x‖-1| < η})
    (hρ : Continuous ρ) (hper : Periodic ρ (2*Real.pi))
    (hρb : ∀ t,1-η < ρ t ∧ ρ t < 1)
    (m : ℕ) (t : Fin (m+1) → ℝ) (ht : StrictMono t)
    (ht0 : t 0=0) (htT : t (Fin.last m)=2*Real.pi)
    (hρs : ∀ i : Fin m,ContDiffOn ℝ ∞ ρ (Icc (t i.castSucc) (t i.succ))) :
    ∃ a b : ℝ,0<a ∧ a<b ∧ b<1 ∧
      ∃ (A : E2 → ℝ) (F : E2 → E2),
        (∀ z,A (unitCircleParameter z)=ρ z) ∧
        (∀ x,1-η < A x ∧ A x < b) ∧
        (∀ x,x≠0 → ContinuousAt A x) ∧
        (∀ x (r : ℝ),0<r → A (r • x)=A x) ∧
        ContinuousOn F {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} ∧
        BijOn F {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1} (w '' {y | A y ≤ ‖y‖ ∧ ‖y‖ ≤ 1}) ∧
        (∀ z,F (a • unitCircleParameter z)=w (ρ z • unitCircleParameter z)) ∧
        EqOn F w {x | b ≤ ‖x‖} ∧
        (∃ K : NNReal,LipschitzOnWith K F {x | a ≤ ‖x‖}) ∧
        ∀ i : Fin m,
          ContDiffOn ℝ ∞ (fun z : ℝ×ℝ => F (z.1 • unitCircleParameter z.2))
            (Icc a b ×ˢ Icc (t i.castSucc) (t i.succ)) := by
  obtain ⟨a,b,ha,hab,hb,A,F,hAu,hA,hAc,hAh,hFc,hFb,hFa,hFout,hFexpr,hFpolar⟩ :=
    VM03CapV437RawFormula.support_AnnularWithFormula w η ρ hw.continuous hη0 hη1 hi hρ hper hρb
  obtain ⟨Kρ,hKρ⟩ := periodic_smooth_pieces_lipschitz ρ hper m t ht ht0 htT hρs
  obtain ⟨KA,hKA⟩ := sphere_lipschitz_of_periodic_trace A ρ hper Kρ hKρ hAu
  obtain ⟨KN,hKN⟩ := normalized_lipschitz_away a ha normalized_dist_mul_le
  have hLA : LipschitzOnWith (KA*KN) A {x | a ≤ ‖x‖} :=
    homogeneous_lipschitz_away A a ha hAh KA KN hKA hKN
  obtain ⟨KT,hKT⟩ := polynomial_annulus_lipschitz A a b ha hab.le (KA*KN) KN hLA hKN
    (fun x => ⟨by linarith [(hA x).1],(hA x).2.le⟩)
  obtain ⟨Kw,hKw⟩ := hwL
  have hFL1 : LipschitzOnWith (Kw*KT) F {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hFexpr x hx.1 hx.2,hFexpr y hy.1 hy.2]
    exact (hKw.comp_lipschitzOnWith hKT).dist_le_mul x hx y hy
  have hFL2 : LipschitzOnWith Kw F {x | b ≤ ‖x‖} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hFout hx,hFout hy]
    exact hKw.dist_le_mul x y
  have hFL : LipschitzOnWith (max (Kw*KT) Kw) F {x | a ≤ ‖x‖} :=
    radial_lipschitz_glue_away F a b hab.le _ (hFL1.weaken (le_max_left _ _))
      (hFL2.weaken (le_max_right _ _))
  refine ⟨a,b,ha,hab,hb,A,F,hAu,hA,hAc,hAh,hFc,hFb,hFa,hFout,⟨_,hFL⟩,?_⟩
  intro i
  exact (annular_polar_tile w hw ρ (t i.castSucc) (t i.succ) a b (hρs i)).congr
    (fun z hz => hFpolar z.1 z.2 hz.1.1 hz.1.2)
end VM03CapV437RawRegular
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
namespace VM03CapV437InnerTracked

private theorem radial_boundary_extension
    (Q : Set E2) (hQc : Convex ℝ Q) (hQ0 : Q ∈ 𝓝 (0:E2))
    (hQclosed : IsClosed Q) (hQb : Bornology.IsBounded Q)
    (β : E2 → E2) (hβc : ContinuousOn β (sphere 0 1))
    (hβ : BijOn β (sphere 0 1) (frontier Q)) :
    ∃ C : E2 → E2, Continuous C ∧ Bijective C ∧
      BijOn C (closedBall 0 1) Q ∧ BijOn C (ball 0 1) (interior Q) ∧
      EqOn C β (sphere 0 1) ∧ C 0=0 ∧
      (∀ x (r : ℝ), 0 ≤ r → C (r • x)=r • C x) ∧
      ∀ x, x ≠ 0 → C x=‖x‖ • β (‖x‖⁻¹ • x) := by
  classical
  let n : E2 → E2 := fun x => ‖x‖⁻¹ • x
  have hn (x : E2) (hx : x ≠ 0) : n x ∈ sphere 0 1 := by
    simp [n,mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx)),hx]
  have hnn (x : E2) (hx : x ∈ sphere 0 1) : n x=x := by
    have hh := mem_sphere_zero_iff_norm.mp hx
    simp [n,hh]
  have hns (x : E2) (r : ℝ) (hr : 0 < r) : n (r • x)=n x := by
    dsimp [n]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,smul_smul]
    congr 1
    field_simp
  let C : E2 → E2 := fun x => ‖x‖ • β (n x)
  have hC0 : C 0=0 := by simp [C]
  have hQg : ∀ x, 0 < gauge Q x ↔ x ≠ 0 := fun x =>
    gauge_pos (absorbent_nhds_zero hQ0) (NormedSpace.isVonNBounded_of_isBounded ℝ hQb)
  have hCg (x : E2) : gauge Q (C x)=‖x‖ := by
    by_cases hx : x=0
    · simp [hx,hC0]
    · rw [show C x=‖x‖ • β (n x) from rfl,gauge_smul_of_nonneg (norm_nonneg x)]
      have hh := (gauge_eq_one_iff_mem_frontier hQc hQ0).mpr (hβ.mapsTo (hn x hx))
      simp [hh,smul_eq_mul]
  have hCh (x : E2) (r : ℝ) (hr : 0 ≤ r) : C (r • x)=r • C x := by
    rcases hr.eq_or_lt with hr | hr
    · simp [← hr,hC0]
    · dsimp only [C]
      rw [hns x r hr,norm_smul,Real.norm_eq_abs,abs_of_pos hr,smul_smul]
  have hCi : Injective C := by
    intro x y he
    have hnorm : ‖x‖=‖y‖ := by simpa only [hCg] using congrArg (gauge Q) he
    by_cases hx : x=0
    · subst x
      exact (norm_eq_zero.mp (by simpa using hnorm.symm)).symm
    · have hy : y ≠ 0 := by intro hy; exact hx (norm_eq_zero.mp (by simpa [hy] using hnorm))
      have heβ : β (n x)=β (n y) := by
        apply smul_right_injective E2 (norm_pos_iff.mpr hx).ne'
        change ‖x‖ • β (n x)=‖x‖ • β (n y)
        simpa only [C,hnorm] using he
      have hen : n x=n y := hβ.injOn (hn x hx) (hn y hy) heβ
      have hxnorm : ‖x‖ • n x=x := by simp [n,smul_smul,hx]
      have hynorm : ‖y‖ • n y=y := by simp [n,smul_smul,hy]
      calc x = ‖x‖ • n x := hxnorm.symm
           _ = ‖y‖ • n y := by rw [hnorm,hen]
           _ = y := hynorm
  have hCs : Surjective C := by
    intro y
    by_cases hy : y=0
    · exact ⟨0,hy ▸ hC0⟩
    · let r := gauge Q y
      have hr : 0 < r := (hQg y).mpr hy
      have hg : gauge Q (r⁻¹ • y)=1 := by
        rw [gauge_smul_of_nonneg (inv_nonneg.mpr hr.le),smul_eq_mul]
        exact inv_mul_cancel₀ hr.ne'
      obtain ⟨u,hu,heu⟩ := hβ.surjOn ((gauge_eq_one_iff_mem_frontier hQc hQ0).mp hg)
      refine ⟨r • u,?_⟩
      have hnu : ‖u‖=1 := mem_sphere_zero_iff_norm.mp hu
      rw [hCh u r hr.le]
      change r • (‖u‖ • β (n u))=y
      rw [hnu,one_smul,hnn u hu,heu,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hCcont : Continuous C := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x=0
    · subst x
      obtain ⟨B,hB⟩ := (isCompact_sphere (0:E2) 1).image_of_continuousOn hβc |>.isBounded.exists_norm_le
      have hbound (y : E2) : ‖C y‖ ≤ ‖y‖*B := by
        by_cases hy : y=0
        · simp [hy,hC0]
        · rw [show C y=‖y‖ • β (n y) from rfl,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg y)]
          exact mul_le_mul_of_nonneg_left (hB _ (mem_image_of_mem β (hn y hy))) (norm_nonneg y)
      apply Metric.continuousAt_iff.mpr
      intro ε hε
      refine ⟨ε/(|B|+1),by positivity,?_⟩
      intro y hy
      rw [hC0,dist_zero_right]
      rw [dist_zero_right] at hy
      calc ‖C y‖ ≤ ‖y‖*B := hbound y
           _ ≤ ‖y‖*|B| := mul_le_mul_of_nonneg_left (le_abs_self B) (norm_nonneg y)
           _ < ε := by
             have hh : ‖y‖*(|B|+1) < ε := (lt_div_iff₀ (by positivity)).mp hy
             nlinarith [norm_nonneg y,abs_nonneg B]
    · have hnc : ContinuousAt n x := continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx) |>.smul continuousAt_id
      have hbn : ContinuousAt (β ∘ n) x := by
        apply (hβc (n x) (hn x hx)).tendsto.comp
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within n hnc
        filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
        exact hn y hy
      exact continuous_norm.continuousAt.smul hbn
  have hclosed (x : E2) : C x ∈ Q ↔ x ∈ closedBall 0 1 := by
    rw [← hQclosed.closure_eq,← gauge_le_one_iff_mem_closure hQc hQ0,hCg,mem_closedBall_zero_iff]
  have hopen (x : E2) : C x ∈ interior Q ↔ x ∈ ball 0 1 := by
    rw [← gauge_lt_one_iff_mem_interior hQc hQ0,hCg,mem_ball_zero_iff]
  refine ⟨C,hCcont,⟨hCi,hCs⟩,?_,?_,?_,hC0,hCh,fun _ _ => rfl⟩
  · refine ⟨fun x hx => (hclosed x).mpr hx,hCi.injOn,?_⟩
    intro y hy
    obtain ⟨x,rfl⟩ := hCs y
    exact ⟨x,(hclosed x).mp hy,rfl⟩
  · refine ⟨fun x hx => (hopen x).mpr hx,hCi.injOn,?_⟩
    intro y hy
    obtain ⟨x,rfl⟩ := hCs y
    exact ⟨x,(hopen x).mp hy,rfl⟩
  · intro x hx
    change ‖x‖ • β (n x)=β x
    rw [mem_sphere_zero_iff_norm.mp hx,one_smul,hnn x hx]


open DifferentialGeometry.Topology.PiecewiseLinear

private theorem inner_pl_disk_with_prescribed_boundary
    (D : Set E2) (hD : IsPLBall 2 D) (hDc : IsClosed D)
    (B : E2 → E2) (hBc : ContinuousOn B (sphere 0 1))
    (hB : BijOn B (sphere 0 1) (frontier D)) :
    ∃ (K : Geometry.SimplicialComplex ℝ E2) (F C G : E2 → E2),
      K.faces.Finite ∧ Convex ℝ K.space ∧ IsCompact K.space ∧ K.space ∈ 𝓝 (0:E2) ∧
      IsPLBall 2 K.space ∧ IsPLHomeomorphOn F K.space D ∧
      Continuous C ∧ Bijective C ∧ BijOn C (closedBall 0 1) K.space ∧
      BijOn C (ball 0 1) (interior K.space) ∧
      (∀ x, G x=F (C x)) ∧ ContinuousOn G (closedBall 0 1) ∧
      BijOn G (closedBall 0 1) D ∧ BijOn G (ball 0 1) (interior D) ∧
      EqOn G B (sphere 0 1) ∧
      (∀ x,C x=‖x‖ • invFunOn F K.space (B (‖x‖⁻¹ • x))) ∧
      BijOn (invFunOn F K.space ∘ B) (sphere 0 1) (frontier K.space) ∧
      MapsTo C (sphere 0 1) (frontier K.space) := by
  classical
  obtain ⟨T,hT,hcard,h0,hsub,hT0⟩ := exists_affineIndependent_openSimplex_subset
    (n:=1) (E:=E2) (by simp) (0:E2) (Filter.univ_mem : (univ : Set E2) ∈ 𝓝 0)
  let K := simplexComplex T hT
  have hKspace : K.space=convexHull ℝ (T:Set E2) := simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKc : IsCompact K.space := by rw [hKspace]; exact T.finite_toSet.isCompact_convexHull ℝ
  have hKconv : Convex ℝ K.space := by rw [hKspace]; exact convex_convexHull ℝ _
  have hK0 : K.space ∈ 𝓝 (0:E2) := hKspace.symm ▸ hT0
  have hK : IsPLBall 2 K.space := by
    rw [hKspace]
    exact isPLBall_convexHull_of_affineIndependent T hT hcard
  obtain ⟨f,hf⟩ := hK
  obtain ⟨g,hg⟩ := hD
  let F : E2 → E2 := g ∘ invFunOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hF : IsPLHomeomorphOn F K.space D := hf.symm.trans hg
  let V := invFunOn F K.space
  have hV : IsPLHomeomorphOn V D K.space := hF.symm
  have hfront : F '' frontier K.space=frontier D := hF.image_frontier rfl hKc.isClosed hDc
  have hVfront : V '' frontier D=frontier K.space := hV.image_frontier rfl hDc hKc.isClosed
  have hVb : BijOn V (frontier D) (frontier K.space) :=
    ⟨by intro y hy; exact hVfront ▸ mem_image_of_mem V hy,
      hV.bijOn.injOn.mono (frontier_subset_closure.trans hDc.closure_eq.subset),
      by intro y hy; exact hVfront.symm ▸ hy⟩
  let β := V ∘ B
  have hβ : BijOn β (sphere 0 1) (frontier K.space) := hVb.comp hB
  have hβc : ContinuousOn β (sphere 0 1) := hV.isPiecewiseAffineOn.continuousOn.comp hBc
    (hB.mapsTo.mono_right (frontier_subset_closure.trans hDc.closure_eq.subset))
  obtain ⟨C,hCc,hCi,hCclosed,hCopen,hCboundary,hC0,hCh,hCformula⟩ :=
    radial_boundary_extension K.space hKconv hK0 hKc.isClosed hKc.isBounded β hβc hβ
  let G := F ∘ C
  have hFI : BijOn F (interior K.space) (interior D) :=
    ⟨by intro x hx; exact hF.image_interior rfl ▸ mem_image_of_mem F hx,
      hF.bijOn.injOn.mono interior_subset,
      by intro y hy; exact (hF.image_interior rfl).symm ▸ hy⟩
  refine ⟨K,F,C,G,simplexComplex_faces_finite T hT,hKconv,hKc,hK0,⟨f,hf⟩,hF,
    hCc,hCi,hCclosed,hCopen,fun _ => rfl,
    hF.isPiecewiseAffineOn.continuousOn.comp hCc.continuousOn hCclosed.mapsTo,
    hF.bijOn.comp hCclosed,hFI.comp hCopen,?_,?_,hβ,?_⟩
  · intro x hx
    change F (C x)=B x
    rw [hCboundary hx]
    exact hF.bijOn.invOn_invFunOn.2
      ((frontier_subset_closure.trans hDc.closure_eq.subset) (hB.mapsTo hx))
  · intro x
    by_cases hx : x=0
    · subst x
      simp [hC0]
    · exact hCformula x hx
  · intro x hx
    rw [hCboundary hx]
    exact hβ.mapsTo hx
end VM03CapV437InnerTracked
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Topology.PiecewiseLinear
namespace VM03CapV437RawReplacement
private theorem relative_inner_replacement
    (Q D : Set E2) (hQ : IsClosed Q) (hD : IsClosed D)
    (F J C B : E2 → E2) (hF : IsPLHomeomorphOn F Q D)
    (hJi : InjOn J Q) (hJimage : J '' Q=F '' Q) (hJboundary : EqOn J F (frontier Q))
    (hCclosed : BijOn C (closedBall 0 1) Q)
    (hCopen : BijOn C (ball 0 1) (interior Q))
    (hCfront : MapsTo C (sphere 0 1) (frontier Q))
    (htrace : ∀ x∈sphere 0 1,F (C x)=B x) :
    BijOn (J ∘ C) (closedBall 0 1) D ∧
      BijOn (J ∘ C) (ball 0 1) (interior D) ∧ EqOn (J ∘ C) B (sphere 0 1) := by
  have hJQ : J '' Q=D := hJimage.trans hF.image_eq
  have hJfront : J '' frontier Q=frontier D :=
    (image_congr hJboundary).trans (hF.image_frontier rfl hQ hD)
  have hJint : J '' interior Q=interior D := by
    rw [← self_sdiff_frontier Q, hJi.image_sdiff_subset (frontier_subset_closure.trans hQ.closure_eq.subset),
      hJQ,hJfront,self_sdiff_frontier]
  have hJclosed : BijOn J Q D := ⟨fun _ hx => hJQ ▸ mem_image_of_mem J hx,hJi,
    fun y hy => hJQ.symm ▸ hy⟩
  have hJopen : BijOn J (interior Q) (interior D) :=
    ⟨fun _ hx => hJint ▸ mem_image_of_mem J hx,hJi.mono interior_subset,
      fun y hy => hJint.symm ▸ hy⟩
  refine ⟨hJclosed.comp hCclosed,hJopen.comp hCopen,?_⟩
  intro x hx
  exact (hJboundary (hCfront hx)).trans (htrace x hx)
end VM03CapV437RawReplacement
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
namespace VM03CapV437RawInnerPolar
private theorem inner_polar_tile
    (Q : Set E2) (hQc : Convex ℝ Q) (hQ0 : 0∈interior Q)
    (J : E2 → E2) (hJs : ∀ x∈interior Q,ContDiffAt ℝ 1 J x)
    (S : Set E2)
    (hJb : ∀ x∈frontier Q, x∉S → ∃ (U : Set E2) (L : E2 →ᵃ[ℝ] E2),
      IsOpen U ∧ x∈U ∧ EqOn J L (U∩Q))
    (β : ℝ → E2) (a l u : ℝ) (ha : 0<a)
    (hβ : ContDiffOn ℝ ∞ β (Icc l u))
    (hβQ : ∀ t∈Icc l u,β t∈frontier Q ∩ Q)
    (hβS : ∀ t∈Ioo l u,β t∉S) :
    ContDiffOn ℝ 1 (fun z : ℝ×ℝ => J ((z.1/a) • β z.2))
      ((Icc (0:ℝ) a ×ˢ Icc l u) \ (({0,a}:Set ℝ) ×ˢ ({l,u}:Set ℝ))) := by
  let D := (Icc (0:ℝ) a ×ˢ Icc l u) \ (({0,a}:Set ℝ) ×ˢ ({l,u}:Set ℝ))
  let q : ℝ×ℝ → E2 := fun z => (z.1/a) • β z.2
  have hq : ContDiffOn ℝ 1 q (Icc (0:ℝ) a ×ˢ Icc l u) := by
    have hb : ContDiffOn ℝ 1 (fun z : ℝ×ℝ => β z.2) (Icc (0:ℝ) a ×ˢ Icc l u) :=
      (hβ.of_le (by simp)).comp contDiffOn_snd (fun _ hz => hz.2)
    exact (contDiffOn_fst.div_const a).smul hb
  have hqQ : MapsTo q (Icc (0:ℝ) a ×ˢ Icc l u) Q := by
    intro z hz
    have hs : 0≤z.1/a := div_nonneg hz.1.1 ha.le
    have hs1 : z.1/a≤1 := (div_le_one ha).mpr hz.1.2
    have hh := hQc (interior_subset hQ0) (hβQ z.2 hz.2).2 (sub_nonneg.mpr hs1) hs
      (by ring : (1-z.1/a)+z.1/a=1)
    simpa only [smul_zero,zero_add] using hh
  intro z hz
  have hzD : z∈D := hz
  have hqz : ContDiffWithinAt ℝ 1 q D z := (hq z hz.1).mono sdiff_subset
  by_cases hrad : z.1<a
  · have hqin : q z∈interior Q := by
      have hs : 0≤z.1/a := div_nonneg hz.1.1.1 ha.le
      have hs1 : z.1/a<1 := (div_lt_one ha).mpr hrad
      have hh := hQc.combo_interior_self_mem_interior hQ0 (hβQ z.2 hz.1.2).2
        (sub_pos.mpr hs1) hs (by ring : (1-z.1/a)+z.1/a=1)
      simpa only [q,smul_zero,zero_add] using hh
    exact (hJs (q z) hqin).comp_contDiffWithinAt z hqz
  · have hza : z.1=a := le_antisymm hz.1.1.2 (le_of_not_gt hrad)
    have hzin : z.2∈Ioo l u := by
      constructor
      · apply lt_of_le_of_ne hz.1.2.1
        intro he
        exact hz.2 ⟨by simp [hza],by simp [he]⟩
      · apply lt_of_le_of_ne hz.1.2.2
        intro he
        exact hz.2 ⟨by simp [hza],by simp [he]⟩
    have hqeq : q z=β z.2 := by simp [q,hza,ha.ne']
    obtain ⟨U,L,hU,hzU,hJL⟩ := hJb (β z.2) (hβQ z.2 hz.1.2).1 (hβS z.2 hzin)
    have hL : ContDiff ℝ 1 L :=
      (show E2 →ᴬ[ℝ] E2 from ⟨L,L.continuous_of_finiteDimensional⟩).contDiff
    have he : (fun y => J (q y)) =ᶠ[𝓝[D] z] (fun y => L (q y)) := by
      have hnear : ∀ᶠ y in 𝓝[D] z,q y∈U :=
        hqz.continuousWithinAt.eventually (hU.mem_nhds (hqeq.symm ▸ hzU))
      filter_upwards [hnear,self_mem_nhdsWithin] with y hy hyD
      exact hJL ⟨hy,hqQ hyD.1⟩
    exact (hL.contDiffAt.comp_contDiffWithinAt z hqz).congr_of_eventuallyEq_of_mem he hzD
end VM03CapV437RawInnerPolar
namespace VM03CapV437RawInnerPolar
private theorem cone_polar_identity (β : E2 → E2) (r : ℝ) (hr : 0≤r) (u : E2) (hu : ‖u‖=1) :
    ‖r • u‖ • β (‖r • u‖⁻¹ • (r • u))=r • β u := by
  rcases hr.eq_or_lt with hr|hr
  · subst r
    simp
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hu,mul_one,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]

private theorem inner_polar_tile_transport
    (Q : Set E2) (hQc : Convex ℝ Q) (hQ0 : 0∈interior Q)
    (J : E2 → E2) (hJs : ∀ x∈interior Q,ContDiffAt ℝ 1 J x)
    (S : Set E2)
    (hJb : ∀ x∈frontier Q,x∉S → ∃ (U : Set E2) (L : E2 →ᵃ[ℝ] E2),
      IsOpen U ∧ x∈U ∧ EqOn J L (U∩Q))
    (C β : E2 → E2) (γ : ℝ → E2) (u : ℝ → E2)
    (hu : ∀ t,‖u t‖=1) (hC : ∀ x,C x=‖x‖ • β (‖x‖⁻¹ • x))
    (hβ : ∀ t,β (u t)=γ t) (a l v : ℝ) (ha : 0<a)
    (hγ : ContDiffOn ℝ ∞ γ (Icc l v))
    (hγQ : ∀ t∈Icc l v,γ t∈frontier Q∩Q)
    (hγS : ∀ t∈Ioo l v,γ t∉S) :
    ContDiffOn ℝ 1 (fun z : ℝ×ℝ => J (C (a⁻¹ • (z.1 • u z.2))))
      ((Icc (0:ℝ) a ×ˢ Icc l v) \ (({0,a}:Set ℝ) ×ˢ ({l,v}:Set ℝ))) := by
  apply (inner_polar_tile Q hQc hQ0 J hJs S hJb γ a l v ha hγ hγQ hγS).congr
  intro z hz
  congr 1
  rw [hC,smul_smul,cone_polar_identity β _ (mul_nonneg (inv_nonneg.mpr ha.le) hz.1.1.1) _ (hu _),hβ]
  rw [div_eq_inv_mul]
end VM03CapV437RawInnerPolar
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
namespace VM03CapV437RawPolarGrid
private theorem polar_grid_assembly
    (H G F w : E2 → E2) (a b : ℝ) (ha : 0<a) (hab : a<b) (hb : b<1)
    (hw : ContDiff ℝ 1 w)
    (hsmall : EqOn H (fun x => G (a⁻¹ • x)) (closedBall 0 a))
    (hlarge : EqOn H F {x | a ≤ ‖x‖}) (hout : EqOn F w {x | b ≤ ‖x‖})
    (m : ℕ) (t : Fin (m+1) → ℝ)
    (hinner : ∀ j : Fin m,ContDiffOn ℝ 1
      (fun z : ℝ×ℝ => G (a⁻¹ • (z.1 • unitCircleParameter z.2)))
      ((Icc (0:ℝ) a ×ˢ Icc (t j.castSucc) (t j.succ)) \
        (({0,a}:Set ℝ) ×ˢ ({t j.castSucc,t j.succ}:Set ℝ))))
    (hannulus : ∀ j : Fin m,ContDiffOn ℝ 1
      (fun z : ℝ×ℝ => F (z.1 • unitCircleParameter z.2))
      (Icc a b ×ˢ Icc (t j.castSucc) (t j.succ))) :
    ∃ r : Fin 4 → ℝ,StrictMono r ∧ r 0=0 ∧ 0<r 3 ∧ r 3<1 ∧
      (∀ x,r 3 ≤ ‖x‖ → ContDiffAt ℝ 1 H x) ∧
      ∀ (i : Fin 3) (j : Fin m),ContDiffOn ℝ 1
        (fun z : ℝ×ℝ => H (z.1 • unitCircleParameter z.2))
        ((Icc (r i.castSucc) (r i.succ) ×ˢ Icc (t j.castSucc) (t j.succ)) \
          (({r i.castSucc,r i.succ}:Set ℝ) ×ˢ ({t j.castSucc,t j.succ}:Set ℝ))) := by
  let c := (b+1)/2
  have hbc : b<c := by dsimp [c]; linarith
  have hc : c<1 := by dsimp [c]; linarith
  let r : Fin 4 → ℝ := ![0,a,b,c]
  have hr : StrictMono r := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [r] at * <;> linarith
  have hnorm (s z : ℝ) (hs : 0 ≤ s) : ‖s • unitCircleParameter z‖=s := by
    have hu : ‖unitCircleParameter z‖=1 := by
      have hh : ‖unitCircleParameter z‖^2=1 := by
        rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
        exact Real.cos_sq_add_sin_sq z
      nlinarith [norm_nonneg (unitCircleParameter z)]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs,hu,mul_one]
  have hHout : EqOn H w {x | b ≤ ‖x‖} := fun x hx =>
    (hlarge (hab.le.trans hx)).trans (hout hx)
  have hwpolar : ContDiff ℝ 1 (fun z : ℝ×ℝ => w (z.1 • unitCircleParameter z.2)) := by
    have hu : ContDiff ℝ 1 unitCircleParameter := by
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp
      apply contDiff_pi.mpr
      intro i
      fin_cases i <;> simp [unitCircleParameter] <;> fun_prop
    exact hw.comp (contDiff_fst.smul (hu.comp contDiff_snd))
  refine ⟨r,hr,rfl,?_,hc,?_,?_⟩
  · change 0<c
    linarith
  · intro x hx
    apply hw.contDiffAt.congr_of_eventuallyEq
    have hbx : b<‖x‖ := hbc.trans_le hx
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hbx] with y hy
    exact hHout hy.le
  · intro i j
    fin_cases i
    · apply (hinner j).congr
      intro z hz
      exact hsmall (mem_closedBall_zero_iff.mpr (by rw [hnorm z.1 z.2 hz.1.1.1]; exact hz.1.1.2))
    · apply ((hannulus j).mono sdiff_subset).congr
      intro z hz
      exact hlarge (by change a ≤ ‖z.1 • unitCircleParameter z.2‖; rw [hnorm z.1 z.2 (ha.le.trans hz.1.1.1)]; exact hz.1.1.1)
    · apply hwpolar.contDiffOn.congr
      intro z hz
      exact hHout (by change b ≤ ‖z.1 • unitCircleParameter z.2‖; rw [hnorm z.1 z.2 ((ha.trans hab).le.trans hz.1.1.1)]; exact hz.1.1.1)
end VM03CapV437RawPolarGrid
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
namespace VM03CapV437RawCompact
private theorem compact_smooth_extension (w : E2 → E2) (hw : ContDiff ℝ ∞ w) :
    ∃ v : E2 → E2, ContDiff ℝ ∞ v ∧ (∃ K : NNReal,LipschitzWith K v) ∧
      EqOn v w (closedBall 0 2) := by
  let b : ContDiffBump (0:E2) := {rIn := 2,rOut := 3,rIn_pos := by norm_num,rIn_lt_rOut := by norm_num}
  let v : E2 → E2 := fun x => b x • w x
  have hv : ContDiff ℝ ∞ v := b.contDiff.smul hw
  have hvs : HasCompactSupport v := b.hasCompactSupport.smul_right
  refine ⟨v,hv,hv.lipschitzWith_of_hasCompactSupport hvs (by simp),?_⟩
  intro x hx
  have hb : b x=1 := b.one_of_mem_closedBall hx
  simp only [v,hb,one_smul]

private theorem compact_collar_preservation
    (w : E2 → E2) (hw : ContDiff ℝ ∞ w) (η : ℝ) (hη : η<1) :
    ∃ v : E2 → E2, ContDiff ℝ ∞ v ∧ (∃ K : NNReal,LipschitzWith K v) ∧
      EqOn v w (closedBall 0 2) ∧
      ∀ x : E2, |‖x‖-1|<η → v x=w x ∧ fderiv ℝ v x=fderiv ℝ w x := by
  obtain ⟨v,hv,hvL,he⟩ := compact_smooth_extension w hw
  refine ⟨v,hv,hvL,he,?_⟩
  intro x hx
  have hx2 : ‖x‖<2 := by have hh := (abs_lt.mp hx).2; linarith
  have hxball : x∈ball (0:E2) 2 := mem_ball_zero_iff.mpr hx2
  have hev : v =ᶠ[𝓝 x] w := by
    filter_upwards [isOpen_ball.mem_nhds hxball] with y hy
    exact he (ball_subset_closedBall hy)
  exact ⟨hev.self_of_nhds,hev.fderiv_eq⟩
end VM03CapV437RawCompact
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open Schoenflies DifferentialGeometry.Topology.PiecewiseLinear
namespace VM03CapV437
-- Internal assembly consumer. The relative PL producer remains an owned proof obligation,
-- not an added premise of the original sharp comparator.
private theorem actual_raw_cap_of_relative_PL
    (hPL : ∀ (K : Geometry.SimplicialComplex ℝ E2) [Finite K.faces],
      IsPLBall 2 K.space → Convex ℝ K.space → ∀ (F : E2 → E2),
      IsPiecewiseAffineOn F K.space → InjOn F K.space →
      ∃ J : E2 → E2,(∃ L : NNReal,LipschitzWith L J) ∧ InjOn J K.space ∧
        J '' K.space=F '' K.space ∧ EqOn J F (frontier K.space) ∧
        (∀ x∈interior K.space,ContDiffAt ℝ 1 J x) ∧
        ∃ S : Finset E2,(S:Set E2) ⊆ frontier K.space ∧
          ∀ x∈frontier K.space,x∉(S:Set E2) → ∃ (U : Set E2) (L : E2 →ᵃ[ℝ] E2),
            IsOpen U ∧ x∈U ∧ EqOn J L (U∩K.space))
    (R : ℝ) (Ω : SmoothFlatJordanDomain R) (w : E2 → E2) (η : ℝ)
    (hw : ContDiff ℝ ∞ w) (hwL : ∃ K : NNReal,LipschitzWith K w)
    (hb : ∀ t,w (unitCircleParameter t)=Ω.boundary.gamma t)
    (hη0 : 0<η) (hη1 : η<1)
    (hi : InjOn w {x : E2 | |‖x‖-1|<η})
    (hdet : ∀ x : E2,|‖x‖-1|<η → (fderiv ℝ w x).det≠0)
    (hinward : ∀ x : E2,1-η<‖x‖ → ‖x‖<1 → w x∈Ω.domain) :
    ∃ (H : E2 → E2) (b : ℝ) (m : ℕ) (_ : 0 < m) (r : Fin 4 → ℝ) (t : Fin (m+1) → ℝ),
      (∃ L : NNReal,LipschitzWith L H) ∧ InjOn H (closedBall 0 1) ∧
      H '' ball 0 1=Ω.domain ∧
      (∀ z,H (unitCircleParameter z)=Ω.boundary.gamma z) ∧
      EqOn H w {x | b ≤ ‖x‖} ∧ b<1 ∧
      StrictMono r ∧ StrictMono t ∧ r 0=0 ∧ 0<r 3 ∧ r 3<1 ∧
      t 0=0 ∧ t (Fin.last m)=2*Real.pi ∧
      (∀ x,r 3 ≤ ‖x‖ → ContDiffAt ℝ 1 H x) ∧
      ∀ (i : Fin 3) (j : Fin m),ContDiffOn ℝ 1
        (fun z : ℝ×ℝ => H (z.1 • unitCircleParameter z.2))
        ((Icc (r i.castSucc) (r i.succ) ×ˢ Icc (t j.castSucc) (t j.succ)) \
          (({r i.castSucc,r i.succ}:Set ℝ) ×ˢ ({t j.castSucc,t j.succ}:Set ℝ))) := by
  classical
  let r₀ := 1-η/2
  have hr₀ : 1-η<r₀ := by dsimp [r₀]; linarith
  have hr₀1 : r₀<1 := by dsimp [r₀]; linarith
  obtain ⟨N,ρ,hN,hρ,hρp,hρb,hρv,hcar,hpieces⟩ :=
    support_BoundaryReparameterization_1 w η r₀ hw hη0 hη1 hr₀ hr₀1 hi hdet
  obtain ⟨n,P,hPcar,hPball⟩ := support_SamePolygon_1 R Ω w η hw.continuous hb hη1 hi
    ρ hρ hρp hρb N (by omega)
    (fun i => w (r₀ • unitCircleParameter ((i:ℝ)*(2*Real.pi/N)))) hcar
  have hPJ : IsJordanCurve P.carrier := isJordanCurve_of_isPLSphere_one (closedPolygon_isPLSphere P)
  have hΓ : IsJordanCurve (frontier Ω.domain) := by
    rw [← Ω.boundary.image]
    exact periodic_jordan Ω.boundary.gamma Ω.boundary.smooth.continuous Ω.boundary.periodic
      (fun t u he => (Ω.boundary.simple t u).mp he)
  have hPV : P.carrier ⊆ Ω.domain := by
    rw [hPcar]
    rintro y ⟨t,rfl⟩
    have hρpos : 0<ρ t := by linarith [(hρb t).1]
    have hn : ‖ρ t • unitCircleParameter t‖=ρ t := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hρpos,circle_norm,mul_one]
    apply hinward
    · rw [hn]; exact (hρb t).1
    · rw [hn]; exact (hρb t).2
  have hinside : closure (inside P.carrier) ⊆ Ω.domain :=
    inner_polygon_subset_domain Ω.domain P.carrier Ω.open_domain Ω.connected_domain Ω.bounded_domain
      hΓ hPJ hPV
  obtain ⟨A₀,hA₀c,hA₀h,hA₀u,hA₀r⟩ := angular_profile ρ hρ hρp
  have hA₀ (x : E2) : 1-η<A₀ x ∧ A₀ x<1 := by
    obtain ⟨t,ht⟩ := hA₀r x
    rw [ht]
    exact hρb t
  obtain ⟨B,hBc,hBb,hBtrace⟩ := sphere_boundary_bijection w η A₀ ρ hw.continuous hη1 hi hA₀c hA₀ hA₀u
  let D := closure (inside P.carrier)
  have hB : BijOn B (sphere 0 1) (frontier D) := by
    dsimp [D]
    rw [frontier_closure_inside_of_isPLSphere_one (closedPolygon_isPLSphere P),hPcar]
    exact hBb
  obtain ⟨K,L,C,G₀,hKfin,hKconv,hKcomp,hK0,hKball,hL,hCc,hCb,hCclosed,hCopen,
    hG₀formula,hG₀c,hG₀closed,hG₀open,hG₀trace,hCformula,hβbij,hCfront⟩ :=
    VM03CapV437InnerTracked.inner_pl_disk_with_prescribed_boundary D hPball isClosed_closure B hBc hB
  letI : Finite K.faces := hKfin.to_subtype
  obtain ⟨J,⟨KJ,hJL⟩,hJi,hJim,hJboundary,hJs,S,hS,hJb⟩ :=
    hPL K hKball hKconv L hL.isPiecewiseAffineOn hL.bijOn.injOn
  let V := invFunOn L K.space
  let β := V ∘ B
  let γ := fun t => V (w (ρ t • unitCircleParameter t))
  have hV : IsPiecewiseAffineOn V D := hL.symm.isPiecewiseAffineOn
  have hγD : range (fun t => w (ρ t • unitCircleParameter t)) ⊆ D := by
    rw [← hPcar]
    intro x hx
    exact frontier_subset_closure (by
      rwa [← (jordan_curve_theorem hPJ).frontier_inside] at hx)
  obtain ⟨m₀,hm₀,t₀,ht₀,ht₀0,ht₀T,hgrid₀,KC,hCL⟩ :=
    VM03CapV437RawRegular.actual_boundary_regular_grid w r₀ ρ N hN B hBb.injOn hBtrace
      (fun i => by
        obtain ⟨hρs,hρL,τ,hτs,hτL,him,ha,hb,he⟩ := hpieces i
        exact ⟨hρs,τ,hτs,him,ha,hb,he⟩) V D hV hγD
  have hβtrace (t : ℝ) : β (unitCircleParameter t)=γ t := congrArg V (hBtrace t)
  obtain ⟨m,hm,t,ht,ht0,htT,hgrid⟩ :=
    VM03CapV437RawRegular.regular_grid_avoid_boundary_vertices β hβbij.injOn γ ρ hβtrace
      m₀ hm₀ t₀ ht₀ ht₀0 ht₀T hgrid₀ S
  have hCL' : LipschitzWith KC C := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [hCformula,hCformula]
    exact hCL.dist_le_mul x y
  obtain ⟨a,b,ha,hab,hb1,A,F,hAu,hA,hAc,hAh,hFc,hFb,hFtrace,hFout,⟨KF,hFL⟩,hFpolar⟩ :=
    VM03CapV437RawRegular.support_RegularAnnular w η ρ hw hwL hη0 hη1 hi hρ hρp hρb
      m t ht ht0 htT (fun i => (hgrid i).2.1)
  let G := J ∘ C
  have hG₀trace' : ∀ x∈sphere 0 1,L (C x)=B x := by
    intro x hx
    rw [← hG₀formula]
    exact hG₀trace hx
  obtain ⟨hGclosed,hGopen,hGtrace⟩ := VM03CapV437RawReplacement.relative_inner_replacement
    K.space D hKcomp.isClosed isClosed_closure L J C B hL hJi hJim hJboundary
      hCclosed hCopen hCfront hG₀trace'
  change EqOn G B (sphere 0 1) at hGtrace
  have hGL : LipschitzWith (KJ*KC) G := hJL.comp hCL'
  have hGc : ContinuousOn G (closedBall 0 1) := hGL.continuous.continuousOn
  have ha1 : a<1 := hab.trans hb1
  have hAb (x : E2) : 1-η<A x ∧ A x<1 := ⟨(hA x).1,(hA x).2.trans hb1⟩
  have hApos (x : E2) : 0<A x := by linarith [(hA x).1]
  have hI : interior (closure (inside P.carrier))=inside P.carrier := by
    apply Subset.antisymm
    · intro x hx
      have hm := interior_subset hx
      rw [(IsRegionOf.inside P.carrier).closure_eq (jordan_curve_theorem hPJ)] at hm
      apply hm.resolve_right
      intro hxP
      have hf : x ∈ frontier (closure (inside P.carrier)) := by
        rwa [frontier_closure_inside_of_isPLSphere_one (closedPolygon_isPLSphere P)]
      exact hf.2 hx
    · have hh := interior_mono (subset_closure (s:=inside P.carrier))
      rwa [(jordan_curve_theorem hPJ).isOpen_inside.interior_eq] at hh
  have hGim : G '' ball 0 1=inside P.carrier := hGopen.image_eq.trans hI
  have hseam : ∀ x : E2, ‖x‖=a → G (a⁻¹ • x)=F x := by
    intro x hx
    have hn : a⁻¹ • x ∈ sphere 0 1 := by simp [norm_smul,Real.norm_eq_abs,abs_of_pos ha,hx,ha.ne']
    obtain ⟨t,ht⟩ := circle_surjective (a⁻¹ • x) hn
    have he : a • unitCircleParameter t=x := by rw [ht,smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
    rw [← ht,hGtrace (mem_sphere_zero_iff_norm.mpr (circle_norm t)),hBtrace,← hFtrace,he]
  obtain ⟨H,hHc,hHsmall,hHlarge,hHclosed,hHopen⟩ := disk_annulus_glue a ha ha1 G F hGc hFc hseam
  have hJdata : P.carrier=w '' {x : E2 | ‖x‖=A x} :=
    hPcar.trans (radial_boundary_level w A ρ hApos hAh hAu)
  have hout : ∀ x : E2, A x < ‖x‖ → ‖x‖ ≤ 1 → w x ∈ outside P.carrier :=
    radial_annular_image_outside w η A P.carrier Ω.domain hw.continuous hη1 hi hAb hAh
      hPJ hJdata hinside (by
        intro x hx
        obtain ⟨t,rfl⟩ := circle_surjective x (mem_sphere_zero_iff_norm.mpr hx)
        rw [hb]
        have hf : Ω.boundary.gamma t ∈ frontier Ω.domain := Ω.boundary.image ▸ mem_range_self t
        rw [Ω.open_domain.frontier_eq] at hf
        exact hf.2)
  have hdis : Disjoint (G '' ball 0 1) (F '' {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ 1}) := by
    rw [hGim,hFb.image_eq]
    apply disjoint_left.mpr
    rintro y hy ⟨x,hx,rfl⟩
    rcases hx.1.eq_or_lt with he | he
    · exact inside_subset_compl hy (hJdata.symm ▸ mem_image_of_mem w (show x ∈ {x | ‖x‖=A x} from he.symm))
    · exact disjoint_left.mp disjoint_inside_outside hy (hout x he hx.2)
  have hHi : InjOn H (closedBall 0 1) := disk_annulus_glue_injective a ha ha1 G F H
    hGclosed.injOn hFb.injOn hHsmall hHlarge hdis
  have hHout : EqOn H w {x | b ≤ ‖x‖} := by
    intro x hx
    exact (hHlarge (hab.le.trans hx)).trans (hFout hx)
  have hHtrace (t : ℝ) : H (unitCircleParameter t)=Ω.boundary.gamma t := by
    apply (hHout (by change b ≤ ‖unitCircleParameter t‖; rw [circle_norm]; exact hb1.le)).trans
    exact hb t
  have hboundary : H '' sphere 0 1=frontier Ω.domain := by
    rw [← Ω.boundary.image]
    apply Subset.antisymm
    · rintro y ⟨x,hx,rfl⟩
      obtain ⟨t,rfl⟩ := circle_surjective x hx
      exact ⟨t,(hHtrace t).symm⟩
    · rintro y ⟨t,rfl⟩
      exact ⟨unitCircleParameter t,mem_sphere_zero_iff_norm.mpr (circle_norm t),hHtrace t⟩
  obtain ⟨hHo,hHconn,hHbounded,hHfront⟩ := embedded_disk_frontier H hHc hHi
  have hHV : H '' ball 0 1=Ω.domain := by
    exact (bounded_region_eq_inside _ _ hHo hHconn hHbounded hΓ (hHfront.trans hboundary)).trans
      (bounded_region_eq_inside Ω.domain (frontier Ω.domain) Ω.open_domain Ω.connected_domain
        Ω.bounded_domain hΓ rfl).symm

  have hGscale : LipschitzWith ((KJ*KC)*‖a⁻¹‖₊) (fun x : E2 => G (a⁻¹ • x)) :=
    hGL.comp (lipschitzWith_smul (a⁻¹))
  have hHL0 : LipschitzOnWith ((KJ*KC)*‖a⁻¹‖₊) H {x | ‖x‖ ≤ a} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hHsmall (mem_closedBall_zero_iff.mpr hx),hHsmall (mem_closedBall_zero_iff.mpr hy)]
    exact hGscale.dist_le_mul x y
  have hHL1 : LipschitzOnWith KF H {x | a ≤ ‖x‖} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hHlarge hx,hHlarge hy]
    exact hFL.dist_le_mul x hx y hy
  have hHL : LipschitzWith (max ((KJ*KC)*‖a⁻¹‖₊) KF) H :=
    VM03CapV437RawRegular.radial_lipschitz_glue H a _
      (hHL0.weaken (le_max_left _ _)) (hHL1.weaken (le_max_right _ _))
  have hinner (j : Fin m) : ContDiffOn ℝ 1
      (fun z : ℝ×ℝ => G (a⁻¹ • (z.1 • unitCircleParameter z.2)))
      ((Icc (0:ℝ) a ×ˢ Icc (t j.castSucc) (t j.succ)) \
        (({0,a}:Set ℝ) ×ˢ ({t j.castSucc,t j.succ}:Set ℝ))) := by
    apply VM03CapV437RawInnerPolar.inner_polar_tile_transport K.space hKconv
      (mem_interior_iff_mem_nhds.mpr hK0) J hJs (S:Set E2) hJb C β γ
      unitCircleParameter circle_norm hCformula hβtrace a (t j.castSucc) (t j.succ) ha
      (hgrid j).1
    · intro z hz
      have hβfront : β (unitCircleParameter z)∈frontier K.space :=
        hβbij.mapsTo (mem_sphere_zero_iff_norm.mpr (circle_norm z))
      rw [hβtrace] at hβfront
      exact ⟨hβfront,(frontier_subset_closure.trans hKcomp.isClosed.closure_eq.subset) hβfront⟩
    · exact (hgrid j).2.2
  obtain ⟨r,hr,hr0,hr3,hr31,hHoutcd,hHtiles⟩ :=
    VM03CapV437RawPolarGrid.polar_grid_assembly H G F w a b ha hab hb1
      (hw.of_le (by simp)) hHsmall hHlarge hFout m t hinner
      (fun j => (hFpolar j).of_le (by simp))
  exact ⟨H,b,m,hm,r,t,⟨_,hHL⟩,hHi,hHV,hHtrace,hHout,hb1,hr,ht,hr0,hr3,hr31,
    ht0,htT,hHoutcd,hHtiles⟩
end VM03CapV437

namespace VM03CapV437
-- Internal consumer only: both construction producers remain separate proof obligations.
private theorem actual_c1_cap_of_producers
    (hPL : ∀ (K : Geometry.SimplicialComplex ℝ E2) [Finite K.faces],
      IsPLBall 2 K.space → Convex ℝ K.space → ∀ (F : E2 → E2),
      IsPiecewiseAffineOn F K.space → InjOn F K.space →
      ∃ J : E2 → E2,(∃ L : NNReal,LipschitzWith L J) ∧ InjOn J K.space ∧
        J '' K.space=F '' K.space ∧ EqOn J F (frontier K.space) ∧
        (∀ x∈interior K.space,ContDiffAt ℝ 1 J x) ∧
        ∃ S : Finset E2,(S:Set E2) ⊆ frontier K.space ∧
          ∀ x∈frontier K.space,x∉(S:Set E2) → ∃ (U : Set E2) (L : E2 →ᵃ[ℝ] E2),
            IsOpen U ∧ x∈U ∧ EqOn J L (U∩K.space))
    (hPolar : ∀ (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
  (r : Fin (n+1) → ℝ) (t : Fin (m+1) → ℝ)
  (hr : StrictMono r) (ht : StrictMono t),
  r 0=0 → 0 < r (Fin.last n) → r (Fin.last n) < 1 →
  t 0=0 → t (Fin.last m)=2*Real.pi →
  ∀ (H : E2 → E2), (∃ L : NNReal, LipschitzWith L H) →
  (∀ x, r (Fin.last n) ≤ ‖x‖ → ContDiffAt ℝ 1 H x) →
  (∀ (i : Fin n) (j : Fin m),
    ContDiffOn ℝ 1 (fun z : ℝ×ℝ => H (z.1 • unitCircleParameter z.2))
      ((Icc (r i.castSucc) (r i.succ) ×ˢ Icc (t j.castSucc) (t j.succ)) \
        (({r i.castSucc,r i.succ}:Set ℝ) ×ˢ ({t j.castSucc,t j.succ}:Set ℝ)))) →
  ∃ (T : E2 → E2) (b : ℝ), r (Fin.last n) < b ∧ b < 1 ∧
    Bijective T ∧ ContDiff ℝ 1 T ∧ (∃ L : NNReal, LipschitzWith L T) ∧
    EqOn T id {x | b ≤ ‖x‖} ∧ T '' ball 0 1=ball 0 1 ∧
    ContDiff ℝ 1 (H ∘ T) ∧ (∃ L : NNReal, LipschitzWith L (H ∘ T)))

    (R : ℝ) (Ω : SmoothFlatJordanDomain R) (w : E2 → E2) (η : ℝ)
    (hw : ContDiff ℝ ∞ w)
    (hb : ∀ t,w (unitCircleParameter t)=Ω.boundary.gamma t)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hi : InjOn w {x : E2 | |‖x‖-1| < η})
    (hdet : ∀ x : E2,|‖x‖-1| < η → (fderiv ℝ w x).det≠0)
    (hinward : ∀ x : E2,1-η < ‖x‖ → ‖x‖ < 1 → w x∈Ω.domain) :
    ∃ q : E2 → E2,ContDiff ℝ 1 q ∧ (∃ L : NNReal,LipschitzWith L q) ∧
      InjOn q (closedBall 0 1) ∧ q '' ball 0 1=Ω.domain ∧
      ∀ z,q (unitCircleParameter z)=Ω.boundary.gamma z := by
  obtain ⟨v,hv,hvL,he,hvd⟩ := VM03CapV437RawCompact.compact_collar_preservation w hw η hη1
  have hvb (z : ℝ) : v (unitCircleParameter z)=Ω.boundary.gamma z := by
    rw [he (mem_closedBall_zero_iff.mpr (by rw [circle_norm]; norm_num)),hb]
  have hvi : InjOn v {x : E2 | |‖x‖-1| < η} := by
    intro x hx y hy hxy
    rw [(hvd x hx).1,(hvd y hy).1] at hxy
    exact hi hx hy hxy
  have hvdet (x : E2) (hx : |‖x‖-1| < η) : (fderiv ℝ v x).det≠0 := by
    rw [(hvd x hx).2]
    exact hdet x hx
  have hvin (x : E2) (hx : 1-η < ‖x‖) (hx1 : ‖x‖ < 1) : v x∈Ω.domain := by
    rw [(hvd x (abs_lt.mpr ⟨by linarith,by linarith⟩)).1]
    exact hinward x hx hx1
  obtain ⟨H,b₀,m,hm,r,t,hHL,hHi,hHim,hHtrace,hHout,hb₀,hr,ht,hr0,hr3,hr31,
    ht0,htT,hHo,hHtiles⟩ :=
    actual_raw_cap_of_relative_PL hPL R Ω v η hv hvL hvb hη0 hη1 hvi hvdet hvin
  obtain ⟨T,b,hbr,hb1,hTbij,hTs,hTL,hTout,hTim,hqcd,hqL⟩ :=
    hPolar 3 m (by norm_num) hm r t hr ht hr0 hr3 hr31 ht0 htT H hHL hHo hHtiles
  have hTcircle (x : E2) (hx : ‖x‖=1) : T x=x :=
    hTout (by change b ≤ ‖x‖; rw [hx]; exact hb1.le)
  have hTclosed : MapsTo T (closedBall 0 1) (closedBall 0 1) := by
    intro x hx
    have hxn := mem_closedBall_zero_iff.mp hx
    rcases hxn.eq_or_lt with hx1 | hx1
    · rw [hTcircle x hx1]
      exact hx
    · exact ball_subset_closedBall (hTim ▸ mem_image_of_mem T (mem_ball_zero_iff.mpr hx1))
  refine ⟨H ∘ T,hqcd,hqL,?_,?_,?_⟩
  · intro x hx y hy hexy
    exact hTbij.injective (hHi (hTclosed hx) (hTclosed hy) hexy)
  · rw [image_comp,hTim,hHim]
  · intro z
    change H (T (unitCircleParameter z))=Ω.boundary.gamma z
    rw [hTcircle _ (circle_norm z),hHtrace]
end VM03CapV437
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CountGeometry
open SeifertSurfaces.AppendixACoordinates

set_option maxHeartbeats 800000 in
private theorem support_PaidInward (R : ℝ) (Ω : SmoothFlatJordanDomain R) :
    ∃ w : E2 → E2, ∃ η : ℝ,
      ContDiff ℝ ∞ w ∧
      (∀ t, w (unitCircleParameter t) = Ω.boundary.gamma t) ∧
      0 < η ∧ η < 1 ∧
      InjOn w {x : E2 | |‖x‖ - 1| < η} ∧
      (∀ x : E2, |‖x‖ - 1| < η → (fderiv ℝ w x).det ≠ 0) ∧
      (∀ x : E2, 1 - η < ‖x‖ → ‖x‖ < 1 → w x ∈ Ω.domain) := by
  have compatible :
    ∃ v : E2 → E2, ∃ U : Set E2, ∃ δ : ℝ,
      ContDiff ℝ ∞ v ∧
      (∀ t, v (unitCircleParameter t) = Ω.boundary.gamma t) ∧
      IsOpen U ∧ Metric.sphere (0 : E2) 1 ⊆ U ∧ InjOn v U ∧
      (∀ x ∈ U, 0 < (fderiv ℝ v x).det) ∧
      0 < δ ∧ δ < 1 ∧ {x : E2 | |‖x‖ - 1| < δ} ⊆ U ∧
      ((∀ x : E2, 1 - δ < ‖x‖ → ‖x‖ < 1 → v x ∈ Ω.domain) ∨
       (∀ x : E2, 1 < ‖x‖ → ‖x‖ < 1 + δ → v x ∈ Ω.domain)) := by
    have collar :
      ∃ v : E2 → E2, ∃ U : Set E2, ∃ δ : ℝ,
        ContDiff ℝ ∞ v ∧ WeakMonotoneBoundaryLift Ω (fun t => t) 1 ∧
        (∀ t, v (unitCircleParameter t) = Ω.boundary.gamma t) ∧
        IsOpen U ∧ Metric.sphere (0 : E2) 1 ⊆ U ∧ InjOn v U ∧
        (∀ x ∈ U, 0 < (fderiv ℝ v x).det) ∧
        0 < δ ∧ Metric.cthickening δ (Metric.sphere (0 : E2) 1) ⊆ U := by
      have boundary_local :
        ∃ v : E2 → E2, ContDiff ℝ ∞ v ∧
          WeakMonotoneBoundaryLift Ω (fun t => t) 1 ∧
          (∀ t, v (unitCircleParameter t) = Ω.boundary.gamma t) ∧
          (∀ t, 0 < (fderiv ℝ v (unitCircleParameter t)).det) ∧
          ∀ t, ∃ U : Set E2, IsOpen U ∧ unitCircleParameter t ∈ U ∧ InjOn v U  := by
        have collar : ∃ v : E2 → E2, ContDiff ℝ ∞ v ∧
            (∀ t, v (unitCircleParameter t) = Ω.boundary.gamma t) ∧
            ∀ t, 0 < (fderiv ℝ v (unitCircleParameter t)).det := by
          have angular (gamma : ℝ → E2) (hgamma : ContDiff ℝ ∞ gamma)
              (hperiodic : Periodic gamma (2 * Real.pi)) :
              ∃ w : E2 → E2, ContDiff ℝ ∞ w ∧
                (∀ x ∈ Metric.ball (0 : E2) (1 / 4), w x = 0) ∧
                ∀ r t : ℝ, 1 / 2 ≤ r → w (r • unitCircleParameter t) = gamma t := by
            let e : E2 ≃L[ℝ] ℂ :=
              ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
                (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).trans Complex.equivRealProdCLM.symm
            let b : ContDiffBump (0 : E2) := {
              rIn := 1 / 4
              rOut := 1 / 2
              rIn_pos := by norm_num
              rIn_lt_rOut := by norm_num }
            let v : E2 → E2 := fun x => (1 - b x) • gamma (Complex.arg (e x))
            have hmod (a d : ℝ) (heq : (a : Real.Angle) = (d : Real.Angle)) :
                gamma a = gamma d := by
              obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp heq
              have hp := hperiodic.zsmul k d
              rw [zsmul_eq_mul] at hp
              have ha : a = d + (k : ℝ) * (2 * Real.pi) := by nlinarith [hk]
              rw [ha]
              exact hp
            have hneg (z : ℂ) (hz : z ≠ 0) :
                gamma (Complex.arg (-z) + Real.pi) = gamma (Complex.arg z) := by
              apply hmod
              rw [Real.Angle.coe_add, Complex.arg_neg_coe_angle hz, add_assoc,
                ← Real.Angle.coe_add, ← two_mul, Real.Angle.coe_two_pi, add_zero]
            have harg (z : ℂ) (hz : z ∈ Complex.slitPlane) : ContDiffAt ℝ ∞ Complex.arg z := by
              have hl : ContDiffAt ℝ ∞ Complex.log z := (Complex.contDiffAt_log hz).restrict_scalars ℝ
              have hi : ContDiffAt ℝ ∞ (fun z : ℂ => (Complex.log z).im) z :=
                Complex.imCLM.contDiff.contDiffAt.comp z hl
              simpa only [Complex.log_im] using hi
            have haway (x : E2) (hx : x ≠ 0) :
                ContDiffAt ℝ ∞ (fun x => gamma (Complex.arg (e x))) x := by
              have he : e x ≠ 0 := fun he => hx (e.injective (by simpa using he))
              by_cases hs : e x ∈ Complex.slitPlane
              · exact hgamma.contDiffAt.comp x ((harg (e x) hs).comp x e.contDiff.contDiffAt)
              · have hns : -e x ∈ Complex.slitPlane := by
                  change 0 < (-e x).re ∨ (-e x).im ≠ 0
                  change ¬(0 < (e x).re ∨ (e x).im ≠ 0) at hs
                  push_neg at hs
                  have hn : (e x).re ≠ 0 := fun hn => he (Complex.ext hn hs.2)
                  exact Or.inl (by simpa using neg_pos.mpr (lt_of_le_of_ne hs.1 hn))
                have hg : ContDiffAt ℝ ∞ (fun y => gamma (Complex.arg (-e y) + Real.pi)) x :=
                  hgamma.contDiffAt.comp x
                    (((harg (-e x) hns).comp x e.contDiff.contDiffAt.neg).add contDiffAt_const)
                apply hg.congr_of_eventuallyEq
                filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
                exact (hneg (e y) (fun he => hy (e.injective (by simpa using he)))).symm
            have hv : ContDiff ℝ ∞ v := by
              rw [contDiff_iff_contDiffAt]
              intro x
              by_cases hx : x = 0
              · subst x
                apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E2 => (0 : E2)) 0).congr_of_eventuallyEq
                filter_upwards [b.eventuallyEq_one] with y hy
                simp [v, hy]
              · exact (contDiffAt_const.sub b.contDiffAt).smul (haway x hx)
            refine ⟨v, hv, ?_, ?_⟩
            · intro x hx
              have hb : b x = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
              simp [v, hb]
            · intro r t hr
              have hn : ‖unitCircleParameter t‖ = 1 := by
                have hh : ‖unitCircleParameter t‖ ^ 2 = 1 := by
                  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
                  exact Real.cos_sq_add_sin_sq t
                nlinarith [norm_nonneg (unitCircleParameter t)]
              have hb : b (r • unitCircleParameter t) = 0 := b.zero_of_le_dist (by dsimp only [b]; simp only [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ r), hn, mul_one]; exact hr)
              simp only [v, hb, sub_zero, one_smul]
              have he : e (unitCircleParameter t) = Real.cos t + Real.sin t * Complex.I := by
                apply Complex.ext <;> simp only [e, unitCircleParameter,
                  ContinuousLinearEquiv.trans_apply, Complex.equivRealProdCLM_symm_apply,
                  Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
                  Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
                all_goals simp
              rw [map_smul, Complex.real_smul, he, Complex.ofReal_cos, Complex.ofReal_sin,
                Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod (by linarith : 0 < r)]
              exact hmod _ _ (Real.Angle.coe_toIocMod t (-Real.pi))
          let N : ℝ → E2 := fun t => (EuclideanSpace.equiv (Fin 2) ℝ).symm
            ![(deriv Ω.boundary.gamma t) 1, -(deriv Ω.boundary.gamma t) 0]
          have hdgamma : ContDiff ℝ ∞ (deriv Ω.boundary.gamma) := by
            apply ContDiff.deriv'
            simpa using Ω.boundary.smooth
          have hN : ContDiff ℝ ∞ N := by
            apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp
            apply contDiff_pi.mpr
            intro k
            fin_cases k
            · exact (EuclideanSpace.proj 1 : E2 →L[ℝ] ℝ).contDiff.comp hdgamma
            · exact ((EuclideanSpace.proj 0 : E2 →L[ℝ] ℝ).contDiff.comp hdgamma).neg
          have hdp : Periodic (deriv Ω.boundary.gamma) (2 * Real.pi) := by
            intro t
            have h1 := (Ω.boundary.smooth.differentiable (by simp) (t+2*Real.pi)).hasDerivAt.scomp t
              ((hasDerivAt_id t).add_const (2*Real.pi))
            have h2 := (Ω.boundary.smooth.differentiable (by simp) t).hasDerivAt
            have hp : (fun s => Ω.boundary.gamma (s+2*Real.pi)) = Ω.boundary.gamma := funext Ω.boundary.periodic
            have he : HasDerivAt Ω.boundary.gamma (deriv Ω.boundary.gamma (t+2*Real.pi)) t := by
              simpa only [Function.comp_def, id_eq, hp, one_smul] using h1
            exact he.unique h2
          have hNp : Periodic N (2 * Real.pi) := by
            intro t
            dsimp only [N]
            rw [hdp t]
          obtain ⟨g, hg, hgzero, hgann⟩ := angular Ω.boundary.gamma Ω.boundary.smooth Ω.boundary.periodic
          obtain ⟨n, hn, hnzero, hnann⟩ := angular N hN hNp
          let v : E2 → E2 := fun x => g x + (‖x‖ - 1) • n x
          have hv : ContDiff ℝ ∞ v := by
            rw [contDiff_iff_contDiffAt]
            intro x
            by_cases hx : x = 0
            · subst x
              apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E2 => (0 : E2)) 0).congr_of_eventuallyEq
              filter_upwards [Metric.ball_mem_nhds (0 : E2) (by norm_num : 0 < (1 / 4 : ℝ))] with y hy
              simp [v, hgzero y hy, hnzero y hy]
            · exact hg.contDiffAt.add ((contDiffAt_id.norm ℝ hx).sub contDiffAt_const |>.smul hn.contDiffAt)
          have hcn (t : ℝ) : ‖unitCircleParameter t‖ = 1 := by
            have hs : ‖unitCircleParameter t‖ ^ 2 = 1 := by
              rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
              exact Real.cos_sq_add_sin_sq t
            nlinarith [norm_nonneg (unitCircleParameter t)]
          have hradial (r t : ℝ) (hr : 1 / 2 ≤ r) :
              v (r • unitCircleParameter t) = Ω.boundary.gamma t + (r-1) • N t := by
            dsimp only [v]
            rw [hgann r t hr, hnann r t hr, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (by linarith : 0 ≤ r), hcn, mul_one]
          have hboundary (t : ℝ) : v (unitCircleParameter t) = Ω.boundary.gamma t := by
            simpa using hradial 1 t (by norm_num)
          refine ⟨v, hv, hboundary, ?_⟩
          intro t
          let T : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-Real.sin t, Real.cos t]
          have hcder : HasDerivAt unitCircleParameter T t := by
            have he : HasDerivAt (fun s : ℝ => ![Real.cos s, Real.sin s]) ![-Real.sin t, Real.cos t] t := by
              apply hasDerivAt_pi.mpr
              intro k
              fin_cases k
              · exact Real.hasDerivAt_cos t
              · exact Real.hasDerivAt_sin t
            exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t he
          have htan : fderiv ℝ v (unitCircleParameter t) T = deriv Ω.boundary.gamma t := by
            have h1 := (hv.differentiable (by simp) (unitCircleParameter t)).hasFDerivAt.comp_hasDerivAt t hcder
            have h2 := (Ω.boundary.smooth.differentiable (by simp) t).hasDerivAt
            have he : (v ∘ unitCircleParameter) = Ω.boundary.gamma := funext hboundary
            rw [he] at h1
            exact h1.unique h2
          have hrad : fderiv ℝ v (unitCircleParameter t) (unitCircleParameter t) = N t := by
            have hmap : HasFDerivAt v (fderiv ℝ v (unitCircleParameter t)) ((1 : ℝ) • unitCircleParameter t) := by
              simpa only [one_smul] using (hv.differentiable (by simp) (unitCircleParameter t)).hasFDerivAt
            have h1 := hmap.comp_hasDerivAt 1
              ((hasDerivAt_id (1 : ℝ)).smul_const (unitCircleParameter t))
            have h2 : HasDerivAt (fun r : ℝ => Ω.boundary.gamma t + (r-1) • N t) (N t) 1 := by
              have hc : HasDerivAt (fun _ : ℝ => Ω.boundary.gamma t) (0 : E2) 1 := hasDerivAt_const _ _
              have hr : HasDerivAt (fun r : ℝ => (r-1) • N t) (N t) 1 := by
                simpa only [id_eq, sub_zero, one_smul] using
                  (((hasDerivAt_id (1 : ℝ)).sub_const 1).smul_const (N t))
              convert! hc.add hr using 1 <;> simp only [zero_add]
            have he : HasDerivAt (fun r : ℝ => v (r • unitCircleParameter t)) (N t) 1 := by
              apply h2.congr_of_eventuallyEq
              filter_upwards [Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)] with r hr
              exact hradial r t hr.le
            simpa only [one_smul] using h1.unique he
          have hdet : (fderiv ℝ v (unitCircleParameter t)).det =
              (deriv Ω.boundary.gamma t 0)^2 + (deriv Ω.boundary.gamma t 1)^2 := by
            let L := fderiv ℝ v (unitCircleParameter t)
            have hc : unitCircleParameter t =
                Real.cos t • coordinateVector 2 0 + Real.sin t • coordinateVector 2 1 := by
              apply PiLp.ext
              intro k
              fin_cases k <;> simp [unitCircleParameter, coordinateVector, PiLp.single_apply]
            have hT : T = -Real.sin t • coordinateVector 2 0 + Real.cos t • coordinateVector 2 1 := by
              apply PiLp.ext
              intro k
              fin_cases k <;> simp [T, coordinateVector, PiLp.single_apply]
            have hmatrix : L.det =
                (L (coordinateVector 2 0)) 0 * (L (coordinateVector 2 1)) 1 -
                (L (coordinateVector 2 1)) 0 * (L (coordinateVector 2 0)) 1 := by
              change LinearMap.det L.toLinearMap = _
              rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
                Matrix.det_fin_two]
              rfl
            have hf : L.det = (L (unitCircleParameter t)) 0 * (L T) 1 -
                (L T) 0 * (L (unitCircleParameter t)) 1 := by
              rw [hmatrix, hc, hT, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
              simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
              linear_combination -((L (coordinateVector 2 0)) 0 * (L (coordinateVector 2 1)) 1 -
                (L (coordinateVector 2 1)) 0 * (L (coordinateVector 2 0)) 1) * Real.cos_sq_add_sin_sq t
            change L.det = _
            rw [hf]
            change (fderiv ℝ v (unitCircleParameter t) (unitCircleParameter t)) 0 *
                (fderiv ℝ v (unitCircleParameter t) T) 1 -
                (fderiv ℝ v (unitCircleParameter t) T) 0 *
                (fderiv ℝ v (unitCircleParameter t) (unitCircleParameter t)) 1 = _
            rw [hrad, htan]
            change (deriv Ω.boundary.gamma t 1) * (deriv Ω.boundary.gamma t 1) -
              (deriv Ω.boundary.gamma t 0) * (-(deriv Ω.boundary.gamma t 0)) = _
            ring
          rw [hdet]
          have hp := sq_pos_of_pos (norm_pos_iff.mpr (Ω.boundary.regular t))
          simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] using hp
        have local_inverse (v : E2 → E2) (hv : ContDiff ℝ 1 v) (x : E2)
            (hdet : (fderiv ℝ v x).det ≠ 0) :
            ∃ U : Set E2, IsOpen U ∧ x ∈ U ∧ InjOn v U := by
          let L := (fderiv ℝ v x).toLinearMap.equivOfDetNeZero hdet
          let e := L.toContinuousLinearEquiv
          have he : (e : E2 →L[ℝ] E2) = fderiv ℝ v x := by ext z; rfl
          have hd : HasFDerivAt v (e : E2 →L[ℝ] E2) x := by
            rw [he]
            exact (hv.differentiable (by norm_num) x).hasFDerivAt
          let H := hv.contDiffAt.toOpenPartialHomeomorph v hd (by norm_num)
          refine ⟨H.source, H.open_source, ?_, ?_⟩
          · exact hv.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by norm_num)
          · exact H.injOn
        obtain ⟨v, hv, hb, hd⟩ := collar
        refine ⟨v, hv, ?_, hb, hd, ?_⟩
        · refine ⟨Or.inl rfl, continuous_id, ?_, by simp⟩
          intro a b hab
          simpa only [one_mul] using hab
        · intro t
          exact local_inverse v (hv.of_le (by simp)) (unitCircleParameter t) (hd t).ne'
    
      obtain ⟨v, hv, hl, hb, hd, hloc⟩ := boundary_local
      have circle_norm (t : ℝ) : ‖unitCircleParameter t‖ = 1 := by
        have hs : ‖unitCircleParameter t‖ ^ 2 = 1 := by
          rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
          exact Real.cos_sq_add_sin_sq t
        nlinarith [norm_nonneg (unitCircleParameter t)]
      have circle_surj (x : E2) (hx : x ∈ Metric.sphere (0 : E2) 1) :
          ∃ t, unitCircleParameter t = x := by
        have hxnorm : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
        let z : ℂ := ⟨x 0, x 1⟩
        have hs : (x 0)^2 + (x 1)^2 = 1 := by
          have h := EuclideanSpace.real_norm_sq_eq x
          rw [hxnorm] at h
          simpa only [Fin.sum_univ_two, one_pow] using h.symm
        have hz : ‖z‖ = 1 := by
          have hsq : ‖z‖^2 = 1 := by
            rw [← Complex.normSq_eq_norm_sq]
            simpa [z, Complex.normSq_apply, pow_two] using hs
          nlinarith [norm_nonneg z]
        have hne : z ≠ 0 := by intro h; simp [h] at hz
        refine ⟨Complex.arg z, ?_⟩
        apply PiLp.ext
        intro j
        fin_cases j
        · change Real.cos (Complex.arg z) = x 0
          rw [Complex.cos_arg hne, hz]
          simp [z]
        · change Real.sin (Complex.arg z) = x 1
          rw [Complex.sin_arg, hz]
          simp [z]
      have hinj : InjOn v (Metric.sphere (0 : E2) 1) := by
        intro x hx y hy hxy
        obtain ⟨t, rfl⟩ := circle_surj x hx
        obtain ⟨u, rfl⟩ := circle_surj y hy
        rw [hb t, hb u] at hxy
        obtain ⟨k, hk⟩ := (Ω.boundary.simple t u).mp hxy
        have ht : t = u + (k : ℝ) * (2 * Real.pi) := by linarith
        rw [ht]
        apply PiLp.ext
        intro j
        fin_cases j
        · exact Real.cos_periodic.int_mul k u
        · exact Real.sin_periodic.int_mul k u
      obtain ⟨U, hU, hSU, hUv⟩ := hinj.exists_isOpen_superset
        (isCompact_sphere (0 : E2) 1) (fun x _ => hv.continuous.continuousAt) (by
          intro x hx
          obtain ⟨t, rfl⟩ := circle_surj x hx
          obtain ⟨V, hV, hxV, hVv⟩ := hloc t
          exact ⟨V, hV.mem_nhds hxV, hVv⟩)
      let D : Set E2 := {x | 0 < (fderiv ℝ v x).det}
      have hD : IsOpen D := by
        apply isOpen_lt continuous_const
        have hc (i j : Fin 2) : Continuous (fun x =>
            (fderiv ℝ v x (coordinateVector 2 j)) i) :=
          (EuclideanSpace.proj i).continuous.comp
            ((hv.continuous_fderiv (by simp)).clm_apply continuous_const)
        convert! ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0)) using 1
        funext x
        change LinearMap.det (fderiv ℝ v x).toLinearMap = _
        rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
          Matrix.det_fin_two]
        rfl
      have hSD : Metric.sphere (0 : E2) 1 ⊆ U ∩ D := by
        intro x hx
        obtain ⟨t, rfl⟩ := circle_surj x hx
        exact ⟨hSU hx, hd t⟩
      obtain ⟨δ, hδ, hδU⟩ := (isCompact_sphere (0 : E2) 1).exists_cthickening_subset_open
        (hU.inter hD) hSD
      exact ⟨v, U ∩ D, δ, hv, hl, hb, hU.inter hD, hSD,
        hUv.mono inter_subset_left, fun x hx => hx.2, hδ, hδU⟩
    obtain ⟨v, U, ε, hv, hl, hb, hU, hSU, hinj, hdet, hε, hεU⟩ := collar
    have circle_norm (t : ℝ) : ‖unitCircleParameter t‖ = 1 := by
      have hs : ‖unitCircleParameter t‖ ^ 2 = 1 := by
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
        exact Real.cos_sq_add_sin_sq t
      nlinarith [norm_nonneg (unitCircleParameter t)]
    have circle_surj (x : E2) (hx : ‖x‖ = 1) :
        ∃ t, unitCircleParameter t = x := by
      let z : ℂ := ⟨x 0, x 1⟩
      have hs : (x 0)^2 + (x 1)^2 = 1 := by
        have h := EuclideanSpace.real_norm_sq_eq x
        rw [hx] at h
        simpa only [Fin.sum_univ_two, one_pow] using h.symm
      have hz : ‖z‖ = 1 := by
        have hsq : ‖z‖^2 = 1 := by
          rw [← Complex.normSq_eq_norm_sq]
          simpa [z, Complex.normSq_apply, pow_two] using hs
        nlinarith [norm_nonneg z]
      have hne : z ≠ 0 := by intro he; simp [he] at hz
      refine ⟨Complex.arg z, ?_⟩
      apply PiLp.ext
      intro j
      fin_cases j
      · change Real.cos (Complex.arg z) = x 0
        rw [Complex.cos_arg hne, hz]
        simp [z]
      · change Real.sin (Complex.arg z) = x 1
        rw [Complex.sin_arg, hz]
        simp [z]
    have hcircle (t : ℝ) : unitCircleParameter t ∈ Metric.sphere (0 : E2) 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using circle_norm t
    have hpolar (x : E2) (hx : 0 < ‖x‖) :
        ∃ t, ‖x‖ • unitCircleParameter t = x := by
      have hn : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx), inv_mul_cancel₀ hx.ne']
      obtain ⟨t, ht⟩ := circle_surj _ hn
      refine ⟨t, ?_⟩
      rw [ht, smul_smul, mul_inv_cancel₀ hx.ne', one_smul]
    let δ : ℝ := min ε (1 / 2)
    have hδ : 0 < δ := lt_min hε (by norm_num)
    have hδε : δ ≤ ε := min_le_left _ _
    have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hband : {x : E2 | |‖x‖ - 1| < δ} ⊆ U := by
      intro x hx
      change |‖x‖ - 1| < δ at hx
      have hxn : 0 < ‖x‖ := by have hh := (abs_lt.mp hx).1; linarith
      obtain ⟨t, ht⟩ := hpolar x hxn
      apply hεU
      apply Metric.mem_cthickening_of_dist_le x (unitCircleParameter t) ε _ (hcircle t)
      have he : x - unitCircleParameter t = (‖x‖ - 1) • unitCircleParameter t := by
        rw [sub_smul, one_smul, ht]
      rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, circle_norm, mul_one]
      exact hx.le.trans hδε
    have havoid (x : E2) (hxU : x ∈ U) (hxn : ‖x‖ ≠ 1) :
        v x ∉ frontier Ω.domain := by
      intro hxF
      rw [← Ω.boundary.image] at hxF
      obtain ⟨t, ht⟩ := hxF
      have he : x = unitCircleParameter t :=
        hinj hxU (hSU (hcircle t)) (ht.symm.trans (hb t).symm)
      exact hxn (he ▸ circle_norm t)
    have hpre (a b : ℝ) (ha : 0 ≤ a) :
        IsPreconnected {x : E2 | a < ‖x‖ ∧ ‖x‖ < b} := by
      have hc : Continuous unitCircleParameter := by
        apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
        apply continuous_pi
        intro j
        fin_cases j
        · exact Real.continuous_cos
        · exact Real.continuous_sin
      have he : {x : E2 | a < ‖x‖ ∧ ‖x‖ < b} =
          (fun p : ℝ × ℝ => p.1 • unitCircleParameter p.2) '' (Ioo a b ×ˢ univ) := by
        ext x
        constructor
        · intro hx
          obtain ⟨t, ht⟩ := hpolar x (lt_of_le_of_lt ha hx.1)
          exact ⟨(‖x‖, t), ⟨hx, mem_univ t⟩, ht⟩
        · rintro ⟨⟨r,t⟩, ⟨hr, ht⟩, rfl⟩
          simpa only [mem_setOf_eq, mem_Ioo, norm_smul, Real.norm_eq_abs,
            abs_of_pos (lt_of_le_of_lt ha hr.1), circle_norm, mul_one] using hr
      rw [he]
      exact (isPreconnected_Ioo.prod isPreconnected_univ).image _
        (continuous_fst.smul (hc.comp continuous_snd)).continuousOn
    have hside (a b : ℝ) (ha : 0 ≤ a)
        (hsideU : {x : E2 | a < ‖x‖ ∧ ‖x‖ < b} ⊆ U)
        (hsideN : ∀ x : E2, a < ‖x‖ → ‖x‖ < b → ‖x‖ ≠ 1)
        (hx : ∃ x : E2, a < ‖x‖ ∧ ‖x‖ < b ∧ v x ∈ Ω.domain) :
        ∀ x : E2, a < ‖x‖ → ‖x‖ < b → v x ∈ Ω.domain := by
      have hc := (hpre a b ha).image v hv.continuous.continuousOn
      have hs : v '' {x : E2 | a < ‖x‖ ∧ ‖x‖ < b} ⊆ Ω.domain := by
        apply hc.subset_of_closure_inter_subset Ω.open_domain
        · obtain ⟨x, hx₁, hx₂, hxΩ⟩ := hx
          exact ⟨v x, ⟨x, ⟨hx₁, hx₂⟩, rfl⟩, hxΩ⟩
        · intro y hy
          by_contra hn
          have hf : y ∈ frontier Ω.domain := by
            rw [Ω.open_domain.frontier_eq]
            exact ⟨hy.1, hn⟩
          obtain ⟨x, hx, rfl⟩ := hy.2
          exact havoid x (hsideU hx) (hsideN x hx.1 hx.2) hf
      exact fun x hx₁ hx₂ => hs ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
    let z : E2 := unitCircleParameter 0
    have hzU : z ∈ U := hSU (hcircle 0)
    let L := (fderiv ℝ v z).toLinearMap.equivOfDetNeZero (hdet z hzU).ne'
    let e := L.toContinuousLinearEquiv
    have he : (e : E2 →L[ℝ] E2) = fderiv ℝ v z := by ext x; rfl
    have hd : HasFDerivAt v (e : E2 →L[ℝ] E2) z := by
      rw [he]
      exact (hv.differentiable (by simp) z).hasFDerivAt
    let H := hv.contDiffAt.toOpenPartialHomeomorph v hd (by simp)
    have hzH : z ∈ H.source := hv.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
    have hball : IsOpen (H.source ∩ Metric.ball z δ) := H.open_source.inter Metric.isOpen_ball
    have himage : IsOpen (v '' (H.source ∩ Metric.ball z δ)) :=
      H.isOpen_image_of_subset_source hball inter_subset_left
    have hzimage : v z ∈ v '' (H.source ∩ Metric.ball z δ) :=
      ⟨z, ⟨hzH, Metric.mem_ball_self hδ⟩, rfl⟩
    have hzcl : v z ∈ closure Ω.domain := by
      apply frontier_subset_closure
      rw [← Ω.boundary.image, hb]
      exact mem_range_self 0
    obtain ⟨y, ⟨x, hx, rfl⟩, hxΩ⟩ := mem_closure_iff.mp hzcl _ himage hzimage
    have hxband : |‖x‖ - 1| < δ := by
      have h := abs_norm_sub_norm_le x z
      rw [circle_norm 0] at h
      exact h.trans_lt hx.2
    have hxn : ‖x‖ ≠ 1 := by
      intro heq
      obtain ⟨t, ht⟩ := circle_surj x heq
      have hf : v x ∈ frontier Ω.domain := by
        rw [← ht, hb, ← Ω.boundary.image]
        exact mem_range_self t
      rw [Ω.open_domain.frontier_eq] at hf
      exact hf.2 hxΩ
    refine ⟨v, U, δ, hv, hb, hU, hSU, hinj, hdet, hδ, hδ1, hband, ?_⟩
    rcases lt_or_gt_of_ne hxn with hxlt | hxgt
    · left
      apply hside (1 - δ) 1 (by linarith)
      · intro w hw
        apply hband
        change |‖w‖ - 1| < δ
        change 1 - δ < ‖w‖ ∧ ‖w‖ < 1 at hw
        exact abs_lt.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩
      · exact fun w _ hw => hw.ne
      · exact ⟨x, by linarith [(abs_lt.mp hxband).1], hxlt, hxΩ⟩
    · right
      apply hside 1 (1 + δ) (by norm_num)
      · intro w hw
        apply hband
        change |‖w‖ - 1| < δ
        change 1 < ‖w‖ ∧ ‖w‖ < 1 + δ at hw
        exact abs_lt.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩
      · exact fun w hw _ => hw.ne'
      · exact ⟨x, hxgt, by linarith [(abs_lt.mp hxband).2], hxΩ⟩
  obtain ⟨v, U, δ, hv, hb, hU, hSU, hinj, hdet, hδ, hδ1, hband, hside⟩ := compatible
  rcases hside with hin | hout
  · exact ⟨v, δ, hv, hb, hδ, hδ1, hinj.mono hband,
      fun x hx => (hdet x (hband hx)).ne', hin⟩
  let b : ContDiffBump (0 : E2) := {
    rIn := 1 / 4
    rOut := 1 / 2
    rIn_pos := by norm_num
    rIn_lt_rOut := by norm_num }
  let I : E2 → E2 := EuclideanGeometry.inversion 0 1
  let w : E2 → E2 := fun x => (1 - b x) • v (I x)
  have hI (x : E2) (hx : x ≠ 0) : ContDiffAt ℝ ∞ I x :=
    contDiffAt_const.inversion contDiffAt_const contDiffAt_id hx
  have hw : ContDiff ℝ ∞ w := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst x
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E2 => (0 : E2)) 0).congr_of_eventuallyEq
      filter_upwards [b.eventuallyEq_one] with y hy
      simp [w, hy]
    · exact (contDiffAt_const.sub b.contDiffAt).smul (hv.contDiffAt.comp x (hI x hx))
  have heq (x : E2) (hx : 1 / 2 ≤ ‖x‖) : w x = v (I x) := by
    have hb0 : b x = 0 := b.zero_of_le_dist (by simpa [b, dist_zero_right] using hx)
    simp [w, hb0]
  have hInorm (x : E2) : ‖I x‖ = 1 / ‖x‖ := by
    simpa [I, dist_zero_right] using EuclideanGeometry.dist_inversion_center (0 : E2) x (1 : ℝ)
  have hIdet (x : E2) (hx : x ≠ 0) : (fderiv ℝ I x).det ≠ 0 := by
    have hIx : I x ≠ 0 := by
      exact (EuclideanGeometry.inversion_eq_center (by norm_num : (1 : ℝ) ≠ 0)).not.mpr hx
    have hcomp := fderiv_comp x ((hI (I x) hIx).differentiableAt (by simp))
      ((hI x hx).differentiableAt (by simp))
    have hII : I ∘ I = id := funext (EuclideanGeometry.inversion_inversion (0 : E2) (by norm_num))
    rw [hII, fderiv_id] at hcomp
    have he : (fderiv ℝ I (I x)).det * (fderiv ℝ I x).det = 1 := by
      rw [← LinearMap.det_comp]
      exact (congrArg (fun L : E2 →L[ℝ] E2 => L.det) hcomp.symm).trans LinearMap.det_id
    exact fun hz => by rw [hz, mul_zero] at he; norm_num at he
  have hwb (t : ℝ) : w (unitCircleParameter t) = Ω.boundary.gamma t := by
    have hn : ‖unitCircleParameter t‖ = 1 := by
      have hs : ‖unitCircleParameter t‖ ^ 2 = 1 := by
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
        exact Real.cos_sq_add_sin_sq t
      nlinarith [norm_nonneg (unitCircleParameter t)]
    rw [heq _ (by rw [hn]; norm_num)]
    have hIeq : I (unitCircleParameter t) = unitCircleParameter t :=
      EuclideanGeometry.inversion_of_mem_sphere (by simpa [Metric.mem_sphere, dist_zero_right] using hn)
    rw [hIeq, hb]
  let η : ℝ := δ / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η < 1 / 2 := by dsimp [η]; linarith
  have hinvband (x : E2) (hx : |‖x‖ - 1| < η) :
      1 / 2 < ‖x‖ ∧ |‖I x‖ - 1| < δ := by
    have hxlo := (abs_lt.mp hx).1
    have hxhi := (abs_lt.mp hx).2
    have hxn : 1 / 2 < ‖x‖ := by linarith
    have hxpos : 0 < ‖x‖ := by linarith
    refine ⟨hxn, ?_⟩
    rw [hInorm]
    apply abs_lt.mpr
    constructor
    · have hh : 1 - δ < 1 / ‖x‖ := by
        apply (lt_div_iff₀ hxpos).mpr
        dsimp [η] at hxlo hxhi
        nlinarith
      linarith
    · have hh : 1 / ‖x‖ < 1 + δ := by
        apply (div_lt_iff₀ hxpos).mpr
        dsimp [η] at hxlo hxhi
        nlinarith
      linarith
  refine ⟨w, η, hw, hwb, hη, by linarith, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hxi := hinvband x hx
    have hyi := hinvband y hy
    rw [heq x hxi.1.le, heq y hyi.1.le] at hxy
    exact EuclideanGeometry.inversion_injective (0 : E2) (by norm_num : (1 : ℝ) ≠ 0)
      (hinj (hband hxi.2) (hband hyi.2) hxy)
  · intro x hx
    obtain ⟨hxn, hxi⟩ := hinvband x hx
    have hne : x ≠ 0 := by intro hx0; norm_num [hx0] at hxn
    have hweq : w =ᶠ[𝓝 x] v ∘ I := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hxn] with y hy
      exact heq y hy.le
    rw [hweq.fderiv_eq, fderiv_comp x (hv.differentiable (by simp) (I x))
      ((hI x hne).differentiableAt (by simp))]
    change ((fderiv ℝ v (I x)).toLinearMap.comp (fderiv ℝ I x).toLinearMap).det ≠ 0
    rw [LinearMap.det_comp]
    exact mul_ne_zero (hdet (I x) (hband hxi)).ne' (hIdet x hne)
  · intro x hxlo hxhi
    have hxband : |‖x‖ - 1| < η := abs_lt.mpr ⟨by linarith, by linarith⟩
    obtain ⟨hxn, hxi⟩ := hinvband x hxband
    rw [heq x hxn.le]
    apply hout
    · rw [hInorm]
      apply (lt_div_iff₀ (by linarith : 0 < ‖x‖)).mpr
      simpa using hxhi
    · linarith [(abs_lt.mp hxi).2]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CountGeometry
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CountGeometry
open SeifertSurfaces.AppendixACoordinates

private theorem support_PaidExactReduction (R : ℝ) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (hM : Continuous M)
    (filling : ∃ q : E2 → E2, ContDiff ℝ 1 q ∧ InjOn q (disc 1) ∧
      q '' disc 1 = Ω.domain ∧
      ∀ t, q (unitCircleParameter t) = Ω.boundary.gamma t) :
    ∃ q : E2 → E2, ∃ dq : Fin 2 → E2 → E2,
      MetricAdmissible Ω q dq ∧ ContDiffOn ℝ 1 q (closedDisc 1) ∧
      q '' disc 1 = Ω.domain ∧ InjOn q (closedDisc 1) ∧
      (∀ i j, (fun x => dq i x j) =ᵐ[volume.restrict (disc 1)]
        (fun x => jacobianWithin q (closedDisc 1) x i j)) ∧
      metricArea M q dq = ∫ y in Ω.domain, Real.sqrt (Matrix.det (M y)) := by
  have area_calculation (R : ℝ) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
      (hM : Continuous M) (v : E2 → E2) (hv : ContDiff ℝ 1 v)
      (hinj : InjOn v (disc 1)) (himage : v '' disc 1 = Ω.domain) :
      let dv : Fin 2 → E2 → E2 := fun i x =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm
          (fun j => (fderiv ℝ v x (coordinateVector 2 j)) i)
      metricArea M v dv = ∫ x in Ω.domain, Real.sqrt (Matrix.det (M x)) := by
    let dv : Fin 2 → E2 → E2 := fun i x =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun j => (fderiv ℝ v x (coordinateVector 2 j)) i)
    change metricArea M v dv = _
    have hdet (x : E2) : Matrix.det (weakJacobian dv x) = (fderiv ℝ v x).det := by
      have hmat : weakJacobian dv x =
          LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (fderiv ℝ v x).toLinearMap := by
        ext i j
        simp [weakJacobian, dv, LinearMap.toMatrix_apply, coordinateVector,
          EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
      rw [hmat, LinearMap.det_toMatrix]
    have hchange := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
      (f := v) (f' := fderiv ℝ v) (s := disc 1) Metric.isOpen_ball.measurableSet
      (fun x _ => (hv.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt)
      hinj (fun x => Real.sqrt (Matrix.det (M x)))
    rw [himage] at hchange
    have harea : metricArea M v dv = ∫ x in Ω.domain, Real.sqrt (Matrix.det (M x)) := by
      rw [hchange]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only [metricAreaDensity, hdet, smul_eq_mul, mul_comm]
    exact harea
  have green_admissibility (R : ℝ) (Ω : SmoothFlatJordanDomain R) (v : E2 → E2)
      (hv : ContDiff ℝ 1 v) (theta : ℝ → ℝ) (orientation : ℝ)
      (hlift : WeakMonotoneBoundaryLift Ω theta orientation)
      (hboundary : ∀ t, v (unitCircleParameter t) = Ω.boundary.gamma (theta t))
      (hgreen : HasGreenBoundaryTrace v (fun i x =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm
          (fun j => (fderiv ℝ v x (coordinateVector 2 j)) i))
        (fun t => v (unitCircleParameter t))) :
      MetricAdmissible Ω v (fun i x =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm
          (fun j => (fderiv ℝ v x (coordinateVector 2 j)) i)) := by
    let dv : Fin 2 → E2 → E2 := fun i x =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun j => (fderiv ℝ v x (coordinateVector 2 j)) i)
    have hvc (i : Fin 2) : Continuous (fun x => v x i) :=
      (EuclideanSpace.proj i).continuous.comp hv.continuous
    have hentry (i j : Fin 2) : Continuous (fun x =>
        (fderiv ℝ v x (coordinateVector 2 j)) i) := by
      exact (EuclideanSpace.proj i).continuous.comp
        ((hv.continuous_fderiv (by norm_num)).clm_apply
          (continuous_const : Continuous (fun _ : E2 => coordinateVector 2 j)))
    have hdc (i : Fin 2) : Continuous (dv i) := by
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
      apply continuous_pi
      intro j
      exact hentry i j
    have hl2 {F : Type} [NormedAddCommGroup F] (a : E2 → F) (ha : Continuous a) :
        MemLp a 2 (volume.restrict (disc 1)) := by
      haveI : IsFiniteMeasure (volume.restrict (disc 1)) :=
        isFiniteMeasure_restrict.mpr (ne_of_lt (measure_ball_lt_top))
      obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E2) 1).exists_bound_of_continuousOn ha.continuousOn
      apply MemLp.of_bound ha.aestronglyMeasurable.restrict C
      filter_upwards [ae_restrict_mem (show MeasurableSet (disc 1) from Metric.isOpen_ball.measurableSet)] with x hx
      exact hC x (Metric.ball_subset_closedBall hx)
    have hcircle (t : ℝ) : unitCircleParameter t ∉ disc 1 := by
      have hn : ‖unitCircleParameter t‖ ^ 2 = 1 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        change (∑ i : Fin 2, (![Real.cos t, Real.sin t] i) ^ 2) = 1
        simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one] using Real.cos_sq_add_sin_sq t
      intro ht
      have ht' : ‖unitCircleParameter t‖ < 1 := mem_ball_zero_iff.mp ht
      nlinarith [norm_nonneg (unitCircleParameter t)]
    have hint {F : Type} [NormedAddCommGroup F] (a : E2 → F) (ha : Continuous a) :
        IntegrableOn a (disc 1) :=
      (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : E2) 1)
        ha.continuousOn).mono_set Metric.ball_subset_closedBall
    refine ⟨fun i => ⟨?_, hl2 _ (hvc i), hl2 _ (hdc i)⟩, theta, orientation, hlift, ?_⟩
    · refine ⟨(hvc i).continuousOn.locallyIntegrableOn Metric.isOpen_ball.measurableSet,
        (hdc i).continuousOn.locallyIntegrableOn Metric.isOpen_ball.measurableSet, ?_⟩
      intro phi hphi hcompact hs j
      have hz (t : ℝ) : phi (unitCircleParameter t) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        exact hcircle t (hs hmem)
      have hsum := (hgreen phi hphi i j).2.2
      have hc1 : Continuous (fun x => v x i * fderiv ℝ phi x (coordinateVector 2 j)) :=
        (hvc i).mul ((hphi.continuous_fderiv (by simp)).clm_apply
          (continuous_const : Continuous (fun _ : E2 => coordinateVector 2 j)))
      have hc2 : Continuous (fun x => dv i x j * phi x) :=
        ((EuclideanSpace.proj j).continuous.comp (hdc i)).mul hphi.continuous
      change (∫ x in disc 1, v x i * fderiv ℝ phi x (coordinateVector 2 j) +
        dv i x j * phi x) = _ at hsum
      rw [integral_add (hint _ hc1) (hint _ hc2)] at hsum
      have hzero : (∫ t in Icc 0 (2 * Real.pi), v (unitCircleParameter t) i *
          phi (unitCircleParameter t) * (unitCircleParameter t) j) = 0 := by
        simp only [hz, mul_zero, zero_mul, integral_zero]
      rw [hzero] at hsum
      exact eq_neg_of_add_eq_zero_left hsum
    · have hb : (fun t => v (unitCircleParameter t)) = liftedBoundaryValue Ω theta := by
        funext t
        exact hboundary t
      rwa [← hb]
  have classical_green (v : E2 → E2) (hv : ContDiff ℝ 1 v) :
      HasGreenBoundaryTrace v (fun i x =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm
          (fun j => (fderiv ℝ v x (coordinateVector 2 j)) i))
        (fun t => v (unitCircleParameter t)) := by
    have hscalar (h : E2 → ℝ) (hh : ContDiff ℝ 1 h) (j : Fin 2) :
        (∫ x in disc 1, fderiv ℝ h x (coordinateVector 2 j)) =
          ∫ t in Icc 0 (2 * Real.pi), h (unitCircleParameter t) *
            (unitCircleParameter t) j := by
      let c := unitCircleParameter
      let T : ℝ → E2 := fun t =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-Real.sin t, Real.cos t]
      have hc : ContDiff ℝ ∞ c := by
        apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp
        apply contDiff_pi.mpr
        intro k
        fin_cases k
        · exact Real.contDiff_cos
        · exact Real.contDiff_sin
      have hcd (t : ℝ) : HasDerivAt c (T t) t := by
        have hd : HasDerivAt (fun t : ℝ => ![Real.cos t, Real.sin t])
            ![-Real.sin t, Real.cos t] t := by
          apply hasDerivAt_pi.mpr
          intro k
          fin_cases k
          · exact Real.hasDerivAt_cos t
          · exact Real.hasDerivAt_sin t
        exact ((EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hd
      have hTd (t : ℝ) : HasDerivAt T (-c t) t := by
        have hd : HasDerivAt (fun t : ℝ => ![-Real.sin t, Real.cos t])
            ![-Real.cos t, -Real.sin t] t := by
          apply hasDerivAt_pi.mpr
          intro k
          fin_cases k
          · exact (Real.hasDerivAt_sin t).neg
          · exact Real.hasDerivAt_cos t
        convert ((EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hd using 1
        · rfl
        · apply PiLp.ext
          intro k
          fin_cases k <;> rfl
      have hn (t : ℝ) : ‖c t‖ = 1 := by
        have hs : ‖c t‖ ^ 2 = 1 := by
          rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
          exact Real.cos_sq_add_sin_sq t
        nlinarith [norm_nonneg (c t)]
      have hpolar (f : E2 → ℝ) :
          (∫ x in disc 1, f x) =
            ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi, p.1 * f (p.1 • c p.2) := by
        let e : E2 ≃L[ℝ] (ℝ × ℝ) :=
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
            (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
        have hmp : MeasurePreserving e volume volume :=
          (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
        let Q := Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi
        have he (r t : ℝ) : e.symm (polarCoord.symm (r,t)) = r • c t := by
          apply PiLp.ext
          intro k
          fin_cases k <;> dsimp only [e, c, unitCircleParameter] <;> simp [polarCoord_symm_apply]
        have hnorm (r t : ℝ) : ‖r • c t‖ = |r| := by
          rw [norm_smul, Real.norm_eq_abs, hn, mul_one]
        have hdisc : MeasurableSet (disc (1 : ℝ)) := Metric.isOpen_ball.measurableSet
        have hq : MeasurableSet Q := measurableSet_Ioo.prod measurableSet_Ioo
        have hsub : Q ⊆ polarCoord.target := fun p hp => ⟨hp.1.1,hp.2⟩
        calc
          (∫ x in disc 1, f x) = ∫ x : E2, (disc 1).indicator f x := (integral_indicator hdisc).symm
          _ = ∫ p : ℝ × ℝ, (disc 1).indicator f (e.symm p) := by
            simpa only [e.symm_apply_apply] using
              (hmp.integral_comp e.toHomeomorph.measurableEmbedding (fun p => (disc 1).indicator f (e.symm p)))
          _ = ∫ p in polarCoord.target, p.1 * (disc 1).indicator f (e.symm (polarCoord.symm p)) := by
            simpa only [smul_eq_mul] using (integral_comp_polarCoord_symm (fun p => (disc 1).indicator f (e.symm p))).symm
          _ = ∫ p in polarCoord.target, Q.indicator (fun p => p.1 * f (p.1 • c p.2)) p := by
            apply setIntegral_congr_fun polarCoord.open_target.measurableSet
            intro p hp
            have hm : e.symm (polarCoord.symm p) ∈ disc 1 ↔ p ∈ Q := by
              rw [he p.1 p.2]
              change dist (p.1 • c p.2) 0 < 1 ↔ _
              rw [dist_zero_right, hnorm, abs_of_pos hp.1]
              exact ⟨fun h => ⟨⟨hp.1,h⟩,hp.2⟩,fun h => h.1.2⟩
            change p.1 * (disc 1).indicator f (e.symm (polarCoord.symm p)) = _
            by_cases ht : p ∈ Q
            · rw [indicator_of_mem ht, indicator_of_mem (hm.mpr ht), he p.1 p.2]
            · rw [indicator_of_notMem ht, indicator_of_notMem (mt hm.mp ht), mul_zero]
          _ = ∫ p in polarCoord.target ∩ Q, p.1 * f (p.1 • c p.2) := by
            rw [setIntegral_indicator hq]
          _ = ∫ p in Q, p.1 * f (p.1 • c p.2) := by rw [inter_eq_right.mpr hsub]
      let P : ℝ × ℝ → E2 := fun p => p.1 • c p.2
      let F : ℝ × ℝ → ℝ := fun p => p.1 * (c p.2) j * h (P p)
      let K : ℝ × ℝ → ℝ := fun p => (T p.2) j * h (P p)
      have hPc : ContDiff ℝ 1 P := contDiff_fst.smul ((hc.of_le (by norm_num)).comp contDiff_snd)
      have hF : ContDiff ℝ 1 F := by
        apply ContDiff.mul
        · apply ContDiff.mul contDiff_fst
          exact ((EuclideanSpace.proj j : E2 →L[ℝ] ℝ).contDiff.comp (hc.of_le (by norm_num))).comp contDiff_snd
        · exact hh.comp hPc
      have hTc : ContDiff ℝ ∞ T := by
        apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp
        apply contDiff_pi.mpr
        intro k
        fin_cases k
        · exact Real.contDiff_sin.neg
        · exact Real.contDiff_cos
      have hK : ContDiff ℝ 1 K :=
        (((EuclideanSpace.proj j : E2 →L[ℝ] ℝ).contDiff.comp (hTc.of_le (by norm_num))).comp contDiff_snd).mul (hh.comp hPc)
      have hdiv (p : ℝ × ℝ) :
          fderiv ℝ F p (1,0) + fderiv ℝ K p (0,1) =
            p.1 * fderiv ℝ h (P p) (coordinateVector 2 j) := by
        have hr := (hh.differentiable (by norm_num) (P p)).hasFDerivAt.comp_hasDerivAt p.1
          ((hasDerivAt_id p.1).smul_const (c p.2))
        have hfr : HasDerivAt (fun r : ℝ => F (r,p.2))
            ((c p.2) j * h (P p) + p.1 * (c p.2) j *
              fderiv ℝ h (P p) (c p.2)) p.1 := by
          convert ((hasDerivAt_id p.1).mul_const ((c p.2) j)).mul hr using 1
          · funext r
            simp only [F, P, Function.comp_apply, id_eq, Pi.mul_apply] <;> ring
          · simp only [F, P, Function.comp_apply, id_eq, one_mul, one_smul] <;> ring
        have hfr' := (hF.differentiable (by norm_num) p).hasFDerivAt.comp_hasDerivAt p.1
          ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
        have hfrEq : fderiv ℝ F p (1,0) =
            (c p.2) j * h (P p) + p.1 * (c p.2) j * fderiv ℝ h (P p) (c p.2) :=
          hfr'.unique hfr
        have ht := (hh.differentiable (by norm_num) (P p)).hasFDerivAt.comp_hasDerivAt p.2
          ((hcd p.2).const_smul p.1)
        have hcoord := (EuclideanSpace.proj j : E2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt p.2 (hTd p.2)
        have hkt : HasDerivAt (fun t : ℝ => K (p.1,t))
            (-(c p.2) j * h (P p) + (T p.2) j *
              fderiv ℝ h (P p) (p.1 • T p.2)) p.2 := by
          convert hcoord.mul ht using 1
          · rfl
          · simp only [Function.comp_apply, EuclideanSpace.coe_proj, PiLp.neg_apply,
              Pi.smul_apply, P]
        have hkt' := (hK.differentiable (by norm_num) p).hasFDerivAt.comp_hasDerivAt p.2
          ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
        have hktEq : fderiv ℝ K p (0,1) =
            -(c p.2) j * h (P p) + (T p.2) j * fderiv ℝ h (P p) (p.1 • T p.2) :=
          hkt'.unique hkt
        have hframe : (c p.2 j) • c p.2 + (T p.2 j) • T p.2 = coordinateVector 2 j := by
          apply PiLp.ext
          intro k
          fin_cases j <;> fin_cases k <;>
            simp [c, T, unitCircleParameter, coordinateVector, PiLp.single_apply]
          all_goals nlinarith [Real.cos_sq_add_sin_sq p.2]
        rw [hfrEq, hktEq, ← hframe, map_add, map_smul, map_smul, map_smul]
        simp only [smul_eq_mul]
        ring
      have he := integral_divergence_prod_Icc_of_hasFDerivAt_of_le F K
        (fderiv ℝ F) (fderiv ℝ K) (0,-Real.pi) (1,Real.pi)
        (by constructor <;> dsimp <;> linarith [Real.pi_pos])
        hF.continuous.continuousOn hK.continuous.continuousOn
        (fun p _ => (hF.differentiable (by norm_num) p).hasFDerivAt)
        (fun p _ => (hK.differentiable (by norm_num) p).hasFDerivAt)
        (by
          have hd : Continuous (fun p : ℝ × ℝ => p.1 * fderiv ℝ h (P p) (coordinateVector 2 j)) :=
            continuous_fst.mul (((hh.continuous_fderiv (by norm_num)).comp hPc.continuous).clm_apply continuous_const)
          simpa only [hdiv] using hd.continuousOn.integrableOn_compact isCompact_Icc)
      have hKends (r : ℝ) : K (r,Real.pi) = K (r,-Real.pi) := by
        fin_cases j <;> simp [K, P, T, c, unitCircleParameter, Real.sin_pi, Real.cos_pi]
      have hFzero (t : ℝ) : F (0,t) = 0 := by simp [F]
      have hFone (t : ℝ) : F (1,t) = h (c t) * (c t) j := by simp [F, P, mul_comm]
      simp only [hdiv, hKends, sub_self, hFzero, intervalIntegral.integral_zero,
        sub_zero, zero_add, hFone] at he
      have hrect : Icc ((0 : ℝ), -Real.pi) (1,Real.pi) =
          Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi := by
        ext p
        change ((0 ≤ p.1 ∧ -Real.pi ≤ p.2) ∧ (p.1 ≤ 1 ∧ p.2 ≤ Real.pi)) ↔
          ((0 ≤ p.1 ∧ p.1 ≤ 1) ∧ (-Real.pi ≤ p.2 ∧ p.2 ≤ Real.pi))
        tauto
      rw [hrect] at he
      have hsets : (Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) =ᵐ[volume]
          (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi) :=
        Measure.set_prod_ae_eq Ioo_ae_eq_Icc.symm Ioo_ae_eq_Icc.symm
      rw [setIntegral_congr_set hsets] at he
      rw [hpolar]
      change (∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 * fderiv ℝ h (P p) (coordinateVector 2 j)) = _
      rw [he]
      have hp : Periodic (fun t => h (c t) * (c t) j) (2 * Real.pi) := by
        intro t
        have hcp : c (t + 2 * Real.pi) = c t := by
          apply PiLp.ext
          intro k
          fin_cases k <;> simp [c, unitCircleParameter, Real.cos_add_two_pi, Real.sin_add_two_pi]
        change h (c (t + 2 * Real.pi)) * (c (t + 2 * Real.pi)) j = h (c t) * (c t) j
        rw [hcp]
      have hs := hp.intervalIntegral_add_eq (-Real.pi) 0
      have hpi : -Real.pi + 2 * Real.pi = Real.pi := by ring
      rw [hpi] at hs
      simpa only [zero_add, intervalIntegral.integral_of_le
        (by positivity : (0 : ℝ) ≤ 2 * Real.pi), integral_Icc_eq_integral_Ioc] using hs
    have hc : Continuous unitCircleParameter := by
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
      apply continuous_pi
      intro k
      fin_cases k
      · exact Real.continuous_cos
      · exact Real.continuous_sin
    intro psi hpsi i j
    have hvc : ContDiff ℝ 1 (fun x => v x i) := (EuclideanSpace.proj i : E2 →L[ℝ] ℝ).contDiff.comp hv
    have hprod : ContDiff ℝ 1 (fun x => v x i * psi x) := hvc.mul (hpsi.of_le (by simp))
    have hentry : Continuous (fun x => (fderiv ℝ v x (coordinateVector 2 j)) i) :=
      (EuclideanSpace.proj i).continuous.comp ((hv.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    have hbulk : Continuous (fun x => v x i * fderiv ℝ psi x (coordinateVector 2 j) +
        (fderiv ℝ v x (coordinateVector 2 j)) i * psi x) :=
      ((EuclideanSpace.proj i).continuous.comp hv.continuous).mul
        ((hpsi.continuous_fderiv (by simp)).clm_apply continuous_const) |>.add
          (hentry.mul hpsi.continuous)
    have hb : Continuous (fun t => v (unitCircleParameter t) i * psi (unitCircleParameter t) *
        (unitCircleParameter t) j) :=
      ((((EuclideanSpace.proj i).continuous.comp hv.continuous).comp hc).mul
        (hpsi.continuous.comp hc)).mul ((EuclideanSpace.proj j).continuous.comp hc)
    refine ⟨(hbulk.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E2) 1)).mono_set
        Metric.ball_subset_closedBall, hb.continuousOn.integrableOn_Icc, ?_⟩
    have hd (x : E2) : fderiv ℝ (fun x => v x i * psi x) x (coordinateVector 2 j) =
        v x i * fderiv ℝ psi x (coordinateVector 2 j) +
          (fderiv ℝ v x (coordinateVector 2 j)) i * psi x := by
      have hcder := (EuclideanSpace.proj i : E2 →L[ℝ] ℝ).hasFDerivAt.comp x
        (hv.differentiable (by norm_num) x).hasFDerivAt
      have hm := hcder.mul (hpsi.differentiable (by simp) x).hasFDerivAt
      change fderiv ℝ ((EuclideanSpace.proj i : E2 →L[ℝ] ℝ) ∘ v * psi) x (coordinateVector 2 j) = _
      rw [hm.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, Function.comp_apply, PiLp.proj_apply, smul_eq_mul]
      ring
    change (∫ x in disc 1, v x i * fderiv ℝ psi x (coordinateVector 2 j) +
      (fderiv ℝ v x (coordinateVector 2 j)) i * psi x) = _
    simpa only [hd, mul_assoc] using hscalar (fun x => v x i * psi x) hprod j

  obtain ⟨q, hq, hi, him, hb⟩ := filling
  let dq : Fin 2 → E2 → E2 := fun i x =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm
      (fun j => (fderiv ℝ q x (coordinateVector 2 j)) i)
  have hl : WeakMonotoneBoundaryLift Ω (fun t => t) 1 := by
    refine ⟨Or.inl rfl, continuous_id, ?_, by simp⟩
    intro a b hab
    simpa only [one_mul] using hab
  have circle_surj (x : E2) (hx : ‖x‖ = 1) : ∃ t, unitCircleParameter t = x := by
    let z : ℂ := ⟨x 0, x 1⟩
    have hs : (x 0)^2 + (x 1)^2 = 1 := by
      have h := EuclideanSpace.real_norm_sq_eq x
      rw [hx] at h
      simpa only [Fin.sum_univ_two, one_pow] using h.symm
    have hz : ‖z‖ = 1 := by
      have hsq : ‖z‖^2 = 1 := by
        rw [← Complex.normSq_eq_norm_sq]
        simpa [z, Complex.normSq_apply, pow_two] using hs
      nlinarith [norm_nonneg z]
    have hne : z ≠ 0 := by intro h; simp [h] at hz
    refine ⟨Complex.arg z, ?_⟩
    apply PiLp.ext
    intro j
    fin_cases j
    · change Real.cos (Complex.arg z) = x 0
      rw [Complex.cos_arg hne, hz]
      simp [z]
    · change Real.sin (Complex.arg z) = x 1
      rw [Complex.sin_arg, hz]
      simp [z]
  have hboundary_inj : InjOn q {x : E2 | ‖x‖ = 1} := by
    intro x hx y hy he
    obtain ⟨t, rfl⟩ := circle_surj x hx
    obtain ⟨u, rfl⟩ := circle_surj y hy
    rw [hb t, hb u] at he
    obtain ⟨k, hk⟩ := (Ω.boundary.simple t u).mp he
    have ht : t = u + (k : ℝ) * (2 * Real.pi) := by linarith
    rw [ht]
    apply PiLp.ext
    intro j
    fin_cases j
    · exact Real.cos_periodic.int_mul k u
    · exact Real.sin_periodic.int_mul k u
  have hfrontier (x : E2) (hx : ‖x‖ = 1) : q x ∈ frontier Ω.domain := by
    obtain ⟨t, rfl⟩ := circle_surj x hx
    rw [hb, ← Ω.boundary.image]
    exact mem_range_self t
  have hdisjoint (x : E2) (hx : x ∈ disc 1) (y : E2) (hy : ‖y‖ = 1) :
      q x ≠ q y := by
    have hxin : q x ∈ Ω.domain := him ▸ mem_image_of_mem q hx
    have hyout : q y ∉ Ω.domain := by
      have h := (hfrontier y hy).2
      rw [Ω.open_domain.interior_eq] at h
      exact h
    intro he
    exact hyout (he ▸ hxin)
  have hc : InjOn q (closedDisc 1) := by
    intro x hx y hy he
    have hxn : ‖x‖ ≤ 1 := by simpa [closedDisc, Metric.mem_closedBall, dist_zero_right] using hx
    have hyn : ‖y‖ ≤ 1 := by simpa [closedDisc, Metric.mem_closedBall, dist_zero_right] using hy
    by_cases hxlt : ‖x‖ < 1
    · have hxd : x ∈ disc 1 := by simpa [disc, Metric.mem_ball, dist_zero_right] using hxlt
      by_cases hylt : ‖y‖ < 1
      · exact hi hxd (by simpa [disc, Metric.mem_ball, dist_zero_right] using hylt) he
      · exact False.elim ((hdisjoint x hxd y (by linarith)) he)
    · have hxe : ‖x‖ = 1 := by linarith
      by_cases hylt : ‖y‖ < 1
      · exact False.elim ((hdisjoint y (by simpa [disc, Metric.mem_ball, dist_zero_right] using hylt) x hxe) he.symm)
      · exact hboundary_inj hxe (show ‖y‖ = 1 from le_antisymm hyn (le_of_not_gt hylt)) he
  refine ⟨q, dq, green_admissibility R Ω q hq (fun t => t) 1 hl hb
    (classical_green q hq), hq.contDiffOn, him, hc, ?_, ?_⟩
  · intro i j
    filter_upwards [ae_restrict_mem (Metric.isOpen_ball : IsOpen (disc 1)).measurableSet] with x hx
    have hnb : closedDisc 1 ∈ 𝓝 x :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hx) Metric.ball_subset_closedBall
    change (fderiv ℝ q x (coordinateVector 2 j)) i =
      (fderivWithin ℝ q (closedDisc 1) x (coordinateVector 2 j)) i
    rw [fderivWithin_of_mem_nhds hnb]
  · exact area_calculation R Ω M hM q hq hi him

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CountGeometry
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CountGeometry
-- Both local construction producer terms remain unpaid; this is not the original theorem.
private theorem original_qdq_of_producers
    (hPL : ∀ (K : Geometry.SimplicialComplex ℝ E2) [Finite K.faces],
      IsPLBall 2 K.space → Convex ℝ K.space → ∀ (F : E2 → E2),
      IsPiecewiseAffineOn F K.space → InjOn F K.space →
      ∃ J : E2 → E2,(∃ L : NNReal,LipschitzWith L J) ∧ InjOn J K.space ∧
        J '' K.space=F '' K.space ∧ EqOn J F (frontier K.space) ∧
        (∀ x∈interior K.space,ContDiffAt ℝ 1 J x) ∧
        ∃ S : Finset E2,(S:Set E2) ⊆ frontier K.space ∧
          ∀ x∈frontier K.space,x∉(S:Set E2) → ∃ (U : Set E2) (L : E2 →ᵃ[ℝ] E2),
            IsOpen U ∧ x∈U ∧ EqOn J L (U∩K.space))
    (hPolar : ∀ (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
  (r : Fin (n+1) → ℝ) (t : Fin (m+1) → ℝ)
  (hr : StrictMono r) (ht : StrictMono t),
  r 0=0 → 0 < r (Fin.last n) → r (Fin.last n) < 1 →
  t 0=0 → t (Fin.last m)=2*Real.pi →
  ∀ (H : E2 → E2), (∃ L : NNReal, LipschitzWith L H) →
  (∀ x, r (Fin.last n) ≤ ‖x‖ → ContDiffAt ℝ 1 H x) →
  (∀ (i : Fin n) (j : Fin m),
    ContDiffOn ℝ 1 (fun z : ℝ×ℝ => H (z.1 • unitCircleParameter z.2))
      ((Icc (r i.castSucc) (r i.succ) ×ˢ Icc (t j.castSucc) (t j.succ)) \
        (({r i.castSucc,r i.succ}:Set ℝ) ×ˢ ({t j.castSucc,t j.succ}:Set ℝ)))) →
  ∃ (T : E2 → E2) (b : ℝ), r (Fin.last n) < b ∧ b < 1 ∧
    Bijective T ∧ ContDiff ℝ 1 T ∧ (∃ L : NNReal, LipschitzWith L T) ∧
    EqOn T id {x | b ≤ ‖x‖} ∧ T '' ball 0 1=ball 0 1 ∧
    ContDiff ℝ 1 (H ∘ T) ∧ (∃ L : NNReal, LipschitzWith L (H ∘ T)))


    (R : ℝ) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2) (hM : Continuous M) :
    ∃ q : E2 → E2, ∃ dq : Fin 2 → E2 → E2,
      MetricAdmissible Ω q dq ∧ ContDiffOn ℝ 1 q (closedDisc 1) ∧
      q '' disc 1=Ω.domain ∧ InjOn q (closedDisc 1) ∧
      (∀ i j,(fun x => dq i x j) =ᵐ[volume.restrict (disc 1)]
        (fun x => jacobianWithin q (closedDisc 1) x i j)) ∧
      metricArea M q dq=∫ y in Ω.domain,Real.sqrt (Matrix.det (M y)) := by
  obtain ⟨w,η,hw,hb,hη0,hη1,hi,hdet,hinward⟩ := support_PaidInward R Ω
  obtain ⟨q,hq,hqL,hqi,hqim,hqb⟩ :=
    VM03CapV437.actual_c1_cap_of_producers hPL hPolar R Ω w η hw hb hη0 hη1 hi hdet hinward
  exact support_PaidExactReduction R Ω M hM
    ⟨q,hq,hqi.mono ball_subset_closedBall,hqim,hqb⟩
end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CountGeometry
noncomputable section
open Set Filter Function
open scoped Topology
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Topology.PiecewiseLinear
namespace VM03CapV437TrackedEdges

/- An actual full-dimensional face model of an injective PL map is an affine
   equivalence. No invertible-model premise is added. -/
private theorem triangle_model_equiv
    (K : Geometry.SimplicialComplex ℝ E2) (f : E2 → E2)
    (hi : InjOn f K.space) (s : Finset E2) (hs : s ∈ K.faces) (hcard : s.card=3)
    (A : E2 →ᵃ[ℝ] E2) (hA : EqOn f A (convexHull ℝ (s:Set E2))) :
    ∃ e : E2 ≃ᵃ[ℝ] E2, (∀ x, e x=A x) ∧ EqOn f e (convexHull ℝ (s:Set E2)) := by
  have hin : (interior (convexHull ℝ (s:Set E2))).Nonempty := by
    rw [interior_convexHull_eq_openSimplex (K.indep hs) (by simpa using hcard)]
    exact ⟨s.centroid ℝ id,centroid_mem_openSimplex (K.nonempty_of_mem_faces hs)⟩
  have hil : Injective A.linear := linear_injective_of_injOn_of_interior_nonempty
    (fun x hx y hy hxy => hi (K.convexHull_subset_space hs hx) (K.convexHull_subset_space hs hy)
      (by rw [hA hx,hA hy]; exact hxy)) hin
  let e : E2 ≃ᵃ[ℝ] E2 := AffineEquiv.mk' A (LinearEquiv.ofInjectiveEndo A.linear hil) 0
    (fun p => by simpa using A.map_vadd (0:E2) p)
  exact ⟨e,fun _ => rfl,hA⟩

private theorem support_ActualAffineModels_1 (K : Geometry.SimplicialComplex ℝ E2) [Finite K.faces]
    (f : E2 → E2) (hf : IsPiecewiseAffineOn f K.space) (hi : InjOn f K.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E2, IsSubdivision K' K ∧ K'.faces.Finite ∧
      ∀ s ∈ K'.faces, s.card=3 →
        ∃ e : E2 ≃ᵃ[ℝ] E2, EqOn f e (convexHull ℝ (s:Set E2)) := by
  obtain ⟨K',hsub,hfin,hA⟩ := hf.exists_isSubdivision_affineOn_faces K
  refine ⟨K',hsub,hfin,?_⟩
  intro s hs hcard
  obtain ⟨A,hA⟩ := hA s hs
  have hi' : InjOn f K'.space := by rw [hsub.space_eq]; exact hi
  obtain ⟨e,he,hfe⟩ := triangle_model_equiv K' f hi' s hs hcard A hA
  exact ⟨e,hfe⟩

private theorem affine_axis_normal_form (C : (ℝ×ℝ) ≃ᵃ[ℝ] (ℝ×ℝ))
    (hfix : ∀ t : ℝ, C (t,0)=(t,0)) :
    ∃ a b : ℝ, b ≠ 0 ∧ ∀ z : ℝ×ℝ, C z=(z.1+a*z.2,b*z.2) := by
  have h0 : C 0=0 := hfix 0
  have hlin (z : ℝ×ℝ) : C z=C.linear z := by
    have h := C.map_vadd (0:ℝ×ℝ) z
    simpa only [vadd_eq_add,add_zero,h0] using h
  let v : ℝ×ℝ := C (0,1)
  have hform (z : ℝ×ℝ) : C z=(z.1+v.1*z.2,v.2*z.2) := by
    have hz : z=z.1 • (1,0)+z.2 • (0,1) := by ext <;> simp
    rw [hlin,hz,map_add,map_smul,map_smul,← hlin,← hlin,hfix]
    dsimp only [v]
    ext <;> simp [mul_comm]
  refine ⟨v.1,v.2,?_,hform⟩
  intro hb
  have he : C (0,1)=C (v.1,0) := by rw [hform,hfix,hb]; simp
  have hh := congrArg Prod.snd (C.injective he)
  norm_num at hh

/- The sign needed by edge smoothing follows from local injectivity itself. -/
private theorem positive_normal_coefficient (a b : ℝ) (W : Set (ℝ×ℝ)) (hW : W ∈ 𝓝 (0:ℝ×ℝ))
    (hi : InjOn (fun z : ℝ×ℝ => if 0≤z.2 then z else (z.1+a*z.2,b*z.2)) W) : 0<b := by
  by_contra hb
  have hb : b≤0 := le_of_not_gt hb
  have hc₁ : ContinuousAt (fun t : ℝ => ((0:ℝ),-t)) 0 := by fun_prop
  have hc₂ : ContinuousAt (fun t : ℝ => (-a*t,-b*t)) 0 := by fun_prop
  have he₁ : ∀ᶠ t : ℝ in 𝓝 0, ((0:ℝ),-t) ∈ W := by
    apply hc₁.eventually
    have hz : ((fun t : ℝ => ((0:ℝ),-t)) 0)=(0:ℝ×ℝ) := by ext <;> norm_num
    rw [hz]
    exact hW
  have he₂ : ∀ᶠ t : ℝ in 𝓝 0, (-a*t,-b*t) ∈ W := by
    apply hc₂.eventually
    have hz : ((fun t : ℝ => (-a*t,-b*t)) 0)=(0:ℝ×ℝ) := by ext <;> norm_num
    rw [hz]
    exact hW
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (he₁.and he₂)
  let t := ε/2
  have ht : 0<t := by dsimp [t]; positivity
  have htmem : t ∈ Metric.ball (0:ℝ) ε := by
    rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos ht]
    dsimp [t]; linarith
  have hmem := hball htmem
  have hnorm : 0≤-b*t := mul_nonneg (neg_nonneg.mpr hb) ht.le
  have he := hi hmem.1 hmem.2 (by
    change (if 0≤-t then ((0:ℝ),-t) else (0+a*(-t),b*(-t))) =
      (if 0≤-b*t then (-a*t,-b*t) else _)
    rw [if_neg (by linarith),if_pos hnorm]
    ext <;> simp [mul_neg,neg_mul])
  have hz := congrArg Prod.snd he
  change -t = -b*t at hz
  nlinarith

/- Both sides of the actual edge have now been reduced to the paid positive
   shear model. The hypothesis below is local injectivity, not an orientation. -/
private theorem support_ActualAffineModels_2 (C : (ℝ×ℝ) ≃ᵃ[ℝ] (ℝ×ℝ))
    (hfix : ∀ t : ℝ, C (t,0)=(t,0))
    (W : Set (ℝ×ℝ)) (hW : W ∈ 𝓝 (0:ℝ×ℝ))
    (hi : InjOn (fun z : ℝ×ℝ => if 0≤z.2 then z else C z) W) :
    ∃ a b : ℝ, 0<b ∧ ∀ z : ℝ×ℝ,
      (if 0≤z.2 then z else C z) =
        if 0≤z.2 then (z.1+0*z.2,1*z.2) else (z.1+a*z.2,b*z.2) := by
  obtain ⟨a,b,hb,hform⟩ := affine_axis_normal_form C hfix
  have hi' : InjOn (fun z : ℝ×ℝ => if 0≤z.2 then z else (z.1+a*z.2,b*z.2)) W := by
    simpa only [hform] using hi
  refine ⟨a,b,positive_normal_coefficient a b W hW hi',?_⟩
  intro z
  rw [hform]
  simp


/- A chart for the actual edge endpoints, obtained without a chosen normal or
   an orientation premise. -/
private theorem edge_axis_chart (p q : E2) (hpq : p≠q) :
    ∃ A : E2 ≃ᵃ[ℝ] (ℝ×ℝ), A p=(0,0) ∧ A q=(1,0) := by
  let e : E2 ≃L[ℝ] (ℝ×ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have hd : e (q-p) ≠ 0 := fun h => hpq (sub_eq_zero.mp (e.injective (by simpa using h))).symm
  obtain ⟨B,hB⟩ := SeparatingDual.exists_continuousLinearEquiv_apply_eq (R:=ℝ)
    hd (show ((1,0):ℝ×ℝ)≠0 by intro h; have := congrArg Prod.fst h; norm_num at this)
  let L := e.trans B
  let A : E2 ≃ᵃ[ℝ] (ℝ×ℝ) :=
    (AffineEquiv.vaddConst ℝ p).symm.trans L.toLinearEquiv.toAffineEquiv
  have hAp : A p=(0,0) := by simp [A]; rfl
  have hAq : A q=(1,0) := by change B (e (q-p))=(1,0); exact hB
  exact ⟨A,hAp,hAq⟩

private theorem edge_pair_normal_form (p q : E2) (hpq : p≠q) (f g : E2 ≃ᵃ[ℝ] E2)
    (hfp : f p=g p) (hfq : f q=g q) :
    ∃ (A : E2 ≃ᵃ[ℝ] (ℝ×ℝ)) (B : (ℝ×ℝ) ≃ᵃ[ℝ] E2) (a b : ℝ),
      A p=(0,0) ∧ A q=(1,0) ∧ b≠0 ∧
      (∀ z : ℝ×ℝ, f (A.symm z)=B z) ∧
      (∀ z : ℝ×ℝ, g (A.symm z)=B (z.1+a*z.2,b*z.2)) := by
  obtain ⟨A,hAp,hAq⟩ := edge_axis_chart p q hpq
  let B := A.symm.trans f
  let C := (A.symm.trans g).trans B.symm
  have hfix : ∀ t : ℝ, C (t,0)=(t,0) := by
    intro t
    have h0 : C (0,0)=(0,0) := by
      change B.symm (g (A.symm (0,0)))=(0,0)
      rw [← hAp,A.symm_apply_apply,← hfp]
      simpa [B] using B.symm_apply_apply (A p)
    have h1 : C (1,0)=(1,0) := by
      change B.symm (g (A.symm (1,0)))=(1,0)
      rw [← hAq,A.symm_apply_apply,← hfq]
      simpa [B] using B.symm_apply_apply (A q)
    have he := C.apply_lineMap (0,0) (1,0) t
    rw [h0,h1] at he
    simpa [AffineMap.lineMap_apply_module] using he
  obtain ⟨a,b,hb,hform⟩ := affine_axis_normal_form C hfix
  refine ⟨A,B,a,b,hAp,hAq,hb,fun _ => rfl,?_⟩
  intro z
  have hh := congrArg B (hform z)
  simpa [C] using hh

private theorem height_ne_zero_of_triangle
    (K : Geometry.SimplicialComplex ℝ E2) (p q a : E2)
    (ha : a ∉ ({p,q}:Finset E2)) (hs : insert a ({p,q}:Finset E2) ∈ K.faces)
    (A : E2 ≃ᵃ[ℝ] (ℝ×ℝ)) (hAp : A p=(0,0)) (hAq : A q=(1,0)) : (A a).2≠0 := by
  classical
  have hId : AffineIndepOn ℝ id ((insert a ({p,q}:Finset E2)):Set E2) := by
    convert! (K.indep hs).affineIndepOn_id using 1
    ext z
    simp
  have hnot : a ∉ affineSpan ℝ ({p,q}:Set E2) := by
    have h := (affineIndepOn_insert (k:=ℝ) (p:=id) (by simpa using ha)).mp
      (show AffineIndepOn ℝ id (insert a ({p,q}:Set E2)) by simpa using hId)
    simpa using h.2
  intro hzero
  apply hnot
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  refine ⟨(A a).1,A.injective ?_⟩
  rw [A.apply_lineMap,hAp,hAq]
  ext <;> simp [AffineMap.lineMap_apply_module,hzero]

private theorem triangle_height_nonneg
    (p q a : E2) (A : E2 ≃ᵃ[ℝ] (ℝ×ℝ))
    (hAp : (A p).2=0) (hAq : (A q).2=0) (ha : 0≤(A a).2) :
    convexHull ℝ ({a,p,q}:Set E2) ⊆ {x : E2 | 0≤(A x).2} := by
  have hc : Convex ℝ {z : ℝ×ℝ | 0≤z.2} :=
    (convex_Ici (0:ℝ)).linear_preimage (LinearMap.snd ℝ ℝ ℝ)
  apply convexHull_min _ (hc.affine_preimage A.toAffineMap)
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact ha
  · simp [hAp]
  · simp [hAq]

private theorem triangle_height_nonpos
    (p q a : E2) (A : E2 ≃ᵃ[ℝ] (ℝ×ℝ))
    (hAp : (A p).2=0) (hAq : (A q).2=0) (ha : (A a).2≤0) :
    convexHull ℝ ({a,p,q}:Set E2) ⊆ {x : E2 | (A x).2≤0} := by
  have hc : Convex ℝ {z : ℝ×ℝ | z.2≤0} :=
    (convex_Iic (0:ℝ)).linear_preimage (LinearMap.snd ℝ ℝ ℝ)
  apply convexHull_min _ (hc.affine_preimage A.toAffineMap)
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact ha
  · simp [hAp]
  · simp [hAq]

private theorem axis_halfspace_not_nhds
    (A : E2 ≃ᵃ[ℝ] (ℝ×ℝ)) (x : E2) (hx : (A x).2=0) :
    {y : E2 | 0≤(A y).2} ∉ 𝓝 x ∧ {y : E2 | (A y).2≤0} ∉ 𝓝 x := by
  have hc : Continuous A.symm := A.symm.toAffineMap.continuous_of_finiteDimensional
  constructor
  · intro h
    have ht : Tendsto (fun t : ℝ => A.symm ((A x).1,-t)) (𝓝 0) (𝓝 x) := by
      have hh : Continuous (fun t : ℝ => A.symm ((A x).1,-t)) := by fun_prop
      have hval : A.symm ((A x).1,-(0:ℝ))=x := by
        rw [neg_zero,← hx,Prod.mk.eta,A.symm_apply_apply]
      have hh' := hh.continuousAt (x:=0)
      change Tendsto _ (𝓝 0) (𝓝 (A.symm ((A x).1,-(0:ℝ)))) at hh'
      rw [hval] at hh'
      exact hh'
    have hh := ht.eventually h
    obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hh
    let t := ε/2
    have htpos : 0<t := by dsimp [t]; positivity
    have ht := hball (y:=t) (by rw [dist_zero_right,Real.norm_eq_abs,abs_of_pos htpos]; dsimp [t]; linarith)
    have hv : 0≤-t := by simpa only [A.apply_symm_apply] using ht
    linarith
  · intro h
    have ht : Tendsto (fun t : ℝ => A.symm ((A x).1,t)) (𝓝 0) (𝓝 x) := by
      have hh : Continuous (fun t : ℝ => A.symm ((A x).1,t)) := by fun_prop
      have hval : A.symm ((A x).1,(0:ℝ))=x := by
        rw [← hx,Prod.mk.eta,A.symm_apply_apply]
      have hh' := hh.continuousAt (x:=0)
      change Tendsto _ (𝓝 0) (𝓝 (A.symm ((A x).1,(0:ℝ)))) at hh'
      rw [hval] at hh'
      exact hh'
    have hh := ht.eventually h
    obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hh
    let t := ε/2
    have htpos : 0<t := by dsimp [t]; positivity
    have ht := hball (y:=t) (by rw [dist_zero_right,Real.norm_eq_abs,abs_of_pos htpos]; dsimp [t]; linarith)
    have hv : t≤0 := by simpa only [A.apply_symm_apply] using ht
    linarith

/- Interior incidence forces the actual two third vertices to lie on opposite
   sides of the common edge in every normalized affine chart. -/
private theorem opposite_triangle_heights (K : Geometry.SimplicialComplex ℝ E2) (p q a b x : E2)
    (ha : a∉({p,q}:Finset E2)) (hb : b∉({p,q}:Finset E2))
    (hfa : insert a ({p,q}:Finset E2) ∈ K.faces)
    (hfb : insert b ({p,q}:Finset E2) ∈ K.faces)
    (A : E2 ≃ᵃ[ℝ] (ℝ×ℝ)) (hAp : A p=(0,0)) (hAq : A q=(1,0))
    (hx : (A x).2=0)
    (hnh : (convexHull ℝ ({a,p,q}:Set E2) ∪ convexHull ℝ ({b,p,q}:Set E2)) ∈ 𝓝 x) :
    (0<(A a).2 ∧ (A b).2<0) ∨ ((A a).2<0 ∧ 0<(A b).2) := by
  have hAn := height_ne_zero_of_triangle K p q a ha hfa A hAp hAq
  have hBn := height_ne_zero_of_triangle K p q b hb hfb A hAp hAq
  have hp : (A p).2=0 := congrArg Prod.snd hAp
  have hq : (A q).2=0 := congrArg Prod.snd hAq
  have hn := axis_halfspace_not_nhds A x hx
  rcases lt_or_gt_of_ne hAn with hAn | hAp'
  · right
    refine ⟨hAn,?_⟩
    by_contra hb'
    apply hn.2
    apply Filter.mem_of_superset hnh
    exact union_subset (triangle_height_nonpos p q a A hp hq hAn.le)
      (triangle_height_nonpos p q b A hp hq (le_of_not_gt hb'))
  · left
    refine ⟨hAp',?_⟩
    by_contra hb'
    apply hn.1
    apply Filter.mem_of_superset hnh
    exact union_subset (triangle_height_nonneg p q a A hp hq hAp'.le)
      (triangle_height_nonneg p q b A hp hq (le_of_not_gt hb'))

private theorem affine_agreement_on_axis (p q : E2) (A : E2 ≃ᵃ[ℝ] (ℝ×ℝ))
    (hAp : A p=(0,0)) (hAq : A q=(1,0)) (f g : E2 ≃ᵃ[ℝ] E2)
    (hfp : f p=g p) (hfq : f q=g q) (x : E2) (hx : (A x).2=0) : f x=g x := by
  have hxline : AffineMap.lineMap p q (A x).1=x := by
    apply A.injective
    rw [A.apply_lineMap,hAp,hAq]
    ext <;> simp [AffineMap.lineMap_apply_module,hx]
  rw [← hxline,f.apply_lineMap,g.apply_lineMap,hfp,hfq]

/- Equality of the actual PL map with the two affine pieces on its entire
   two-triangle neighborhood, including the common edge. -/
private theorem actual_piecewise_model (F : E2 → E2) (p q a b : E2) (A : E2 ≃ᵃ[ℝ] (ℝ×ℝ))
    (hAp : A p=(0,0)) (hAq : A q=(1,0)) (ha : 0≤(A a).2) (hb : (A b).2≤0)
    (f g : E2 ≃ᵃ[ℝ] E2)
    (hFf : EqOn F f (convexHull ℝ ({a,p,q}:Set E2)))
    (hFg : EqOn F g (convexHull ℝ ({b,p,q}:Set E2))) :
    EqOn F (fun x => if 0≤(A x).2 then f x else g x)
      (convexHull ℝ ({a,p,q}:Set E2) ∪ convexHull ℝ ({b,p,q}:Set E2)) := by
  have hfp : f p=g p := (hFf (subset_convexHull ℝ _ (by simp))).symm.trans
    (hFg (subset_convexHull ℝ _ (by simp)))
  have hfq : f q=g q := (hFf (subset_convexHull ℝ _ (by simp))).symm.trans
    (hFg (subset_convexHull ℝ _ (by simp)))
  have hp : (A p).2=0 := congrArg Prod.snd hAp
  have hq : (A q).2=0 := congrArg Prod.snd hAq
  intro x hx
  change F x=(if 0≤(A x).2 then f x else g x)
  rcases hx with hx | hx
  · have hsign : 0≤(A x).2 := triangle_height_nonneg p q a A hp hq ha hx
    rw [if_pos hsign]
    exact hFf hx
  · have hsign : (A x).2≤0 := triangle_height_nonpos p q b A hp hq hb hx
    by_cases hh : 0≤(A x).2
    · rw [if_pos hh]
      exact (hFg hx).trans (affine_agreement_on_axis p q A hAp hAq f g hfp hfq x (le_antisymm hsign hh)).symm
    · rw [if_neg hh]
      exact hFg hx

private theorem positive_normal_at_axis (a b t : ℝ) (W : Set (ℝ×ℝ)) (hW : W ∈ 𝓝 (t,0))
    (hi : InjOn (fun z : ℝ×ℝ => if 0≤z.2 then z else (z.1+a*z.2,b*z.2)) W) : 0<b := by
  let T : (ℝ×ℝ) → (ℝ×ℝ) := fun z => (z.1+t,z.2)
  have hc : Continuous T := by dsimp [T]; fun_prop
  have hn : T ⁻¹' W ∈ 𝓝 (0:ℝ×ℝ) := by
    have hh := (hc.continuousAt (x:=(0:ℝ×ℝ))).preimage_mem_nhds
      (show W ∈ 𝓝 (T 0) by simpa [T] using hW)
    exact hh
  apply positive_normal_coefficient a b (T ⁻¹' W) hn
  intro x hx y hy hxy
  have hxy' : T x=T y := hi hx hy (by
    have he (z : ℝ×ℝ) :
        (if 0≤(T z).2 then T z else ((T z).1+a*(T z).2,b*(T z).2)) =
          T (if 0≤z.2 then z else (z.1+a*z.2,b*z.2)) := by
      dsimp [T]
      split_ifs <;> simp <;> ring
    change (if 0≤(T x).2 then T x else ((T x).1+a*(T x).2,b*(T x).2)) =
      (if 0≤(T y).2 then T y else ((T y).1+a*(T y).2,b*(T y).2))
    rw [he,he]
    exact congrArg T hxy)
  apply Prod.ext
  · have hh := congrArg Prod.fst hxy'
    dsimp [T] at hh
    linarith
  · have hh := congrArg Prod.snd hxy'
    exact hh

private theorem normalize_given_axis (p q : E2) (A : E2 ≃ᵃ[ℝ] (ℝ×ℝ))
    (hAp : A p=(0,0)) (hAq : A q=(1,0)) (f g : E2 ≃ᵃ[ℝ] E2)
    (hfp : f p=g p) (hfq : f q=g q) :
    ∃ (B : (ℝ×ℝ) ≃ᵃ[ℝ] E2) (a b : ℝ), b≠0 ∧
      (∀ z, f (A.symm z)=B z) ∧
      (∀ z, g (A.symm z)=B (z.1+a*z.2,b*z.2)) := by
  let B := A.symm.trans f
  let C := (A.symm.trans g).trans B.symm
  have hfix : ∀ t : ℝ, C (t,0)=(t,0) := by
    intro t
    have he := affine_agreement_on_axis p q A hAp hAq f g hfp hfq
      (A.symm (t,0)) (by simp)
    change B.symm (g (A.symm (t,0)))=(t,0)
    rw [← he]
    exact B.symm_apply_apply _
  obtain ⟨a,b,hb,hform⟩ := affine_axis_normal_form C hfix
  refine ⟨B,a,b,hb,fun _ => rfl,?_⟩
  intro z
  have hh := congrArg B (hform z)
  simpa [C] using hh

/- The complete positive shear chart is extracted from the actual pair of
   incident triangles and injectivity of F on their union. -/
private theorem support_ActualAffineModels_3 (K : Geometry.SimplicialComplex ℝ E2) (F : E2 → E2) (p q u v x : E2)
    (hpq : p≠q) (hu : u∉({p,q}:Finset E2)) (hv : v∉({p,q}:Finset E2))
    (hfu : insert u ({p,q}:Finset E2) ∈ K.faces)
    (hfv : insert v ({p,q}:Finset E2) ∈ K.faces)
    (hx : x ∈ segment ℝ p q)
    (hnh : (convexHull ℝ ({u,p,q}:Set E2) ∪ convexHull ℝ ({v,p,q}:Set E2)) ∈ 𝓝 x)
    (f g : E2 ≃ᵃ[ℝ] E2)
    (hFf : EqOn F f (convexHull ℝ ({u,p,q}:Set E2)))
    (hFg : EqOn F g (convexHull ℝ ({v,p,q}:Set E2)))
    (hi : InjOn F (convexHull ℝ ({u,p,q}:Set E2) ∪ convexHull ℝ ({v,p,q}:Set E2))) :
    ∃ (A : E2 ≃ᵃ[ℝ] (ℝ×ℝ)) (B : (ℝ×ℝ) ≃ᵃ[ℝ] E2) (a b : ℝ),
      A p=(0,0) ∧ A q=(1,0) ∧ 0<b ∧
      EqOn F (fun y => B (if 0≤(A y).2 then A y else
        ((A y).1+a*(A y).2,b*(A y).2)))
        (convexHull ℝ ({u,p,q}:Set E2) ∪ convexHull ℝ ({v,p,q}:Set E2)) := by
  obtain ⟨A,hAp,hAq⟩ := edge_axis_chart p q hpq
  have hx0 : (A x).2=0 := by
    obtain ⟨t,ht,rfl⟩ := (segment_eq_image_lineMap ℝ p q) ▸ hx
    rw [A.apply_lineMap,hAp,hAq]
    simp [AffineMap.lineMap_apply_module]
  have hfp : f p=g p := (hFf (subset_convexHull ℝ _ (by simp))).symm.trans
    (hFg (subset_convexHull ℝ _ (by simp)))
  have hfq : f q=g q := (hFf (subset_convexHull ℝ _ (by simp))).symm.trans
    (hFg (subset_convexHull ℝ _ (by simp)))
  have hnorm (u v : E2) (f g : E2 ≃ᵃ[ℝ] E2)
      (hu : 0≤(A u).2) (hv : (A v).2≤0)
      (hFf : EqOn F f (convexHull ℝ ({u,p,q}:Set E2)))
      (hFg : EqOn F g (convexHull ℝ ({v,p,q}:Set E2)))
      (hfp : f p=g p) (hfq : f q=g q)
      (hnh : (convexHull ℝ ({u,p,q}:Set E2) ∪ convexHull ℝ ({v,p,q}:Set E2)) ∈ 𝓝 x)
      (hi : InjOn F (convexHull ℝ ({u,p,q}:Set E2) ∪ convexHull ℝ ({v,p,q}:Set E2))) :
      ∃ (B : (ℝ×ℝ) ≃ᵃ[ℝ] E2) (a b : ℝ), 0<b ∧
        EqOn F (fun y => B (if 0≤(A y).2 then A y else
          ((A y).1+a*(A y).2,b*(A y).2)))
          (convexHull ℝ ({u,p,q}:Set E2) ∪ convexHull ℝ ({v,p,q}:Set E2)) := by
    obtain ⟨B,a,b,hb,hpos,hneg⟩ := normalize_given_axis p q A hAp hAq f g hfp hfq
    have hmodel := actual_piecewise_model F p q u v A hAp hAq hu hv f g hFf hFg
    let W := convexHull ℝ ({u,p,q}:Set E2) ∪ convexHull ℝ ({v,p,q}:Set E2)
    have heq : EqOn F (fun y => B (if 0≤(A y).2 then A y else
        ((A y).1+a*(A y).2,b*(A y).2))) W := by
      intro y hy
      rw [hmodel hy]
      dsimp only
      by_cases h : 0≤(A y).2
      · rw [if_pos h,if_pos h]
        simpa using hpos (A y)
      · rw [if_neg h,if_neg h]
        simpa using hneg (A y)
    have hn : A.symm ⁻¹' W ∈ 𝓝 ((A x).1,0) := by
      have hc : Continuous (A.symm : (ℝ×ℝ) → E2) := A.symm.toAffineMap.continuous_of_finiteDimensional
      have hh := (hc.continuousAt (x:=A x)).preimage_mem_nhds
        (show W ∈ 𝓝 (A.symm (A x)) by simpa using hnh)
      simpa only [← hx0,Prod.mk.eta] using hh
    have hbpos : 0<b := by
      apply positive_normal_at_axis a b (A x).1 (A.symm ⁻¹' W) hn
      intro z hz t ht hzt
      apply A.symm.injective
      apply hi hz ht
      rw [heq hz,heq ht]
      simpa only [A.apply_symm_apply] using congrArg B hzt
    exact ⟨B,a,b,hbpos,heq⟩
  rcases opposite_triangle_heights K p q u v x hu hv hfu hfv A hAp hAq hx0 hnh with hside | hside
  · obtain ⟨B,a,b,hb,heq⟩ := hnorm u v f g hside.1.le hside.2.le hFf hFg hfp hfq hnh hi
    exact ⟨A,B,a,b,hAp,hAq,hb,heq⟩
  · obtain ⟨B,a,b,hb,heq⟩ := hnorm v u g f hside.2.le hside.1.le hFg hFf hfp.symm hfq.symm
      (by simpa only [union_comm] using hnh) (by simpa only [union_comm] using hi)
    exact ⟨A,B,a,b,hAp,hAq,hb,by simpa only [union_comm] using heq⟩
end VM03CapV437TrackedEdges
noncomputable section
open Set Function
open scoped Topology
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Topology.PiecewiseLinear
namespace VM03CapV437TrackedEdges

private theorem zero_sphere_pair {P : Set E2} (hP : IsPLSphere 0 P) :
    ∃ a b : E2, a≠b ∧ P={a,b} := by
  obtain ⟨f,hf⟩ := hP
  let a : Fin 2 → ℝ := ![1,0]
  let b : Fin 2 → ℝ := ![0,1]
  have ha : a ∈ stdSimplexBoundary 1 := by
    refine ⟨?_,1,by simp [a]⟩
    constructor
    · intro i; fin_cases i <;> simp [a]
    · simp [a,Fin.sum_univ_two]
  have hb : b ∈ stdSimplexBoundary 1 := by
    refine ⟨?_,0,by simp [b]⟩
    constructor
    · intro i; fin_cases i <;> simp [b]
    · simp [b,Fin.sum_univ_two]
  have hab : a≠b := by intro h; have hh := congrFun h 0; norm_num [a,b] at hh
  have hbound : stdSimplexBoundary 1={a,b} := by
    apply Subset.antisymm
    · rintro x ⟨⟨hx,hxs⟩,i,hi⟩
      rw [Fin.sum_univ_two] at hxs
      fin_cases i
      · change x 0=0 at hi
        right
        funext j
        fin_cases j <;> simp [b] <;> linarith
      · change x 1=0 at hi
        left
        funext j
        fin_cases j <;> simp [a] <;> linarith
    · rintro x (rfl|rfl) <;> assumption
  refine ⟨f a,f b,fun h => hab (hf.bijOn.injOn ha hb h),?_⟩
  rw [← hf.image_eq,hbound]
  simp

private theorem zero_ball_singleton {P : Set E2} (hP : IsPLBall 0 P) :
    ∃ a : E2, P={a} := by
  obtain ⟨a,ha⟩ := hP.nonempty
  exact ⟨a,Set.Subset.antisymm (fun x hx => hP.subsingleton_of_zero hx ha)
    (singleton_subset_iff.mpr ha)⟩

/- The actual edge link of a PL disk has one or two vertices; these are exactly
   the third vertices of the incident triangles. -/
private theorem edge_cofaces (K : Geometry.SimplicialComplex ℝ E2) [Finite K.faces]
    (hK : IsPLBall 2 K.space) (e : Finset E2) (he : e ∈ K.faces) (hec : e.card=2) :
    (∃ a : E2, a ∉ e ∧ insert a e ∈ K.faces ∧
      ∀ s ∈ K.faces, e ⊆ s → s=e ∨ s=insert a e) ∨
    (∃ a b : E2, a≠b ∧ a ∉ e ∧ b ∉ e ∧ insert a e ∈ K.faces ∧ insert b e ∈ K.faces ∧
      ∀ s ∈ K.faces, e ⊆ s → s=e ∨ s=insert a e ∨ s=insert b e) := by
  classical
  let L := DifferentialGeometry.Topology.SimplicialComplex.geometricLink K e
  have hL : IsPLSphere 0 L.space ∨ IsPLBall 0 L.space :=
    isPLSphere_or_isPLBall_geometricLink_faces_of_isPLBall (m:=1) K hK he (k:=1) hec (by omega)
  have hvertex (a : E2) (ha : a ∈ L.space) : a ∉ e ∧ insert a e ∈ K.faces := by
    obtain ⟨t,ht,hat⟩ := L.mem_space_iff.mp ha
    have htc : t.card ≤ 1 := by
      simpa using card_le_of_isPLBall_or_isPLSphere L hL.symm ht
    have htn : t.Nonempty := L.nonempty_of_mem_faces ht
    have ht1 : t.card=1 := by have := Finset.card_pos.mpr htn; omega
    obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp ht1
    have hav : a=v := by simpa using hat
    subst a
    change ({v}:Finset E2).Nonempty ∧ Disjoint e {v} ∧ e ∪ {v} ∈ K.faces at ht
    exact ⟨by simpa using ht.2.1,by simpa [Finset.union_comm] using ht.2.2⟩
  have hcoface (s : Finset E2) (hs : s ∈ K.faces) (hes : e ⊆ s) :
      s=e ∨ ∃ a ∈ L.space, s=insert a e := by
    by_cases hse : s=e
    · exact Or.inl hse
    have hsc : s.card ≤ 3 := card_le_of_isPLBall_or_isPLSphere K (Or.inl hK) hs
    have hlt : e.card<s.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hes,Ne.symm hse⟩)
    have hsd : (s \ e).card=1 := by rw [Finset.card_sdiff_of_subset hes,hec]; omega
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hsd
    have hno : a ∉ e := by
      have hh : a ∈ s \ e := by rw [ha]; simp
      exact (Finset.mem_sdiff.mp hh).2
    have hse' : s=insert a e := by
      have hh := Finset.union_sdiff_of_subset hes
      rw [ha] at hh
      simpa [Finset.union_comm] using hh.symm
    have hsf : ({a}:Finset E2) ∈ L.faces := by
      change ({a}:Finset E2).Nonempty ∧ Disjoint e {a} ∧ e ∪ {a} ∈ K.faces
      exact ⟨Finset.singleton_nonempty _,by simpa using hno,by simpa [hse',Finset.union_comm] using hs⟩
    exact Or.inr ⟨a,L.convexHull_subset_space hsf (by simp),hse'⟩
  rcases hL with hL | hL
  · obtain ⟨a,b,hab,hspace⟩ := zero_sphere_pair hL
    have ha : a ∈ L.space := hspace ▸ (by simp : a ∈ ({a,b}:Set E2))
    have hb : b ∈ L.space := hspace ▸ (by simp : b ∈ ({a,b}:Set E2))
    refine Or.inr ⟨a,b,hab,(hvertex a ha).1,(hvertex b hb).1,(hvertex a ha).2,(hvertex b hb).2,?_⟩
    intro s hs hes
    rcases hcoface s hs hes with heq | ⟨c,hc,hsc⟩
    · exact Or.inl heq
    · rw [hspace] at hc
      rcases hc with rfl | rfl
      · exact Or.inr (Or.inl hsc)
      · exact Or.inr (Or.inr hsc)
  · obtain ⟨a,hspace⟩ := zero_ball_singleton hL
    have ha : a ∈ L.space := hspace ▸ (by simp : a ∈ ({a}:Set E2))
    refine Or.inl ⟨a,(hvertex a ha).1,(hvertex a ha).2,?_⟩
    intro s hs hes
    rcases hcoface s hs hes with heq | ⟨c,hc,hsc⟩
    · exact Or.inl heq
    · rw [hspace] at hc
      have hca : c=a := hc
      subst c
      exact Or.inr hsc


/- For an interior edge the singleton-link alternative is impossible: its
   single triangle would contain a neighborhood of an open edge point. -/
private theorem support_EdgeIncidence_1 (K : Geometry.SimplicialComplex ℝ E2) [Finite K.faces]
    (hK : IsPLBall 2 K.space) (e : Finset E2) (he : e ∈ K.faces) (hec : e.card=2)
    (x : E2) (hxe : x ∈ openSimplex e) (hxK : K.space ∈ 𝓝 x) :
    ∃ a b : E2, a≠b ∧ a ∉ e ∧ b ∉ e ∧ insert a e ∈ K.faces ∧ insert b e ∈ K.faces ∧
      (∀ s ∈ K.faces, e ⊆ s → s=e ∨ s=insert a e ∨ s=insert b e) ∧
      (convexHull ℝ ((insert a e:Finset E2):Set E2) ∪
        convexHull ℝ ((insert b e:Finset E2):Set E2)) ∈ 𝓝 x := by
  classical
  rcases edge_cofaces K hK e he hec with ⟨a,ha,hfa,hco⟩ | ⟨a,b,hab,ha,hb,hfa,hfb,hco⟩
  · have hnh : convexHull ℝ ((insert a e:Finset E2):Set E2) ∈ 𝓝 x := by
      apply Filter.mem_of_superset (closedStar_mem_nhds K hxK)
      intro y hy
      obtain ⟨s,⟨hs,hxs⟩,hys⟩ := mem_iUnion₂.mp hy
      have hes := face_subset_of_mem_openSimplex_of_mem_convexHull K he hs hxe hxs
      rcases hco s hs hes with hs0 | hs1
      · rw [hs0] at hys
        simpa only [Finset.coe_insert] using (convexHull_mono (by simp : (e:Set E2) ⊆ (insert a e:Set E2)) hys)
      · simpa [hs1] using hys
    have hxi : x ∈ interior (convexHull ℝ ((insert a e:Finset E2):Set E2)) := mem_interior_iff_mem_nhds.mpr hnh
    rw [interior_convexHull_eq_openSimplex (K.indep hfa)
      (by simpa [Finset.card_insert_of_notMem ha,hec])] at hxi
    have heq := face_eq_of_mem_openSimplex K he hfa hxe hxi
    have hh := congrArg Finset.card heq
    simp [Finset.card_insert_of_notMem ha,hec] at hh
  · refine ⟨a,b,hab,ha,hb,hfa,hfb,hco,?_⟩
    apply Filter.mem_of_superset (closedStar_mem_nhds K hxK)
    intro y hy
    obtain ⟨s,⟨hs,hxs⟩,hys⟩ := mem_iUnion₂.mp hy
    have hes := face_subset_of_mem_openSimplex_of_mem_convexHull K he hs hxe hxs
    rcases hco s hs hes with hs0 | hs1 | hs2
    · rw [hs0] at hys
      exact Or.inl (by simpa only [Finset.coe_insert] using (convexHull_mono (by simp : (e:Set E2) ⊆ (insert a e:Set E2)) hys))
    · exact Or.inl (by simpa [hs1] using hys)
    · exact Or.inr (by simpa [hs2] using hys)
end VM03CapV437TrackedEdges
noncomputable section
open Set Function Filter Metric
open scoped Topology
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Topology.PiecewiseLinear
namespace VM03CapV437TrackedEdges

private theorem triangle_axis_is_edge (p q a : E2) (ha : a∉({p,q}:Finset E2))
    (A : E2 ≃ᵃ[ℝ] (ℝ×ℝ)) (hAp : A p=(0,0)) (hAq : A q=(1,0)) (haa : (A a).2≠0)
    (x : E2) (hx : x ∈ convexHull ℝ ({a,p,q}:Set E2)) (hx0 : (A x).2=0) :
    x ∈ segment ℝ p q := by
  classical
  have hz0 (z : E2) (hz : z ∈ segment ℝ p q) : (A z).2=0 := by
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    rw [A.apply_lineMap,hAp,hAq]
    simp [AffineMap.lineMap_apply_module]
  rcases exists_combo_of_mem_convexHull_insert ha (by simpa using hx) with rfl | ⟨z,hz,s,hs,hs1,hx⟩
  · exact (haa hx0).elim
  · have hze : z ∈ segment ℝ p q := by simpa only [Finset.coe_pair,convexHull_pair] using hz
    have hxline : x=AffineMap.lineMap a z s := by rw [hx]; simp [AffineMap.lineMap_apply_module]; module
    have h0 := congrArg Prod.snd (congrArg A hxline)
    rw [A.apply_lineMap] at h0
    simp only [AffineMap.lineMap_apply_module,hx0] at h0
    change 0=(1-s)*(A a).2+s*(A z).2 at h0
    rw [hz0 z hze] at h0
    have hs' : s=1 := by
      have he : (1-s)*(A a).2=0 := by nlinarith [h0]
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right haa) |>.symm
    rw [hxline,hs',AffineMap.lineMap_apply_one]
    exact hze

/- A collar of the closed edge can have its closure leave the desired open
   two-triangle neighborhood only at the two vertices. -/
private theorem closed_edge_patch (p q : E2) (V : Set E2) (hV : IsOpen V)
    (hcover : segment ℝ p q \ ({p,q}:Set E2) ⊆ V) :
    ∃ U : Set E2, IsOpen U ∧ Bornology.IsBounded U ∧
      segment ℝ p q \ ({p,q}:Set E2) ⊆ U ∧ U ⊆ V ∧
      closure U ⊆ V ∪ ({p,q}:Set E2) := by
  let C := segment ℝ p q
  have hC : IsCompact C := by
    dsimp [C]
    rw [← convexHull_pair]
    exact (Set.toFinite ({p,q}:Set E2)).isCompact_convexHull ℝ
  have hCne : C.Nonempty := ⟨p,left_mem_segment ℝ p q⟩
  by_cases hVc : Vᶜ=∅
  · have hVu : V=univ := compl_empty_iff.mp hVc
    refine ⟨thickening 1 C,isOpen_thickening,hC.isBounded.thickening,?_,?_,?_⟩
    · intro x hx
      exact self_subset_thickening zero_lt_one C hx.1
    · simp [hVu]
    · simp [hVu]
  have hVcne : Vᶜ.Nonempty := nonempty_iff_ne_empty.mpr hVc
  let U := thickening 1 C ∩ {x : E2 | infDist x C < infDist x Vᶜ / 2}
  have hU : IsOpen U := isOpen_thickening.inter
    (isOpen_lt (continuous_infDist_pt _) ((continuous_infDist_pt _).div_const 2))
  have hUV : U ⊆ V := by
    intro x hx
    by_contra hn
    have hh : infDist x C < infDist x Vᶜ / 2 := hx.2
    rw [infDist_zero_of_mem (show x∈Vᶜ from hn)] at hh
    have := infDist_nonneg (x:=x) (s:=C)
    linarith
  have hcl : closure U ⊆ {x : E2 | infDist x C ≤ infDist x Vᶜ/2} := by
    apply closure_minimal (s:=U) (t:={x : E2 | infDist x C ≤ infDist x Vᶜ/2})
      (by
        intro x hx
        change infDist x C ≤ infDist x Vᶜ/2
        exact le_of_lt hx.2)
    exact isClosed_le (continuous_infDist_pt _) ((continuous_infDist_pt _).div_const 2)
  refine ⟨U,hU,hC.isBounded.thickening.subset inter_subset_left,?_,hUV,?_⟩
  · intro x hx
    refine ⟨self_subset_thickening zero_lt_one C hx.1,?_⟩
    change infDist x C < infDist x Vᶜ/2
    rw [infDist_zero_of_mem (show x∈C from hx.1)]
    have hd : 0 < infDist x Vᶜ := hV.isClosed_compl.notMem_iff_infDist_pos hVcne |>.mp
      (show x∉Vᶜ by simpa using hcover hx)
    linarith
  · intro x hx
    by_cases hxV : x∈V
    · exact Or.inl hxV
    · right
      have hh : infDist x C ≤ infDist x Vᶜ/2 := hcl hx
      rw [infDist_zero_of_mem (show x∈Vᶜ from hxV)] at hh
      have hd : infDist x C=0 := le_antisymm (by simpa using hh) infDist_nonneg
      have hxC : x∈C := hC.isClosed.mem_iff_infDist_zero hCne |>.mpr hd
      by_contra hxp
      exact hxV (hcover ⟨hxC,hxp⟩)

/- On the frontier of such a patch, the model axis can meet the two triangles
   only at exceptional vertices. -/
private theorem support_TriangleFrontier_1 (p q : E2) (A : E2 ≃ᵃ[ℝ] (ℝ×ℝ)) (W U : Set E2)
    (hU : IsOpen U) (hcover : segment ℝ p q \ ({p,q}:Set E2) ⊆ U)
    (hcl : closure U ⊆ W ∪ ({p,q}:Set E2))
    (haxis : ∀ x∈W, (A x).2=0 → x∈segment ℝ p q) :
    ∀ x∈frontier U, x∉({p,q}:Set E2) → (A x).2≠0 := by
  intro x hxf hxp hx0
  have hxcl : x∈closure U := frontier_subset_closure hxf
  have hxW : x∈W := (hcl hxcl).resolve_right hxp
  have hxU := hcover ⟨haxis x hxW hx0,hxp⟩
  rw [frontier,hU.interior_eq] at hxf
  exact hxf.2 hxU
end VM03CapV437TrackedEdges
noncomputable section
open Set Function
open scoped ContDiff
open SeifertSurfaces.AppendixACoordinates
namespace VM03CapV437TrackedEdges

private theorem rank_one_injective
    (a α b β κ : ℝ) (hb : 0 < b) (hκ : 0 ≤ κ)
    (hsmall : |β|+κ*(|a*β-α*b|+|β|) < b)
    (P : (ℝ × ℝ) → ℝ)
    (hP : ∀ x y : ℝ × ℝ,
      |P x-P y| ≤ (1+κ)*|x.2-y.2|+κ*|x.1-y.1|) :
    Injective (fun z : ℝ × ℝ => (z.1+a*z.2+α*P z,b*z.2+β*P z)) := by
  intro x y hxy
  have h1 := congrArg Prod.fst hxy
  have h2 := congrArg Prod.snd hxy
  dsimp only at h1 h2
  have hx : b*(x.1-y.1) = (a*β-α*b)*(P x-P y) := by linear_combination b*h1-a*h2
  have hy : b*(x.2-y.2) = -β*(P x-P y) := by nlinarith [h2]
  have hxabs : b*|x.1-y.1| = |a*β-α*b| *|P x-P y| := by
    simpa only [abs_mul,abs_of_pos hb] using congrArg abs hx
  have hyabs : b*|x.2-y.2| = |β| *|P x-P y| := by
    simpa only [abs_mul,abs_of_pos hb,abs_neg] using congrArg abs hy
  have hp := mul_le_mul_of_nonneg_left (hP x y) hb.le
  have hP0 : P x-P y=0 := by
    apply abs_eq_zero.mp
    nlinarith [abs_nonneg (P x-P y)]
  rw [hP0,mul_zero] at hx hy
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hb.ne'))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hb.ne'))

private theorem rank_one_surjective
    (a α b β κ : ℝ) (hb : 0 < b) (hκ : 0 ≤ κ)
    (hsmall : |β|+κ*(|a*β-α*b|+|β|) < b)
    (P : (ℝ × ℝ) → ℝ)
    (hP : ∀ x y : ℝ × ℝ,
      |P x-P y| ≤ (1+κ)*|x.2-y.2|+κ*|x.1-y.1|) :
    Surjective (fun z : ℝ × ℝ => (z.1+a*z.2+α*P z,b*z.2+β*P z)) := by
  intro z
  let k : ℝ := (|β|+κ*(|a*β-α*b|+|β|))/b
  have hk0 : 0 ≤ k := div_nonneg (by positivity) hb.le
  have hk1 : k<1 := (div_lt_one hb).mpr hsmall
  let v : ℝ → ℝ × ℝ := fun s => (z.1-a*z.2/b+(a*β-α*b)/b*s,(z.2-β*s)/b)
  let f : ℝ → ℝ := fun s => P (v s)
  have hf : ContractingWith ⟨k,hk0⟩ f := by
    refine ⟨by exact_mod_cast hk1,LipschitzWith.of_dist_le_mul ?_⟩
    intro s t
    rw [Real.dist_eq,Real.dist_eq]
    change |P (v s)-P (v t)| ≤ k*|s-t|
    have h := hP (v s) (v t)
    have hv1 : (v s).1-(v t).1=(a*β-α*b)/b*(s-t) := by dsimp [v]; ring
    have hv2 : (v s).2-(v t).2=(-β/b)*(s-t) := by dsimp [v]; ring
    rw [hv1,hv2,abs_mul,abs_mul,abs_div,abs_div,abs_of_pos hb,abs_neg] at h
    convert h using 1
    dsimp [k]
    ring
  let s := ContractingWith.fixedPoint f hf
  have hs : P (v s)=s := hf.fixedPoint_isFixedPt
  refine ⟨v s,?_⟩
  dsimp only
  rw [hs]
  apply Prod.ext <;> dsimp [v] <;> field_simp <;> ring

private theorem image_eq_of_bijective_eqOn_compl {X Y : Type*}
    (F G : X → Y) (U : Set X) (hF : Bijective F) (hG : Bijective G)
    (hEq : EqOn F G Uᶜ) : F '' U=G '' U := by
  apply Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy⟩ := hG.2 (F x)
    refine ⟨y,?_,hy⟩
    by_contra hyn
    have hyx : y=x := hF.1 ((hEq hyn).trans hy)
    exact hyn (hyx ▸ hx)
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy⟩ := hF.2 (G x)
    refine ⟨y,?_,hy⟩
    by_contra hyn
    have hyx : y=x := hG.1 ((hEq hyn).symm.trans hy)
    exact hyn (hyx ▸ hx)

private theorem pair_norm_difference (r s t u : ℝ) :
    |‖r • (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))+
        s • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)‖ -
      ‖t • (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))+
        u • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)‖| ≤ |r-t|+|s-u| := by
  let e₀ : E2 := EuclideanSpace.single 0 1
  let e₁ : E2 := EuclideanSpace.single 1 1
  change |‖r • e₀+s • e₁‖-‖t • e₀+u • e₁‖| ≤ _
  have h₀ : ‖e₀‖=1 := by simp [e₀]
  have h₁ : ‖e₁‖=1 := by simp [e₁]
  have hid : (r • e₀+s • e₁)-(t • e₀+u • e₁)=(r-t) • e₀+(s-u) • e₁ := by module
  have h := dist_norm_norm_le (r • e₀+s • e₁) (t • e₀+u • e₁)
  rw [Real.dist_eq,hid] at h
  exact h.trans ((norm_add_le _ _).trans_eq (by
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,h₀,h₁,mul_one,mul_one]))

private theorem compact_smooth_lipschitz (g : (ℝ × ℝ) → ℝ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ K : NNReal, LipschitzWith K g := by
  have hd := hg.continuous_fderiv (by simp)
  have hb := ((hc.fderiv ℝ).isCompact_range hd).isBounded
  obtain ⟨C,hC⟩ := hb.exists_norm_le
  let K : NNReal := ⟨max C 0,le_max_right _ _⟩
  refine ⟨K,lipschitzWith_of_nnnorm_fderiv_le (hg.differentiable (by simp)) ?_⟩
  intro x
  exact_mod_cast (hC _ (mem_range_self x)).trans (le_max_left C 0)

private theorem small_open_width (U : Set (ℝ×ℝ)) (hU : IsOpen U)
    (hbounded : Bornology.IsBounded U) (κ : ℝ) (hκ : 0 < κ) :
    ∃ η : (ℝ×ℝ) → ℝ, ContDiff ℝ ∞ η ∧ (∀ z, 0 ≤ η z) ∧
      (∀ z ∈ U, 0 < η z) ∧ (∀ z ∉ U, η z=0) ∧
      (∀ x y, |η x-η y| ≤ κ*(|x.1-y.1|+|x.2-y.2|)) := by
  obtain ⟨g,hgs,hg,hgrange⟩ := hU.exists_contDiff_support_eq (n:=(⊤ : ℕ∞))
  have hcpt : HasCompactSupport g := by
    change IsCompact (closure (Function.support g))
    rw [hgs]
    exact hbounded.isCompact_closure
  obtain ⟨K,hK⟩ := compact_smooth_lipschitz g hg hcpt
  let c : ℝ := κ/((K:ℝ)+1)
  have hc : 0<c := div_pos hκ (by positivity)
  have hcK : c*(K:ℝ) ≤ κ := by
    have heq : c*((K:ℝ)+1)=κ := by dsimp [c]; field_simp
    nlinarith
  refine ⟨fun z => c*g z,contDiff_const.mul hg,?_,?_,?_,?_⟩
  · intro z
    exact mul_nonneg hc.le (hgrange (mem_range_self z)).1
  · intro z hz
    apply mul_pos hc
    have hgz : g z ≠ 0 := by
      change z ∈ Function.support g
      rw [hgs]
      exact hz
    exact lt_of_le_of_ne (hgrange (mem_range_self z)).1 hgz.symm
  · intro z hz
    have hgz : g z=0 := by
      by_contra h
      apply hz
      rw [← hgs]
      exact h
    dsimp only
    rw [hgz,mul_zero]
  · intro x y
    rw [← mul_sub,abs_mul,abs_of_pos hc]
    have hk := hK.dist_le_mul x y
    rw [Real.dist_eq,Prod.dist_eq,Real.dist_eq,Real.dist_eq] at hk
    have hsum : max |x.1-y.1| |x.2-y.2| ≤ |x.1-y.1|+|x.2-y.2| :=
      max_le (by linarith [abs_nonneg (x.2-y.2)]) (by linarith [abs_nonneg (x.1-y.1)])
    calc
      _ ≤ c*((K:ℝ)*max |x.1-y.1| |x.2-y.2|) := mul_le_mul_of_nonneg_left hk hc.le
      _ ≤ c*(K:ℝ)*(|x.1-y.1|+|x.2-y.2|) := by nlinarith [mul_nonneg hc.le K.coe_nonneg]
      _ ≤ κ*(|x.1-y.1|+|x.2-y.2|) := mul_le_mul_of_nonneg_right hcK (by positivity)

private theorem open_edge_smoothing (U : Set (ℝ×ℝ)) (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (ap am bp bm : ℝ) (hbp : 0 < bp) (hbm : 0 < bm) :
    ∃ F : (ℝ × ℝ) → (ℝ × ℝ), Bijective F ∧
      (∃ K : NNReal, LipschitzWith K F) ∧
      (∀ z ∈ U, ContDiffAt ℝ ∞ F z) ∧
      (∀ z, z.2 ≠ 0 → ContDiffAt ℝ ∞ F z) ∧
      (∀ z, z ∉ U →
        F z = if 0 ≤ z.2 then (z.1+ap*z.2,bp*z.2) else (z.1+am*z.2,bm*z.2)) ∧
      F '' U =
        (fun z : ℝ × ℝ => if 0 ≤ z.2 then (z.1+ap*z.2,bp*z.2) else (z.1+am*z.2,bm*z.2)) ''
          U := by
  let a := (ap+am)/2
  let α := (ap-am)/2
  let b := (bp+bm)/2
  let β := (bp-bm)/2
  have hb : 0<b := by dsimp [b]; linarith
  have hβ : |β|<b := by rw [abs_lt]; dsimp [β,b]; constructor <;> linarith
  let D := |a*β-α*b|+|β|
  have hD : 0 ≤ D := add_nonneg (abs_nonneg _) (abs_nonneg _)
  let κ := (b-|β|)/(2*(D+1))
  have hκ : 0<κ := div_pos (sub_pos.mpr hβ) (by positivity)
  have hsmall : |β|+κ*(|a*β-α*b|+|β|)<b := by
    change |β|+κ*D<b
    have hκeq : κ*(2*(D+1))=b-|β| := by dsimp [κ]; field_simp
    nlinarith
  obtain ⟨η,hη,hηnon,hηpos,hηzero,hηLip⟩ := small_open_width U hU hbounded κ hκ
  let e₀ : E2 := EuclideanSpace.single 0 1
  let e₁ : E2 := EuclideanSpace.single 1 1
  let V : (ℝ × ℝ) → E2 := fun z => z.2 • e₀+η z • e₁
  let P : (ℝ × ℝ) → ℝ := fun z => ‖V z‖
  let F : (ℝ × ℝ) → (ℝ × ℝ) := fun z => (z.1+a*z.2+α*P z,b*z.2+β*P z)
  have hPLip : ∀ x y : ℝ × ℝ,
      |P x-P y| ≤ (1+κ)*|x.2-y.2|+κ*|x.1-y.1| := by
    intro x y
    have hnorm := pair_norm_difference x.2 (η x) y.2 (η y)
    have hηb := hηLip x y
    change |P x-P y| ≤ |x.2-y.2|+|η x-η y| at hnorm
    nlinarith
  have hV : ContDiff ℝ ∞ V :=
    (contDiff_snd.smul contDiff_const).add (hη.smul contDiff_const)
  have hcoords (z : ℝ × ℝ) : V z 0=z.2 ∧ V z 1=η z := by
    simp [V,e₀,e₁,EuclideanSpace.single_apply]
  have hsmooth (z : ℝ × ℝ) (hne : V z ≠ 0) : ContDiffAt ℝ ∞ F z := by
    have hP : ContDiffAt ℝ ∞ P z := (contDiffAt_norm ℝ hne).comp z hV.contDiffAt
    exact ((contDiffAt_fst.add (contDiffAt_const.mul contDiffAt_snd)).add
      (contDiffAt_const.mul hP)).prodMk
      ((contDiffAt_const.mul contDiffAt_snd).add (contDiffAt_const.mul hP))
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun z =>
    if 0 ≤ z.2 then (z.1+ap*z.2,bp*z.2) else (z.1+am*z.2,bm*z.2)
  have hEq : ∀ z, z ∉ U → F z=G z := by
    intro z hz
    have hP : P z=|z.2| := by
      simp only [P,V,hηzero z hz,zero_smul,add_zero]
      rw [norm_smul,Real.norm_eq_abs]
      simp [e₀]
    dsimp only [F]
    rw [hP]
    dsimp only [G]
    split_ifs with hsign
    · rw [abs_of_nonneg hsign]
      dsimp [a,α,b,β]
      congr 1 <;> ring
    · rw [abs_of_neg (lt_of_not_ge hsign)]
      dsimp [a,α,b,β]
      congr 1 <;> ring
  have hbij : Bijective F := ⟨rank_one_injective a α b β κ hb hκ.le hsmall P hPLip,
    rank_one_surjective a α b β κ hb hκ.le hsmall P hPLip⟩
  have hPL : LipschitzWith ⟨1+2*κ,by positivity⟩ P := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have hx : |x.1-y.1| ≤ dist x y := by
      simpa only [Prod.dist_eq,Real.dist_eq] using
        (le_max_left (dist x.1 y.1) (dist x.2 y.2))
    have hy : |x.2-y.2| ≤ dist x y := by
      simpa only [Prod.dist_eq,Real.dist_eq] using
        (le_max_right (dist x.1 y.1) (dist x.2 y.2))
    have hp := hPLip x y
    change |P x-P y| ≤ (1+2*κ)*dist x y
    nlinarith [mul_le_mul_of_nonneg_left hx hκ.le,
      mul_le_mul_of_nonneg_left hy (show 0≤1+κ by positivity)]
  have hFL : ∃ K : NNReal, LipschitzWith K F := by
    have hfst : LipschitzWith 1 (Prod.fst : ℝ×ℝ → ℝ) := LipschitzWith.prod_fst
    have hsnd : LipschitzWith 1 (Prod.snd : ℝ×ℝ → ℝ) := LipschitzWith.prod_snd
    exact ⟨_, ((hfst.add ((lipschitzWith_smul a).comp hsnd)).add
      ((lipschitzWith_smul α).comp hPL)).prodMk
      (((lipschitzWith_smul b).comp hsnd).add ((lipschitzWith_smul β).comp hPL))⟩
  refine ⟨F,hbij,hFL,?_,?_,hEq,?_⟩
  · intro z hz
    apply hsmooth z
    intro heq
    have heq0 := congrArg (fun p : E2 => p 0) heq
    have heq1 := congrArg (fun p : E2 => p 1) heq
    have hz0 : z.2=0 := by simpa only [(hcoords z).1,PiLp.zero_apply] using heq0
    have hηz : 0<η z := hηpos z hz
    have : η z=0 := by simpa only [(hcoords z).2,PiLp.zero_apply] using heq1
    linarith
  · intro z hz
    apply hsmooth z
    intro heq
    exact hz (by simpa only [(hcoords z).1,PiLp.zero_apply] using congrArg (fun p : E2 => p 0) heq)

  · have hP0 : ∀ x y : ℝ × ℝ,
        |(|x.2|)-(|y.2|)| ≤ (1+κ)*|x.2-y.2|+κ*|x.1-y.1| := by
      intro x y
      have h := abs_abs_sub_abs_le_abs_sub x.2 y.2
      nlinarith [mul_nonneg hκ.le (abs_nonneg (x.2-y.2)),
        mul_nonneg hκ.le (abs_nonneg (x.1-y.1))]
    have hform : (fun z : ℝ × ℝ => (z.1+a*z.2+α*|z.2|,b*z.2+β*|z.2|)) = G := by
      funext z
      dsimp only [G]
      split_ifs with hz
      · rw [abs_of_nonneg hz]
        dsimp [a,α,b,β]
        congr 1 <;> ring
      · rw [abs_of_neg (lt_of_not_ge hz)]
        dsimp [a,α,b,β]
        congr 1 <;> ring
    have hGbij : Bijective G := by
      rw [← hform]
      exact ⟨rank_one_injective a α b β κ hb hκ.le hsmall _ hP0,
        rank_one_surjective a α b β κ hb hκ.le hsmall _ hP0⟩
    apply image_eq_of_bijective_eqOn_compl F G _ hbij hGbij
    intro z hz
    apply hEq
    exact hz

end VM03CapV437TrackedEdges

namespace VM03CapV437TrackedEdges
/- Affine transport of the paid normalized seam, including its new Lipschitz
   invariant.  Affine charts here are ordinary finite-dimensional equivalences. -/
private theorem affine_edge_smoothing (A : E2 ≃ᵃ[ℝ] (ℝ×ℝ)) (B : (ℝ×ℝ) ≃ᵃ[ℝ] E2)
    (U : Set (ℝ×ℝ)) (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (ap am bp bm : ℝ) (hbp : 0 < bp) (hbm : 0 < bm) :
    let G : E2 → E2 := fun x => B (if 0 ≤ (A x).2 then
      ((A x).1+ap*(A x).2,bp*(A x).2) else ((A x).1+am*(A x).2,bm*(A x).2))
    let V := A ⁻¹' U
    ∃ F : E2 → E2, Bijective F ∧ (∃ K : NNReal, LipschitzWith K F) ∧
      (∀ x, A x ∈ U ∨ (A x).2 ≠ 0 → ContDiffAt ℝ ∞ F x) ∧
      EqOn F G Vᶜ ∧ F '' V = G '' V := by
  dsimp only
  obtain ⟨f,hbij,hLip,hsmooth,hoff,heq,him⟩ := open_edge_smoothing U hU hbounded ap am bp bm hbp hbm
  let a : E2 →ᴬ[ℝ] (ℝ×ℝ) := ⟨A.toAffineMap,A.toAffineMap.continuous_of_finiteDimensional⟩
  let b : (ℝ×ℝ) →ᴬ[ℝ] E2 := ⟨B.toAffineMap,B.toAffineMap.continuous_of_finiteDimensional⟩
  let F : E2 → E2 := fun x => B (f (A x))
  refine ⟨F,B.bijective.comp (hbij.comp A.bijective),?_,?_,?_,?_⟩
  · obtain ⟨k,hk⟩ := hLip
    obtain ⟨ka,hka⟩ := A.toAffineMap.lipschitzWith_of_finiteDimensional
    obtain ⟨kb,hkb⟩ := B.toAffineMap.lipschitzWith_of_finiteDimensional
    exact ⟨kb*(k*ka),hkb.comp (hk.comp hka)⟩
  · intro x hx
    have hf : ContDiffAt ℝ ∞ f (A x) := hx.elim (hsmooth (A x)) (hoff (A x))
    exact b.contDiff.contDiffAt.comp x (hf.comp x a.contDiff.contDiffAt)
  · intro x hx
    exact congrArg B (heq (A x) hx)
  · let V := U
    have hA : A '' (A ⁻¹' V)=V := image_preimage_eq V A.surjective
    have him' := congrArg (fun s : Set (ℝ×ℝ) => B '' s) him
    change B '' (f '' V) = B '' ((fun z : ℝ×ℝ =>
      if 0 ≤ z.2 then (z.1+ap*z.2,bp*z.2) else (z.1+am*z.2,bm*z.2)) '' V) at him'
    have h1 : (fun x => B (f (A x))) '' (A ⁻¹' V) = B '' (f '' V) := by
      rw [← image_image B (fun x => f (A x)),← image_image f A,hA]
    have h2 : (fun x => B ((fun z : ℝ×ℝ => if 0 ≤ z.2 then
        (z.1+ap*z.2,bp*z.2) else (z.1+am*z.2,bm*z.2)) (A x))) '' (A ⁻¹' V) =
        B '' ((fun z : ℝ×ℝ => if 0 ≤ z.2 then
        (z.1+ap*z.2,bp*z.2) else (z.1+am*z.2,bm*z.2)) '' V) := by
      rw [← image_image B (fun x => (if 0 ≤ (A x).2 then
        ((A x).1+ap*(A x).2,bp*(A x).2) else ((A x).1+am*(A x).2,bm*(A x).2)))]
      rw [← image_image (fun z : ℝ×ℝ => if 0 ≤ z.2 then
        (z.1+ap*z.2,bp*z.2) else (z.1+am*z.2,bm*z.2)) A,hA]
    exact h1.trans (him'.trans h2.symm)

end VM03CapV437TrackedEdges

namespace VM03CapV437TrackedEdges
open scoped Topology

private theorem affine_edge_model_lipschitz
    (A : E2 ≃ᵃ[ℝ] (ℝ×ℝ)) (B : (ℝ×ℝ) ≃ᵃ[ℝ] E2) (ap am bp bm : ℝ) :
    ∃ K : NNReal, LipschitzWith K (fun x : E2 => B (if 0 ≤ (A x).2 then
      ((A x).1+ap*(A x).2,bp*(A x).2) else ((A x).1+am*(A x).2,bm*(A x).2))) := by
  let a := (ap+am)/2
  let α := (ap-am)/2
  let b := (bp+bm)/2
  let β := (bp-bm)/2
  let G : (ℝ×ℝ) → (ℝ×ℝ) := fun z => (z.1+a*z.2+α*|z.2|,b*z.2+β*|z.2|)
  have hform (z : ℝ×ℝ) : G z = if 0 ≤ z.2 then
      (z.1+ap*z.2,bp*z.2) else (z.1+am*z.2,bm*z.2) := by
    dsimp only [G]
    split_ifs with hz
    · rw [abs_of_nonneg hz]; dsimp [a,α,b,β]; congr 1 <;> ring
    · rw [abs_of_neg (lt_of_not_ge hz)]; dsimp [a,α,b,β]; congr 1 <;> ring
  have hfst : LipschitzWith 1 (Prod.fst : ℝ×ℝ → ℝ) := LipschitzWith.prod_fst
  have hsnd : LipschitzWith 1 (Prod.snd : ℝ×ℝ → ℝ) := LipschitzWith.prod_snd
  have habs : LipschitzWith 1 (fun z : ℝ×ℝ => |z.2|) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq,NNReal.coe_one,one_mul]
    exact (abs_abs_sub_abs_le_abs_sub x.2 y.2).trans (by simpa [Real.dist_eq] using hsnd.dist_le_mul x y)
  have hGL : ∃ K : NNReal, LipschitzWith K G :=
    ⟨_,((hfst.add ((lipschitzWith_smul a).comp hsnd)).add
      ((lipschitzWith_smul α).comp habs)).prodMk
      (((lipschitzWith_smul b).comp hsnd).add ((lipschitzWith_smul β).comp habs))⟩
  obtain ⟨k,hk⟩ := hGL
  obtain ⟨ka,hka⟩ := A.toAffineMap.lipschitzWith_of_finiteDimensional
  obtain ⟨kb,hkb⟩ := B.toAffineMap.lipschitzWith_of_finiteDimensional
  refine ⟨kb*(k*ka),?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (hkb.comp (hk.comp hka)).dist_le_mul x y
  change dist (B (G (A x))) (B (G (A y))) ≤ _ at h
  simpa only [hform] using h

/- Install the normalized edge replacement into an arbitrary ambient map F.
   The correction L-G vanishes outside V, avoiding a new piecewise seam. -/
private theorem install_affine_edge (F : E2 → E2) (hFL : ∃ K : NNReal, LipschitzWith K F)
    (A : E2 ≃ᵃ[ℝ] (ℝ×ℝ)) (B : (ℝ×ℝ) ≃ᵃ[ℝ] E2)
    (U : Set (ℝ×ℝ)) (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (ap am bp bm : ℝ) (hbp : 0 < bp) (hbm : 0 < bm) :
    let G : E2 → E2 := fun x => B (if 0 ≤ (A x).2 then
      ((A x).1+ap*(A x).2,bp*(A x).2) else ((A x).1+am*(A x).2,bm*(A x).2))
    let V := A ⁻¹' U
    ∀ S : Set E2,
      EqOn F G V →
      (∀ x ∈ frontier V, x ∉ S → F =ᶠ[𝓝 x] G) →
      (∀ x ∈ frontier V, x ∉ S → (A x).2 ≠ 0) →
      ∃ P : E2 → E2, (∃ K : NNReal, LipschitzWith K P) ∧ InjOn P V ∧
        EqOn P F Vᶜ ∧ P '' V=F '' V ∧
        (∀ x ∈ V, ContDiffAt ℝ ∞ P x) ∧
        (∀ x ∈ frontier V, x ∉ S → ContDiffAt ℝ ∞ P x) := by
  dsimp only
  intro S hFG hlocal hfront
  let G : E2 → E2 := fun x => B (if 0 ≤ (A x).2 then
      ((A x).1+ap*(A x).2,bp*(A x).2) else ((A x).1+am*(A x).2,bm*(A x).2))
  let V := A ⁻¹' U
  obtain ⟨L,hLb,hLL,hLCD,hLout,hLim⟩ := affine_edge_smoothing A B U hU hbounded ap am bp bm hbp hbm
  let P : E2 → E2 := fun x => F x+(L x-G x)
  have hPV : EqOn P L V := by
    intro x hx
    dsimp only [P]
    rw [hFG hx]
    change G x+(L x-G x)=L x
    abel
  have hPc : EqOn P F Vᶜ := by
    intro x hx
    dsimp only [P]
    rw [hLout hx]
    change F x+(G x-G x)=F x
    simp only [sub_self,add_zero]
  have hVL : IsOpen V := hU.preimage A.toAffineMap.continuous_of_finiteDimensional
  refine ⟨P,?_,?_,hPc,?_,?_,?_⟩
  · obtain ⟨a,ha⟩ := hFL
    obtain ⟨b,hb⟩ := hLL
    obtain ⟨c,hc⟩ := affine_edge_model_lipschitz A B ap am bp bm
    exact ⟨a+(b+c),ha.add (hb.sub hc)⟩
  · intro x hx y hy hxy
    exact hLb.1 (by simpa only [hPV hx,hPV hy] using hxy)
  · calc
      P '' V = L '' V := image_congr hPV
      _ = G '' V := hLim
      _ = F '' V := (image_congr hFG).symm
  · intro x hx
    apply (hLCD x (Or.inl hx)).congr_of_eventuallyEq
    filter_upwards [hVL.mem_nhds hx] with y hy
    exact hPV hy
  · intro x hx hxS
    apply (hLCD x (Or.inr (hfront x hx hxS))).congr_of_eventuallyEq
    filter_upwards [hlocal x hx hxS] with y hy
    dsimp only [P]
    rw [hy]
    change G y+(L y-G y)=L y
    abel
end VM03CapV437TrackedEdges
namespace VM03CapV437TrackedEdges
private theorem pair_open_edge (K : Geometry.SimplicialComplex ℝ E2) (p q : E2)
    (hpq : p≠q) (he : ({p,q}:Finset E2)∈K.faces) :
    segment ℝ p q \ ({p,q}:Set E2) ⊆ openSimplex ({p,q}:Finset E2) := by
  classical
  rintro x ⟨hx,hxp⟩
  have hxC : x∈convexHull ℝ (({p,q}:Finset E2):Set E2) := by
    simpa only [Finset.coe_pair,convexHull_pair] using hx
  obtain ⟨s,hs,hne,hxs⟩ := exists_openSimplex_of_mem_convexHull hxC
  by_cases hse : s=({p,q}:Finset E2)
  · simpa only [hse] using hxs
  · have hcard : s.card<2 := by
      have hh := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs,hse⟩)
      simpa [Finset.card_pair hpq] using hh
    have h1 : s.card=1 := by have hh := Finset.card_pos.mpr hne; omega
    obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp h1
    have hxa : x=a := by simpa using openSimplex_subset_convexHull _ hxs
    have ha : a∈({p,q}:Finset E2) := hs (by simp)
    exact (hxp (by simpa [hxa] using ha)).elim

/- An actual interior edge of a finite PL disk now supplies every chart,
   orientation, local agreement and frontier condition required by the sealed
   smoothing installation. The exceptional set is exactly its two endpoints. -/
private theorem actual_edge_one (K : Geometry.SimplicialComplex ℝ E2) [Finite K.faces]
    (hK : IsPLBall 2 K.space) (F : E2 → E2)
    (hFL : ∃ L : NNReal, LipschitzWith L F) (hFi : InjOn F K.space)
    (hmodels : ∀ s∈K.faces, s.card=3 → ∃ f : E2 →ᵃ[ℝ] E2,
      EqOn F f (convexHull ℝ (s:Set E2)))
    (p q : E2) (hpq : p≠q) (he : ({p,q}:Finset E2)∈K.faces)
    (hinterior : ∀ x∈openSimplex ({p,q}:Finset E2), K.space∈𝓝 x)
    (O : Set E2) (hO : IsOpen O)
    (hOC : segment ℝ p q \ ({p,q}:Set E2) ⊆ O) :
    ∃ (U : Set E2) (P : E2 → E2), IsOpen U ∧ Bornology.IsBounded U ∧
      segment ℝ p q \ ({p,q}:Set E2) ⊆ U ∧ U ⊆ interior K.space ∧ U ⊆ O ∧
      closure U ⊆ interior K.space ∪ ({p,q}:Set E2) ∧
      (∃ L : NNReal, LipschitzWith L P) ∧ InjOn P U ∧ EqOn P F Uᶜ ∧
      P '' U=F '' U ∧ (∀ x∈U, ContDiffAt ℝ ∞ P x) ∧
      (∀ x∈frontier U, x∉({p,q}:Set E2) → ContDiffAt ℝ ∞ P x) := by
  classical
  let e := ({p,q}:Finset E2)
  let x := e.centroid ℝ id
  have hxe : x∈openSimplex e := centroid_mem_openSimplex (by simp [e])
  have hec : e.card=2 := by simp [e,hpq]
  obtain ⟨u,v,huv,hu,hv,hfu,hfv,hco,hnh⟩ := support_EdgeIncidence_1 K hK e he hec x hxe
    (hinterior x hxe)
  let W := convexHull ℝ ({u,p,q}:Set E2) ∪ convexHull ℝ ({v,p,q}:Set E2)
  have hWS : W ⊆ K.space := union_subset
    (by simpa [e] using K.convexHull_subset_space hfu)
    (by simpa [e] using K.convexHull_subset_space hfv)
  have hnhAll : ∀ y∈openSimplex e, W∈𝓝 y := by
    intro y hy
    apply Filter.mem_of_superset (closedStar_mem_nhds K (hinterior y hy))
    intro z hz
    obtain ⟨s,⟨hs,hys⟩,hzs⟩ := mem_iUnion₂.mp hz
    have hes := face_subset_of_mem_openSimplex_of_mem_convexHull K he hs hy hys
    rcases hco s hs hes with hse | hsu | hsv
    · rw [hse] at hzs
      exact Or.inl (by simpa [e] using
        convexHull_mono (show (e:Set E2) ⊆ (insert u e:Set E2) by simp) hzs)
    · exact Or.inl (by simpa [hsu,e] using hzs)
    · exact Or.inr (by simpa [hsv,e] using hzs)
  have hcover : segment ℝ p q \ ({p,q}:Set E2) ⊆ interior W := by
    intro y hy
    exact mem_interior_iff_mem_nhds.mpr (hnhAll y (pair_open_edge K p q hpq he hy))
  obtain ⟨f,hf⟩ := hmodels (insert u e) hfu (by simp [Finset.card_insert_of_notMem hu,hec])
  obtain ⟨g,hg⟩ := hmodels (insert v e) hfv (by simp [Finset.card_insert_of_notMem hv,hec])
  obtain ⟨f,hf0,hf⟩ := triangle_model_equiv K F hFi (insert u e) hfu
    (by simp [Finset.card_insert_of_notMem hu,hec]) f hf
  obtain ⟨g,hg0,hg⟩ := triangle_model_equiv K F hFi (insert v e) hfv
    (by simp [Finset.card_insert_of_notMem hv,hec]) g hg
  obtain ⟨A,B,a,b,hAp,hAq,hb,hmodel⟩ := support_ActualAffineModels_3 K F p q u v x hpq hu hv hfu hfv
    (by simpa only [e,Finset.coe_pair,convexHull_pair] using openSimplex_subset_convexHull e hxe)
    (by simpa [e] using hnh) f g (by simpa [e] using hf) (by simpa [e] using hg)
    (hFi.mono hWS)
  obtain ⟨U,hU,hUb,hUC,hUV,hcl⟩ := closed_edge_patch p q (interior W ∩ O) (isOpen_interior.inter hO)
    (subset_inter hcover hOC)
  have haxis : ∀ y∈W, (A y).2=0 → y∈segment ℝ p q := by
    intro y hy hy0
    rcases hy with hy | hy
    · exact triangle_axis_is_edge p q u hu A hAp hAq
        (height_ne_zero_of_triangle K p q u hu hfu A hAp hAq) y hy hy0
    · exact triangle_axis_is_edge p q v hv A hAp hAq
        (height_ne_zero_of_triangle K p q v hv hfv A hAp hAq) y hy hy0
  have hclW : closure U ⊆ W ∪ ({p,q}:Set E2) := hcl.trans
    (union_subset_union (inter_subset_left.trans interior_subset) subset_rfl)
  have hfront := support_TriangleFrontier_1 p q A W U hU hUC hclW haxis
  let V := A '' U
  have hAV : A ⁻¹' V=U := preimage_image_eq U A.injective
  have hV : IsOpen V := by
    have heq : V=A.symm ⁻¹' U := by ext z; simp [V]
    rw [heq]
    exact hU.preimage A.symm.toAffineMap.continuous_of_finiteDimensional
  have hVb : Bornology.IsBounded V := by
    obtain ⟨c,hc⟩ := A.toAffineMap.lipschitzWith_of_finiteDimensional
    exact hc.isBounded_image hUb
  have hnorm : EqOn F (fun y => B (if 0≤(A y).2 then
      ((A y).1+0*(A y).2,1*(A y).2) else ((A y).1+a*(A y).2,b*(A y).2))) W := by
    simpa only [zero_mul,add_zero,one_mul,Prod.mk.eta] using hmodel
  obtain ⟨P,hPL,hPi,hPe,hPim,hPC,hPfront⟩ := install_affine_edge F hFL A B V hV hVb 0 a 1 b
    zero_lt_one hb ({p,q}:Set E2)
    (by rw [hAV]; exact hnorm.mono (hUV.trans (inter_subset_left.trans interior_subset)))
    (by
      rw [hAV]
      intro y hy hyp
      have hyV : y∈interior W := ((hcl (frontier_subset_closure hy)).resolve_right hyp).1
      filter_upwards [mem_interior_iff_mem_nhds.mp hyV] with z hz
      exact hnorm hz)
    (by rw [hAV]; exact hfront)
  rw [hAV] at hPi hPe hPim hPC hPfront
  exact ⟨U,P,hU,hUb,hUC,hUV.trans (inter_subset_left.trans (interior_mono hWS)),hUV.trans inter_subset_right,
    hcl.trans (union_subset_union (inter_subset_left.trans (interior_mono hWS)) subset_rfl),
    hPL,hPi,hPe,hPim,hPC,hPfront⟩

/- A supplied PL map itself provides the common finite affine subdivision.
   Each interior edge can be installed inside any prescribed open neighborhood
   of that edge, so the paid disjoint-neighborhood family can be consumed. -/
private theorem edge_subdivision_installer (K : Geometry.SimplicialComplex ℝ E2) [Finite K.faces]
    (hK : IsPLBall 2 K.space) (F : E2 → E2)
    (hf : IsPiecewiseAffineOn F K.space) (hFi : InjOn F K.space)
    (hFL : ∃ L : NNReal, LipschitzWith L F) :
    ∃ K' : Geometry.SimplicialComplex ℝ E2, IsSubdivision K' K ∧ K'.faces.Finite ∧
      (∀ s∈K'.faces, ∃ A : E2 →ᵃ[ℝ] E2,EqOn F A (convexHull ℝ (s:Set E2))) ∧
      ∀ p q : E2, p≠q → ({p,q}:Finset E2)∈K'.faces →
      (∀ x∈openSimplex ({p,q}:Finset E2), K'.space∈𝓝 x) →
      ∀ O : Set E2, IsOpen O → segment ℝ p q \ ({p,q}:Set E2) ⊆ O →
      ∃ (U : Set E2) (P : E2 → E2), IsOpen U ∧ Bornology.IsBounded U ∧
        segment ℝ p q \ ({p,q}:Set E2) ⊆ U ∧ U ⊆ interior K'.space ∧ U ⊆ O ∧
        closure U ⊆ interior K'.space ∪ ({p,q}:Set E2) ∧
        (∃ L : NNReal, LipschitzWith L P) ∧ InjOn P U ∧ EqOn P F Uᶜ ∧
        P '' U=F '' U ∧ (∀ x∈U, ContDiffAt ℝ ∞ P x) ∧
        (∀ x∈frontier U, x∉({p,q}:Set E2) → ContDiffAt ℝ ∞ P x) := by
  obtain ⟨K',hsub,hfin,hfaces⟩ := hf.exists_isSubdivision_affineOn_faces K
  letI : Finite K'.faces := hfin.to_subtype
  refine ⟨K',hsub,hfin,hfaces,?_⟩
  intro p q hpq he hinterior O hO hOC
  have hK' : IsPLBall 2 K'.space := by rw [hsub.space_eq]; exact hK
  have hFi' : InjOn F K'.space := by rw [hsub.space_eq]; exact hFi
  exact actual_edge_one K' hK' F hFL hFi' (fun s hs _ => hfaces s hs)
    p q hpq he hinterior O hO hOC
end VM03CapV437TrackedEdges
noncomputable section
open Set Function Metric
open SeifertSurfaces.AppendixACoordinates
namespace VM03CapV437TrackedEdges

/- Open nearest-edge cells separate all finite edge interiors even when their
   closures meet at vertices.  Intersecting a prescribed open region keeps each
   patch inside the two-triangle affine chart chosen for that edge. -/
private theorem nearest_edge_patches {ι : Type*} [Fintype ι] (C : ι → Set E2) (V : ι → Set E2)
    (hC : ∀ i, IsClosed (C i)) (hCne : ∀ i, (C i).Nonempty)
    (hV : ∀ i, IsOpen (V i)) (hVb : ∀ i, Bornology.IsBounded (V i)) :
    ∃ U : ι → Set E2,
      (∀ i, IsOpen (U i) ∧ Bornology.IsBounded (U i) ∧ U i ⊆ V i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      (∀ i, {x | x ∈ C i ∧ x ∈ V i ∧ ∀ j, j ≠ i → x ∉ C j} ⊆ U i) ∧
      (∀ i j, i ≠ j → U i ∩ C j = ∅) := by
  classical
  let U : ι → Set E2 := fun i =>
    V i ∩ ⋂ j : {j : ι // j ≠ i}, {x | infDist x (C i) < infDist x (C j)}
  have hmem (i : ι) (x : E2) : x ∈ U i ↔
      x ∈ V i ∧ ∀ j, j ≠ i → infDist x (C i) < infDist x (C j) := by
    simp [U]
  refine ⟨U,?_,?_,?_,?_⟩
  · intro i
    refine ⟨(hV i).inter (isOpen_iInter_of_finite fun j =>
      isOpen_lt (continuous_infDist_pt _) (continuous_infDist_pt _)),
      (hVb i).subset inter_subset_left,inter_subset_left⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hi := (hmem i x).mp hxi
    have hj := (hmem j x).mp hxj
    exact lt_asymm (hi.2 j hij.symm) (hj.2 i hij)
  · intro i x hx
    apply (hmem i x).mpr
    refine ⟨hx.2.1,?_⟩
    intro j hji
    rw [infDist_zero_of_mem hx.1]
    exact (hC j).notMem_iff_infDist_pos (hCne j) |>.mp (hx.2.2 j hji)
  · intro i j hij
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxi,hxj⟩
    have hi := ((hmem i x).mp hxi).2 j hij.symm
    rw [infDist_zero_of_mem hxj] at hi
    exact (not_lt_of_ge infDist_nonneg) hi

open DifferentialGeometry.Topology.PiecewiseLinear

/- Actual patches for the finite triangulation, localized to the union of
   cofaces of each edge.  The index is the triangulation's own set of edges. -/
private theorem actual_triangulation_neighborhoods (K : Geometry.SimplicialComplex ℝ E2) [Finite K.faces] :
    let I := {e : K.faces // e.1.card=2}
    ∃ U : I → Set E2,
      (∀ i, IsOpen (U i) ∧ Bornology.IsBounded (U i)) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      (∀ i, openSimplex i.1.1 ⊆ U i) ∧
      (∀ i j, i ≠ j → U i ∩ convexHull ℝ (j.1.1 : Set E2)=∅) ∧
      (∀ i s, s ∈ K.faces → ¬i.1.1 ⊆ s → U i ∩ convexHull ℝ (s:Set E2)=∅) ∧
      (∀ i, frontier (U i) ∩ openSimplex i.1.1=∅) := by
  classical
  dsimp only
  let I := {e : K.faces // e.1.card=2}
  letI : Fintype I := Fintype.ofFinite I
  let C : I → Set E2 := fun i => convexHull ℝ (i.1.1 : Set E2)
  let Bad : I → Set E2 := fun i =>
    ⋃ s ∈ {s ∈ K.faces | ¬i.1.1 ⊆ s}, convexHull ℝ (s:Set E2)
  let V : I → Set E2 := fun i => thickening 1 (C i) ∩ (Bad i)ᶜ
  have hC : ∀ i, IsCompact (C i) := fun i => i.1.1.finite_toSet.isCompact_convexHull ℝ
  have hBad : ∀ i, IsClosed (Bad i) := by
    intro i
    apply ((Set.toFinite K.faces).subset (Set.sep_subset _ _)).isClosed_biUnion
    intro s hs
    exact (s.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hne : ∀ i, (C i).Nonempty := by
    intro i
    obtain ⟨v,hv⟩ := K.nonempty_of_mem_faces i.1.2
    exact ⟨v,subset_convexHull ℝ _ hv⟩
  have hV : ∀ i, IsOpen (V i) := fun i => isOpen_thickening.inter (hBad i).isOpen_compl
  have hVb : ∀ i, Bornology.IsBounded (V i) := fun i =>
    (hC i).isBounded.thickening.subset inter_subset_left
  have hopen (i : I) (x : E2) (hx : x ∈ openSimplex i.1.1) : x ∈ V i := by
    refine ⟨self_subset_thickening zero_lt_one (C i) (openSimplex_subset_convexHull _ hx),?_⟩
    intro hxb
    obtain ⟨s,⟨hs,hns⟩,hxs⟩ := mem_iUnion₂.mp hxb
    exact hns (face_subset_of_mem_openSimplex_of_mem_convexHull K i.1.2 hs hx hxs)
  obtain ⟨U,hU,hdis,hcover,havoid⟩ := nearest_edge_patches C V
    (fun i => (hC i).isClosed) hne hV hVb
  have hUC : ∀ i, openSimplex i.1.1 ⊆ U i := by
    intro i x hx
    apply hcover i
    refine ⟨openSimplex_subset_convexHull _ hx,hopen i x hx,?_⟩
    intro j hji hxj
    have hij : i.1.1 ⊆ j.1.1 :=
      face_subset_of_mem_openSimplex_of_mem_convexHull K i.1.2 j.1.2 hx hxj
    have heq : i.1.1=j.1.1 := Finset.eq_of_subset_of_card_le hij (by rw [i.2,j.2])
    exact hji (Subtype.ext (Subtype.ext heq.symm))
  refine ⟨U,fun i => ⟨(hU i).1,(hU i).2.1⟩,hdis,hUC,havoid,?_,?_⟩
  · intro i s hs hns
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx,hxs⟩
    have hxV := (hU i).2.2 hx
    exact hxV.2 (mem_iUnion₂.mpr ⟨s,⟨hs,hns⟩,hxs⟩)
  · intro i
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxf,hxo⟩
    rw [frontier,(hU i).1.interior_eq] at hxf
    exact hxf.2 (hUC i hxo)
end VM03CapV437TrackedEdges
namespace VM03CapV437TrackedEdges
private theorem open_pair_mem_sdiff (K : Geometry.SimplicialComplex ℝ E2) (p q : E2)
    (hpq : p≠q) (he : ({p,q}:Finset E2)∈K.faces) :
    openSimplex ({p,q}:Finset E2) ⊆ segment ℝ p q \ ({p,q}:Set E2) := by
  classical
  intro x hx
  refine ⟨by simpa only [Finset.coe_pair,convexHull_pair] using openSimplex_subset_convexHull _ hx,?_⟩
  intro hxp
  have hxp' : x=p ∨ x=q := by simpa using hxp
  · rcases hxp' with hhx | hhx
    · have hs : ({p}:Finset E2)∈K.faces := K.down_closed he (by simp) (by simp)
      have hh := face_eq_of_mem_openSimplex K hs he (mem_openSimplex_singleton p) (hhx ▸ hx)
      have hc := congrArg Finset.card hh
      simp [hpq] at hc
    · have hs : ({q}:Finset E2)∈K.faces := K.down_closed he (by simp) (by simp)
      have hh := face_eq_of_mem_openSimplex K hs he (mem_openSimplex_singleton q) (hhx ▸ hx)
      have hc := congrArg Finset.card hh
      simp [hpq] at hc

/- All actual interior-edge replacements are installed simultaneously in
   disjoint source patches. Their hypotheses are provided by the PL map and
   the geometry of the returned finite subdivision. -/
private theorem tracked_edge_installation (K : Geometry.SimplicialComplex ℝ E2) [Finite K.faces]
    (hK : IsPLBall 2 K.space) (F : E2 → E2)
    (hf : IsPiecewiseAffineOn F K.space) (hFi : InjOn F K.space)
    (hFL : ∃ L : NNReal, LipschitzWith L F) :
    ∃ K' : Geometry.SimplicialComplex ℝ E2, IsSubdivision K' K ∧ K'.faces.Finite ∧
      (∀ s∈K'.faces,∃ A : E2 →ᵃ[ℝ] E2,EqOn F A (convexHull ℝ (s:Set E2))) ∧
      let I := {e : K'.faces // e.1.card=2 ∧ ∀ x∈openSimplex e.1, K'.space∈𝓝 x}
      ∃ (U : I → Set E2) (P : I → E2 → E2),
        (∀ i, IsOpen (U i) ∧ Bornology.IsBounded (U i) ∧ U i ⊆ interior K'.space) ∧
        Pairwise (fun i j => Disjoint (U i) (U j)) ∧
        (∀ i, openSimplex i.1.1 ⊆ U i) ∧
        (∀ i, closure (U i) ⊆ interior K'.space ∪ (i.1.1:Set E2)) ∧
        (∀ i, (∃ L : NNReal, LipschitzWith L (P i)) ∧ InjOn (P i) (U i) ∧
          EqOn (P i) F (U i)ᶜ ∧ P i '' U i=F '' U i ∧
          (∀ x∈U i, ContDiffAt ℝ ∞ (P i) x) ∧
          (∀ x∈frontier (U i), x∉(i.1.1:Set E2) → ContDiffAt ℝ ∞ (P i) x)) := by
  classical
  obtain ⟨K',hsub,hfin,hfaces,hedge⟩ := edge_subdivision_installer K hK F hf hFi hFL
  letI : Finite K'.faces := hfin.to_subtype
  refine ⟨K',hsub,hfin,hfaces,?_⟩
  dsimp only
  let I := {e : K'.faces // e.1.card=2 ∧ ∀ x∈openSimplex e.1, K'.space∈𝓝 x}
  let J := {e : K'.faces // e.1.card=2}
  let j : I → J := fun i => ⟨i.1,i.2.1⟩
  have hji : Injective j := by
    intro i k hik
    apply Subtype.ext
    exact congrArg (fun z : J => z.1) hik
  obtain ⟨O,hO,hdis,hcover,havoid,havoidface,hfront⟩ := actual_triangulation_neighborhoods K'
  have hex (i : I) : ∃ (U : Set E2) (P : E2 → E2),
      IsOpen U ∧ Bornology.IsBounded U ∧ openSimplex i.1.1 ⊆ U ∧
      U ⊆ interior K'.space ∧ U ⊆ O (j i) ∧
      closure U ⊆ interior K'.space ∪ (i.1.1:Set E2) ∧
      (∃ L : NNReal, LipschitzWith L P) ∧ InjOn P U ∧ EqOn P F Uᶜ ∧
      P '' U=F '' U ∧ (∀ x∈U, ContDiffAt ℝ ∞ P x) ∧
      (∀ x∈frontier U, x∉(i.1.1:Set E2) → ContDiffAt ℝ ∞ P x) := by
    obtain ⟨p,q,hpq,heq⟩ := Finset.card_eq_two.mp i.2.1
    have he : ({p,q}:Finset E2)∈K'.faces := heq ▸ i.1.2
    obtain ⟨U,P,hU,hUb,hUC,hUK,hUO,hUcl,hPL,hPi,hPe,hPim,hPC,hPF⟩ :=
      hedge p q hpq he (by rw [← heq]; exact i.2.2) (O (j i)) (hO (j i)).1
      (by
        intro x hx
        apply hcover (j i)
        rw [show (j i).1.1=({p,q}:Finset E2) from heq]
        exact pair_open_edge K' p q hpq he hx)
    refine ⟨U,P,hU,hUb,?_,hUK,hUO,?_,hPL,hPi,hPe,hPim,hPC,?_⟩
    · rw [heq]
      exact (open_pair_mem_sdiff K' p q hpq he).trans hUC
    · simpa only [heq,Finset.coe_pair] using hUcl
    · simpa only [heq,Finset.coe_pair] using hPF
  choose U P hU hUb hUC hUK hUO hUcl hPL hPi hPe hPim hPC hPF using hex
  refine ⟨U,P,fun i => ⟨hU i,hUb i,hUK i⟩,?_,hUC,hUcl,?_⟩
  · intro i k hik
    exact (hdis (fun hjk => hik (hji hjk))).mono (hUO i) (hUO k)
  · intro i
    exact ⟨hPL i,hPi i,hPe i,hPim i,hPC i,hPF i⟩
end VM03CapV437TrackedEdges

namespace VM03CapV437TrackedEdges
private theorem convex_openSegment_interior (D : Set E2) (hD : Convex ℝ D)
    (p q x : E2) (hp : p∈D) (hq : q∈D)
    (hxseg : x∈openSegment ℝ p q) (hx : x∈interior D) :
    openSegment ℝ p q ⊆ interior D := by
  have hxline : x∈range (AffineMap.lineMap p q : ℝ → E2) := by
    rw [openSegment_eq_image_lineMap] at hxseg
    exact image_subset_range _ _ hxseg
  refine (openSegment_subset_union p q hxline).trans ?_
  exact insert_subset_iff.mpr ⟨hx,union_subset
    (hD.openSegment_self_interior_subset_interior hp hx)
    (hD.openSegment_interior_self_subset_interior hx hq)⟩

private theorem edge_interior_all (K : Geometry.SimplicialComplex ℝ E2)
    (hK : Convex ℝ K.space) (e : Finset E2) (he : e∈K.faces) (hec : e.card=2)
    (x : E2) (hxe : x∈openSimplex e) (hx : x∈interior K.space) :
    ∀ y∈openSimplex e,K.space∈𝓝 y := by
  classical
  obtain ⟨p,q,hpq,rfl⟩ := Finset.card_eq_two.mp hec
  have hopen (z : E2) (hz : z∈openSimplex ({p,q}:Finset E2)) : z∈openSegment ℝ p q := by
    obtain ⟨hzs,hzne⟩ := open_pair_mem_sdiff K p q hpq he hz
    exact mem_openSegment_of_ne_left_right (fun hpz => hzne (by simp [← hpz]))
      (fun hqz => hzne (by simp [← hqz])) hzs
  have hp : p∈K.space := K.subset_space he (by simp)
  have hq : q∈K.space := K.subset_space he (by simp)
  intro y hy
  exact mem_interior_iff_mem_nhds.mp
    (convex_openSegment_interior K.space hK p q x hp hq (hopen x hxe) hx (hopen y hy))

private theorem interior_point_classification (K : Geometry.SimplicialComplex ℝ E2)
    (hK : Convex ℝ K.space) (x : E2) (hx : x∈interior K.space) :
    ({x}:Finset E2)∈K.faces ∨
    (∃ e∈K.faces,e.card=2 ∧ x∈openSimplex e ∧
      ∀ y∈openSimplex e,K.space∈𝓝 y) ∨
    ∃ s∈K.faces,s.card=3 ∧ x∈interior (convexHull ℝ (s:Set E2)) := by
  classical
  obtain ⟨s,hs,hxs⟩ := exists_face_mem_openSimplex K (interior_subset hx)
  have hc : s.card ≤ 3 := by
    simpa using card_le_finrank_succ_of_mem_faces K hs
  have hp : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
  by_cases h1 : s.card=1
  · obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp h1
    have hxv : x=v := by simpa using openSimplex_subset_convexHull ({v}:Finset E2) hxs
    exact Or.inl (hxv ▸ hs)
  by_cases h2 : s.card=2
  · exact Or.inr (Or.inl ⟨s,hs,h2,hxs,edge_interior_all K hK s hs h2 x hxs hx⟩)
  · have h3 : s.card=3 := by omega
    refine Or.inr (Or.inr ⟨s,hs,h3,?_⟩)
    rw [interior_convexHull_eq_openSimplex (K.indep hs) (by simpa using h3)]
    exact hxs
end VM03CapV437TrackedEdges

namespace VM03CapV437TrackedEdges
private theorem pl_ball_frontier_sphere (K : Geometry.SimplicialComplex ℝ E2) [Finite K.faces]
    (hK : IsPLBall 2 K.space) : IsPLSphere 1 (frontier K.space) := by
  classical
  obtain ⟨T,hT,hcard,h0,hsub,hT0⟩ := exists_affineIndependent_openSimplex_subset
    (n:=1) (E:=E2) (by simp) (0:E2) (Filter.univ_mem : (univ:Set E2)∈𝓝 0)
  let Q := convexHull ℝ (T:Set E2)
  have hQ : IsPLBall 2 Q := isPLBall_convexHull_of_affineIndependent T hT hcard
  have hQc : IsClosed Q := T.finite_toSet.isCompact_convexHull ℝ |>.isClosed
  have hKc : IsClosed K.space :=
    (DifferentialGeometry.Topology.SimplicialComplex.isCompact_geometricSpace K).isClosed
  obtain ⟨f,hf⟩ := hQ
  obtain ⟨g,hg⟩ := hK
  let F : E2 → E2 := g ∘ invFunOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hF : IsPLHomeomorphOn F Q K.space := hf.symm.trans hg
  have hfront : frontier Q=(simplexBoundary T hT).space :=
    frontier_convexHull_eq_simplexBoundary hT (by simpa using hcard)
  letI : Finite (simplexBoundary T hT).faces := (simplexBoundary_faces_finite T hT).to_subtype
  have hB : IsPLSphere 1 (simplexBoundary T hT).space := by
    rw [simplexBoundary_space T hT (by omega)]
    exact isPLSphere_biUnion_erase T hT hcard
  have hBsub : (simplexBoundary T hT).space ⊆ Q := by
    rw [← hfront]
    exact frontier_subset_closure.trans hQc.closure_eq.subset
  have hFim : F '' (simplexBoundary T hT).space=frontier K.space := by
    rw [← hfront]
    exact hF.image_frontier rfl hQc hKc
  rw [← hFim]
  exact hB.of_isPLHomeomorphOn (hF.restrict (isPolyhedron_space _) hBsub)

private theorem boundary_affine_germ (K : Geometry.SimplicialComplex ℝ E2) [Finite K.faces]
    (hK : IsPLBall 2 K.space) (F : E2 → E2)
    (hmodels : ∀ s∈K.faces,∃ A : E2 →ᵃ[ℝ] E2,EqOn F A (convexHull ℝ (s:Set E2)))
    (x : E2) (hx : x∈frontier K.space) (hxv : ({x}:Finset E2)∉K.faces) :
    ∃ (U : Set E2) (A : E2 →ᵃ[ℝ] E2),IsOpen U ∧ x∈U ∧ EqOn F A (U∩K.space) := by
  classical
  have hKc : IsClosed K.space :=
    (DifferentialGeometry.Topology.SimplicialComplex.isCompact_geometricSpace K).isClosed
  obtain ⟨e,he,hxe⟩ := exists_face_mem_openSimplex K (hKc.frontier_subset hx)
  have hc : e.card ≤ 3 := by simpa using card_le_of_isPLBall K hK he
  have hp : 0 < e.card := Finset.card_pos.mpr (K.nonempty_of_mem_faces he)
  have he2 : e.card=2 := by
    by_contra hn
    by_cases h1 : e.card=1
    · obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp h1
      have hxve : x=v := by simpa using openSimplex_subset_convexHull ({v}:Finset E2) hxe
      exact hxv (hxve ▸ he)
    · have h3 : e.card=3 := by omega
      have hint : x∈interior (convexHull ℝ (e:Set E2)) := by
        rw [interior_convexHull_eq_openSimplex (K.indep he) (by simpa using h3)]
        exact hxe
      exact hx.2 (interior_mono (K.convexHull_subset_space he) hint)
  have hBspace : (boundaryComplex 2 K).space=frontier K.space :=
    boundaryComplex_space_eq_of_isPLBall_of_frontier K hK (pl_ball_frontier_sphere K hK) rfl
  have heB : e∈(boundaryComplex 2 K).faces := by
    by_contra hnot
    exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset 2 K) he hnot hxe
      (hBspace.symm ▸ hx)
  have hball : IsPLBall 0 (DifferentialGeometry.Topology.SimplicialComplex.geometricLink K e).space := by
    rcases heB with ⟨_,s,hs,hes,hsc,hbs⟩
    have hes' : e=s := Finset.eq_of_subset_of_card_le hes (by omega)
    subst s
    simpa only [he2] using hbs
  have hone : ∃ a : E2,a∉e ∧ insert a e∈K.faces ∧
      ∀ s∈K.faces,e ⊆ s → s=e ∨ s=insert a e := by
    rcases edge_cofaces K hK e he he2 with hh | ⟨a,b,hab,ha,hb,hfa,hfb,hco⟩
    · exact hh
    · exfalso
      let L := DifferentialGeometry.Topology.SimplicialComplex.geometricLink K e
      have hmem (v : E2) (hv : v∉e) (hfv : insert v e∈K.faces) : v∈L.space := by
        apply L.subset_space (s:=({v}:Finset E2)) ?_ (by simp)
        change ({v}:Finset E2).Nonempty ∧ Disjoint e {v} ∧ e∪{v}∈K.faces
        exact ⟨Finset.singleton_nonempty v,by simpa using hv,by simpa [Finset.union_comm] using hfv⟩
      exact hab (hball.subsingleton_of_zero (hmem a ha hfa) (hmem b hb hfb))
  obtain ⟨a,ha,hfa,hco⟩ := hone
  obtain ⟨A,hA⟩ := hmodels (insert a e) hfa
  have hev : ∀ᶠ y in 𝓝[K.space] x,F y=A y := by
    filter_upwards [closedStar_mem_nhdsWithin K x] with y hy
    obtain ⟨s,⟨hs,hxs⟩,hys⟩ := mem_iUnion₂.mp hy
    have hes := face_subset_of_mem_openSimplex_of_mem_convexHull K he hs hxe hxs
    apply hA
    rcases hco s hs hes with hse | hse
    · rw [hse] at hys
      simpa only [Finset.coe_insert] using
        convexHull_mono (show (e:Set E2) ⊆ (insert a e:Set E2) by simp) hys
    · simpa [hse] using hys
  obtain ⟨U,hU,hxU,hUA⟩ := mem_nhdsWithin.mp hev
  exact ⟨U,A,hU,hxU,fun y hy => hUA hy⟩
end VM03CapV437TrackedEdges
noncomputable section
open Set Filter Function
open scoped Topology
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Topology.PiecewiseLinear
namespace VM03CapV437PLAssembly

private theorem affine_on_faces_local_bound
    (K : Geometry.SimplicialComplex ℝ E2) [Finite K.faces]
    (f : E2 → E2) (A : K.faces → E2 →ᵃ[ℝ] E2)
    (C : NNReal) (hA : ∀ s, EqOn f (A s) (convexHull ℝ (s.1 : Set E2)))
    (hL : ∀ s, LipschitzWith C (A s)) (x : E2) :
    ∀ᶠ y in 𝓝[K.space] x, dist (f y) (f x) ≤ C * dist y x := by
  filter_upwards [closedStar_mem_nhdsWithin K x] with y hy
  obtain ⟨s,⟨hs,hxs⟩,hys⟩ := mem_iUnion₂.mp hy
  rw [hA ⟨s,hs⟩ hys,hA ⟨s,hs⟩ hxs]
  exact (hL ⟨s,hs⟩).dist_le_mul y x

/- A uniform local estimate with one endpoint fixed suffices on a convex set.
   This avoids assuming derivatives along triangulation edges. -/
private theorem convex_lipschitz_of_local_bound
    (D : Set E2) (hD : Convex ℝ D) (f : E2 → E2) (hc : ContinuousOn f D)
    (C : NNReal)
    (hlocal : ∀ x ∈ D, ∀ᶠ y in 𝓝[D] x, dist (f y) (f x) ≤ C * dist y x) :
    LipschitzOnWith C f D := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let p : ℝ → E2 := fun t => x+t • (y-x)
  have hp : Continuous p := by dsimp [p]; fun_prop
  have hpD : MapsTo p (Icc (0:ℝ) 1) D := by
    intro t ht
    have hh := hD hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
    convert hh using 1
    dsimp [p]
    module
  have hp0 : p 0=x := by simp [p]
  have hp1 : p 1=y := by simp [p]
  let g : ℝ → ℝ := fun t => ‖f (p t)-f x‖
  have hgc : ContinuousOn g (Icc (0:ℝ) 1) :=
    ((hc.comp hp.continuousOn hpD).sub continuousOn_const).norm
  let b : ℝ := (C:ℝ)*‖y-x‖
  have hB : ∀ t : ℝ, HasDerivAt (fun t => b*t) b t := by
    intro t
    simpa using (hasDerivAt_id t).const_mul b
  have hsl : ∀ t ∈ Ico (0:ℝ) 1, ∀ r : ℝ, b<r →
      ∃ᶠ z in 𝓝[>] t, slope g t z<r := by
    intro t ht r hr
    have hpt : p t ∈ D := hpD ⟨ht.1,ht.2.le⟩
    obtain ⟨V,hV,hptV,hVB⟩ := mem_nhdsWithin.mp (hlocal (p t) hpt)
    have hevV : ∀ᶠ z in 𝓝[>] t, p z ∈ V :=
      (hp.continuousAt.eventually (hV.mem_nhds hptV)).filter_mono nhdsWithin_le_nhds
    have hev1 : ∀ᶠ z in 𝓝[>] t, z<1 :=
      (gt_mem_nhds ht.2).filter_mono nhdsWithin_le_nhds
    have hev : ∀ᶠ z in 𝓝[>] t, slope g t z<r := by
      filter_upwards [hevV,hev1,self_mem_nhdsWithin] with z hzV hz1 hzt
      have hzt' : t<z := hzt
      have hzD : p z ∈ D := hpD ⟨ht.1.trans hzt'.le,hz1.le⟩
      have hl : dist (f (p z)) (f (p t)) ≤ C * dist (p z) (p t) := hVB ⟨hzV,hzD⟩
      have hnorm : dist (p z) (p t)=(z-t)*‖y-x‖ := by
        rw [dist_eq_norm]
        have he : p z-p t=(z-t) • (y-x) := by dsimp [p]; module
        rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hzt')]
      have hg : g z-g t ≤ b*(z-t) := by
        have hn := norm_sub_norm_le (f (p z)-f x) (f (p t)-f x)
        rw [sub_sub_sub_cancel_right] at hn
        rw [hnorm,dist_eq_norm] at hl
        dsimp [g,b]
        nlinarith
      rw [slope_def_field]
      apply (div_le_iff₀ (sub_pos.mpr hzt')).mpr hg |>.trans_lt hr
    exact hev.frequently
  have hbound : ∀ z ∈ Icc (0:ℝ) 1, g z ≤ b*z := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary hgc
      (by simp [g,hp0]) (by fun_prop)
      (fun t _ => (hB t).hasDerivWithinAt)
    intro t ht r hr
    exact hsl t ht r hr
  have hf := hbound 1 ⟨by norm_num,le_rfl⟩
  simpa only [g,hp1,mul_one,b,dist_eq_norm,norm_sub_rev] using hf

private theorem pl_lipschitz (K : Geometry.SimplicialComplex ℝ E2) [Finite K.faces]
    (hconv : Convex ℝ K.space) (f : E2 → E2)
    (hf : IsPiecewiseAffineOn f K.space) :
    ∃ C : NNReal, LipschitzOnWith C f K.space := by
  classical
  obtain ⟨K',hsub,hfin,hfaces⟩ := hf.exists_isSubdivision_affineOn_faces K
  letI : Finite K'.faces := hfin.to_subtype
  letI : Fintype K'.faces := Fintype.ofFinite _
  choose A hA using fun s : K'.faces => hfaces s.1 s.2
  choose c hc using fun s : K'.faces => (A s).lipschitzWith_of_finiteDimensional
  let C : NNReal := Finset.univ.sup c
  have hC : ∀ s, LipschitzWith C (A s) := fun s =>
    (hc s).weaken (Finset.le_sup (f:=c) (Finset.mem_univ s))
  refine ⟨C,convex_lipschitz_of_local_bound K.space hconv f hf.continuousOn C ?_⟩
  intro x hx
  rw [← hsub.space_eq]
  exact affine_on_faces_local_bound K' f A C hA hC x

/- The Lipschitz ambient extension is actual data extracted from the PL disk;
   no global injectivity assertion is imposed on the extension. -/
private theorem paid_PLDiskLipschitz (K : Geometry.SimplicialComplex ℝ E2) [Finite K.faces]
    (hconv : Convex ℝ K.space) (f : E2 → E2)
    (hf : IsPiecewiseAffineOn f K.space) :
    ∃ F : E2 → E2, (∃ C : NNReal, LipschitzWith C F) ∧ EqOn F f K.space ∧
      F '' K.space=f '' K.space ∧ (InjOn f K.space → InjOn F K.space) := by
  obtain ⟨C,hC⟩ := pl_lipschitz K hconv f hf
  obtain ⟨F,hF,he⟩ := hC.extend_finite_dimension
  refine ⟨F,⟨_,hF⟩,he.symm,image_congr he.symm,?_⟩
  intro hi x hx y hy hxy
  exact hi hx hy (by simpa only [← he hx,← he hy] using hxy)
end VM03CapV437PLAssembly
noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators
open SeifertSurfaces.AppendixACoordinates
namespace VM03CapV437PLAssembly

/- Relative finite assembly needs injectivity only on the actual disk D.
   This permits using the ambient Lipschitz extension of a PL disk map. -/
private theorem paid_FiniteDiskAssembly {ι : Type*} [Fintype ι] (F : E2 → E2) (G : ι → E2 → E2)
    (U : ι → Set E2) (S D : Set E2)
    (hUD : ∀ i, U i ⊆ D)
    (hU : ∀ i, IsOpen (U i)) (hdis : Pairwise fun i j => Disjoint (U i) (U j))
    (hFinj : InjOn F D) (hGinj : ∀ i, InjOn (G i) (U i))
    (himage : ∀ i, G i '' U i = F '' U i)
    (heq : ∀ i, EqOn (G i) F (U i)ᶜ)
    (hFl : ∃ K : NNReal, LipschitzWith K F)
    (hGl : ∀ i, ∃ K : NNReal, LipschitzWith K (G i))
    (hGcd : ∀ i x, x ∈ U i → x ∉ S → ContDiffAt ℝ 1 (G i) x)
    (hFcd : ∀ x, (∀ i, x ∉ U i) → x ∉ S → ContDiffAt ℝ 1 F x)
    (hseam : ∀ i x, x ∈ frontier (U i) → x ∉ S → ContDiffAt ℝ 1 (G i) x) :
    ∃ P : E2 → E2, InjOn P D ∧ P '' D = F '' D ∧
      (∀ i, EqOn P (G i) (U i)) ∧ EqOn P F (⋃ i, U i)ᶜ ∧
      (∃ K : NNReal, LipschitzWith K P) ∧
      (∀ x, x ∉ S → ContDiffAt ℝ 1 P x) := by
  classical
  let P : E2 → E2 := fun x => F x + ∑ i, (G i x - F x)
  have hPU : ∀ i, EqOn P (G i) (U i) := by
    intro i x hx
    dsimp only [P]
    rw [Finset.sum_eq_single i]
    · abel
    · intro j hj hji
      have hxj : x ∉ U j := fun hxj => (Set.disjoint_left.mp (hdis hji)) hxj hx
      rw [heq j hxj, sub_self]
    · simp
  have hPc : EqOn P F (⋃ i, U i)ᶜ := by
    intro x hx
    have hxall : ∀ i, x ∉ U i := by simpa using hx
    dsimp only [P]
    have hz : ∑ i, (G i x - F x) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [heq i (hxall i), sub_self]
    rw [hz, add_zero]
  have hPinj : InjOn P D := by
    intro x hxD y hyD hxy
    by_cases hx : ∃ i, x ∈ U i
    · obtain ⟨i,hxi⟩ := hx
      by_cases hyi : y ∈ U i
      · exact hGinj i hxi hyi (by simpa only [hPU i hxi,hPU i hyi] using hxy)
      · have hximage : G i x ∈ F '' U i := himage i ▸ mem_image_of_mem (G i) hxi
        obtain ⟨a,hai,ha⟩ := hximage
        by_cases hy : ∃ j, y ∈ U j
        · obtain ⟨j,hyj⟩ := hy
          have hyimage : G j y ∈ F '' U j := himage j ▸ mem_image_of_mem (G j) hyj
          obtain ⟨b,hbj,hb⟩ := hyimage
          have hab : a=b := hFinj (hUD i hai) (hUD j hbj) (by
            rw [hPU i hxi,hPU j hyj] at hxy
            exact ha.trans (hxy.trans hb.symm))
          have hij : i ≠ j := fun hij => hyi (hij ▸ hyj)
          exact ((Set.disjoint_left.mp (hdis hij)) hai (hab ▸ hbj)).elim
        · have hyall : y ∈ (⋃ j, U j)ᶜ := by simpa using hy
          have hay : a=y := hFinj (hUD i hai) hyD (by
            rw [hPU i hxi,hPc hyall] at hxy
            exact ha.trans hxy)
          exact (hyi (hay ▸ hai)).elim
    · have hxall : x ∈ (⋃ i, U i)ᶜ := by simpa using hx
      by_cases hy : ∃ j, y ∈ U j
      · obtain ⟨j,hyj⟩ := hy
        have hyimage : G j y ∈ F '' U j := himage j ▸ mem_image_of_mem (G j) hyj
        obtain ⟨b,hbj,hb⟩ := hyimage
        have hbx : b=x := hFinj (hUD j hbj) hxD (by
          rw [hPc hxall,hPU j hyj] at hxy
          exact hb.trans hxy.symm)
        exact (hx ⟨j,hbx ▸ hbj⟩).elim
      · have hyall : y ∈ (⋃ i, U i)ᶜ := by simpa using hy
        exact hFinj hxD hyD (by simpa only [hPc hxall,hPc hyall] using hxy)
  have hPrange : P '' D = F '' D := by
    apply Subset.antisymm
    · rintro _ ⟨x,hxD,rfl⟩
      by_cases hx : ∃ i, x ∈ U i
      · obtain ⟨i,hxi⟩ := hx
        rw [hPU i hxi]
        exact image_mono (hUD i) (himage i ▸ mem_image_of_mem (G i) hxi)
      · rw [hPc (by simpa using hx)]
        exact mem_image_of_mem F hxD
    · rintro _ ⟨x,hxD,rfl⟩
      by_cases hx : ∃ i, x ∈ U i
      · obtain ⟨i,hxi⟩ := hx
        have him : F x ∈ G i '' U i := (himage i).symm ▸ mem_image_of_mem F hxi
        obtain ⟨y,hy,hyval⟩ := him
        exact ⟨y,hUD i hy,(hPU i hy).trans hyval⟩
      · exact ⟨x,hxD,hPc (by simpa using hx)⟩
  have hPl : ∃ K : NNReal, LipschitzWith K P := by
    obtain ⟨k,hk⟩ := hFl
    have hs : ∀ s : Finset ι, ∃ K : NNReal,
        LipschitzWith K (fun x => ∑ i ∈ s, (G i x-F x)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨0,by simpa using (LipschitzWith.const (0:E2))⟩
      | @insert i s his ih =>
        obtain ⟨a,ha⟩ := hGl i
        obtain ⟨b,hb⟩ := ih
        exact ⟨a+k+b,by simpa only [Finset.sum_insert his] using (ha.sub hk).add hb⟩
    obtain ⟨a,ha⟩ := hs Finset.univ
    exact ⟨k+a,hk.add ha⟩
  refine ⟨P,hPinj,hPrange,hPU,hPc,hPl,?_⟩
  intro x hxS
  by_cases hx : ∃ i, x ∈ U i
  · obtain ⟨i,hxi⟩ := hx
    apply (hGcd i x hxi hxS).congr_of_eventuallyEq
    exact Filter.Eventually.mono ((hU i).mem_nhds hxi) fun y hy => hPU i hy
  · have hxall : ∀ i, x ∉ U i := by simpa using hx
    have hFc := hFcd x hxall hxS
    have hGc : ∀ i, ContDiffAt ℝ 1 (G i) x := by
      intro i
      by_cases hxc : x ∈ closure (U i)
      · apply hseam i x _ hxS
        rw [frontier, (hU i).interior_eq]
        exact ⟨hxc,hxall i⟩
      · apply hFc.congr_of_eventuallyEq
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxc] with y hy
        exact heq i (fun hyU => hy (subset_closure hyU))
    exact hFc.add (ContDiffAt.sum fun i _ => (hGc i).sub hFc)

end VM03CapV437PLAssembly
noncomputable section
open Set Filter Function Asymptotics
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
namespace VM03CapV437RelativeVertex

/- Multiplying a Lipschitz cone map by a smooth radial coefficient vanishing at the
   vertex removes the derivative singularity there.  Smoothness off the vertex is
   explicit: this lemma does not silently smooth the angular seams of a PL fan. -/
private theorem radial_coefficient_contDiff_one
    (H : E2 → E2) {K : NNReal} (hLip : LipschitzWith K H) (hzero : H 0 = 0)
    (hH : ∀ x : E2, x ≠ 0 → ContDiffAt ℝ 1 H x)
    (a : ℝ → ℝ) (ha : ContDiff ℝ 1 a) (ha0 : a 0 = 0) :
    ContDiff ℝ 1 (fun x : E2 => a ‖x‖ • H x) := by
  let F : E2 → E2 := fun x => a ‖x‖ • H x
  have hac : Continuous a := ha.continuous
  have hnorm (x : E2) : ‖H x‖ ≤ (K:ℝ)*‖x‖ := by
    simpa only [hzero,dist_zero_right] using hLip.dist_le_mul x 0
  have hF0 : F 0 = 0 := by simp [F,ha0]
  have hder0 : HasFDerivAt F (0 : E2 →L[ℝ] E2) 0 := by
    rw [hasFDerivAt_iff_isLittleO]
    simp only [hF0, ContinuousLinearMap.zero_apply, sub_zero]
    apply IsLittleO.of_bound
    intro ε hε
    have hc : ContinuousAt (fun x : E2 => |a ‖x‖| *(K:ℝ)) 0 := by fun_prop
    have hev : ∀ᶠ x : E2 in 𝓝 0, |a ‖x‖| *(K:ℝ) < ε := by
      exact hc.eventually (by simpa [ha0] using (gt_mem_nhds hε))
    filter_upwards [hev] with x hx
    change ‖a ‖x‖ • H x‖ ≤ ε*‖x‖
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ |a ‖x‖| *((K:ℝ)*‖x‖) := mul_le_mul_of_nonneg_left (hnorm x) (abs_nonneg _)
      _ ≤ ε*‖x‖ := by nlinarith [norm_nonneg x]
  have hF (x : E2) (hx : x ≠ 0) : ContDiffAt ℝ 1 F x :=
    (ha.contDiffAt.comp x (contDiffAt_norm ℝ hx)).smul (hH x hx)
  have hbound (x : E2) : ‖fderiv ℝ F x‖ ≤
      |a ‖x‖| *(K:ℝ)+|deriv a ‖x‖| *((K:ℝ)*‖x‖) := by
    by_cases hx : x=0
    · subst x
      rw [hder0.fderiv]
      simp [ha0]
    · have hn : DifferentiableAt ℝ (fun z : E2 => ‖z‖) x :=
        (contDiffAt_norm ℝ hx).differentiableAt one_ne_zero
      have hdH := (hH x hx).differentiableAt one_ne_zero
      have hdA := (ha.differentiable one_ne_zero ‖x‖).hasDerivAt.comp_hasFDerivAt x hn.hasFDerivAt
      have hdF := hdA.smul hdH.hasFDerivAt
      change HasFDerivAt F _ x at hdF
      rw [hdF.fderiv]
      calc
        _ ≤ ‖a ‖x‖ • fderiv ℝ H x‖ +
            ‖(deriv a ‖x‖ • fderiv ℝ (fun z : E2 => ‖z‖) x).smulRight (H x)‖ := norm_add_le _ _
        _ = |a ‖x‖| *‖fderiv ℝ H x‖+
            (|deriv a ‖x‖| *‖fderiv ℝ (fun z : E2 => ‖z‖) x‖)*‖H x‖ := by
          rw [norm_smul,Real.norm_eq_abs,ContinuousLinearMap.norm_smulRight_apply,
            norm_smul,Real.norm_eq_abs]
        _ ≤ |a ‖x‖| *(K:ℝ)+|deriv a ‖x‖| *((K:ℝ)*‖x‖) := by
          have h1 := norm_fderiv_le_of_lipschitz ℝ hLip (x₀ := x)
          have h2 := norm_fderiv_norm hn
          rw [h2,mul_one]
          exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (hnorm x) (abs_nonneg _))
  apply contDiff_one_iff_fderiv.mpr
  refine ⟨fun x => ?_, continuous_iff_continuousAt.mpr ?_⟩
  · by_cases hx : x=0
    · subst x; exact hder0.differentiableAt
    · exact (hF x hx).differentiableAt one_ne_zero
  · intro x
    by_cases hx : x=0
    · subst x
      change Tendsto (fderiv ℝ F) (𝓝 0) (𝓝 (fderiv ℝ F 0))
      rw [hder0.fderiv]
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      have hc : ContinuousAt (fun x : E2 =>
          |a ‖x‖| *(K:ℝ)+|deriv a ‖x‖| *((K:ℝ)*‖x‖)) 0 := by
        have hd : Continuous (deriv a) := ha.continuous_deriv (by rfl)
        fun_prop
      have hev : ∀ᶠ x : E2 in 𝓝 0,
          |a ‖x‖| *(K:ℝ)+|deriv a ‖x‖| *((K:ℝ)*‖x‖) < ε :=
        hc.eventually (by simpa [ha0] using (gt_mem_nhds hε))
      filter_upwards [hev] with x hx
      rw [dist_zero_right]
      exact (hbound x).trans_lt hx
    · exact (hF x hx).continuousAt_fderiv one_ne_zero

private theorem homogeneous_vertex_regularization (H : E2 → E2) {K : NNReal} (hLip : LipschitzWith K H)
    (hzero : H 0 = 0) (hinj : Injective H)
    (hhom : ∀ (r : ℝ), 0 ≤ r → ∀ x, H (r • x) = r • H x)
    (hH : ∀ x : E2, x ≠ 0 → ContDiffAt ℝ 1 H x) :
    ∃ F : E2 → E2, ContDiff ℝ 1 F ∧ Injective F ∧
      F 0 = 0 ∧ fderiv ℝ F 0 = 0 ∧
      (∀ x, 1 ≤ ‖x‖ → F x = H x) ∧
      F '' Metric.ball 0 1 = H '' Metric.ball 0 1 := by
  let a := Real.smoothTransition
  let F : E2 → E2 := fun x => a ‖x‖ • H x
  have ha : ContDiff ℝ 1 a := Real.smoothTransition.contDiff
  have ha0 : a 0=0 := Real.smoothTransition.zero
  have hFn : ContDiff ℝ 1 F := radial_coefficient_contDiff_one H hLip hzero hH a ha ha0
  have hrad : StrictMonoOn (fun r : ℝ => a r*r) (Ici 0) := by
    intro r hr s hs hrs
    have hspos : 0<s := lt_of_le_of_lt hr hrs
    have has : 0<a s := Real.smoothTransition.pos_of_pos hspos
    have har : a r ≤ a s := Real.smoothTransition.monotone hrs.le
    exact (mul_le_mul_of_nonneg_right har hr).trans_lt (mul_lt_mul_of_pos_left hrs has)
  have hFinj : Injective F := by
    intro x y hxy
    have hxpos : 0 ≤ a ‖x‖ := Real.smoothTransition.nonneg _
    have hypos : 0 ≤ a ‖y‖ := Real.smoothTransition.nonneg _
    have hscale : a ‖x‖ • x = a ‖y‖ • y := hinj (by
      rw [hhom _ hxpos,hhom _ hypos]
      exact hxy)
    have hnorm : ‖x‖ = ‖y‖ := hrad.injOn (norm_nonneg x) (norm_nonneg y) (by
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hxpos,abs_of_nonneg hypos]
        using congrArg norm hscale)
    by_cases hx : x=0
    · subst x
      have hy : y=0 := norm_eq_zero.mp (by simpa using hnorm.symm)
      exact hy.symm
    · have hax : a ‖x‖ ≠ 0 := (Real.smoothTransition.pos_of_pos (norm_pos_iff.mpr hx)).ne'
      rw [← hnorm] at hscale
      exact (smul_right_injective _ hax) hscale
  have hout : ∀ x, 1 ≤ ‖x‖ → F x = H x := by
    intro x hx
    dsimp only [F,a]
    rw [Real.smoothTransition.one_of_one_le hx,one_smul]
  refine ⟨F,hFn,hFinj,by simp [F,ha0],?_,hout,?_⟩
  · have hF0 : F 0 = 0 := by simp [F,ha0]
    have hd : HasFDerivAt F (0 : E2 →L[ℝ] E2) 0 := by
      rw [hasFDerivAt_iff_isLittleO]
      simp only [hF0,ContinuousLinearMap.zero_apply,sub_zero]
      apply IsLittleO.of_bound
      intro ε hε
      have hc : ContinuousAt (fun x : E2 => |a ‖x‖| *(K:ℝ)) 0 := by fun_prop
      have hev : ∀ᶠ x : E2 in 𝓝 0, |a ‖x‖| *(K:ℝ)<ε :=
        hc.eventually (by simpa [ha0] using (gt_mem_nhds hε))
      filter_upwards [hev] with x hx
      have hn : ‖H x‖ ≤ (K:ℝ)*‖x‖ := by simpa [hzero] using hLip.dist_le_mul x 0
      change ‖a ‖x‖ • H x‖ ≤ ε*‖x‖
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hn (abs_nonneg _)).trans (by nlinarith [norm_nonneg x])
    exact hd.fderiv
  · apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      refine ⟨a ‖x‖ • x,?_,?_⟩
      · rw [Metric.mem_ball,dist_zero_right] at hx ⊢
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact (mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)).trans_lt hx
      · exact hhom _ (Real.smoothTransition.nonneg _) x
    · rintro _ ⟨y,hy,rfl⟩
      by_cases hy0 : y=0
      · subst y
        exact ⟨0,by simpa using hy,by simp [F,ha0,hzero]⟩
      have hyr : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      have hyr1 : ‖y‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
      have hc : Continuous (fun r : ℝ => a r*r) := ha.continuous.mul continuous_id
      obtain ⟨t,ht,hteq⟩ := intermediate_value_Icc (show (0:ℝ)≤1 by norm_num) hc.continuousOn
        (show ‖y‖ ∈ Icc (a 0*0) (a 1*1) by
          simpa only [mul_zero,mul_one,show a 1=1 from Real.smoothTransition.one,Set.mem_Icc] using
            And.intro hyr.le hyr1.le)
      change a t*t=‖y‖ at hteq
      have ht1 : t<1 := by
        by_contra hn
        have htone : t=1 := le_antisymm ht.2 (le_of_not_gt hn)
        rw [htone,show a 1=1 from Real.smoothTransition.one,mul_one] at hteq
        linarith
      let x : E2 := (t/‖y‖) • y
      have hxnorm : ‖x‖=t := by
        dsimp [x]
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg ht.1 hyr.le)]
        field_simp
      refine ⟨x,by simpa only [Metric.mem_ball,dist_zero_right,hxnorm] using ht1,?_⟩
      change a ‖x‖ • H x=H y
      rw [← hhom _ (Real.smoothTransition.nonneg _),hxnorm]
      congr 1
      dsimp [x]
      rw [smul_smul]
      have hcoeff : a t*(t/‖y‖)=1 := by rw [← mul_div_assoc,hteq]; exact div_self hyr.ne'
      rw [hcoeff,one_smul]

/- The paid radial regularization of the identity is globally Lipschitz: its
   difference from the identity is C¹ and compactly supported. -/
private theorem radial_flattening :
    ∃ R : E2 → E2, ContDiff ℝ 1 R ∧ Bijective R ∧
      (∃ K : NNReal, LipschitzWith K R) ∧ R 0 = 0 ∧ fderiv ℝ R 0 = 0 ∧
      (∀ x, 1 ≤ ‖x‖ → R x = x) ∧ R '' Metric.ball 0 1 = Metric.ball 0 1 := by
  obtain ⟨R,hR,hi,h0,hd,hout,him⟩ := homogeneous_vertex_regularization
    (id : E2 → E2) LipschitzWith.id rfl injective_id
    (fun _ _ _ => rfl) (fun _ _ => contDiffAt_id)
  have him' : R '' Metric.ball 0 1 = Metric.ball 0 1 := by simpa using him
  have hsur : Surjective R := by
    intro y
    by_cases hy : y ∈ Metric.ball (0:E2) 1
    · obtain ⟨x,hx,he⟩ := him'.symm ▸ hy
      exact ⟨x,he⟩
    · exact ⟨y,hout y (by simpa [Metric.mem_ball] using hy)⟩
  have hs : HasCompactSupport (fun x => R x-x) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0:E2) 1)
    intro x hx
    have hn : 1 ≤ ‖x‖ := le_of_lt (by simpa using hx)
    simp [hout x hn]
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs
    (hR.sub contDiff_id) one_ne_zero
  have hl : LipschitzWith (K+1) R := by
    simpa using hK.add (LipschitzWith.id (α:=E2))
  exact ⟨R,hR,⟨hi,hsur⟩,⟨K+1,hl⟩,h0,hd,hout,him'⟩

private theorem centered_flattening (c : E2) (r : ℝ) (hr : 0<r) :
    ∃ T : E2 → E2, ContDiff ℝ 1 T ∧ Bijective T ∧
      (∃ K : NNReal, LipschitzWith K T) ∧ T c = c ∧ fderiv ℝ T c = 0 ∧
      EqOn T id (Metric.ball c r)ᶜ ∧ T '' Metric.ball c r = Metric.ball c r := by
  obtain ⟨R,hR,hRb,hRl,hR0,hRd,hRout,hRim⟩ := radial_flattening
  let A : E2 → E2 := fun x => r⁻¹ • (x-c)
  let B : E2 → E2 := fun x => c+r • x
  have hAB : ∀ x, A (B x)=x := by
    intro x
    simp [A,B,smul_smul,hr.ne']
  have hBA : ∀ x, B (A x)=x := by
    intro x
    simp [A,B,smul_smul,hr.ne']
  have hAc : ContDiff ℝ 1 A := by
    dsimp only [A]
    fun_prop
  have hBc : ContDiff ℝ 1 B := by
    dsimp only [B]
    fun_prop
  have hAm (x : E2) : A x ∈ Metric.ball 0 1 ↔ x ∈ Metric.ball c r := by
    simp only [A,Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr),dist_eq_norm,sub_zero,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
    rw [inv_mul_lt_iff₀ hr]
    simp
  let T : E2 → E2 := B ∘ R ∘ A
  have hTc : ContDiff ℝ 1 T := hBc.comp (hR.comp hAc)
  have hT0 : T c=c := by simp [T,A,B,hR0]
  have hTi : Injective T :=
    (Function.LeftInverse.injective hAB).comp (hRb.1.comp (Function.LeftInverse.injective hBA))
  have hTs : Surjective T :=
    (Function.RightInverse.surjective hBA).comp (hRb.2.comp (Function.RightInverse.surjective hAB))
  obtain ⟨K,hK⟩ := hRl
  have hAl : LipschitzWith ‖r⁻¹‖₊ A := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [A,dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,
      NNReal.coe_mk,coe_nnnorm]
    rw [sub_sub_sub_cancel_right]
  have hBl : LipschitzWith ‖r‖₊ B := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [B,dist_eq_norm,add_sub_add_left_eq_sub,← smul_sub,norm_smul,
      coe_nnnorm]
    exact le_rfl
  refine ⟨T,hTc,⟨hTi,hTs⟩,⟨_,hBl.comp (hK.comp hAl)⟩,hT0,?_,?_,?_⟩
  · dsimp only [T]
    rw [fderiv_comp c (hBc.differentiable one_ne_zero _) ((hR.comp hAc).differentiable one_ne_zero c)]
    rw [fderiv_comp c (hR.differentiable one_ne_zero _) (hAc.differentiable one_ne_zero c)]
    simp [A,hRd]
  · intro x hx
    change B (R (A x))=x
    rw [hRout (A x) (by simpa [Metric.mem_ball] using (mt (hAm x).mp hx))]
    exact hBA x
  · apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      have hm : R (A x) ∈ Metric.ball (0:E2) 1 := hRim ▸ mem_image_of_mem R ((hAm x).mpr hx)
      apply (hAm _).mp
      simpa only [T,comp_apply,hAB] using hm
    · intro y hy
      obtain ⟨a,ha,hea⟩ := hRim.symm ▸ ((hAm y).mpr hy)
      refine ⟨B a,(hAm _).mp (by simpa only [hAB] using ha),?_⟩
      change B (R (A (B a)))=y
      rw [hAB,hea,hBA]

/- The derivative estimate is local near c.  Other singular vertices of H are
   permitted outside W and therefore do not become extra hypotheses. -/
private theorem flat_precomposition_at
    (H T : E2 → E2) {K : NNReal} (hLip : LipschitzWith K H)
    (hT : ContDiff ℝ 1 T) (c : E2) (hTc : T c=c) (hTd : fderiv ℝ T c=0)
    (W : Set E2) (hW : W ∈ 𝓝 c)
    (hH : ∀ x ∈ W, x ≠ c → ContDiffAt ℝ 1 H (T x)) :
    ContDiffAt ℝ 1 (H ∘ T) c := by
  let F : E2 → E2 := H ∘ T
  have hF0 : F c=H c := by simp [F,hTc]
  have hderT : HasFDerivAt T (0:E2 →L[ℝ] E2) c := by
    simpa only [hTd] using (hT.differentiable one_ne_zero c).hasFDerivAt
  have hTO : (fun x => T x-c) =o[𝓝 c] (fun x => x-c) := by
    simpa only [hTc,zero_apply,sub_zero] using hderT.isLittleO
  have hderF : HasFDerivAt F (0:E2 →L[ℝ] E2) c := by
    rw [hasFDerivAt_iff_isLittleO]
    simp only [hF0,zero_apply,sub_zero]
    apply (IsBigO.of_bound (K:ℝ) ?_).trans_isLittleO hTO
    exact Filter.Eventually.of_forall fun x => by
      simpa only [F,comp_apply,dist_eq_norm] using hLip.dist_le_mul (T x) c
  have hF (x : E2) (hx : x ∈ W) (hxc : x ≠ c) : ContDiffAt ℝ 1 F x :=
    (hH x hx hxc).comp x hT.contDiffAt
  have hbound (x : E2) (hx : x ∈ W) : ‖fderiv ℝ F x‖ ≤ (K:ℝ)*‖fderiv ℝ T x‖ := by
    by_cases hxc : x=c
    · subst x; simp [hderF.fderiv,hTd]
    · change ‖fderiv ℝ (H ∘ T) x‖ ≤ _
      rw [fderiv_comp x ((hH x hx hxc).differentiableAt one_ne_zero)
        (hT.differentiable one_ne_zero x)]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg _))
  have hdcont : ContinuousAt (fderiv ℝ F) c := by
    change Tendsto (fderiv ℝ F) (𝓝 c) (𝓝 (fderiv ℝ F c))
    rw [hderF.fderiv]
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hc : ContinuousAt (fun x : E2 => (K:ℝ)*‖fderiv ℝ T x‖) c :=
      continuousAt_const.mul (hT.continuous_fderiv one_ne_zero).continuousAt.norm
    have hev : ∀ᶠ x : E2 in 𝓝 c, (K:ℝ)*‖fderiv ℝ T x‖<ε :=
      hc.eventually (by simpa only [hTd,norm_zero,mul_zero] using (gt_mem_nhds hε))
    filter_upwards [hev,hW] with x hx hxW
    rw [dist_zero_right]
    exact (hbound x hxW).trans_lt hx
  apply contDiffAt_one_iff.mpr
  refine ⟨fderiv ℝ F,W,hW,?_,?_⟩
  · intro x hx
    by_cases hxc : x=c
    · subst x; exact hdcont.continuousWithinAt
    · exact (hF x hx hxc).continuousAt_fderiv one_ne_zero |>.continuousWithinAt
  · intro x hx
    by_cases hxc : x=c
    · subst x; simpa only [hderF.fderiv] using hderF
    · exact ((hF x hx hxc).differentiableAt one_ne_zero).hasFDerivAt

private theorem install_one_vertex (H : E2 → E2) {K : NNReal}
    (hLip : LipschitzWith K H) (S : Finset E2) (c : E2) (hc : c ∉ S)
    (U : Set E2) (hU : IsOpen U) (hcU : c ∈ U)
    (hH : ∀ x, x ∉ insert c (S:Set E2) → ContDiffAt ℝ 1 H x) :
    ∃ T : E2 → E2, ContDiff ℝ 1 T ∧ Bijective T ∧
      (∃ L : NNReal, LipschitzWith L T) ∧ EqOn T id Uᶜ ∧
      (∀ D : Set E2, U ⊆ D → T '' D=D) ∧
      (∀ x, x ∉ (S:Set E2) → ContDiffAt ℝ 1 (H ∘ T) x) := by
  classical
  have hW : IsOpen (U \ (S:Set E2)) := hU.sdiff S.finite_toSet.isClosed
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hW c ⟨hcU,hc⟩
  obtain ⟨T,hT,hTb,hTl,hTc,hTd,hout,him⟩ := centered_flattening c r hr
  have hnon (x : E2) (hx : x ≠ c) : T x ≠ c := fun he => hx (hTb.1 (he.trans hTc.symm))
  have hTs (x : E2) (hx : x ∉ (S:Set E2)) : T x ∉ (S:Set E2) := by
    by_cases hxb : x ∈ Metric.ball c r
    · exact (hball (him ▸ mem_image_of_mem T hxb)).2
    · simpa only [hout hxb,id_eq] using hx
  have hUout : EqOn T id Uᶜ := by
    intro x hx
    exact hout (fun hxb => hx (hball hxb).1)
  refine ⟨T,hT,hTb,hTl,hUout,?_,?_⟩
  · intro D hUD
    have hTD (x : E2) : x ∈ D ↔ T x ∈ D := by
      by_cases hxb : x ∈ Metric.ball c r
      · exact iff_of_true (hUD (hball hxb).1)
          (hUD (hball (him ▸ mem_image_of_mem T hxb)).1)
      · rw [hout hxb]; rfl
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (hTD x).mp hx
    · intro y hy
      obtain ⟨x,rfl⟩ := hTb.2 y
      exact ⟨x,(hTD x).mpr hy,rfl⟩
  · intro x hx
    by_cases hxc : x=c
    · subst x
      apply flat_precomposition_at H T hLip hT c hTc hTd (Metric.ball c r)
        (Metric.ball_mem_nhds c hr)
      intro y hy hyc
      apply hH
      simp only [mem_insert_iff,not_or]
      exact ⟨hnon y hyc,hTs y (hball hy).2⟩
    · apply (hH (T x) ?_).comp x hT.contDiffAt
      simp only [mem_insert_iff,not_or]
      exact ⟨hnon x hxc,hTs x hx⟩

/- This is a complete finite vertex installation, relative to any prescribed
   open neighborhood of the finite vertex set.  Every containing domain is
   preserved exactly, so injectivity on a compact disk can be transported. -/
private theorem paid_global_vertices (S : Finset E2) (H : E2 → E2) {K : NNReal}
    (hLip : LipschitzWith K H) (U : Set E2) (hU : IsOpen U)
    (hSU : (S:Set E2) ⊆ U)
    (hH : ∀ x, x ∉ (S:Set E2) → ContDiffAt ℝ 1 H x) :
    ∃ T : E2 → E2, ContDiff ℝ 1 T ∧ Bijective T ∧
      (∃ L : NNReal, LipschitzWith L T) ∧ EqOn T id Uᶜ ∧
      (∀ D : Set E2, U ⊆ D → T '' D=D) ∧ ContDiff ℝ 1 (H ∘ T) ∧
      (∃ L : NNReal, LipschitzWith L (H ∘ T)) ∧
      (∀ D : Set E2, U ⊆ D → H ∘ T '' D=H '' D ∧
        (InjOn H D → InjOn (H ∘ T) D)) := by
  classical
  induction S using Finset.induction_on generalizing H K with
  | empty =>
    refine ⟨id,contDiff_id,bijective_id,⟨1,LipschitzWith.id⟩,fun _ _ => rfl,
      fun _ _ => image_id _,?_,⟨K,by simpa using hLip⟩,?_⟩
    · exact contDiff_iff_contDiffAt.mpr fun x => hH x (by simp)
    · intro D hUD
      exact ⟨by simp,fun h => by simpa using h⟩
  | @insert c S hc ih =>
    have hcU : c ∈ U := hSU (by simp)
    have hSU' : (S:Set E2) ⊆ U := fun x hx => hSU (by simp [hx])
    obtain ⟨T,hT,hTb,⟨L,hL⟩,hout,him,hcd⟩ := install_one_vertex H hLip S c hc U hU hcU
      (by simpa only [Finset.coe_insert] using hH)
    obtain ⟨V,hV,hVb,⟨M,hM⟩,hVout,hVim,hVcd,hVL,hVD⟩ :=
      ih (H ∘ T) (hLip.comp hL) hSU' hcd
    refine ⟨T ∘ V,hT.comp hV,hTb.comp hVb,⟨L*M,hL.comp hM⟩,?_,?_,hVcd,hVL,?_⟩
    · intro x hx
      change T (V x)=x
      rw [hVout hx]
      exact hout hx
    · intro D hUD
      rw [image_comp T V D,hVim D hUD,him D hUD]
    · intro D hUD
      have heq : (T ∘ V) '' D=D := by rw [image_comp T V D,hVim D hUD,him D hUD]
      refine ⟨by rw [image_comp H (T ∘ V) D,heq],?_⟩
      intro hinj x hx y hy hxy
      apply (hTb.comp hVb).1
      apply hinj
      · exact heq ▸ mem_image_of_mem (T ∘ V) hx
      · exact heq ▸ mem_image_of_mem (T ∘ V) hy
      · exact hxy
end VM03CapV437RelativeVertex

namespace VM03CapV437RelativeVertex
private theorem install_one_vertex_relative (H : E2 → E2) {K : NNReal}
    (hLip : LipschitzWith K H) (S : Finset E2) (c : E2) (hc : c ∉ S)
    (U W : Set E2) (hU : IsOpen U) (hUW : U ⊆ W) (hcU : c∈U)
    (hH : ∀ x∈W,x∉insert c (S:Set E2) → ContDiffAt ℝ 1 H x) :
    ∃ T : E2 → E2,ContDiff ℝ 1 T ∧ Bijective T ∧
      (∃ L : NNReal,LipschitzWith L T) ∧ EqOn T id Uᶜ ∧
      (∀ D : Set E2,U ⊆ D → T '' D=D) ∧
      (∀ x∈W,x∉(S:Set E2) → ContDiffAt ℝ 1 (H ∘ T) x) := by
  classical
  have hO : IsOpen (U \ (S:Set E2)) := hU.sdiff S.finite_toSet.isClosed
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hO c ⟨hcU,hc⟩
  obtain ⟨T,hT,hTb,hTl,hTc,hTd,hout,him⟩ := centered_flattening c r hr
  have hnon (x : E2) (hx : x≠c) : T x≠c := fun he => hx (hTb.1 (he.trans hTc.symm))
  have hTs (x : E2) (hx : x∉(S:Set E2)) : T x∉(S:Set E2) := by
    by_cases hxb : x∈Metric.ball c r
    · exact (hball (him ▸ mem_image_of_mem T hxb)).2
    · simpa only [hout hxb,id_eq] using hx
  have hUout : EqOn T id Uᶜ := by
    intro x hx
    exact hout (fun hxb => hx (hball hxb).1)
  have hpres (D : Set E2) (hUD : U ⊆ D) : T '' D=D := by
    have hTD (x : E2) : x∈D ↔ T x∈D := by
      by_cases hxb : x∈Metric.ball c r
      · exact iff_of_true (hUD (hball hxb).1)
          (hUD (hball (him ▸ mem_image_of_mem T hxb)).1)
      · rw [hout hxb]; rfl
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (hTD x).mp hx
    · intro y hy
      obtain ⟨x,rfl⟩ := hTb.2 y
      exact ⟨x,(hTD x).mpr hy,rfl⟩
  have hTW : MapsTo T W W := fun x hx => hpres W hUW ▸ mem_image_of_mem T hx
  refine ⟨T,hT,hTb,hTl,hUout,hpres,?_⟩
  intro x hxW hx
  by_cases hxc : x=c
  · subst x
    apply flat_precomposition_at H T hLip hT c hTc hTd (Metric.ball c r)
      (Metric.ball_mem_nhds c hr)
    intro y hy hyc
    apply hH (T y) (hTW (hUW (hball hy).1))
    simp only [mem_insert_iff,not_or]
    exact ⟨hnon y hyc,hTs y (hball hy).2⟩
  · apply (hH (T x) (hTW hxW) ?_).comp x hT.contDiffAt
    simp only [mem_insert_iff,not_or]
    exact ⟨hnon x hxc,hTs x hx⟩

-- Relative form required by a PL disk: no regularity is assumed outside W.
private theorem finite_vertices_relative (S : Finset E2) (H : E2 → E2) {K : NNReal}
    (hLip : LipschitzWith K H) (U W : Set E2) (hU : IsOpen U) (hUW : U ⊆ W)
    (hSU : (S:Set E2) ⊆ U)
    (hH : ∀ x∈W,x∉(S:Set E2) → ContDiffAt ℝ 1 H x) :
    ∃ T : E2 → E2,ContDiff ℝ 1 T ∧ Bijective T ∧
      (∃ L : NNReal,LipschitzWith L T) ∧ EqOn T id Uᶜ ∧
      (∀ D : Set E2,U ⊆ D → T '' D=D) ∧
      (∀ x∈W,ContDiffAt ℝ 1 (H ∘ T) x) ∧
      (∃ L : NNReal,LipschitzWith L (H ∘ T)) ∧
      (∀ D : Set E2,U ⊆ D → (H ∘ T) '' D=H '' D ∧
        (InjOn H D → InjOn (H ∘ T) D)) := by
  classical
  induction S using Finset.induction_on generalizing H K with
  | empty =>
    refine ⟨id,contDiff_id,bijective_id,⟨1,LipschitzWith.id⟩,fun _ _ => rfl,
      fun _ _ => image_id _,?_,⟨K,by simpa using hLip⟩,?_⟩
    · intro x hx
      exact hH x hx (by simp)
    · intro D hUD
      exact ⟨by simp,fun h => by simpa using h⟩
  | @insert c S hc ih =>
    have hcU : c∈U := hSU (by simp)
    have hSU' : (S:Set E2) ⊆ U := fun x hx => hSU (by simp [hx])
    obtain ⟨T,hT,hTb,⟨L,hL⟩,hout,him,hcd⟩ :=
      install_one_vertex_relative H hLip S c hc U W hU hUW hcU
        (by simpa only [Finset.coe_insert] using hH)
    obtain ⟨V,hV,hVb,⟨M,hM⟩,hVout,hVim,hVcd,hVL,hVD⟩ :=
      ih (H ∘ T) (hLip.comp hL) hSU' hcd
    refine ⟨T ∘ V,hT.comp hV,hTb.comp hVb,⟨L*M,hL.comp hM⟩,?_,?_,hVcd,hVL,?_⟩
    · intro x hx
      change T (V x)=x
      rw [hVout hx]
      exact hout hx
    · intro D hUD
      rw [image_comp T V D,hVim D hUD,him D hUD]
    · intro D hUD
      have heq : (T ∘ V) '' D=D := by rw [image_comp T V D,hVim D hUD,him D hUD]
      refine ⟨by rw [image_comp H (T ∘ V) D,heq],?_⟩
      intro hinj x hx y hy hxy
      apply (hTb.comp hVb).1
      exact hinj (heq ▸ mem_image_of_mem (T ∘ V) hx)
        (heq ▸ mem_image_of_mem (T ∘ V) hy) hxy
end VM03CapV437RelativeVertex
namespace VM03CapV437RelativeVertex
private theorem relative_vertices_preserve_boundary_germs
    (S : Finset E2) (H : E2 → E2) {K : NNReal} (hLip : LipschitzWith K H)
    (W : Set E2) (hW : IsOpen W) (hSW : (S:Set E2) ⊆ W)
    (hH : ∀ x∈W,x∉(S:Set E2) → ContDiffAt ℝ 1 H x) :
    ∃ J : E2 → E2,(∃ L : NNReal,LipschitzWith L J) ∧
      (∀ x∈W,ContDiffAt ℝ 1 J x) ∧
      (∀ x∉W,J =ᶠ[𝓝 x] H) ∧
      (∀ D : Set E2,W ⊆ D → J '' D=H '' D ∧ (InjOn H D → InjOn J D)) := by
  obtain ⟨U,hU,hSU,hUW⟩ := S.finite_toSet.isCompact.exists_isOpen_closure_subset
    (hW.mem_nhdsSet.mpr hSW)
  have hUW' : U ⊆ W := subset_closure.trans hUW
  obtain ⟨T,hT,hTb,hTl,hout,him,hcd,hL,hD⟩ :=
    finite_vertices_relative S H hLip U W hU hUW' hSU hH
  refine ⟨H ∘ T,hL,hcd,?_,?_⟩
  · intro x hx
    have hxU : x∈(closure U)ᶜ := fun hh => hx (hUW hh)
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxU] with y hy
    change H (T y)=H y
    rw [hout (fun hh => hy (subset_closure hh))]
    rfl
  · intro D hWD
    exact hD D (hUW'.trans hWD)
end VM03CapV437RelativeVertex
namespace VM03CapV437PLAssembly
open VM03CapV437TrackedEdges VM03CapV437RelativeVertex
private theorem relative_PL_producer
    (K : Geometry.SimplicialComplex ℝ E2) [Finite K.faces]
    (hK : IsPLBall 2 K.space) (hconv : Convex ℝ K.space)
    (F : E2 → E2) (hf : IsPiecewiseAffineOn F K.space) (hi : InjOn F K.space) :
    ∃ J : E2 → E2,(∃ L : NNReal,LipschitzWith L J) ∧ InjOn J K.space ∧
      J '' K.space=F '' K.space ∧ EqOn J F (frontier K.space) ∧
      (∀ x∈interior K.space,ContDiffAt ℝ 1 J x) ∧
      ∃ S : Finset E2,(S:Set E2) ⊆ frontier K.space ∧
        ∀ x∈frontier K.space,x∉(S:Set E2) → ∃ (U : Set E2) (A : E2 →ᵃ[ℝ] E2),
          IsOpen U ∧ x∈U ∧ EqOn J A (U∩K.space) := by
  classical
  obtain ⟨f,hfL,hfF,hfim,hfi⟩ := paid_PLDiskLipschitz K hconv F hf
  have hfp : IsPiecewiseAffineOn f K.space := hf.congr hfF
  obtain ⟨K',hsub,hfin,hmodels,U,P,hU,hdis,hcover,hcl,hpatch⟩ :=
    tracked_edge_installation K hK f hfp (hfi hi) hfL
  letI : Finite K'.faces := hfin.to_subtype
  let I := {e : K'.faces // e.1.card=2 ∧ ∀ x∈openSimplex e.1,K'.space∈𝓝 x}
  letI : Fintype I := Fintype.ofFinite I
  have hK' : IsPLBall 2 K'.space := hsub.space_eq.symm ▸ hK
  have hconv' : Convex ℝ K'.space := hsub.space_eq.symm ▸ hconv
  have hfi' : InjOn f K'.space := hsub.space_eq.symm ▸ hfi hi
  have hverts : K'.vertices.Finite := by
    rw [K'.vertices_eq]
    exact hfin.biUnion fun s hs => s.finite_toSet
  let V := hverts.toFinset
  have hV (x : E2) : x∈V ↔ ({x}:Finset E2)∈K'.faces := by
    simp only [V,Set.Finite.mem_toFinset,K'.mem_vertices]
  have hfaceV (s : Finset E2) (hs : s∈K'.faces) : (s:Set E2) ⊆ (V:Set E2) := by
    intro x hx
    exact (hV x).mpr (K'.down_closed hs (by simpa using hx) (by simp))
  let B : Set E2 := (interior K'.space)ᶜ ∪ (V:Set E2)
  have hreg (x : E2) (hxU : ∀ i:I,x∉U i) (hxB : x∉B) : ContDiffAt ℝ 1 f x := by
    have hxint : x∈interior K'.space := by
      by_contra hh
      exact hxB (Or.inl hh)
    have hxV : x∉V := fun hx => hxB (Or.inr hx)
    rcases interior_point_classification K' hconv' x hxint with hv | ⟨e,he,hec,hxe,heall⟩ | ⟨s,hs,hsc,hxs⟩
    · exact (hxV ((hV x).mpr hv)).elim
    · exact (hxU ⟨⟨e,he⟩,hec,heall⟩ (hcover _ hxe)).elim
    · obtain ⟨A,hA⟩ := hmodels s hs
      have hAc : ContDiff ℝ 1 A :=
        (show E2 →ᴬ[ℝ] E2 from ⟨A,A.continuous_of_finiteDimensional⟩).contDiff
      apply hAc.contDiffAt.congr_of_eventuallyEq
      filter_upwards [isOpen_interior.mem_nhds hxs] with y hy
      exact hA (interior_subset hy)
  obtain ⟨G,hGi,hGim,hGU,hGout,⟨KG,hGL⟩,hGc⟩ :=
    paid_FiniteDiskAssembly f P U B K'.space
      (fun i => (hU i).2.2.trans interior_subset) (fun i => (hU i).1) hdis hfi'
      (fun i => (hpatch i).2.1) (fun i => (hpatch i).2.2.2.1)
      (fun i => (hpatch i).2.2.1) hfL (fun i => (hpatch i).1)
      (fun i x hx _ => ((hpatch i).2.2.2.2.1 x hx).of_le (by simp)) hreg
      (fun i x hx hxB => ((hpatch i).2.2.2.2.2 x hx
        (fun hxv => hxB (Or.inr (hfaceV i.1.1 i.1.2 hxv)))).of_le (by simp))
  have hGboundary : EqOn G f (frontier K'.space) := by
    intro x hx
    apply hGout
    intro hh
    obtain ⟨i,hi⟩ := mem_iUnion.mp hh
    exact hx.2 ((hU i).2.2 hi)
  have hGerm (x : E2) (hx : x∈frontier K'.space) (hxV : x∉V) : G =ᶠ[𝓝 x] f := by
    have hnx : x∉⋃ i:I,closure (U i) := by
      intro hh
      obtain ⟨i,hi⟩ := mem_iUnion.mp hh
      rcases hcl i hi with hxi | hxv
      · exact hx.2 hxi
      · exact hxV (hfaceV i.1.1 i.1.2 hxv)
    filter_upwards [(isClosed_iUnion_of_finite (fun i:I => isClosed_closure (s:=U i))).isOpen_compl.mem_nhds hnx] with y hy
    apply hGout
    intro hh
    obtain ⟨i,hi⟩ := mem_iUnion.mp hh
    exact hy (mem_iUnion.mpr ⟨i,subset_closure hi⟩)
  let VI := V.filter (fun x => x∈interior K'.space)
  have hVI : (VI:Set E2) ⊆ interior K'.space := by intro x hx; exact (Finset.mem_filter.mp hx).2
  have hGc' (x : E2) (hx : x∈interior K'.space) (hxVI : x∉(VI:Set E2)) : ContDiffAt ℝ 1 G x := by
    apply hGc
    rintro (hn | hv)
    · exact hn hx
    · exact hxVI (Finset.mem_filter.mpr ⟨hv,hx⟩)
  obtain ⟨J,hJL,hJc,hJG,hJD⟩ := relative_vertices_preserve_boundary_germs VI G hGL
    (interior K'.space) isOpen_interior hVI hGc'
  have hJDi := hJD K'.space interior_subset
  let S := V.filter (fun x => x∈frontier K'.space)
  refine ⟨J,hJL,?_,?_,?_,?_,S,?_,?_⟩
  · rw [← hsub.space_eq]
    exact hJDi.2 hGi
  · rw [← hsub.space_eq,hJDi.1,hGim,hsub.space_eq,hfim]
  · intro x hx
    have hx' : x∈frontier K'.space := hsub.space_eq.symm ▸ hx
    exact ((hJG x hx'.2).self_of_nhds).trans ((hGboundary hx').trans
      (hfF ((DifferentialGeometry.Topology.SimplicialComplex.isCompact_geometricSpace K).isClosed.frontier_subset hx)))
  · rw [← hsub.space_eq]
    exact hJc
  · intro x hx
    rw [← hsub.space_eq]
    exact (Finset.mem_filter.mp hx).2
  · intro x hx hxS
    have hx' : x∈frontier K'.space := hsub.space_eq.symm ▸ hx
    have hxV : x∉V := fun hv => hxS (Finset.mem_filter.mpr ⟨hv,hx'⟩)
    obtain ⟨O,A,hO,hxO,hA⟩ := boundary_affine_germ K' hK' f hmodels x hx'
      (fun hv => hxV ((hV x).mpr hv))
    have he : J =ᶠ[𝓝 x] f := (hJG x hx'.2).trans (hGerm x hx' hxV)
    have ha : ∀ᶠ y in 𝓝[K'.space] x,J y=A y := by
      filter_upwards [he.filter_mono nhdsWithin_le_nhds,
        (show ∀ᶠ y in 𝓝 x,y∈O from hO.mem_nhds hxO).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with y hy hyO hyK
      exact hy.trans (hA ⟨hyO,hyK⟩)
    obtain ⟨O',hO',hxO',hA'⟩ := mem_nhdsWithin.mp ha
    refine ⟨O',A,hO',hxO',?_⟩
    rw [← hsub.space_eq]
    exact hA'
end VM03CapV437PLAssembly

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CountGeometry
private theorem original_qdq_of_polar_producer
    (hPolar : ∀ (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
  (r : Fin (n+1) → ℝ) (t : Fin (m+1) → ℝ)
  (hr : StrictMono r) (ht : StrictMono t),
  r 0=0 → 0 < r (Fin.last n) → r (Fin.last n) < 1 →
  t 0=0 → t (Fin.last m)=2*Real.pi →
  ∀ (H : E2 → E2), (∃ L : NNReal, LipschitzWith L H) →
  (∀ x, r (Fin.last n) ≤ ‖x‖ → ContDiffAt ℝ 1 H x) →
  (∀ (i : Fin n) (j : Fin m),
    ContDiffOn ℝ 1 (fun z : ℝ×ℝ => H (z.1 • unitCircleParameter z.2))
      ((Icc (r i.castSucc) (r i.succ) ×ˢ Icc (t j.castSucc) (t j.succ)) \
        (({r i.castSucc,r i.succ}:Set ℝ) ×ˢ ({t j.castSucc,t j.succ}:Set ℝ)))) →
  ∃ (T : E2 → E2) (b : ℝ), r (Fin.last n) < b ∧ b < 1 ∧
    Bijective T ∧ ContDiff ℝ 1 T ∧ (∃ L : NNReal, LipschitzWith L T) ∧
    EqOn T id {x | b ≤ ‖x‖} ∧ T '' ball 0 1=ball 0 1 ∧
    ContDiff ℝ 1 (H ∘ T) ∧ (∃ L : NNReal, LipschitzWith L (H ∘ T)))


    (R : ℝ) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2) (hM : Continuous M) :
    ∃ q : E2 → E2, ∃ dq : Fin 2 → E2 → E2,
      MetricAdmissible Ω q dq ∧ ContDiffOn ℝ 1 q (closedDisc 1) ∧
      q '' disc 1=Ω.domain ∧ InjOn q (closedDisc 1) ∧
      (∀ i j,(fun x => dq i x j) =ᵐ[volume.restrict (disc 1)]
        (fun x => jacobianWithin q (closedDisc 1) x i j)) ∧
      metricArea M q dq=∫ y in Ω.domain,Real.sqrt (Matrix.det (M y)) := by
  exact original_qdq_of_producers VM03CapV437PLAssembly.relative_PL_producer hPolar R Ω M hM
end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CountGeometry

-- Paid source: PeriodicAngular
noncomputable section
open Set Filter Function
open scoped Topology ContDiff
namespace PolarSeam462

def angularLift (p : ℝ) (hp : 0 < p) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ψ (toIcoMod hp 0 x) + x - toIcoMod hp 0 x

theorem angularLift_translate (p : ℝ) (hp : 0 < p) (ψ : ℝ → ℝ)
    (x : ℝ) (k : ℤ) :
    angularLift p hp ψ (x + k • p) = angularLift p hp ψ x + k • p := by
  simp only [angularLift, toIcoMod_add_zsmul]
  ring

theorem angularLift_eq (p : ℝ) (hp : 0 < p) (ψ : ℝ → ℝ)
    (h0 : ψ 0 = 0) (hp' : ψ p = p) (x : ℝ) (hx : x ∈ Icc 0 p) :
    angularLift p hp ψ x = ψ x := by
  by_cases hxp : x = p
  · subst x
    have he : toIcoMod hp 0 p = 0 := by
      simpa using toIcoMod_add_zsmul hp 0 0 (1 : ℤ)
    simp [angularLift, he, h0, hp']
  · have he : toIcoMod hp 0 x = x :=
      (toIcoMod_eq_self hp).mpr ⟨hx.1, by simpa using lt_of_le_of_ne hx.2 hxp⟩
    simp [angularLift,he]

theorem angularLift_continuous (p : ℝ) (hp : 0 < p) (ψ : ℝ → ℝ)
    (hψ : Continuous ψ) (h0 : ψ 0 = 0) (hp' : ψ p = p) :
    Continuous (angularLift p hp ψ) := by
  letI : Fact (0 < p) := ⟨hp⟩
  let g : ℝ → ℝ := fun x => ψ x - x
  have he : g 0 = g p := by simp [g,h0,hp']
  have hg : Continuous (fun x : ℝ => AddCircle.liftIco p 0 g (x : AddCircle p)) :=
    (AddCircle.liftIco_zero_continuous he (hψ.sub continuous_id).continuousOn).comp
      (AddCircle.continuous_mk' p)
  have heq : angularLift p hp ψ = fun x : ℝ =>
      AddCircle.liftIco p 0 g (x : AddCircle p) + x := by
    funext x
    change ψ (toIcoMod hp 0 x) + x - toIcoMod hp 0 x =
      g (toIcoMod hp 0 x) + x
    dsimp [g]
    ring
  rw [heq]
  exact hg.add continuous_id


theorem angularLift_eq_shift (p : ℝ) (hp : 0 < p) (ψ : ℝ → ℝ)
    (h0 : ψ 0 = 0) (hp' : ψ p = p) (x : ℝ) (k : ℤ)
    (hx : x ∈ Icc (k • p) (k • p + p)) :
    angularLift p hp ψ x = ψ (x - k • p) + k • p := by
  have hu : x - k • p ∈ Icc 0 p := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have htr := angularLift_translate p hp ψ (x - k • p) k
  rw [sub_add_cancel,angularLift_eq p hp ψ h0 hp' _ hu] at htr
  exact htr

theorem angularLift_hasDerivAt_zero (p : ℝ) (hp : 0 < p) (ψ : ℝ → ℝ)
    (h0 : ψ 0 = 0) (hp' : ψ p = p)
    (hd0 : HasDerivAt ψ 0 0) (hdp : HasDerivAt ψ 0 p) :
    HasDerivAt (angularLift p hp ψ) 0 0 := by
  have he0 : angularLift p hp ψ 0 = ψ 0 :=
    angularLift_eq p hp ψ h0 hp' _ ⟨le_rfl,hp.le⟩
  have hdright : HasDerivWithinAt (angularLift p hp ψ) 0 (Icc 0 p) 0 :=
    hd0.hasDerivWithinAt.congr (fun x hx => (angularLift_eq p hp ψ h0 hp' x hx))
      he0
  have hshift : HasDerivAt (fun x : ℝ => ψ (x+p)-p) 0 0 := by
    have hd := (show HasDerivAt ψ 0 ((0 : ℝ)+p) by simpa using hdp).comp 0
      ((hasDerivAt_id (0 : ℝ)).add_const p)
    simpa only [zero_add,mul_one,Function.comp_def,id_eq] using hd.sub_const p
  have hdleft : HasDerivWithinAt (angularLift p hp ψ) 0 (Icc (-p) 0) 0 := by
    apply hshift.hasDerivWithinAt.congr
    · intro x hx
      have he := angularLift_eq_shift p hp ψ h0 hp' x (-1)
        (by simpa using hx)
      simpa only [neg_one_zsmul,sub_neg_eq_add,← sub_eq_add_neg] using he
    · simp [angularLift, h0,hp']
  have hcov : Icc (-p) 0 ∪ Icc 0 p = Icc (-p) p := by
    ext x
    simp only [mem_union,mem_Icc]
    constructor
    · rintro (h | h) <;> constructor <;> linarith [hp]
    · intro h
      rcases le_total x 0 with hx | hx
      · exact Or.inl ⟨h.1,hx⟩
      · exact Or.inr ⟨hx,h.2⟩
  have hn : Icc (-p) p ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (neg_neg_of_pos hp) hp
  exact (hcov ▸ hdleft.union hdright).hasDerivAt hn

theorem angularLift_hasDerivAt (p : ℝ) (hp : 0 < p) (ψ : ℝ → ℝ)
    (hψ : Differentiable ℝ ψ) (h0 : ψ 0 = 0) (hp' : ψ p = p)
    (hd0 : HasDerivAt ψ 0 0) (hdp : HasDerivAt ψ 0 p) (x : ℝ) :
    HasDerivAt (angularLift p hp ψ) (deriv ψ (toIcoMod hp 0 x)) x := by
  let u := toIcoMod hp 0 x
  let k := toIcoDiv hp 0 x
  have hu : u ∈ Ico 0 p := by simpa [u] using toIcoMod_mem_Ico hp 0 x
  have hx : x = u + k • p := by
    simpa [u,k] using (toIcoMod_add_toIcoDiv_zsmul hp 0 x).symm
  have hdu : HasDerivAt (angularLift p hp ψ) (deriv ψ u) u := by
    by_cases hu0 : u=0
    · rw [hu0,hd0.deriv]
      exact angularLift_hasDerivAt_zero p hp ψ h0 hp' hd0 hdp
    · have hup : 0<u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have hn : Icc 0 p ∈ 𝓝 u := Icc_mem_nhds hup hu.2
      have heq : angularLift p hp ψ =ᶠ[𝓝 u] ψ :=
        Filter.eventually_of_mem hn (fun y hy => angularLift_eq p hp ψ h0 hp' y hy)
      exact (hψ u).hasDerivAt.congr_of_eventuallyEq heq
  have hd := hdu.comp x (show HasDerivAt (fun y : ℝ => y - k • p) 1 x by
    simpa using (hasDerivAt_id x).sub_const (k • p))
  have he : x-k • p=u := by rw [hx]; ring
  have hd' := hd.add_const (k • p)
  have heq : (fun y : ℝ => angularLift p hp ψ (y-k • p)+k • p) = angularLift p hp ψ := by
    funext y
    simpa only [sub_add_cancel] using angularLift_translate p hp ψ (y-k • p) k |>.symm
  simpa only [mul_one,Function.comp_def,heq,u] using hd'

theorem angularLift_contDiff (p : ℝ) (hp : 0 < p) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ 1 ψ) (h0 : ψ 0 = 0) (hp' : ψ p = p)
    (hd0 : HasDerivAt ψ 0 0) (hdp : HasDerivAt ψ 0 p) :
    ContDiff ℝ 1 (angularLift p hp ψ) := by
  letI : Fact (0 < p) := ⟨hp⟩
  have hD : Continuous (fun x : ℝ => deriv ψ (toIcoMod hp 0 x)) := by
    have hc : Continuous (deriv ψ) := (contDiff_one_iff_deriv.mp hψ).2
    have he : deriv ψ 0=deriv ψ p := by rw [hd0.deriv,hdp.deriv]
    have hh := (AddCircle.liftIco_zero_continuous he hc.continuousOn).comp
      (AddCircle.continuous_mk' p)
    exact hh
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (angularLift_hasDerivAt p hp ψ (hψ.differentiable one_ne_zero)
    h0 hp' hd0 hdp x).differentiableAt,?_⟩
  have heq : deriv (angularLift p hp ψ) = fun x => deriv ψ (toIcoMod hp 0 x) := by
    funext x
    exact (angularLift_hasDerivAt p hp ψ (hψ.differentiable one_ne_zero)
      h0 hp' hd0 hdp x).deriv
  rwa [heq]


theorem angularLift_strictMono (p : ℝ) (hp : 0 < p) (ψ : ℝ → ℝ)
    (hψ : StrictMono ψ) (h0 : ψ 0 = 0) (hp' : ψ p = p) :
    StrictMono (angularLift p hp ψ) := by
  intro x y hxy
  let u := toIcoMod hp 0 x
  let v := toIcoMod hp 0 y
  let k := toIcoDiv hp 0 x
  let l := toIcoDiv hp 0 y
  have hu : 0≤u ∧ u<p := by simpa [u] using toIcoMod_mem_Ico hp 0 x
  have hv : 0≤v ∧ v<p := by simpa [v] using toIcoMod_mem_Ico hp 0 y
  have hx : x=u+k • p := by simpa [u,k] using (toIcoMod_add_toIcoDiv_zsmul hp 0 x).symm
  have hy : y=v+l • p := by simpa [v,l] using (toIcoMod_add_toIcoDiv_zsmul hp 0 y).symm
  have hkl : k≤l := by
    by_contra h
    have hli : l+1≤k := Int.add_one_le_iff.mpr (lt_of_not_ge h)
    have hmul := mul_le_mul_of_nonneg_right (show (l : ℝ)+1≤k by exact_mod_cast hli) hp.le
    simp only [zsmul_eq_mul] at hx hy
    nlinarith [hv.2,hu.1]
  have hfx : angularLift p hp ψ x=ψ u+k • p := by
    rw [hx,angularLift_translate,angularLift_eq p hp ψ h0 hp' u ⟨hu.1,hu.2.le⟩]
  have hfy : angularLift p hp ψ y=ψ v+l • p := by
    rw [hy,angularLift_translate,angularLift_eq p hp ψ h0 hp' v ⟨hv.1,hv.2.le⟩]
  rw [hfx,hfy]
  rcases hkl.eq_or_lt with hkl | hkl
  · have huv : u<v := by rw [hx,hy,hkl] at hxy; linarith
    rw [hkl]
    linarith [hψ huv]
  · have hli : k+1≤l := Int.add_one_le_iff.mpr hkl
    have hmul := mul_le_mul_of_nonneg_right (show (k : ℝ)+1≤l by exact_mod_cast hli) hp.le
    have hup : ψ u<p := by simpa [hp'] using hψ hu.2
    have hv0 : 0≤ψ v := by simpa [h0] using hψ.monotone hv.1
    simp only [zsmul_eq_mul]
    nlinarith

theorem angularLift_surjective (p : ℝ) (hp : 0 < p) (ψ : ℝ → ℝ)
    (hψ : StrictMono ψ) (hψs : Surjective ψ) (h0 : ψ 0 = 0) (hp' : ψ p = p) :
    Surjective (angularLift p hp ψ) := by
  intro y
  let v := toIcoMod hp 0 y
  let l := toIcoDiv hp 0 y
  have hv : 0≤v ∧ v<p := by simpa [v] using toIcoMod_mem_Ico hp 0 y
  have hy : y=v+l • p := by simpa [v,l] using (toIcoMod_add_toIcoDiv_zsmul hp 0 y).symm
  obtain ⟨u,hu⟩ := hψs v
  have hu0 : 0≤u := hψ.le_iff_le.mp (by rw [h0,hu];exact hv.1)
  have hup : u<p := hψ.lt_iff_lt.mp (by rw [hp',hu];exact hv.2)
  refine ⟨u+l • p,?_⟩
  rw [angularLift_translate,angularLift_eq p hp ψ h0 hp' u ⟨hu0,hup.le⟩,hu]
  exact hy.symm

theorem angularLift_lipschitz (p : ℝ) (hp : 0 < p) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ 1 ψ) (h0 : ψ 0 = 0) (hp' : ψ p = p)
    (hd0 : HasDerivAt ψ 0 0) (hdp : HasDerivAt ψ 0 p)
    (K : NNReal) (hK : LipschitzWith K ψ) :
    LipschitzWith K (angularLift p hp ψ) := by
  have hd := angularLift_hasDerivAt p hp ψ (hψ.differentiable one_ne_zero) h0 hp' hd0 hdp
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hd x).differentiableAt)
  intro x
  rw [(hd x).deriv]
  exact_mod_cast norm_deriv_le_of_lipschitz hK

end PolarSeam462

-- Paid source: PolarGeometry
noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
namespace PolarSeam462

def planeComplex (x : E2) : ℂ := (x 0 : ℂ)+Complex.I*(x 1 : ℂ)
def complexPlane (z : ℂ) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![z.re,z.im]

def planeComplexEquiv : E2 ≃L[ℝ] ℂ where
  toFun := planeComplex
  invFun := complexPlane
  left_inv := by
    intro x
    ext i
    fin_cases i <;> simp [planeComplex,complexPlane]
  right_inv := by
    intro z
    apply Complex.ext <;> simp [planeComplex,complexPlane]
  map_add' := by
    intro x y
    apply Complex.ext <;> simp [planeComplex] <;> ring
  map_smul' := by
    intro r x
    apply Complex.ext <;> simp [planeComplex] <;> ring
  continuous_toFun := by
    unfold planeComplex
    fun_prop
  continuous_invFun := by
    unfold complexPlane
    exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
      (continuous_pi (by intro i;fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] <;> fun_prop))

theorem planeComplex_norm (x : E2) : ‖planeComplex x‖=‖x‖ := by
  have hx := EuclideanSpace.real_norm_sq_eq x
  have hz := Complex.sq_norm (planeComplex x)
  simp [Fin.sum_univ_two] at hx
  simp [planeComplex,Complex.normSq_apply] at hz
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(x 0 : ℂ)+Complex.I*(x 1 : ℂ)‖^2=‖x‖^2
  rw [hz,hx]
  ring

theorem unitCircle_norm (θ : ℝ) : ‖unitCircleParameter θ‖=1 := by
  have hh : ‖unitCircleParameter θ‖^2=1 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
    exact Real.cos_sq_add_sin_sq θ
  nlinarith [norm_nonneg (unitCircleParameter θ)]

theorem polar_norm (r θ : ℝ) (hr : 0≤r) : ‖r • unitCircleParameter θ‖=r := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,unitCircle_norm,mul_one]

theorem unitCircle_contDiff : ContDiff ℝ 1 unitCircleParameter := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ 1 Real.cos
    fun_prop
  · change ContDiff ℝ 1 Real.sin
    fun_prop

theorem unitCircle_period (θ : ℝ) (k : ℤ) :
    unitCircleParameter (θ+k • (2*Real.pi))=unitCircleParameter θ := by
  ext i
  fin_cases i <;> simp [unitCircleParameter,zsmul_eq_mul,
    Real.cos_add_int_mul_two_pi,Real.sin_add_int_mul_two_pi]

theorem unitCircle_eq_iff (θ φ : ℝ) :
    unitCircleParameter θ=unitCircleParameter φ ↔ ∃ k : ℤ, θ=φ+k • (2*Real.pi) := by
  constructor
  · intro he
    have hc : Real.cos θ=Real.cos φ := congrArg (fun x:E2=>x 0) he
    have hs : Real.sin θ=Real.sin φ := congrArg (fun x:E2=>x 1) he
    obtain ⟨k,hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (Real.Angle.cos_sin_inj hc hs)
    exact ⟨k,by rw [zsmul_eq_mul];linarith⟩
  · rintro ⟨k,rfl⟩
    exact unitCircle_period φ k

def planeArgument (x : E2) : ℝ := Complex.arg (planeComplex x)

theorem polar_reconstruct (x : E2) : ‖x‖ • unitCircleParameter (planeArgument x)=x := by
  ext i
  fin_cases i
  · change ‖x‖*Real.cos (Complex.arg (planeComplex x))=x 0
    rw [← planeComplex_norm,Complex.norm_mul_cos_arg]
    simp [planeComplex]
  · change ‖x‖*Real.sin (Complex.arg (planeComplex x))=x 1
    rw [← planeComplex_norm,Complex.norm_mul_sin_arg]
    simp [planeComplex]

theorem local_polar_argument (x : E2) (hx : x≠0) :
    ∃ θ : E2→ℝ, ContDiffAt ℝ 1 θ x ∧
      ∀ y : E2, ‖y‖ • unitCircleParameter (θ y)=y := by
  have hz : planeComplex x≠0 := by
    intro h
    have he : ‖x‖=0 := by rw [← planeComplex_norm,h,norm_zero]
    exact hx (norm_eq_zero.mp he)
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hz with h | h
  · refine ⟨planeArgument,?_,polar_reconstruct⟩
    have hl : ContDiffAt ℝ 1 (fun z:ℂ=>Complex.log z) (planeComplex x) :=
      (Complex.contDiffAt_log h).restrict_scalars ℝ
    have hh := Complex.imCLM.contDiff.contDiffAt.comp x (hl.comp x planeComplexEquiv.contDiff.contDiffAt)
    change ContDiffAt ℝ 1 (fun y:E2=>Complex.arg (planeComplex y)) x
    simpa only [Function.comp_def,Complex.imCLM_apply,Complex.log_im] using hh
  · let θ : E2→ℝ := fun y=>Complex.arg (-planeComplex y)+Real.pi
    refine ⟨θ,?_,?_⟩
    · have hl : ContDiffAt ℝ 1 (fun z:ℂ=>Complex.log z) (-planeComplex x) :=
        (Complex.contDiffAt_log h).restrict_scalars ℝ
      have hn : ContDiff ℝ 1 (fun y:E2=>-planeComplex y) := planeComplexEquiv.contDiff.neg
      have hh := Complex.imCLM.contDiff.contDiffAt.comp x (hl.comp x hn.contDiffAt)
      have hh' : ContDiffAt ℝ 1 (fun y:E2=>Complex.arg (-planeComplex y)) x := by
        simpa only [Function.comp_def,Complex.imCLM_apply,Complex.log_im] using hh
      exact hh'.add contDiffAt_const
    · intro y
      have hneg : planeComplex (-y)=-planeComplex y := planeComplexEquiv.map_neg y
      have he := polar_reconstruct (-y)
      ext i
      fin_cases i
      · change ‖y‖*Real.cos (Complex.arg (-planeComplex y)+Real.pi)=y 0
        have he0:=congrArg (fun z:E2=>z 0) he
        change ‖-y‖*Real.cos (Complex.arg (planeComplex (-y)))=-y 0 at he0
        rw [norm_neg,hneg] at he0
        rw [Real.cos_add_pi]
        linarith
      · change ‖y‖*Real.sin (Complex.arg (-planeComplex y)+Real.pi)=y 1
        have he1:=congrArg (fun z:E2=>z 1) he
        change ‖-y‖*Real.sin (Complex.arg (planeComplex (-y)))=-y 1 at he1
        rw [norm_neg,hneg] at he1
        rw [Real.sin_add_pi]
        linarith

end PolarSeam462

-- Paid source: SupportedPolarMap
noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
namespace PolarSeam462

def polarMap (σ : ℝ→ℝ) (B : ℝ→ℝ→ℝ) (x : E2) : E2 :=
  σ ‖x‖ • unitCircleParameter (B ‖x‖ (planeArgument x))

theorem polarMap_norm (σ : ℝ→ℝ) (B : ℝ→ℝ→ℝ)
    (hσ : StrictMono σ) (h0 : σ 0=0) (x : E2) :
    ‖polarMap σ B x‖=σ ‖x‖ :=
  polar_norm _ _ (by simpa [h0] using hσ.monotone (norm_nonneg x))

theorem polarMap_zero (σ : ℝ→ℝ) (B : ℝ→ℝ→ℝ) (h0 : σ 0=0) :
    polarMap σ B 0=0 := by simp [polarMap,h0]

theorem polarMap_representation (σ : ℝ→ℝ) (B : ℝ→ℝ→ℝ)
    (hB : ∀ r θ (k:ℤ),B r (θ+k • (2*Real.pi))=B r θ+k • (2*Real.pi))
    (x : E2) (hx : x≠0) (θ : ℝ) (hθ : ‖x‖ • unitCircleParameter θ=x) :
    polarMap σ B x=σ ‖x‖ • unitCircleParameter (B ‖x‖ θ) := by
  have hn : ‖x‖≠0 := norm_ne_zero_iff.mpr hx
  have he : unitCircleParameter (planeArgument x)=unitCircleParameter θ := by
    apply smul_right_injective (R:=ℝ) E2 hn
    exact (polar_reconstruct x).trans hθ.symm
  obtain ⟨k,hk⟩ := (unitCircle_eq_iff _ _).mp he
  simp only [polarMap,hk,hB,unitCircle_period]

theorem polarMap_polar (σ : ℝ→ℝ) (B : ℝ→ℝ→ℝ) (h0 : σ 0=0)
    (hB : ∀ r θ (k:ℤ),B r (θ+k • (2*Real.pi))=B r θ+k • (2*Real.pi))
    (r θ : ℝ) (hr : 0≤r) :
    polarMap σ B (r • unitCircleParameter θ)=σ r • unitCircleParameter (B r θ) := by
  by_cases hr0 : r=0
  · simp [hr0,polarMap,h0]
  · have hx : r • unitCircleParameter θ≠0 := by
      intro he
      have hh := polar_norm r θ hr
      rw [he,norm_zero] at hh
      exact hr0 hh.symm
    have he : ‖r • unitCircleParameter θ‖ • unitCircleParameter θ=r • unitCircleParameter θ := by
      rw [polar_norm r θ hr]
    simpa only [polar_norm r θ hr] using polarMap_representation σ B hB _ hx θ he

theorem polarMap_injective (σ : ℝ→ℝ) (B : ℝ→ℝ→ℝ)
    (hσ : StrictMono σ) (h0 : σ 0=0)
    (hB : ∀ r θ (k:ℤ),B r (θ+k • (2*Real.pi))=B r θ+k • (2*Real.pi))
    (hBi : ∀ r,Injective (B r)) : Injective (polarMap σ B) := by
  intro x y hxy
  have hn : ‖x‖=‖y‖ := hσ.injective (by
    simpa only [polarMap_norm σ B hσ h0] using congrArg norm hxy)
  by_cases hx : x=0
  · subst x
    have hy : y=0 := norm_eq_zero.mp (by simpa using hn.symm)
    exact hy.symm
  · have hr : σ ‖x‖≠0 := by
      have hh : 0<σ ‖x‖ := by simpa [h0] using hσ (norm_pos_iff.mpr hx)
      exact hh.ne'
    have he : unitCircleParameter (B ‖x‖ (planeArgument x))=
        unitCircleParameter (B ‖x‖ (planeArgument y)) := by
      apply smul_right_injective (R:=ℝ) E2 hr
      simpa only [polarMap,← hn] using hxy
    obtain ⟨k,hk⟩ := (unitCircle_eq_iff _ _).mp he
    have hang : planeArgument x=planeArgument y+k • (2*Real.pi) := by
      apply hBi ‖x‖
      rw [hB]
      exact hk
    calc
      x=‖x‖ • unitCircleParameter (planeArgument x) := (polar_reconstruct x).symm
      _=‖y‖ • unitCircleParameter (planeArgument y) := by rw [hn,hang,unitCircle_period]
      _=y := polar_reconstruct y

theorem polarMap_surjective (σ : ℝ→ℝ) (B : ℝ→ℝ→ℝ)
    (hσ : StrictMono σ) (hσs : Surjective σ) (h0 : σ 0=0)
    (hB : ∀ r θ (k:ℤ),B r (θ+k • (2*Real.pi))=B r θ+k • (2*Real.pi))
    (hBs : ∀ r,Surjective (B r)) : Surjective (polarMap σ B) := by
  intro y
  obtain ⟨r,hr⟩ := hσs ‖y‖
  have hr0 : 0≤r := hσ.le_iff_le.mp (by rw [h0,hr];exact norm_nonneg y)
  obtain ⟨θ,hθ⟩ := hBs r (planeArgument y)
  refine ⟨r • unitCircleParameter θ,?_⟩
  rw [polarMap_polar σ B h0 hB r θ hr0,hr,hθ]
  exact polar_reconstruct y

theorem polarMap_eqOn (σ : ℝ→ℝ) (B : ℝ→ℝ→ℝ) (b : ℝ)
    (hσ : ∀ r,b≤r→σ r=r) (hB : ∀ r θ,b≤r→B r θ=θ) :
    EqOn (polarMap σ B) id {x:E2 | b≤‖x‖} := by
  intro x hx
  change polarMap σ B x=x
  simp only [polarMap,hσ ‖x‖ hx,hB ‖x‖ (planeArgument x) hx]
  exact polar_reconstruct x

theorem polarMap_contDiffAt (σ : ℝ→ℝ) (B : ℝ→ℝ→ℝ)
    (hσ : ContDiff ℝ 1 σ) (hB : ContDiff ℝ 1 (fun z:ℝ×ℝ=>B z.1 z.2))
    (hBp : ∀ r θ (k:ℤ),B r (θ+k • (2*Real.pi))=B r θ+k • (2*Real.pi))
    (x : E2) (hx : x≠0) : ContDiffAt ℝ 1 (polarMap σ B) x := by
  obtain ⟨θ,hθ,hrep⟩ := local_polar_argument x hx
  have hn : ContDiffAt ℝ 1 (fun y:E2=>‖y‖) x := contDiffAt_norm ℝ hx
  have hf : ContDiffAt ℝ 1 (fun y:E2=>σ ‖y‖ • unitCircleParameter (B ‖y‖ (θ y))) x :=
    (hσ.contDiffAt.comp x hn).smul
      (unitCircle_contDiff.contDiffAt.comp x (hB.contDiffAt.comp x (hn.prodMk hθ)))
  apply hf.congr_of_eventuallyEq
  filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
  exact polarMap_representation σ B hBp y hy (θ y) (hrep y)



def angleBlend (A : ℝ→ℝ) (s : ℝ) (θ : ℝ) : ℝ := (1-s)*θ+s*A θ

theorem angleBlend_period (A : ℝ→ℝ)
    (hA : ∀ θ (k:ℤ),A (θ+k • (2*Real.pi))=A θ+k • (2*Real.pi))
    (s θ : ℝ) (k : ℤ) :
    angleBlend A s (θ+k • (2*Real.pi))=angleBlend A s θ+k • (2*Real.pi) := by
  simp only [angleBlend,hA]
  ring

theorem angleBlend_strictMono (A : ℝ→ℝ) (hA : StrictMono A)
    (s : ℝ) (hs : s ∈ Icc 0 1) : StrictMono (angleBlend A s) := by
  intro x y hxy
  have hAxy := hA hxy
  have hs0 : 0≤1-s := by linarith [hs.2]
  have h1 := mul_nonneg hs0 (sub_nonneg.mpr hxy.le)
  have h2 := mul_nonneg hs.1 (sub_nonneg.mpr hAxy.le)
  by_cases hs0' : s=0
  · simp [angleBlend,hs0',hxy]
  · have hh := mul_pos (lt_of_le_of_ne hs.1 (Ne.symm hs0')) (sub_pos.mpr hAxy)
    dsimp [angleBlend]
    nlinarith

theorem angleBlend_surjective (A : ℝ→ℝ) (hA : Continuous A)
    (hA0 : A 0=0) (hAp : A (2*Real.pi)=2*Real.pi)
    (hAt : ∀ θ (k:ℤ),A (θ+k • (2*Real.pi))=A θ+k • (2*Real.pi))
    (s : ℝ) : Surjective (angleBlend A s) := by
  intro y
  let v := toIcoMod Real.two_pi_pos 0 y
  let k := toIcoDiv Real.two_pi_pos 0 y
  have hv : v ∈ Ico 0 (2*Real.pi) := by simpa [v] using toIcoMod_mem_Ico Real.two_pi_pos 0 y
  have hB0 : angleBlend A s 0=0 := by simp [angleBlend,hA0]
  have hBp : angleBlend A s (2*Real.pi)=2*Real.pi := by dsimp [angleBlend];rw [hAp];ring
  have hc : Continuous (angleBlend A s) := by unfold angleBlend;fun_prop
  obtain ⟨θ,hθ,heθ⟩ := intermediate_value_Icc Real.two_pi_pos.le hc.continuousOn
    (show v ∈ Icc (angleBlend A s 0) (angleBlend A s (2*Real.pi)) by
      rw [hB0,hBp];exact ⟨hv.1,hv.2.le⟩)
  refine ⟨θ+k • (2*Real.pi),?_⟩
  rw [angleBlend_period A hAt,heθ]
  exact toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 y

def radialCutoff (a b r : ℝ) : ℝ := 1-Real.smoothTransition ((r-a)/(b-a))

theorem radialCutoff_contDiff (a b : ℝ) : ContDiff ℝ 1 (radialCutoff a b) := by
  unfold radialCutoff
  fun_prop

theorem radialCutoff_range (a b r : ℝ) : radialCutoff a b r ∈ Icc 0 1 := by
  have h0 := Real.smoothTransition.nonneg ((r-a)/(b-a))
  have h1 := Real.smoothTransition.le_one ((r-a)/(b-a))
  dsimp [radialCutoff]
  exact ⟨by linarith,by linarith⟩

theorem radialCutoff_one (a b r : ℝ) (hab : a < b) (hr : r≤a) :
    radialCutoff a b r=1 := by
  have ht : (r-a)/(b-a)≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  simp [radialCutoff,Real.smoothTransition.zero_of_nonpos ht]

theorem radialCutoff_zero (a b r : ℝ) (hab : a < b) (hr : b≤r) :
    radialCutoff a b r=0 := by
  have ht : 1≤(r-a)/(b-a) := (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
  simp [radialCutoff,Real.smoothTransition.one_of_one_le ht]

theorem supported_angle_contDiff (A : ℝ→ℝ) (hA : ContDiff ℝ 1 A) (a b : ℝ) :
    ContDiff ℝ 1 (fun z:ℝ×ℝ=>angleBlend A (radialCutoff a b z.1) z.2) := by
  unfold angleBlend
  exact ((contDiff_const.sub ((radialCutoff_contDiff a b).comp contDiff_fst)).mul contDiff_snd).add
    (((radialCutoff_contDiff a b).comp contDiff_fst).mul (hA.comp contDiff_snd))

end PolarSeam462

-- Paid source: PolarProfiles
noncomputable section
open Set Function Filter
open scoped ContDiff Topology
namespace VM03CapV437ScalarFlat
private theorem relative_flat_compression :
    ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ StrictMono φ ∧ Surjective φ ∧
      φ 0=0 ∧ HasDerivAt φ 0 0 ∧ (∀ t : ℝ, 1≤|t| → φ t=t) := by
  let φ : ℝ → ℝ := fun t => Real.smoothTransition (t^2)*t
  have hφ : ContDiff ℝ 1 φ := by dsimp [φ]; fun_prop
  have hφ0 : φ 0=0 := by simp [φ]
  have hodd (t : ℝ) : φ (-t) = -φ t := by simp [φ]
  have hmono : StrictMonoOn φ (Ici 0) := by
    intro x hx y hy hxy
    change 0≤x at hx
    change 0≤y at hy
    have hsq : x^2≤y^2 := by nlinarith
    have hcoeff := Real.smoothTransition.monotone hsq
    have hpos : 0<Real.smoothTransition (y^2) :=
      Real.smoothTransition.pos_of_pos (sq_pos_of_pos (lt_of_le_of_lt hx hxy))
    change Real.smoothTransition (x^2)*x < Real.smoothTransition (y^2)*y
    exact (mul_le_mul_of_nonneg_right hcoeff hx).trans_lt (mul_lt_mul_of_pos_left hxy hpos)
  have hstrict : StrictMono φ := by
    intro x y hxy
    by_cases hx : 0≤x
    · exact hmono hx (hx.trans hxy.le) hxy
    · by_cases hy : y≤0
      · have hh := hmono (neg_nonneg.mpr hy) (neg_nonneg.mpr (le_of_not_ge hx)) (neg_lt_neg hxy)
        rw [hodd,hodd] at hh
        linarith
      · have hx0 : φ x<0 := by
          have hh := hmono (by simp : (0:ℝ)∈Ici 0) (neg_nonneg.mpr (le_of_not_ge hx))
            (neg_pos.mpr (lt_of_not_ge hx))
          rw [hodd,hφ0] at hh
          linarith
        have hy0 : 0<φ y := by
          have hh := hmono (by simp : (0:ℝ)∈Ici 0) (le_of_lt (lt_of_not_ge hy)) (lt_of_not_ge hy)
          simpa [hφ0] using hh
        exact hx0.trans hy0
  have hout (t : ℝ) (ht : 1≤|t|) : φ t=t := by
    have hs : 1≤t^2 := by nlinarith [sq_abs t]
    simp [φ,Real.smoothTransition.one_of_one_le hs]
  have hsur : Surjective φ := by
    intro y
    let a := min y (-1)
    let b := max y 1
    have ha : a≤-1 := min_le_right _ _
    have hb : 1≤b := le_max_right _ _
    have hay : a≤y := min_le_left _ _
    have hyb : y≤b := le_max_left _ _
    have haout : φ a=a := hout a (by rw [abs_of_neg (by linarith)]; linarith)
    have hbout : φ b=b := hout b (by rw [abs_of_pos (by linarith)]; exact hb)
    obtain ⟨t,ht,hval⟩ := intermediate_value_Icc (hay.trans hyb) hφ.continuous.continuousOn
      (show y∈Icc (φ a) (φ b) by rw [haout,hbout]; exact ⟨hay,hyb⟩)
    exact ⟨t,hval⟩
  refine ⟨φ,hφ,hstrict,hsur,hφ0,?_,hout⟩
  have hs : DifferentiableAt ℝ (fun t : ℝ => Real.smoothTransition (t^2)) 0 := by fun_prop
  have hd := hs.hasDerivAt.mul (hasDerivAt_id (0:ℝ))
  convert! hd using 1 <;> simp [φ]

private theorem relative_profile_lipschitz (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hout : ∀ t, 1≤|t| → φ t=t) : ∃ K : NNReal, LipschitzWith K φ := by
  have hc : HasCompactSupport (fun t : ℝ => φ t-t) := by
    apply HasCompactSupport.intro' (K:=Icc (-1:ℝ) 1) isCompact_Icc isClosed_Icc
    intro t ht
    have habs : 1≤|t| := by
      by_contra h
      have hlt : |t|<1 := lt_of_not_ge h
      rw [abs_lt] at hlt
      exact ht ⟨hlt.1.le,hlt.2.le⟩
    rw [hout t habs,sub_self]
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc (hφ.sub contDiff_id) (by simp)
  refine ⟨K+1,?_⟩
  convert! hK.add (LipschitzWith.id (α:=ℝ)) using 1 <;> simp


private theorem image_eq_of_bijective_eqOn_compl {X Y : Type*}
    (F G : X → Y) (U : Set X) (hF : Bijective F) (hG : Bijective G)
    (hEq : EqOn F G Uᶜ) : F '' U=G '' U := by
  apply Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy⟩ := hG.2 (F x)
    refine ⟨y,?_,hy⟩
    by_contra hyn
    have hyx : y=x := hF.1 ((hEq hyn).trans hy)
    exact hyn (hyx ▸ hx)
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy⟩ := hF.2 (G x)
    refine ⟨y,?_,hy⟩
    by_contra hyn
    have hyx : y=x := hG.1 ((hEq hyn).symm.trans hy)
    exact hyn (hyx ▸ hx)


end VM03CapV437ScalarFlat

namespace VM03CapV437ScalarFlat
private theorem centered_scalar_flat (c r : ℝ) (hr : 0 < r) :
    ∃ φ : ℝ → ℝ,ContDiff ℝ 1 φ ∧ StrictMono φ ∧ Surjective φ ∧
      (∃ K : NNReal,LipschitzWith K φ) ∧ φ c=c ∧ HasDerivAt φ 0 c ∧
      EqOn φ id (Metric.ball c r)ᶜ := by
  obtain ⟨ψ,hψ,hmono,hsur,hψ0,hdψ0,hout⟩ := relative_flat_compression
  obtain ⟨K,hK⟩ := relative_profile_lipschitz ψ hψ hout
  let φ : ℝ → ℝ := fun x => c+r*ψ ((x-c)/r)
  have hφ : ContDiff ℝ 1 φ := by
    exact contDiff_const.add (contDiff_const.mul
      (hψ.comp ((contDiff_id.sub contDiff_const).div_const r)))
  have hφc : φ c=c := by simp [φ,hψ0]
  have hφmono : StrictMono φ := by
    intro x y hxy
    exact add_lt_add_right (mul_lt_mul_of_pos_left
      (hmono (div_lt_div_of_pos_right (sub_lt_sub_right hxy c) hr)) hr) c
  have hφsur : Surjective φ := by
    intro y
    obtain ⟨z,hz⟩ := hsur ((y-c)/r)
    refine ⟨c+r*z,?_⟩
    dsimp [φ]
    have hh : (c+r*z-c)/r=z := by field_simp; ring
    rw [hh,hz]
    field_simp
    ring
  have hφout : EqOn φ id (Metric.ball c r)ᶜ := by
    intro x hx
    have hdist : r ≤ |x-c| := by simpa [Metric.mem_ball,Real.dist_eq] using hx
    have ha : 1 ≤ |(x-c)/r| := by
      rw [abs_div,abs_of_pos hr]
      exact (le_div_iff₀ hr).mpr (by simpa using hdist)
    dsimp [φ]
    rw [hout _ ha]
    field_simp
    ring
  have hcompact : HasCompactSupport (fun x : ℝ => φ x-x) := by
    apply HasCompactSupport.intro' (K:=Metric.closedBall c r) (isCompact_closedBall _ _) Metric.isClosed_closedBall
    intro x hx
    rw [hφout (fun hxb => hx (Metric.ball_subset_closedBall hxb))]
    simp
  have hφL : ∃ L : NNReal,LipschitzWith L φ := by
    obtain ⟨M,hM⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact (hφ.sub contDiff_id) (by simp)
    refine ⟨M+1,?_⟩
    convert hM.add (LipschitzWith.id (α:=ℝ)) using 1 <;> simp
  refine ⟨φ,hφ,hφmono,hφsur,hφL,hφc,?_,?_⟩
  · have hD : HasDerivAt (fun x : ℝ => (x-c)/r) (1/r) c := by
      simpa using ((hasDerivAt_id c).sub_const c).div_const r
    have hψD : HasDerivAt (fun x : ℝ => ψ ((x-c)/r)) 0 c := by
      have hh := (show HasDerivAt ψ 0 ((c-c)/r) by simpa using hdψ0).comp c hD
      convert hh using 1 <;> simp [Function.comp_def]
    simpa [φ] using (hψD.const_mul r).const_add c
  · intro x hx
    have hdist : r ≤ |x-c| := by simpa [Metric.mem_ball,Real.dist_eq] using hx
    have ha : 1 ≤ |(x-c)/r| := by
      rw [abs_div,abs_of_pos hr]
      exact (le_div_iff₀ hr).mpr (by simpa using hdist)
    dsimp [φ]
    rw [hout _ ha]
    field_simp
    ring

private theorem finite_flat_grid (S : Finset ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hSU : (S:Set ℝ) ⊆ U) :
    ∃ φ : ℝ → ℝ,ContDiff ℝ 1 φ ∧ StrictMono φ ∧ Surjective φ ∧
      (∃ K : NNReal,LipschitzWith K φ) ∧ EqOn φ id Uᶜ ∧
      (∀ c∈S,φ c=c ∧ HasDerivAt φ 0 c) ∧
      (∀ D : Set ℝ,U ⊆ D → φ '' D=D) := by
  classical
  induction S using Finset.induction_on generalizing U with
  | empty =>
    exact ⟨id,contDiff_id,strictMono_id,surjective_id,⟨1,LipschitzWith.id⟩,
      fun _ _ => rfl,by simp,fun _ _ => image_id _⟩
  | @insert c S hc ih =>
    obtain ⟨ψ,hψ,hψm,hψs,⟨K,hK⟩,hψout,hψnodes,hψD⟩ :=
      ih (U \ ({c}:Set ℝ)) (hU.sdiff isClosed_singleton) (by
        intro x hx
        exact ⟨hSU (by simp [hx]),fun hxc => hc (hxc ▸ hx)⟩)
    have hW : IsOpen (U \ (S:Set ℝ)) := hU.sdiff S.finite_toSet.isClosed
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hW c ⟨hSU (by simp),hc⟩
    obtain ⟨χ,hχ,hχm,hχs,⟨L,hL⟩,hχc,hχd,hχout⟩ := centered_scalar_flat c r hr
    have hψc : ψ c=c := hψout (by simp)
    have hχnodes (a : ℝ) (ha : a∈S) : χ a=a := by
      exact hχout (fun hab => (hball hab).2 ha)
    have hχD (D : Set ℝ) (hUD : U ⊆ D) : χ '' D=D := by
      simpa using image_eq_of_bijective_eqOn_compl χ id D ⟨hχm.injective,hχs⟩ bijective_id
        (fun x hx => hχout (fun hxb => hx (hUD (hball hxb).1)))
    refine ⟨ψ ∘ χ,hψ.comp hχ,hψm.comp hχm,hψs.comp hχs,⟨K*L,hK.comp hL⟩,?_,?_,?_⟩
    · intro x hx
      change ψ (χ x)=x
      rw [hχout (fun hxb => hx (hball hxb).1)]
      exact hψout (fun hxW => hx hxW.1)
    · intro a ha
      rcases Finset.mem_insert.mp ha with hac | ha
      · subst a
        refine ⟨by simp only [comp_apply,hχc,hψc],?_⟩
        have hd : HasDerivAt ψ (deriv ψ c) (χ c) := by
          rw [hχc]
          exact (hψ.differentiable one_ne_zero c).hasDerivAt
        simpa only [mul_zero] using hd.comp c hχd
      · refine ⟨by simp only [comp_apply,hχnodes a ha,(hψnodes a ha).1],?_⟩
        have hd : HasDerivAt ψ 0 (χ a) := by rw [hχnodes a ha]; exact (hψnodes a ha).2
        simpa only [zero_mul] using hd.comp a ((hχ.differentiable one_ne_zero a).hasDerivAt)
    · intro D hUD
      rw [image_comp,hχD D hUD,hψD D (inter_subset_left.trans hUD)]
end VM03CapV437ScalarFlat

namespace VM03CapV437ScalarFlat
private theorem radial_grid_profile (n : ℕ) (hn : 0 < n) (r : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hr0 : r 0=0) (hrlast : r (Fin.last n) < 1) :
    ∃ σ : ℝ → ℝ,ContDiff ℝ 1 σ ∧ StrictMono σ ∧ Surjective σ ∧
      (∃ K : NNReal,LipschitzWith K σ) ∧ σ 0=0 ∧
      (∀ i,σ (r i)=r i) ∧
      (∀ i:Fin (n+1),i≠0 → HasDerivAt σ 0 (r i)) ∧
      EqOn σ id (Ioo 0 ((r (Fin.last n)+1)/2))ᶜ ∧
      (∀ i:Fin n,σ '' Icc (r i.castSucc) (r i.succ)=Icc (r i.castSucc) (r i.succ)) := by
  classical
  let S := (Finset.univ.erase (0:Fin (n+1))).image r
  let b := (r (Fin.last n)+1)/2
  have hSb : (S:Set ℝ) ⊆ Ioo 0 b := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have hi0 : (0:Fin (n+1)) < i := Fin.pos_iff_ne_zero.mpr (Finset.mem_erase.mp hi).1
    have hlow : 0 < r i := by simpa [hr0] using hr hi0
    have hu : r i ≤ r (Fin.last n) := hr.monotone (Fin.le_last i)
    exact ⟨hlow,by dsimp [b]; linarith⟩
  obtain ⟨σ,hσ,hσm,hσs,hσL,hout,hfix,hD⟩ := finite_flat_grid S (Ioo 0 b) isOpen_Ioo hSb
  have hzero : σ 0=0 := hout (by simp)
  have hnodes (i : Fin (n+1)) : σ (r i)=r i := by
    by_cases hi : i=0
    · subst i; simpa [hr0] using hzero
    · exact (hfix _ (Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr ⟨hi,Finset.mem_univ i⟩,rfl⟩)).1
  refine ⟨σ,hσ,hσm,hσs,hσL,hzero,hnodes,?_,hout,?_⟩
  · intro i hi
    exact (hfix _ (Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr ⟨hi,Finset.mem_univ i⟩,rfl⟩)).2
  · intro i
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨by simpa [hnodes] using hσm.monotone hx.1,by simpa [hnodes] using hσm.monotone hx.2⟩
    · intro y hy
      obtain ⟨x,rfl⟩ := hσs y
      exact ⟨x,⟨hσm.le_iff_le.mp (by simpa [hnodes] using hy.1),
        hσm.le_iff_le.mp (by simpa [hnodes] using hy.2)⟩,rfl⟩

private theorem angular_grid_profile (m : ℕ) (hm : 0 < m) (t : Fin (m+1) → ℝ)
    (ht : StrictMono t) (ht0 : t 0=0) (htlast : t (Fin.last m)=2*Real.pi) :
    ∃ ψ : ℝ → ℝ,ContDiff ℝ 1 ψ ∧ StrictMono ψ ∧ Surjective ψ ∧
      (∃ K : NNReal,LipschitzWith K ψ) ∧
      (∀ j,ψ (t j)=t j ∧ HasDerivAt ψ 0 (t j)) ∧
      ψ 0=0 ∧ ψ (2*Real.pi)=2*Real.pi ∧
      HasDerivAt ψ 0 0 ∧ HasDerivAt ψ 0 (2*Real.pi) ∧
      (∀ j:Fin m,ψ '' Icc (t j.castSucc) (t j.succ)=Icc (t j.castSucc) (t j.succ)) := by
  classical
  let S := Finset.univ.image t
  obtain ⟨ψ,hψ,hψm,hψs,hψL,hout,hfix,hD⟩ := finite_flat_grid S univ isOpen_univ (subset_univ _)
  have hnodes (j : Fin (m+1)) := hfix (t j) (Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩)
  refine ⟨ψ,hψ,hψm,hψs,hψL,hnodes,?_,?_,?_,?_,?_⟩
  · simpa [ht0] using (hnodes 0).1
  · simpa [htlast] using (hnodes (Fin.last m)).1
  · simpa [ht0] using (hnodes 0).2
  · simpa [htlast] using (hnodes (Fin.last m)).2
  · intro j
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨by simpa [(hnodes _).1] using hψm.monotone hx.1,
        by simpa [(hnodes _).1] using hψm.monotone hx.2⟩
    · intro y hy
      obtain ⟨x,rfl⟩ := hψs y
      exact ⟨x,⟨hψm.le_iff_le.mp (by simpa [(hnodes _).1] using hy.1),
        hψm.le_iff_le.mp (by simpa [(hnodes _).1] using hy.2)⟩,rfl⟩
end VM03CapV437ScalarFlat
noncomputable section
open Set Function Filter
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
namespace VM03CapV437PolarGlue
private theorem finite_closed_c1_glue {ι : Type*} [Fintype ι]
    (s : ι → Set E2) (hs : ∀ i,IsClosed (s i)) (F : E2 → E2)
    (D : E2 → E2 →L[ℝ] E2)
    (hD : ∀ i,ContinuousOn D (s i))
    (hd : ∀ i x,x∈s i → HasFDerivWithinAt F (D x) (s i) x)
    (x : E2) (hx : (⋃ i,s i)∈𝓝 x) : ContDiffAt ℝ 1 F x := by
  classical
  have hcont : ∀ A : Finset ι,ContinuousOn D (⋃ i∈A,s i) := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp
    | @insert i A hi ih =>
      simp only [Finset.mem_insert,iUnion_iUnion_eq_or_left]
      exact (hD i).union_of_isClosed ih (hs i)
        (A.finite_toSet.isClosed_biUnion (fun j hj => hs j))
  have hder (y : E2) : ∀ A : Finset ι,HasFDerivWithinAt F (D y) (⋃ i∈A,s i) y := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp
    | @insert i A hi ih =>
      have hdi : HasFDerivWithinAt F (D y) (s i) y := by
        by_cases hy : y∈s i
        · exact hd i y hy
        · exact HasFDerivWithinAt.of_notMem_closure (by simpa only [(hs i).closure_eq] using hy)
      simpa only [Finset.mem_insert,iUnion_iUnion_eq_or_left] using hdi.union ih
  have hcont' : ContinuousOn D (⋃ i,s i) := by simpa using hcont Finset.univ
  have hder' (y : E2) : HasFDerivWithinAt F (D y) (⋃ i,s i) y := by simpa using hder y Finset.univ
  apply contDiffAt_one_iff.mpr
  refine ⟨D,interior (⋃ i,s i),isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hx),
    hcont'.mono interior_subset,?_⟩
  intro y hy
  exact (hder' y).hasFDerivAt (mem_interior_iff_mem_nhds.mp hy)
end VM03CapV437PolarGlue

namespace PolarSeam462
open VM03CapV437ScalarFlat
theorem radial_flat_grid (n : ℕ) (hn : 0 < n) (r : Fin (n+1)→ℝ)
    (hr : StrictMono r) (hr0 : r 0=0) (hrlast : r (Fin.last n) < 1) :
    ∃ σ : ℝ→ℝ,ContDiff ℝ 1 σ ∧ StrictMono σ ∧ Surjective σ ∧
      (∃ K:NNReal,LipschitzWith K σ) ∧ σ 0=0 ∧ HasDerivAt σ 0 0 ∧
      (∀ i,σ (r i)=r i ∧ HasDerivAt σ 0 (r i)) ∧
      (∀ x:ℝ,(r (Fin.last n)+1)/2 ≤ x → σ x=x) ∧
      (∀ i:Fin n,σ '' Icc (r i.castSucc) (r i.succ)=Icc (r i.castSucc) (r i.succ)) := by
  obtain ⟨σ,hσ,hσm,hσs,⟨K,hK⟩,hσ0,hfix,hflat,hout,himages⟩ :=
    radial_grid_profile n hn r hr hr0 hrlast
  let i : Fin (n+1) := ⟨1,by omega⟩
  have hi : (0:Fin (n+1)) < i := by change 0 < 1;norm_num
  have hri : 0 < r i := by simpa [hr0] using hr hi
  let ε := r i/2
  have hε : 0 < ε := half_pos hri
  obtain ⟨χ,hχ,hχm,hχs,⟨L,hL⟩,hχ0,hχflat,hχout⟩ := centered_scalar_flat 0 ε hε
  have hχnode (j : Fin (n+1)) : χ (r j)=r j := by
    by_cases hj : j=0
    · subst j;simpa [hr0] using hχ0
    · have hij : i ≤ j := by change 1 ≤ j.val;exact Fin.pos_iff_ne_zero.mpr hj
      have hrj := hr.monotone hij
      apply hχout
      simp only [Metric.mem_ball,Real.dist_eq,sub_zero,mem_compl_iff,not_lt]
      rw [abs_of_nonneg (hri.le.trans hrj)]
      dsimp [ε]
      linarith
  have hχlarge (x : ℝ) (hx : (r (Fin.last n)+1)/2≤x) : χ x=x := by
    apply hχout
    simp only [Metric.mem_ball,Real.dist_eq,sub_zero,mem_compl_iff,not_lt]
    have hrimax := hr.monotone (Fin.le_last i)
    have hpos : 0 < x := by linarith
    rw [abs_of_pos hpos]
    dsimp [ε]
    linarith
  have hF0 : (σ ∘ χ) 0=0 := by simp [hχ0,hσ0]
  have hFnodes (j : Fin (n+1)) : (σ ∘ χ) (r j)=r j := by
    simp only [comp_apply,hχnode,hfix]
  have hFflat : HasDerivAt (σ ∘ χ) 0 0 := by
    have hd := (hσ.differentiable one_ne_zero (χ 0)).hasDerivAt.comp 0 hχflat
    simpa only [mul_zero] using hd
  refine ⟨σ ∘ χ,hσ.comp hχ,hσm.comp hχm,hσs.comp hχs,⟨K*L,hK.comp hL⟩,
    hF0,hFflat,?_,?_,?_⟩
  · intro j
    refine ⟨hFnodes j,?_⟩
    by_cases hj : j=0
    · subst j;simpa [hr0] using hFflat
    · have hd : HasDerivAt σ 0 (χ (r j)) := by rw [hχnode];exact hflat j hj
      simpa only [zero_mul] using hd.comp (r j) (hχ.differentiable one_ne_zero _).hasDerivAt
  · intro x hx
    change σ (χ x)=x
    rw [hχlarge x hx]
    exact hout (fun h=>not_lt_of_ge hx h.2)
  · intro j
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨by simpa only [comp_apply,hχnode,hfix] using (hσm.comp hχm).monotone hx.1,
        by simpa only [comp_apply,hχnode,hfix] using (hσm.comp hχm).monotone hx.2⟩
    · intro y hy
      obtain ⟨x,rfl⟩ := (hσs.comp hχs) y
      exact ⟨x,⟨(hσm.comp hχm).le_iff_le.mp (by simpa only [comp_apply,hχnode,hfix] using hy.1),
        (hσm.comp hχm).le_iff_le.mp (by simpa only [comp_apply,hχnode,hfix] using hy.2)⟩,rfl⟩


theorem periodic_angular_grid (m : ℕ) (hm : 0 < m) (t : Fin (m+1)→ℝ)
    (ht : StrictMono t) (ht0 : t 0=0) (htlast : t (Fin.last m)=2*Real.pi) :
    ∃ A : ℝ→ℝ,ContDiff ℝ 1 A ∧ StrictMono A ∧ Surjective A ∧
      (∃ K:NNReal,LipschitzWith K A) ∧ A 0=0 ∧ A (2*Real.pi)=2*Real.pi ∧
      (∀ θ (k:ℤ),A (θ+k • (2*Real.pi))=A θ+k • (2*Real.pi)) ∧
      (∀ j,A (t j)=t j ∧ HasDerivAt A 0 (t j)) ∧
      (∀ j:Fin m,A '' Icc (t j.castSucc) (t j.succ)=Icc (t j.castSucc) (t j.succ)) := by
  obtain ⟨ψ,hψ,hψm,hψs,⟨K,hK⟩,hnodes,h0,hp,hd0,hdp,himages⟩ :=
    angular_grid_profile m hm t ht ht0 htlast
  let A := angularLift (2*Real.pi) Real.two_pi_pos ψ
  have heq (θ : ℝ) (hθ : θ ∈ Icc 0 (2*Real.pi)) : A θ=ψ θ :=
    angularLift_eq _ _ _ h0 hp θ hθ
  have htmem (j : Fin (m+1)) : t j ∈ Icc 0 (2*Real.pi) := by
    exact ⟨by simpa [ht0] using ht.monotone (Fin.zero_le j),
      by simpa [htlast] using ht.monotone (Fin.le_last j)⟩
  have hAm : StrictMono A := angularLift_strictMono _ _ _ hψm h0 hp
  have hAs : Surjective A := angularLift_surjective _ _ _ hψm hψs h0 hp
  have hAc : ContDiff ℝ 1 A := angularLift_contDiff _ _ _ hψ h0 hp hd0 hdp
  have hAnodes (j : Fin (m+1)) : A (t j)=t j := by rw [heq _ (htmem j)];exact (hnodes j).1
  refine ⟨A,hAc,hAm,hAs,⟨K,angularLift_lipschitz _ _ _ hψ h0 hp hd0 hdp K hK⟩,
    by rw [heq _ ⟨le_rfl,Real.two_pi_pos.le⟩,h0],
    by rw [heq _ ⟨Real.two_pi_pos.le,le_rfl⟩,hp],
    angularLift_translate _ _ _,?_,?_⟩
  · intro j
    refine ⟨hAnodes j,?_⟩
    have hd := angularLift_hasDerivAt (2*Real.pi) Real.two_pi_pos ψ (hψ.differentiable one_ne_zero) h0 hp hd0 hdp (t j)
    by_cases hjp : t j=2*Real.pi
    · have he : toIcoMod Real.two_pi_pos 0 (2*Real.pi)=0 := by
        simpa using toIcoMod_add_zsmul Real.two_pi_pos 0 0 (1:ℤ)
      simpa [hjp,he,hd0.deriv] using hd
    · have he : toIcoMod Real.two_pi_pos 0 (t j)=t j :=
        (toIcoMod_eq_self Real.two_pi_pos).mpr ⟨(htmem j).1,
          by simpa only [zero_add] using lt_of_le_of_ne (htmem j).2 hjp⟩
      simpa only [he,(hnodes j).2.deriv] using hd
  · intro j
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨by simpa only [hAnodes] using hAm.monotone hx.1,
        by simpa only [hAnodes] using hAm.monotone hx.2⟩
    · intro y hy
      obtain ⟨x,rfl⟩ := hAs y
      exact ⟨x,⟨hAm.le_iff_le.mp (by simpa only [hAnodes] using hy.1),
        hAm.le_iff_le.mp (by simpa only [hAnodes] using hy.2)⟩,rfl⟩

end PolarSeam462

-- Paid source: PolarLipschitz
noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational

namespace PolarSeam462

theorem normalized_distance_bound (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hsr : s ≤ r)
    (u v : E2) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    s*‖u-v‖ ≤ 2*‖r • u-s • v‖ := by
  have hn : r-s ≤ ‖r • u-s • v‖ := by
    have hh := norm_sub_norm_le (r • u) (s • v)
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,abs_of_nonneg hs,hu,hv,mul_one] using hh
  have he : s • (u-v)=(r • u-s • v)-(r-s) • u := by
    simp only [smul_sub,sub_smul]
    abel
  have hh := norm_sub_le (r • u-s • v) ((r-s) • u)
  rw [← he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hsr),hu,mul_one] at hh
  linarith

theorem angular_sphere_lipschitz (A : ℝ→ℝ) (hA : ContDiff ℝ 1 A)
    (hAt : ∀ θ (k:ℤ),A (θ+k • (2*Real.pi))=A θ+k • (2*Real.pi)) :
    ∃ K:NNReal,LipschitzOnWith K (polarMap id (fun _ θ=>A θ)) (sphere (0:E2) 1) := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (isCompact_sphere _ _)
  intro x hx
  have hx0 : x≠0 := by
    intro he
    subst x
    simpa using hx
  have hc := polarMap_contDiffAt id (fun _ θ=>A θ) contDiff_id
    (hA.comp contDiff_snd) (fun _ θ k=>hAt θ k) x hx0
  obtain ⟨K,U,hU,hK⟩ := hc.exists_lipschitzOnWith
  exact ⟨K,U,mem_nhdsWithin_of_mem_nhds hU,hK.mono (subset_rfl)⟩

theorem radial_angular_lipschitz (σ A : ℝ→ℝ)
    (hσ : StrictMono σ) (hσ0 : σ 0=0) (K : NNReal) (hK : LipschitzWith K σ)
    (L : NNReal) (hL : LipschitzOnWith L (polarMap id (fun _ θ=>A θ)) (sphere (0:E2) 1))
    (hAt : ∀ θ (k:ℤ),A (θ+k • (2*Real.pi))=A θ+k • (2*Real.pi)) :
    LipschitzWith (K*(1+2*L)) (polarMap σ (fun _ θ=>A θ)) := by
  have hbound (x y : E2) (hyx : ‖y‖ ≤ ‖x‖) :
      dist (polarMap σ (fun _ θ=>A θ) x) (polarMap σ (fun _ θ=>A θ) y) ≤ 
        (K*(1+2*L):NNReal)*dist x y := by
    let u := unitCircleParameter (planeArgument x)
    let v := unitCircleParameter (planeArgument y)
    let Ju := unitCircleParameter (A (planeArgument x))
    let Jv := unitCircleParameter (A (planeArgument y))
    have hu : ‖u‖=1 := unitCircle_norm _
    have hv : ‖v‖=1 := unitCircle_norm _
    have hJu : ‖Ju‖=1 := unitCircle_norm _
    have hJv : ‖Jv‖=1 := unitCircle_norm _
    have hrepx : ‖x‖ • u=x := polar_reconstruct x
    have hrepy : ‖y‖ • v=y := polar_reconstruct y
    have hJux : polarMap id (fun _ θ=>A θ) u=Ju := by
      simpa only [id_eq,one_smul] using polarMap_polar id (fun _ θ=>A θ) rfl
        (fun _ θ k=>hAt θ k) 1 (planeArgument x) zero_le_one
    have hJvy : polarMap id (fun _ θ=>A θ) v=Jv := by
      simpa only [id_eq,one_smul] using polarMap_polar id (fun _ θ=>A θ) rfl
        (fun _ θ k=>hAt θ k) 1 (planeArgument y) zero_le_one
    have hdist : ‖Ju-Jv‖ ≤ (L:ℝ)*‖u-v‖ := by
      have hh:=hL.dist_le_mul u (by simp [Metric.mem_sphere,hu]) v (by simp [Metric.mem_sphere,hv])
      simpa only [hJux,hJvy,dist_eq_norm] using hh
    have hσxy : |σ ‖x‖-σ ‖y‖| ≤ (K:ℝ)*(‖x‖-‖y‖) := by
      have hh:=hK.dist_le_mul ‖x‖ ‖y‖
      simpa only [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hyx)] using hh
    have hσy : σ ‖y‖ ≤ (K:ℝ)*‖y‖ := by
      have hh:=hK.dist_le_mul ‖y‖ 0
      have hn : 0 ≤ σ ‖y‖ := by simpa only [hσ0] using hσ.monotone (norm_nonneg y)
      simpa only [hσ0,Real.dist_eq,sub_zero,abs_of_nonneg hn,
        abs_of_nonneg (norm_nonneg y)] using hh
    have hσy0 : 0 ≤ σ ‖y‖ := by simpa only [hσ0] using hσ.monotone (norm_nonneg y)
    have hn := normalized_distance_bound ‖x‖ ‖y‖ (norm_nonneg x) (norm_nonneg y) hyx u v hu hv
    rw [hrepx,hrepy] at hn
    have hdxy := norm_sub_norm_le x y
    have he : σ ‖x‖ • Ju-σ ‖y‖ • Jv=(σ ‖x‖-σ ‖y‖) • Ju+σ ‖y‖ • (Ju-Jv) := by
      simp only [sub_smul,smul_sub]
      abel
    have hb := norm_add_le ((σ ‖x‖-σ ‖y‖) • Ju) (σ ‖y‖ • (Ju-Jv))
    rw [← he,norm_smul,Real.norm_eq_abs,hJu,mul_one,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg hσy0] at hb
    have hh2 : σ ‖y‖*‖Ju-Jv‖ ≤ (K:ℝ)*(L:ℝ)*(2*‖x-y‖) := by
      calc
        σ ‖y‖*‖Ju-Jv‖ ≤ σ ‖y‖*((L:ℝ)*‖u-v‖) := mul_le_mul_of_nonneg_left hdist hσy0
        _ ≤ ((K:ℝ)*‖y‖)*((L:ℝ)*‖u-v‖) := mul_le_mul_of_nonneg_right hσy (by positivity)
        _=(K:ℝ)*(L:ℝ)*(‖y‖*‖u-v‖) := by ring
        _ ≤ (K:ℝ)*(L:ℝ)*(2*‖x-y‖) := mul_le_mul_of_nonneg_left hn (by positivity)
    have hh1 := mul_le_mul_of_nonneg_left hdxy K.coe_nonneg
    change ‖σ ‖x‖ • Ju-σ ‖y‖ • Jv‖ ≤ _ * ‖x-y‖
    push_cast
    nlinarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total ‖y‖ ‖x‖ with hyx | hxy
  · exact hbound x y hyx
  · simpa only [dist_comm] using hbound y x hxy



theorem locally_lipschitz_supported (F : E2→E2) (b : ℝ) (hb : 0≤b)
    (hF : LocallyLipschitz F) (hout : ∀ x,b≤‖x‖→F x=0) :
    ∃ K:NNReal,LipschitzWith K F := by
  let S : Set E2 := closedBall 0 (b+1)
  have hS : IsCompact S := isCompact_closedBall _ _
  obtain ⟨K,hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS hF.locallyLipschitzOn
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn hF.continuous.continuousOn
  let N : NNReal := ⟨max M 0,le_max_right _ _⟩
  have hMN : M≤(N:ℝ) := le_max_left _ _
  have hnear (x y : E2) (hx : x∈S) (hy : y∉S) :
      dist (F x) (F y)≤((K+N:NNReal):ℝ)*dist x y := by
    have hyn : b+1 < ‖y‖ := by simpa [S,Metric.mem_closedBall] using hy
    have hyout : F y=0 := hout y (by linarith)
    by_cases hxb : b≤‖x‖
    · simp only [hout x hxb,hyout,dist_self]
      positivity
    · have hxsmall : ‖x‖ < b := lt_of_not_ge hxb
      have hd : 1≤dist x y := by
        have hh := norm_sub_norm_le y x
        rw [← dist_eq_norm,dist_comm y x] at hh
        linarith
      rw [hyout,dist_zero_right]
      calc
        ‖F x‖≤M := hM x hx
        _≤(N:ℝ) := hMN
        _≤(N:ℝ)*dist x y := by nlinarith [N.coe_nonneg]
        _≤((K+N:NNReal):ℝ)*dist x y := by push_cast;nlinarith [K.coe_nonneg,(show 0≤dist x y from dist_nonneg)]
  refine ⟨K+N,LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  by_cases hx : x∈S
  · by_cases hy : y∈S
    · exact (hK.dist_le_mul x hx y hy).trans (by push_cast;nlinarith [N.coe_nonneg,(show 0≤dist x y from dist_nonneg)])
    · exact hnear x y hx hy
  · by_cases hy : y∈S
    · simpa only [dist_comm] using hnear y x hy hx
    · have hxout : F x=0 := hout x (by
        have hh : b+1 < ‖x‖ := by simpa [S,Metric.mem_closedBall] using hx
        linarith)
      have hyout : F y=0 := hout y (by
        have hh : b+1 < ‖y‖ := by simpa [S,Metric.mem_closedBall] using hy
        linarith)
      simp only [hxout,hyout,dist_self]
      positivity

theorem locally_lipschitz_relative (F : E2→E2) (b : ℝ) (hb : 0≤b)
    (hF : LocallyLipschitz F) (hout : ∀ x,b≤‖x‖→F x=x) :
    ∃ K:NNReal,LipschitzWith K F := by
  have hG : LocallyLipschitz (fun x:E2=>F x-x) := by
    intro x
    obtain ⟨K,U,hU,hK⟩ := hF x
    exact ⟨K+1,U,hU,hK.sub (LipschitzWith.id.lipschitzOnWith)⟩
  obtain ⟨K,hK⟩ := locally_lipschitz_supported (fun x:E2=>F x-x) b hb hG
    (fun x hx=>by rw [hout x hx,sub_self])
  refine ⟨K+1,?_⟩
  simpa only [id_eq,sub_add_cancel] using hK.add (LipschitzWith.id (α:=E2))

theorem supported_polar_lipschitz (σ A : ℝ→ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hσ : ContDiff ℝ 1 σ) (hσm : StrictMono σ) (hσ0 : σ 0=0)
    (hσL : ∃ K:NNReal,LipschitzWith K σ)
    (hσout : ∀ r,b≤r→σ r=r)
    (hA : ContDiff ℝ 1 A)
    (hAt : ∀ θ (k:ℤ),A (θ+k • (2*Real.pi))=A θ+k • (2*Real.pi)) :
    ∃ K:NNReal,LipschitzWith K (polarMap σ (fun r θ=>angleBlend A (radialCutoff a b r) θ)) := by
  let T:=polarMap σ (fun r θ=>angleBlend A (radialCutoff a b r) θ)
  have hTp (r θ:ℝ) (k:ℤ) := angleBlend_period A hAt (radialCutoff a b r) θ k
  have hlocal : LocallyLipschitz T := by
    intro x
    by_cases hx : x=0
    · subst x
      obtain ⟨K,hK⟩ := hσL
      obtain ⟨L,hL⟩ := angular_sphere_lipschitz A hA hAt
      have hcone := radial_angular_lipschitz σ A hσm hσ0 K hK L hL hAt
      have he : EqOn T (polarMap σ (fun _ θ=>A θ)) (ball 0 a) := by
        intro y hy
        have hyn : ‖y‖≤a := (show ‖y‖ < a by simpa [Metric.mem_ball] using hy).le
        simp only [T,polarMap,radialCutoff_one a b ‖y‖ hab hyn,angleBlend,sub_self,
          zero_mul,one_mul,zero_add]
      refine ⟨K*(1+2*L),ball 0 a,ball_mem_nhds _ ha,?_⟩
      intro y hy z hz
      rw [he hy,he hz]
      exact hcone y z
    · have hc := polarMap_contDiffAt σ (fun r θ=>angleBlend A (radialCutoff a b r) θ)
        hσ (supported_angle_contDiff A hA a b) hTp x hx
      exact hc.exists_lipschitzOnWith
  have hout (x:E2) (hx : b≤‖x‖) : T x=x := by
    change polarMap σ (fun r θ=>angleBlend A (radialCutoff a b r) θ) x=x
    simp only [polarMap,hσout ‖x‖ hx,radialCutoff_zero a b ‖x‖ hab hx,angleBlend,
      sub_zero,one_mul,zero_mul,add_zero]
    exact polar_reconstruct x
  exact locally_lipschitz_relative T b (ha.le.trans hab.le) hlocal hout

end PolarSeam462

-- Paid source: ClosedDerivativeGlue
noncomputable section
open Set Filter Function
open scoped ContDiff Topology
namespace PolarSeam462
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem two_closed_c1_glue (s t : Set E) (hs : IsClosed s) (ht : IsClosed t)
    (f : E→F) (Dl Dr : E→E→L[ℝ]F)
    (hDl : ContinuousOn Dl s) (hDr : ContinuousOn Dr t)
    (hdl : ∀ x∈s,HasFDerivWithinAt f (Dl x) s x)
    (hdr : ∀ x∈t,HasFDerivWithinAt f (Dr x) t x)
    (hmatch : ∀ x∈s∩t,Dl x=Dr x) (x : E) (hx : s∪t ∈ 𝓝 x) :
    ContDiffAt ℝ 1 f x := by
  classical
  let D : E→E→L[ℝ]F := s.piecewise Dl Dr
  have hleft : EqOn D Dl s := by intro y hy;simp [D,hy]
  have hright : EqOn D Dr t := by
    intro y hy
    by_cases hys : y∈s
    · simp only [D,piecewise_eq_of_mem s Dl Dr hys]
      exact hmatch y ⟨hys,hy⟩
    · simp [D,hys]
  have hc : ContinuousOn D (s∪t) :=
    (hDl.congr hleft).union_of_isClosed (hDr.congr hright) hs ht
  have hd (y : E) : HasFDerivWithinAt f (D y) (s∪t) y := by
    have hls : HasFDerivWithinAt f (D y) s y := by
      by_cases hy : y∈s
      · rw [hleft hy];exact hdl y hy
      · exact HasFDerivWithinAt.of_notMem_closure (by simpa only [hs.closure_eq] using hy)
    have hrs : HasFDerivWithinAt f (D y) t y := by
      by_cases hy : y∈t
      · rw [hright hy];exact hdr y hy
      · exact HasFDerivWithinAt.of_notMem_closure (by simpa only [ht.closure_eq] using hy)
    exact hls.union hrs
  apply contDiffAt_one_iff.mpr
  refine ⟨D,interior (s∪t),isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hx),
    hc.mono interior_subset,?_⟩
  intro y hy
  exact (hd y).hasFDerivAt (mem_interior_iff_mem_nhds.mp hy)

theorem finite_matching_c1_glue {ι : Type*} [Fintype ι]
    (s : ι→Set E) (hs : ∀ i,IsClosed (s i)) (f : E→F) (D : ι→E→E→L[ℝ]F)
    (hD : ∀ i,ContinuousOn (D i) (s i))
    (hd : ∀ i x,x∈s i→HasFDerivWithinAt f (D i x) (s i) x)
    (hmatch : ∀ i j x,x∈s i∩s j→D i x=D j x)
    (x : E) (hx : (⋃ i,s i)∈𝓝 x) : ContDiffAt ℝ 1 f x := by
  classical
  let U : Set E := ⋃ i,s i
  let pick (y : E) (hy : y∈U) : ι := Classical.choose (mem_iUnion.mp hy)
  have hpick (y : E) (hy : y∈U) : y∈s (pick y hy) := Classical.choose_spec (mem_iUnion.mp hy)
  let Dall : E→E→L[ℝ]F := fun y=>if hy:y∈U then D (pick y hy) y else 0
  have heq (i:ι) : EqOn Dall (D i) (s i) := by
    intro y hy
    have hyU : y∈U := mem_iUnion.mpr ⟨i,hy⟩
    simp only [Dall,dif_pos hyU]
    exact hmatch _ i y ⟨hpick y hyU,hy⟩
  have hc : ∀ A:Finset ι,ContinuousOn Dall (⋃ i∈A,s i) := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp
    | @insert i A hi ih =>
      simp only [Finset.mem_insert,iUnion_iUnion_eq_or_left]
      exact ((hD i).congr (heq i)).union_of_isClosed ih (hs i)
        (A.finite_toSet.isClosed_biUnion (fun j hj=>hs j))
  have hder (y:E) : ∀ A:Finset ι,HasFDerivWithinAt f (Dall y) (⋃ i∈A,s i) y := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp
    | @insert i A hi ih =>
      have hdi : HasFDerivWithinAt f (Dall y) (s i) y := by
        by_cases hy:y∈s i
        · rw [heq i hy];exact hd i y hy
        · exact HasFDerivWithinAt.of_notMem_closure (by simpa only [(hs i).closure_eq] using hy)
      simpa only [Finset.mem_insert,iUnion_iUnion_eq_or_left] using hdi.union ih
  apply contDiffAt_one_iff.mpr
  have hcU : ContinuousOn Dall U := by simpa [U] using hc Finset.univ
  have hdU (y:E) : HasFDerivWithinAt f (Dall y) U y := by simpa [U] using hder y Finset.univ
  refine ⟨Dall,interior U,isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hx),
    hcU.mono interior_subset,?_⟩
  intro y hy
  exact (hdU y).hasFDerivAt (mem_interior_iff_mem_nhds.mp hy)

end PolarSeam462

-- Paid source: FiniteRegularization
noncomputable section
open Set Filter Function Asymptotics
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
namespace VM03CapPolarV464RelativeVertex

/- Multiplying a Lipschitz cone map by a smooth radial coefficient vanishing at the
   vertex removes the derivative singularity there.  Smoothness off the vertex is
   explicit: this lemma does not silently smooth the angular seams of a PL fan. -/
private theorem radial_coefficient_contDiff_one
    (H : E2 → E2) {K : NNReal} (hLip : LipschitzWith K H) (hzero : H 0 = 0)
    (hH : ∀ x : E2, x ≠ 0 → ContDiffAt ℝ 1 H x)
    (a : ℝ → ℝ) (ha : ContDiff ℝ 1 a) (ha0 : a 0 = 0) :
    ContDiff ℝ 1 (fun x : E2 => a ‖x‖ • H x) := by
  let F : E2 → E2 := fun x => a ‖x‖ • H x
  have hac : Continuous a := ha.continuous
  have hnorm (x : E2) : ‖H x‖ ≤ (K:ℝ)*‖x‖ := by
    simpa only [hzero,dist_zero_right] using hLip.dist_le_mul x 0
  have hF0 : F 0 = 0 := by simp [F,ha0]
  have hder0 : HasFDerivAt F (0 : E2 →L[ℝ] E2) 0 := by
    rw [hasFDerivAt_iff_isLittleO]
    simp only [hF0, ContinuousLinearMap.zero_apply, sub_zero]
    apply IsLittleO.of_bound
    intro ε hε
    have hc : ContinuousAt (fun x : E2 => |a ‖x‖| *(K:ℝ)) 0 := by fun_prop
    have hev : ∀ᶠ x : E2 in 𝓝 0, |a ‖x‖| *(K:ℝ) < ε := by
      exact hc.eventually (by simpa [ha0] using (gt_mem_nhds hε))
    filter_upwards [hev] with x hx
    change ‖a ‖x‖ • H x‖ ≤ ε*‖x‖
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ |a ‖x‖| *((K:ℝ)*‖x‖) := mul_le_mul_of_nonneg_left (hnorm x) (abs_nonneg _)
      _ ≤ ε*‖x‖ := by nlinarith [norm_nonneg x]
  have hF (x : E2) (hx : x ≠ 0) : ContDiffAt ℝ 1 F x :=
    (ha.contDiffAt.comp x (contDiffAt_norm ℝ hx)).smul (hH x hx)
  have hbound (x : E2) : ‖fderiv ℝ F x‖ ≤
      |a ‖x‖| *(K:ℝ)+|deriv a ‖x‖| *((K:ℝ)*‖x‖) := by
    by_cases hx : x=0
    · subst x
      rw [hder0.fderiv]
      simp [ha0]
    · have hn : DifferentiableAt ℝ (fun z : E2 => ‖z‖) x :=
        (contDiffAt_norm ℝ hx).differentiableAt one_ne_zero
      have hdH := (hH x hx).differentiableAt one_ne_zero
      have hdA := (ha.differentiable one_ne_zero ‖x‖).hasDerivAt.comp_hasFDerivAt x hn.hasFDerivAt
      have hdF := hdA.smul hdH.hasFDerivAt
      change HasFDerivAt F _ x at hdF
      rw [hdF.fderiv]
      calc
        _ ≤ ‖a ‖x‖ • fderiv ℝ H x‖ +
            ‖(deriv a ‖x‖ • fderiv ℝ (fun z : E2 => ‖z‖) x).smulRight (H x)‖ := norm_add_le _ _
        _ = |a ‖x‖| *‖fderiv ℝ H x‖+
            (|deriv a ‖x‖| *‖fderiv ℝ (fun z : E2 => ‖z‖) x‖)*‖H x‖ := by
          rw [norm_smul,Real.norm_eq_abs,ContinuousLinearMap.norm_smulRight_apply,
            norm_smul,Real.norm_eq_abs]
        _ ≤ |a ‖x‖| *(K:ℝ)+|deriv a ‖x‖| *((K:ℝ)*‖x‖) := by
          have h1 := norm_fderiv_le_of_lipschitz ℝ hLip (x₀ := x)
          have h2 := norm_fderiv_norm hn
          rw [h2,mul_one]
          exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (hnorm x) (abs_nonneg _))
  apply contDiff_one_iff_fderiv.mpr
  refine ⟨fun x => ?_, continuous_iff_continuousAt.mpr ?_⟩
  · by_cases hx : x=0
    · subst x; exact hder0.differentiableAt
    · exact (hF x hx).differentiableAt one_ne_zero
  · intro x
    by_cases hx : x=0
    · subst x
      change Tendsto (fderiv ℝ F) (𝓝 0) (𝓝 (fderiv ℝ F 0))
      rw [hder0.fderiv]
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      have hc : ContinuousAt (fun x : E2 =>
          |a ‖x‖| *(K:ℝ)+|deriv a ‖x‖| *((K:ℝ)*‖x‖)) 0 := by
        have hd : Continuous (deriv a) := ha.continuous_deriv (by rfl)
        fun_prop
      have hev : ∀ᶠ x : E2 in 𝓝 0,
          |a ‖x‖| *(K:ℝ)+|deriv a ‖x‖| *((K:ℝ)*‖x‖) < ε :=
        hc.eventually (by simpa [ha0] using (gt_mem_nhds hε))
      filter_upwards [hev] with x hx
      rw [dist_zero_right]
      exact (hbound x).trans_lt hx
    · exact (hF x hx).continuousAt_fderiv one_ne_zero

private theorem homogeneous_vertex_regularization (H : E2 → E2) {K : NNReal} (hLip : LipschitzWith K H)
    (hzero : H 0 = 0) (hinj : Injective H)
    (hhom : ∀ (r : ℝ), 0 ≤ r → ∀ x, H (r • x) = r • H x)
    (hH : ∀ x : E2, x ≠ 0 → ContDiffAt ℝ 1 H x) :
    ∃ F : E2 → E2, ContDiff ℝ 1 F ∧ Injective F ∧
      F 0 = 0 ∧ fderiv ℝ F 0 = 0 ∧
      (∀ x, 1 ≤ ‖x‖ → F x = H x) ∧
      F '' Metric.ball 0 1 = H '' Metric.ball 0 1 := by
  let a := Real.smoothTransition
  let F : E2 → E2 := fun x => a ‖x‖ • H x
  have ha : ContDiff ℝ 1 a := Real.smoothTransition.contDiff
  have ha0 : a 0=0 := Real.smoothTransition.zero
  have hFn : ContDiff ℝ 1 F := radial_coefficient_contDiff_one H hLip hzero hH a ha ha0
  have hrad : StrictMonoOn (fun r : ℝ => a r*r) (Ici 0) := by
    intro r hr s hs hrs
    have hspos : 0<s := lt_of_le_of_lt hr hrs
    have has : 0<a s := Real.smoothTransition.pos_of_pos hspos
    have har : a r ≤ a s := Real.smoothTransition.monotone hrs.le
    exact (mul_le_mul_of_nonneg_right har hr).trans_lt (mul_lt_mul_of_pos_left hrs has)
  have hFinj : Injective F := by
    intro x y hxy
    have hxpos : 0 ≤ a ‖x‖ := Real.smoothTransition.nonneg _
    have hypos : 0 ≤ a ‖y‖ := Real.smoothTransition.nonneg _
    have hscale : a ‖x‖ • x = a ‖y‖ • y := hinj (by
      rw [hhom _ hxpos,hhom _ hypos]
      exact hxy)
    have hnorm : ‖x‖ = ‖y‖ := hrad.injOn (norm_nonneg x) (norm_nonneg y) (by
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hxpos,abs_of_nonneg hypos]
        using congrArg norm hscale)
    by_cases hx : x=0
    · subst x
      have hy : y=0 := norm_eq_zero.mp (by simpa using hnorm.symm)
      exact hy.symm
    · have hax : a ‖x‖ ≠ 0 := (Real.smoothTransition.pos_of_pos (norm_pos_iff.mpr hx)).ne'
      rw [← hnorm] at hscale
      exact (smul_right_injective _ hax) hscale
  have hout : ∀ x, 1 ≤ ‖x‖ → F x = H x := by
    intro x hx
    dsimp only [F,a]
    rw [Real.smoothTransition.one_of_one_le hx,one_smul]
  refine ⟨F,hFn,hFinj,by simp [F,ha0],?_,hout,?_⟩
  · have hF0 : F 0 = 0 := by simp [F,ha0]
    have hd : HasFDerivAt F (0 : E2 →L[ℝ] E2) 0 := by
      rw [hasFDerivAt_iff_isLittleO]
      simp only [hF0,ContinuousLinearMap.zero_apply,sub_zero]
      apply IsLittleO.of_bound
      intro ε hε
      have hc : ContinuousAt (fun x : E2 => |a ‖x‖| *(K:ℝ)) 0 := by fun_prop
      have hev : ∀ᶠ x : E2 in 𝓝 0, |a ‖x‖| *(K:ℝ)<ε :=
        hc.eventually (by simpa [ha0] using (gt_mem_nhds hε))
      filter_upwards [hev] with x hx
      have hn : ‖H x‖ ≤ (K:ℝ)*‖x‖ := by simpa [hzero] using hLip.dist_le_mul x 0
      change ‖a ‖x‖ • H x‖ ≤ ε*‖x‖
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hn (abs_nonneg _)).trans (by nlinarith [norm_nonneg x])
    exact hd.fderiv
  · apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      refine ⟨a ‖x‖ • x,?_,?_⟩
      · rw [Metric.mem_ball,dist_zero_right] at hx ⊢
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact (mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)).trans_lt hx
      · exact hhom _ (Real.smoothTransition.nonneg _) x
    · rintro _ ⟨y,hy,rfl⟩
      by_cases hy0 : y=0
      · subst y
        exact ⟨0,by simpa using hy,by simp [F,ha0,hzero]⟩
      have hyr : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      have hyr1 : ‖y‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
      have hc : Continuous (fun r : ℝ => a r*r) := ha.continuous.mul continuous_id
      obtain ⟨t,ht,hteq⟩ := intermediate_value_Icc (show (0:ℝ)≤1 by norm_num) hc.continuousOn
        (show ‖y‖ ∈ Icc (a 0*0) (a 1*1) by
          simpa only [mul_zero,mul_one,show a 1=1 from Real.smoothTransition.one,Set.mem_Icc] using
            And.intro hyr.le hyr1.le)
      change a t*t=‖y‖ at hteq
      have ht1 : t<1 := by
        by_contra hn
        have htone : t=1 := le_antisymm ht.2 (le_of_not_gt hn)
        rw [htone,show a 1=1 from Real.smoothTransition.one,mul_one] at hteq
        linarith
      let x : E2 := (t/‖y‖) • y
      have hxnorm : ‖x‖=t := by
        dsimp [x]
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg ht.1 hyr.le)]
        field_simp
      refine ⟨x,by simpa only [Metric.mem_ball,dist_zero_right,hxnorm] using ht1,?_⟩
      change a ‖x‖ • H x=H y
      rw [← hhom _ (Real.smoothTransition.nonneg _),hxnorm]
      congr 1
      dsimp [x]
      rw [smul_smul]
      have hcoeff : a t*(t/‖y‖)=1 := by rw [← mul_div_assoc,hteq]; exact div_self hyr.ne'
      rw [hcoeff,one_smul]

/- The paid radial regularization of the identity is globally Lipschitz: its
   difference from the identity is C¹ and compactly supported. -/
private theorem radial_flattening :
    ∃ R : E2 → E2, ContDiff ℝ 1 R ∧ Bijective R ∧
      (∃ K : NNReal, LipschitzWith K R) ∧ R 0 = 0 ∧ fderiv ℝ R 0 = 0 ∧
      (∀ x, 1 ≤ ‖x‖ → R x = x) ∧ R '' Metric.ball 0 1 = Metric.ball 0 1 := by
  obtain ⟨R,hR,hi,h0,hd,hout,him⟩ := homogeneous_vertex_regularization
    (id : E2 → E2) LipschitzWith.id rfl injective_id
    (fun _ _ _ => rfl) (fun _ _ => contDiffAt_id)
  have him' : R '' Metric.ball 0 1 = Metric.ball 0 1 := by simpa using him
  have hsur : Surjective R := by
    intro y
    by_cases hy : y ∈ Metric.ball (0:E2) 1
    · obtain ⟨x,hx,he⟩ := him'.symm ▸ hy
      exact ⟨x,he⟩
    · exact ⟨y,hout y (by simpa [Metric.mem_ball] using hy)⟩
  have hs : HasCompactSupport (fun x => R x-x) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0:E2) 1)
    intro x hx
    have hn : 1 ≤ ‖x‖ := le_of_lt (by simpa using hx)
    simp [hout x hn]
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs
    (hR.sub contDiff_id) one_ne_zero
  have hl : LipschitzWith (K+1) R := by
    simpa using hK.add (LipschitzWith.id (α:=E2))
  exact ⟨R,hR,⟨hi,hsur⟩,⟨K+1,hl⟩,h0,hd,hout,him'⟩

private theorem centered_flattening (c : E2) (r : ℝ) (hr : 0<r) :
    ∃ T : E2 → E2, ContDiff ℝ 1 T ∧ Bijective T ∧
      (∃ K : NNReal, LipschitzWith K T) ∧ T c = c ∧ fderiv ℝ T c = 0 ∧
      EqOn T id (Metric.ball c r)ᶜ ∧ T '' Metric.ball c r = Metric.ball c r := by
  obtain ⟨R,hR,hRb,hRl,hR0,hRd,hRout,hRim⟩ := radial_flattening
  let A : E2 → E2 := fun x => r⁻¹ • (x-c)
  let B : E2 → E2 := fun x => c+r • x
  have hAB : ∀ x, A (B x)=x := by
    intro x
    simp [A,B,smul_smul,hr.ne']
  have hBA : ∀ x, B (A x)=x := by
    intro x
    simp [A,B,smul_smul,hr.ne']
  have hAc : ContDiff ℝ 1 A := by
    dsimp only [A]
    fun_prop
  have hBc : ContDiff ℝ 1 B := by
    dsimp only [B]
    fun_prop
  have hAm (x : E2) : A x ∈ Metric.ball 0 1 ↔ x ∈ Metric.ball c r := by
    simp only [A,Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr),dist_eq_norm,sub_zero,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
    rw [inv_mul_lt_iff₀ hr]
    simp
  let T : E2 → E2 := B ∘ R ∘ A
  have hTc : ContDiff ℝ 1 T := hBc.comp (hR.comp hAc)
  have hT0 : T c=c := by simp [T,A,B,hR0]
  have hTi : Injective T :=
    (Function.LeftInverse.injective hAB).comp (hRb.1.comp (Function.LeftInverse.injective hBA))
  have hTs : Surjective T :=
    (Function.RightInverse.surjective hBA).comp (hRb.2.comp (Function.RightInverse.surjective hAB))
  obtain ⟨K,hK⟩ := hRl
  have hAl : LipschitzWith ‖r⁻¹‖₊ A := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [A,dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,
      NNReal.coe_mk,coe_nnnorm]
    rw [sub_sub_sub_cancel_right]
  have hBl : LipschitzWith ‖r‖₊ B := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [B,dist_eq_norm,add_sub_add_left_eq_sub,← smul_sub,norm_smul,
      coe_nnnorm]
    exact le_rfl
  refine ⟨T,hTc,⟨hTi,hTs⟩,⟨_,hBl.comp (hK.comp hAl)⟩,hT0,?_,?_,?_⟩
  · dsimp only [T]
    rw [fderiv_comp c (hBc.differentiable one_ne_zero _) ((hR.comp hAc).differentiable one_ne_zero c)]
    rw [fderiv_comp c (hR.differentiable one_ne_zero _) (hAc.differentiable one_ne_zero c)]
    simp [A,hRd]
  · intro x hx
    change B (R (A x))=x
    rw [hRout (A x) (by simpa [Metric.mem_ball] using (mt (hAm x).mp hx))]
    exact hBA x
  · apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      have hm : R (A x) ∈ Metric.ball (0:E2) 1 := hRim ▸ mem_image_of_mem R ((hAm x).mpr hx)
      apply (hAm _).mp
      simpa only [T,comp_apply,hAB] using hm
    · intro y hy
      obtain ⟨a,ha,hea⟩ := hRim.symm ▸ ((hAm y).mpr hy)
      refine ⟨B a,(hAm _).mp (by simpa only [hAB] using ha),?_⟩
      change B (R (A (B a)))=y
      rw [hAB,hea,hBA]

/- The derivative estimate is local near c.  Other singular vertices of H are
   permitted outside W and therefore do not become extra hypotheses. -/
private theorem flat_precomposition_at
    (H T : E2 → E2) {K : NNReal} (hLip : LipschitzWith K H)
    (hT : ContDiff ℝ 1 T) (c : E2) (hTc : T c=c) (hTd : fderiv ℝ T c=0)
    (W : Set E2) (hW : W ∈ 𝓝 c)
    (hH : ∀ x ∈ W, x ≠ c → ContDiffAt ℝ 1 H (T x)) :
    ContDiffAt ℝ 1 (H ∘ T) c := by
  let F : E2 → E2 := H ∘ T
  have hF0 : F c=H c := by simp [F,hTc]
  have hderT : HasFDerivAt T (0:E2 →L[ℝ] E2) c := by
    simpa only [hTd] using (hT.differentiable one_ne_zero c).hasFDerivAt
  have hTO : (fun x => T x-c) =o[𝓝 c] (fun x => x-c) := by
    simpa only [hTc,zero_apply,sub_zero] using hderT.isLittleO
  have hderF : HasFDerivAt F (0:E2 →L[ℝ] E2) c := by
    rw [hasFDerivAt_iff_isLittleO]
    simp only [hF0,zero_apply,sub_zero]
    apply (IsBigO.of_bound (K:ℝ) ?_).trans_isLittleO hTO
    exact Filter.Eventually.of_forall fun x => by
      simpa only [F,comp_apply,dist_eq_norm] using hLip.dist_le_mul (T x) c
  have hF (x : E2) (hx : x ∈ W) (hxc : x ≠ c) : ContDiffAt ℝ 1 F x :=
    (hH x hx hxc).comp x hT.contDiffAt
  have hbound (x : E2) (hx : x ∈ W) : ‖fderiv ℝ F x‖ ≤ (K:ℝ)*‖fderiv ℝ T x‖ := by
    by_cases hxc : x=c
    · subst x; simp [hderF.fderiv,hTd]
    · change ‖fderiv ℝ (H ∘ T) x‖ ≤ _
      rw [fderiv_comp x ((hH x hx hxc).differentiableAt one_ne_zero)
        (hT.differentiable one_ne_zero x)]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg _))
  have hdcont : ContinuousAt (fderiv ℝ F) c := by
    change Tendsto (fderiv ℝ F) (𝓝 c) (𝓝 (fderiv ℝ F c))
    rw [hderF.fderiv]
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hc : ContinuousAt (fun x : E2 => (K:ℝ)*‖fderiv ℝ T x‖) c :=
      continuousAt_const.mul (hT.continuous_fderiv one_ne_zero).continuousAt.norm
    have hev : ∀ᶠ x : E2 in 𝓝 c, (K:ℝ)*‖fderiv ℝ T x‖<ε :=
      hc.eventually (by simpa only [hTd,norm_zero,mul_zero] using (gt_mem_nhds hε))
    filter_upwards [hev,hW] with x hx hxW
    rw [dist_zero_right]
    exact (hbound x hxW).trans_lt hx
  apply contDiffAt_one_iff.mpr
  refine ⟨fderiv ℝ F,W,hW,?_,?_⟩
  · intro x hx
    by_cases hxc : x=c
    · subst x; exact hdcont.continuousWithinAt
    · exact (hF x hx hxc).continuousAt_fderiv one_ne_zero |>.continuousWithinAt
  · intro x hx
    by_cases hxc : x=c
    · subst x; simpa only [hderF.fderiv] using hderF
    · exact ((hF x hx hxc).differentiableAt one_ne_zero).hasFDerivAt

private theorem install_one_vertex (H : E2 → E2) {K : NNReal}
    (hLip : LipschitzWith K H) (S : Finset E2) (c : E2) (hc : c ∉ S)
    (U : Set E2) (hU : IsOpen U) (hcU : c ∈ U)
    (hH : ∀ x, x ∉ insert c (S:Set E2) → ContDiffAt ℝ 1 H x) :
    ∃ T : E2 → E2, ContDiff ℝ 1 T ∧ Bijective T ∧
      (∃ L : NNReal, LipschitzWith L T) ∧ EqOn T id Uᶜ ∧
      (∀ D : Set E2, U ⊆ D → T '' D=D) ∧
      (∀ x, x ∉ (S:Set E2) → ContDiffAt ℝ 1 (H ∘ T) x) := by
  classical
  have hW : IsOpen (U \ (S:Set E2)) := hU.sdiff S.finite_toSet.isClosed
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hW c ⟨hcU,hc⟩
  obtain ⟨T,hT,hTb,hTl,hTc,hTd,hout,him⟩ := centered_flattening c r hr
  have hnon (x : E2) (hx : x ≠ c) : T x ≠ c := fun he => hx (hTb.1 (he.trans hTc.symm))
  have hTs (x : E2) (hx : x ∉ (S:Set E2)) : T x ∉ (S:Set E2) := by
    by_cases hxb : x ∈ Metric.ball c r
    · exact (hball (him ▸ mem_image_of_mem T hxb)).2
    · simpa only [hout hxb,id_eq] using hx
  have hUout : EqOn T id Uᶜ := by
    intro x hx
    exact hout (fun hxb => hx (hball hxb).1)
  refine ⟨T,hT,hTb,hTl,hUout,?_,?_⟩
  · intro D hUD
    have hTD (x : E2) : x ∈ D ↔ T x ∈ D := by
      by_cases hxb : x ∈ Metric.ball c r
      · exact iff_of_true (hUD (hball hxb).1)
          (hUD (hball (him ▸ mem_image_of_mem T hxb)).1)
      · rw [hout hxb]; rfl
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (hTD x).mp hx
    · intro y hy
      obtain ⟨x,rfl⟩ := hTb.2 y
      exact ⟨x,(hTD x).mpr hy,rfl⟩
  · intro x hx
    by_cases hxc : x=c
    · subst x
      apply flat_precomposition_at H T hLip hT c hTc hTd (Metric.ball c r)
        (Metric.ball_mem_nhds c hr)
      intro y hy hyc
      apply hH
      simp only [mem_insert_iff,not_or]
      exact ⟨hnon y hyc,hTs y (hball hy).2⟩
    · apply (hH (T x) ?_).comp x hT.contDiffAt
      simp only [mem_insert_iff,not_or]
      exact ⟨hnon x hxc,hTs x hx⟩

/- This is a complete finite vertex installation, relative to any prescribed
   open neighborhood of the finite vertex set.  Every containing domain is
   preserved exactly, so injectivity on a compact disk can be transported. -/
private theorem paid_global_vertices (S : Finset E2) (H : E2 → E2) {K : NNReal}
    (hLip : LipschitzWith K H) (U : Set E2) (hU : IsOpen U)
    (hSU : (S:Set E2) ⊆ U)
    (hH : ∀ x, x ∉ (S:Set E2) → ContDiffAt ℝ 1 H x) :
    ∃ T : E2 → E2, ContDiff ℝ 1 T ∧ Bijective T ∧
      (∃ L : NNReal, LipschitzWith L T) ∧ EqOn T id Uᶜ ∧
      (∀ D : Set E2, U ⊆ D → T '' D=D) ∧ ContDiff ℝ 1 (H ∘ T) ∧
      (∃ L : NNReal, LipschitzWith L (H ∘ T)) ∧
      (∀ D : Set E2, U ⊆ D → H ∘ T '' D=H '' D ∧
        (InjOn H D → InjOn (H ∘ T) D)) := by
  classical
  induction S using Finset.induction_on generalizing H K with
  | empty =>
    refine ⟨id,contDiff_id,bijective_id,⟨1,LipschitzWith.id⟩,fun _ _ => rfl,
      fun _ _ => image_id _,?_,⟨K,by simpa using hLip⟩,?_⟩
    · exact contDiff_iff_contDiffAt.mpr fun x => hH x (by simp)
    · intro D hUD
      exact ⟨by simp,fun h => by simpa using h⟩
  | @insert c S hc ih =>
    have hcU : c ∈ U := hSU (by simp)
    have hSU' : (S:Set E2) ⊆ U := fun x hx => hSU (by simp [hx])
    obtain ⟨T,hT,hTb,⟨L,hL⟩,hout,him,hcd⟩ := install_one_vertex H hLip S c hc U hU hcU
      (by simpa only [Finset.coe_insert] using hH)
    obtain ⟨V,hV,hVb,⟨M,hM⟩,hVout,hVim,hVcd,hVL,hVD⟩ :=
      ih (H ∘ T) (hLip.comp hL) hSU' hcd
    refine ⟨T ∘ V,hT.comp hV,hTb.comp hVb,⟨L*M,hL.comp hM⟩,?_,?_,hVcd,hVL,?_⟩
    · intro x hx
      change T (V x)=x
      rw [hVout hx]
      exact hout hx
    · intro D hUD
      rw [image_comp T V D,hVim D hUD,him D hUD]
    · intro D hUD
      have heq : (T ∘ V) '' D=D := by rw [image_comp T V D,hVim D hUD,him D hUD]
      refine ⟨by rw [image_comp H (T ∘ V) D,heq],?_⟩
      intro hinj x hx y hy hxy
      apply (hTb.comp hVb).1
      apply hinj
      · exact heq ▸ mem_image_of_mem (T ∘ V) hx
      · exact heq ▸ mem_image_of_mem (T ∘ V) hy
      · exact hxy
end VM03CapPolarV464RelativeVertex

namespace VM03CapPolarV464RelativeVertex
private theorem install_one_vertex_relative (H : E2 → E2) {K : NNReal}
    (hLip : LipschitzWith K H) (S : Finset E2) (c : E2) (hc : c ∉ S)
    (U W : Set E2) (hU : IsOpen U) (hUW : U ⊆ W) (hcU : c∈U)
    (hH : ∀ x∈W,x∉insert c (S:Set E2) → ContDiffAt ℝ 1 H x) :
    ∃ T : E2 → E2,ContDiff ℝ 1 T ∧ Bijective T ∧
      (∃ L : NNReal,LipschitzWith L T) ∧ EqOn T id Uᶜ ∧
      (∀ D : Set E2,U ⊆ D → T '' D=D) ∧
      (∀ x∈W,x∉(S:Set E2) → ContDiffAt ℝ 1 (H ∘ T) x) := by
  classical
  have hO : IsOpen (U \ (S:Set E2)) := hU.sdiff S.finite_toSet.isClosed
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hO c ⟨hcU,hc⟩
  obtain ⟨T,hT,hTb,hTl,hTc,hTd,hout,him⟩ := centered_flattening c r hr
  have hnon (x : E2) (hx : x≠c) : T x≠c := fun he => hx (hTb.1 (he.trans hTc.symm))
  have hTs (x : E2) (hx : x∉(S:Set E2)) : T x∉(S:Set E2) := by
    by_cases hxb : x∈Metric.ball c r
    · exact (hball (him ▸ mem_image_of_mem T hxb)).2
    · simpa only [hout hxb,id_eq] using hx
  have hUout : EqOn T id Uᶜ := by
    intro x hx
    exact hout (fun hxb => hx (hball hxb).1)
  have hpres (D : Set E2) (hUD : U ⊆ D) : T '' D=D := by
    have hTD (x : E2) : x∈D ↔ T x∈D := by
      by_cases hxb : x∈Metric.ball c r
      · exact iff_of_true (hUD (hball hxb).1)
          (hUD (hball (him ▸ mem_image_of_mem T hxb)).1)
      · rw [hout hxb]; rfl
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (hTD x).mp hx
    · intro y hy
      obtain ⟨x,rfl⟩ := hTb.2 y
      exact ⟨x,(hTD x).mpr hy,rfl⟩
  have hTW : MapsTo T W W := fun x hx => hpres W hUW ▸ mem_image_of_mem T hx
  refine ⟨T,hT,hTb,hTl,hUout,hpres,?_⟩
  intro x hxW hx
  by_cases hxc : x=c
  · subst x
    apply flat_precomposition_at H T hLip hT c hTc hTd (Metric.ball c r)
      (Metric.ball_mem_nhds c hr)
    intro y hy hyc
    apply hH (T y) (hTW (hUW (hball hy).1))
    simp only [mem_insert_iff,not_or]
    exact ⟨hnon y hyc,hTs y (hball hy).2⟩
  · apply (hH (T x) (hTW hxW) ?_).comp x hT.contDiffAt
    simp only [mem_insert_iff,not_or]
    exact ⟨hnon x hxc,hTs x hx⟩

-- Relative form required by a PL disk: no regularity is assumed outside W.
private theorem finite_vertices_relative (S : Finset E2) (H : E2 → E2) {K : NNReal}
    (hLip : LipschitzWith K H) (U W : Set E2) (hU : IsOpen U) (hUW : U ⊆ W)
    (hSU : (S:Set E2) ⊆ U)
    (hH : ∀ x∈W,x∉(S:Set E2) → ContDiffAt ℝ 1 H x) :
    ∃ T : E2 → E2,ContDiff ℝ 1 T ∧ Bijective T ∧
      (∃ L : NNReal,LipschitzWith L T) ∧ EqOn T id Uᶜ ∧
      (∀ D : Set E2,U ⊆ D → T '' D=D) ∧
      (∀ x∈W,ContDiffAt ℝ 1 (H ∘ T) x) ∧
      (∃ L : NNReal,LipschitzWith L (H ∘ T)) ∧
      (∀ D : Set E2,U ⊆ D → (H ∘ T) '' D=H '' D ∧
        (InjOn H D → InjOn (H ∘ T) D)) := by
  classical
  induction S using Finset.induction_on generalizing H K with
  | empty =>
    refine ⟨id,contDiff_id,bijective_id,⟨1,LipschitzWith.id⟩,fun _ _ => rfl,
      fun _ _ => image_id _,?_,⟨K,by simpa using hLip⟩,?_⟩
    · intro x hx
      exact hH x hx (by simp)
    · intro D hUD
      exact ⟨by simp,fun h => by simpa using h⟩
  | @insert c S hc ih =>
    have hcU : c∈U := hSU (by simp)
    have hSU' : (S:Set E2) ⊆ U := fun x hx => hSU (by simp [hx])
    obtain ⟨T,hT,hTb,⟨L,hL⟩,hout,him,hcd⟩ :=
      install_one_vertex_relative H hLip S c hc U W hU hUW hcU
        (by simpa only [Finset.coe_insert] using hH)
    obtain ⟨V,hV,hVb,⟨M,hM⟩,hVout,hVim,hVcd,hVL,hVD⟩ :=
      ih (H ∘ T) (hLip.comp hL) hSU' hcd
    refine ⟨T ∘ V,hT.comp hV,hTb.comp hVb,⟨L*M,hL.comp hM⟩,?_,?_,hVcd,hVL,?_⟩
    · intro x hx
      change T (V x)=x
      rw [hVout hx]
      exact hout hx
    · intro D hUD
      rw [image_comp T V D,hVim D hUD,him D hUD]
    · intro D hUD
      have heq : (T ∘ V) '' D=D := by rw [image_comp T V D,hVim D hUD,him D hUD]
      refine ⟨by rw [image_comp H (T ∘ V) D,heq],?_⟩
      intro hinj x hx y hy hxy
      apply (hTb.comp hVb).1
      exact hinj (heq ▸ mem_image_of_mem (T ∘ V) hx)
        (heq ▸ mem_image_of_mem (T ∘ V) hy) hxy
end VM03CapPolarV464RelativeVertex
namespace VM03CapPolarV464RelativeVertex
private theorem relative_vertices_preserve_boundary_germs
    (S : Finset E2) (H : E2 → E2) {K : NNReal} (hLip : LipschitzWith K H)
    (W : Set E2) (hW : IsOpen W) (hSW : (S:Set E2) ⊆ W)
    (hH : ∀ x∈W,x∉(S:Set E2) → ContDiffAt ℝ 1 H x) :
    ∃ J : E2 → E2,(∃ L : NNReal,LipschitzWith L J) ∧
      (∀ x∈W,ContDiffAt ℝ 1 J x) ∧
      (∀ x∉W,J =ᶠ[𝓝 x] H) ∧
      (∀ D : Set E2,W ⊆ D → J '' D=H '' D ∧ (InjOn H D → InjOn J D)) := by
  obtain ⟨U,hU,hSU,hUW⟩ := S.finite_toSet.isCompact.exists_isOpen_closure_subset
    (hW.mem_nhdsSet.mpr hSW)
  have hUW' : U ⊆ W := subset_closure.trans hUW
  obtain ⟨T,hT,hTb,hTl,hout,him,hcd,hL,hD⟩ :=
    finite_vertices_relative S H hLip U W hU hUW' hSU hH
  refine ⟨H ∘ T,hL,hcd,?_,?_⟩
  · intro x hx
    have hxU : x∈(closure U)ᶜ := fun hh => hx (hUW hh)
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxU] with y hy
    change H (T y)=H y
    rw [hout (fun hh => hy (subset_closure hh))]
    rfl
  · intro D hWD
    exact hD D (hUW'.trans hWD)
end VM03CapPolarV464RelativeVertex

namespace PolarSeam462
open Metric
open VM03CapPolarV464RelativeVertex

theorem bijective_relative_image (F : E2 → E2) (hF : Bijective F) (b : ℝ)
    (hout : ∀ x,b ≤ ‖x‖ → F x=x) (hb : b < 1) : F '' ball 0 1=ball 0 1 := by
  apply Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    by_contra hy
    have hyn : 1 ≤ ‖F x‖ := by simpa [Metric.mem_ball] using hy
    have he : F (F x)=F x := hout (F x) (hb.le.trans hyn)
    have hfx : F x=x := hF.1 he
    apply hy
    simpa only [hfx] using hx
  · intro y hy
    obtain ⟨x,hxy⟩ := hF.2 y
    refine ⟨x,?_,hxy⟩
    by_contra hx
    have hxn : 1 ≤ ‖x‖ := by simpa [Metric.mem_ball] using hx
    have he : F x=x := hout x (hb.le.trans hxn)
    have hxy' : x = y := he.symm.trans hxy
    exact hx (hxy'.symm ▸ hy)

theorem finish_polar_finite_vertices (H T0 : E2 → E2) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hH : ∃ K:NNReal,LipschitzWith K H) (hT0b : Bijective T0)
    (hT0L : ∃ K:NNReal,LipschitzWith K T0)
    (hT0out : ∀ x,b ≤ ‖x‖ → T0 x=x)
    (hT0c : ∀ (x : E2), x ≠ 0 → ContDiffAt ℝ 1 T0 x)
    (S : Finset E2) (hSb : (S:Set E2)⊆ball 0 b)
    (hcomp : ∀ (x : E2), x ∉(S:Set E2) → ContDiffAt ℝ 1 (H ∘ T0) x) :
    ∃ T : E2 → E2,Bijective T ∧ ContDiff ℝ 1 T ∧ (∃ K:NNReal,LipschitzWith K T) ∧
      EqOn T id {x|b ≤ ‖x‖} ∧ T '' ball 0 1=ball 0 1 ∧
      ContDiff ℝ 1 (H ∘ T) ∧ (∃ K:NNReal,LipschitzWith K (H ∘ T)) := by
  classical
  obtain ⟨K,hK⟩ := hT0L
  let U : Set E2 := ball 0 (b/2)
  have hU : IsOpen U := isOpen_ball
  have h0U' : (({0}:Finset E2):Set E2)⊆U := by
    intro x hx
    have he : x=0 := by simpa using hx
    subst x
    simp only [U,Metric.mem_ball,dist_self]
    exact half_pos hb0
  obtain ⟨Q,hQc,hQb,⟨L,hL⟩,hQout,hQimages,hT1c,hT1L,hQtransport⟩ :=
    paid_global_vertices ({0}:Finset E2) T0 hK U hU h0U'
      (by intro x hx;exact hT0c x (by simpa using hx))
  let T1:=T0 ∘ Q
  have hT1b : Bijective T1 := hT0b.comp hQb
  have hT1out (x:E2) (hx:b ≤ ‖x‖) : T1 x=x := by
    have hxU : x∉U := by
      simp only [U,Metric.mem_ball,dist_zero_right,not_lt]
      linarith
    simp only [T1,comp_apply,hQout hxU,id_eq,hT0out x hx]
  have hpre : (Q ⁻¹' (S:Set E2)).Finite := Set.Finite.preimage hQb.1.injOn S.finite_toSet
  let S1 : Finset E2 := hpre.toFinset
  have hS1mem (x:E2) : x∈(S1:Set E2) ↔ Q x∈(S:Set E2) := by
    simp only [S1,Finset.mem_coe,Set.Finite.mem_toFinset,mem_preimage]
  have hS1b : (S1:Set E2)⊆ball 0 b := by
    intro x hx
    have hQx := hSb ((hS1mem x).mp hx)
    by_contra hxb
    have hxn : b ≤ ‖x‖ := by simpa [Metric.mem_ball] using hxb
    have hxU : x∉U := by
      simp only [U,Metric.mem_ball,dist_zero_right,not_lt]
      linarith
    rw [hQout hxU] at hQx
    exact hxb hQx
  have hHC (x:E2) (hx:x∉(S1:Set E2)) : ContDiffAt ℝ 1 (H ∘ T1) x := by
    have hc := (hcomp (Q x) (fun hxS=>hx ((hS1mem x).mpr hxS))).comp x hQc.contDiffAt
    exact hc
  obtain ⟨J,hJ⟩ := hH
  have hHT1 : LipschitzWith (J*K*L) (H ∘ T1) := by
    simpa only [mul_assoc] using hJ.comp (hK.comp hL)
  obtain ⟨V,hVc,hVb,⟨M,hM⟩,hVout,hVimages,hFinalc,hFinalL,hVtransport⟩ :=
    paid_global_vertices S1 (H ∘ T1) hHT1 (ball 0 b) isOpen_ball hS1b hHC
  let T:=T1 ∘ V
  have hTout (x:E2) (hx:b ≤ ‖x‖) : T x=x := by
    have hxB : x∉ball (0:E2) b := by simpa [Metric.mem_ball] using hx
    simp only [T,comp_apply,hVout hxB,id_eq,hT1out x hx]
  have hTb : Bijective T := hT1b.comp hVb
  refine ⟨T,hTb,hT1c.comp hVc,⟨K*L*M,?_⟩,fun x hx=>hTout x hx,
    bijective_relative_image T hTb b hTout hb1,hFinalc,hFinalL⟩
  simpa only [mul_assoc] using (hK.comp hL).comp hM

end PolarSeam462

-- Paid source: RectangleSeams

noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology
namespace PolarSeam462

def rectangle (a b c d : ℝ) : Set (ℝ × ℝ) := Icc a b ×ˢ Icc c d
def corners (a b c d : ℝ) : Set (ℝ × ℝ) := ({a,b}:Set ℝ) ×ˢ ({c,d}:Set ℝ)
def cell (a b c d : ℝ) : Set (ℝ × ℝ) := rectangle a b c d \ corners a b c d

theorem corners_finite (a b c d : ℝ) : (corners a b c d).Finite := by
  exact (Set.toFinite _).prod (Set.toFinite _)

theorem cell_uniqueDiff (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    UniqueDiffOn ℝ (cell a b c d) := by
  simpa only [cell,rectangle,sdiff_eq] using
    ((uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc hcd)).inter
      (corners_finite a b c d).isClosed.isOpen_compl

theorem horizontal_cell_eventually (a b c d : ℝ) (w : ℝ × ℝ)
    (hw : w ∈ rectangle a b c d) (hab : a < w.1 ∧ w.1 < b) :
    ∀ᶠ q in 𝓝 w.1, (q,w.2) ∈ cell a b c d := by
  filter_upwards [Ioo_mem_nhds hab.1 hab.2] with q hq
  refine ⟨⟨⟨hq.1.le,hq.2.le⟩,hw.2⟩,?_⟩
  intro hc
  have hqc : q=a ∨ q=b := by simpa [corners] using hc.1
  rcases hqc with hqc | hqc <;> subst q <;> linarith [hq.1,hq.2]

theorem vertical_cell_eventually (a b c d : ℝ) (w : ℝ × ℝ)
    (hw : w ∈ rectangle a b c d) (hcd : c < w.2 ∧ w.2 < d) :
    ∀ᶠ q in 𝓝 w.2, (w.1,q) ∈ cell a b c d := by
  filter_upwards [Ioo_mem_nhds hcd.1 hcd.2] with q hq
  refine ⟨⟨hw.1,⟨hq.1.le,hq.2.le⟩⟩,?_⟩
  intro hc
  have hqc : q=c ∨ q=d := by simpa [corners] using hc.2
  rcases hqc with hqc | hqc <;> subst q <;> linarith [hq.1,hq.2]

theorem horizontal_derivative_match {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (ℝ × ℝ) → F) (w : ℝ × ℝ) (s t : Set (ℝ × ℝ))
    (D E : (ℝ × ℝ) →L[ℝ] F) (hD : HasFDerivWithinAt f D s w)
    (hE : HasFDerivWithinAt f E t w)
    (hs : ∀ᶠ q in 𝓝 w.1, (q,w.2) ∈ s)
    (ht : ∀ᶠ q in 𝓝 w.1, (q,w.2) ∈ t) : D (1,0)=E (1,0) := by
  have h1 := hD.comp_hasFDerivAt w.1 (hasFDerivAt_prodMk_left w.1 w.2) hs
  have h2 := hE.comp_hasFDerivAt w.1 (hasFDerivAt_prodMk_left w.1 w.2) ht
  have he := h1.unique h2
  have hv := congrArg (fun L : ℝ →L[ℝ] F => L 1) he
  simpa using hv

theorem vertical_derivative_match {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (ℝ × ℝ) → F) (w : ℝ × ℝ) (s t : Set (ℝ × ℝ))
    (D E : (ℝ × ℝ) →L[ℝ] F) (hD : HasFDerivWithinAt f D s w)
    (hE : HasFDerivWithinAt f E t w)
    (hs : ∀ᶠ q in 𝓝 w.2, (w.1,q) ∈ s)
    (ht : ∀ᶠ q in 𝓝 w.2, (w.1,q) ∈ t) : D (0,1)=E (0,1) := by
  have h1 := hD.comp_hasFDerivAt w.2 (hasFDerivAt_prodMk_right w.1 w.2) hs
  have h2 := hE.comp_hasFDerivAt w.2 (hasFDerivAt_prodMk_right w.1 w.2) ht
  have he := h1.unique h2
  have hv := congrArg (fun L : ℝ →L[ℝ] F => L 1) he
  simpa using hv

def coordinateMap (σ A : ℝ → ℝ) (z : ℝ × ℝ) := (σ z.1,A z.2)

theorem coordinateMap_contDiff (σ A : ℝ → ℝ)
    (hσ : ContDiff ℝ 1 σ) (hA : ContDiff ℝ 1 A) : ContDiff ℝ 1 (coordinateMap σ A) :=
  (hσ.comp contDiff_fst).prodMk (hA.comp contDiff_snd)

theorem coordinateMap_fderiv (σ A : ℝ → ℝ)
    (hσ : Differentiable ℝ σ) (hA : Differentiable ℝ A) (z : ℝ × ℝ) (v : ℝ × ℝ) :
    fderiv ℝ (coordinateMap σ A) z v = (deriv σ z.1*v.1,deriv A z.2*v.2) := by
  have hs := (hσ z.1).hasDerivAt.hasFDerivAt.comp z hasFDerivAt_fst
  have ha := (hA z.2).hasDerivAt.hasFDerivAt.comp z hasFDerivAt_snd
  have hp : HasFDerivAt (coordinateMap σ A) _ z := hs.prodMk ha
  rw [hp.fderiv]
  simp [ContinuousLinearMap.smulRight_apply,mul_comm]


theorem coordinateMap_maps_cell (σ A : ℝ → ℝ) (hσ : StrictMono σ) (hA : StrictMono A)
    (a b c d : ℝ) (hsa : σ a=a) (hsb : σ b=b) (hac : A c=c) (had : A d=d)
    (z : ℝ × ℝ) (hz : z ∈ cell a b c d) : coordinateMap σ A z ∈ cell a b c d := by
  refine ⟨⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,?_⟩
  · simpa only [coordinateMap,hsa] using hσ.monotone hz.1.1.1
  · simpa only [coordinateMap,hsb] using hσ.monotone hz.1.1.2
  · simpa only [coordinateMap,hac] using hA.monotone hz.1.2.1
  · simpa only [coordinateMap,had] using hA.monotone hz.1.2.2
  · intro hc
    apply hz.2
    have h1 : z.1=a ∨ z.1=b := by
      have hh : σ z.1=a ∨ σ z.1=b := by simpa [corners,coordinateMap] using hc.1
      rcases hh with hh | hh
      · exact Or.inl (hσ.injective (hh.trans hsa.symm))
      · exact Or.inr (hσ.injective (hh.trans hsb.symm))
    have h2 : z.2=c ∨ z.2=d := by
      have hh : A z.2=c ∨ A z.2=d := by simpa [corners,coordinateMap] using hc.2
      rcases hh with hh | hh
      · exact Or.inl (hA.injective (hh.trans hac.symm))
      · exact Or.inr (hA.injective (hh.trans had.symm))
    simpa [corners] using And.intro h1 h2

theorem flat_coordinate_interior (σ : ℝ → ℝ) (hm : StrictMono σ)
    (a b x : ℝ) (ha : σ a=a) (hb : σ b=b)
    (hda : HasDerivAt σ 0 a) (hdb : HasDerivAt σ 0 b)
    (hx : x ∈ Icc a b) (hd : deriv σ x ≠ 0) : σ x ∈ Ioo a b := by
  have hxa : x ≠ a := by intro he;subst x;exact hd hda.deriv
  have hxb : x ≠ b := by intro he;subst x;exact hd hdb.deriv
  refine ⟨?_,?_⟩
  · simpa only [ha] using hm (lt_of_le_of_ne hx.1 hxa.symm)
  · simpa only [hb] using hm (lt_of_le_of_ne hx.2 hxb)

theorem flattened_derivative_match {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (ℝ × ℝ) → F) (σ A : ℝ → ℝ)
    (hσ : ContDiff ℝ 1 σ) (hA : ContDiff ℝ 1 A) (hσm : StrictMono σ) (hAm : StrictMono A)
    (a b c d e g u v : ℝ)
    (hsfix : σ a=a ∧ σ b=b ∧ σ e=e ∧ σ g=g)
    (hafix : A c=c ∧ A d=d ∧ A u=u ∧ A v=v)
    (hsflat : HasDerivAt σ 0 a ∧ HasDerivAt σ 0 b ∧ HasDerivAt σ 0 e ∧ HasDerivAt σ 0 g)
    (haflat : HasDerivAt A 0 c ∧ HasDerivAt A 0 d ∧ HasDerivAt A 0 u ∧ HasDerivAt A 0 v)
    (z : ℝ × ℝ) (hz1 : z ∈ cell a b c d) (hz2 : z ∈ cell e g u v)
    (D E : (ℝ × ℝ) →L[ℝ] F)
    (hD : HasFDerivWithinAt f D (cell a b c d) (coordinateMap σ A z))
    (hE : HasFDerivWithinAt f E (cell e g u v) (coordinateMap σ A z)) :
    D.comp (fderiv ℝ (coordinateMap σ A) z)=E.comp (fderiv ℝ (coordinateMap σ A) z) := by
  have hz1' := coordinateMap_maps_cell σ A hσm hAm a b c d hsfix.1 hsfix.2.1 hafix.1 hafix.2.1 z hz1
  have hz2' := coordinateMap_maps_cell σ A hσm hAm e g u v hsfix.2.2.1 hsfix.2.2.2 hafix.2.2.1 hafix.2.2.2 z hz2
  have hr : D (deriv σ z.1,0)=E (deriv σ z.1,0) := by
    by_cases hd : deriv σ z.1=0
    · simp only [hd]
      change D 0=E 0
      simp
    · have hi1 := flat_coordinate_interior σ hσm a b z.1 hsfix.1 hsfix.2.1 hsflat.1 hsflat.2.1 hz1.1.1 hd
      have hi2 := flat_coordinate_interior σ hσm e g z.1 hsfix.2.2.1 hsfix.2.2.2 hsflat.2.2.1 hsflat.2.2.2 hz2.1.1 hd
      have he := horizontal_derivative_match f (coordinateMap σ A z) _ _ D E hD hE
        (horizontal_cell_eventually a b c d _ hz1'.1 hi1)
        (horizontal_cell_eventually e g u v _ hz2'.1 hi2)
      have hv := congrArg (fun y : F => deriv σ z.1 • y) he
      simpa only [← map_smul,Prod.smul_mk,smul_eq_mul,mul_one,mul_zero] using hv
  have ht : D (0,deriv A z.2)=E (0,deriv A z.2) := by
    by_cases hd : deriv A z.2=0
    · simp only [hd]
      change D 0=E 0
      simp
    · have hi1 := flat_coordinate_interior A hAm c d z.2 hafix.1 hafix.2.1 haflat.1 haflat.2.1 hz1.1.2 hd
      have hi2 := flat_coordinate_interior A hAm u v z.2 hafix.2.2.1 hafix.2.2.2 haflat.2.2.1 haflat.2.2.2 hz2.1.2 hd
      have he := vertical_derivative_match f (coordinateMap σ A z) _ _ D E hD hE
        (vertical_cell_eventually a b c d _ hz1'.1 hi1)
        (vertical_cell_eventually e g u v _ hz2'.1 hi2)
      have hv := congrArg (fun y : F => deriv A z.2 • y) he
      simpa only [← map_smul,Prod.smul_mk,smul_eq_mul,mul_one,mul_zero] using hv
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.comp_apply,
    coordinateMap_fderiv σ A (hσ.differentiable one_ne_zero) (hA.differentiable one_ne_zero)]
  have hw : (deriv σ z.1*w.1,deriv A z.2*w.2)=
      w.1 • (deriv σ z.1,0)+w.2 • (0,deriv A z.2) := by ext <;> simp [mul_comm]
  rw [hw,map_add,map_add,map_smul,map_smul,map_smul,map_smul,hr,ht]

theorem finite_rectangle_flatten {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a b c d : ι → ℝ) (hab : ∀ i,a i < b i) (hcd : ∀ i,c i < d i)
    (f : (ℝ × ℝ) → F) (hf : ∀ i,ContDiffOn ℝ 1 f (cell (a i) (b i) (c i) (d i)))
    (σ A : ℝ → ℝ) (hσ : ContDiff ℝ 1 σ) (hA : ContDiff ℝ 1 A)
    (hσm : StrictMono σ) (hAm : StrictMono A)
    (hsfix : ∀ i,σ (a i)=a i ∧ σ (b i)=b i)
    (hafix : ∀ i,A (c i)=c i ∧ A (d i)=d i)
    (hsflat : ∀ i,HasDerivAt σ 0 (a i) ∧ HasDerivAt σ 0 (b i))
    (haflat : ∀ i,HasDerivAt A 0 (c i) ∧ HasDerivAt A 0 (d i))
    (z : ℝ × ℝ) (hzcov : (⋃ i,rectangle (a i) (b i) (c i) (d i)) ∈ 𝓝 z)
    (hzbad : ∀ i,z ∉ corners (a i) (b i) (c i) (d i)) :
    ContDiffAt ℝ 1 (f ∘ coordinateMap σ A) z := by
  classical
  let Bad : Set (ℝ × ℝ) := ⋃ i,corners (a i) (b i) (c i) (d i)
  have hBad : IsClosed Bad := isClosed_iUnion_of_finite (fun i => (corners_finite (a i) (b i) (c i) (d i)).isClosed)
  have hzB : z ∈ Badᶜ := by simpa only [Bad,mem_compl_iff,mem_iUnion,not_exists] using hzbad
  obtain ⟨ε,hε,hεsub⟩ := Metric.isOpen_iff.mp hBad.isOpen_compl z hzB
  let V := closedBall z (ε/2)
  have hV : IsClosed V := isClosed_closedBall
  have hzV : V ∈ 𝓝 z := closedBall_mem_nhds z (half_pos hε)
  have hVB : V ⊆ Badᶜ := (closedBall_subset_ball (by linarith)).trans hεsub
  let s (i : ι) := rectangle (a i) (b i) (c i) (d i) ∩ V
  have hs (i : ι) : IsClosed (s i) := (isClosed_Icc.prod isClosed_Icc).inter hV
  let P := coordinateMap σ A
  have hP : ContDiff ℝ 1 P := coordinateMap_contDiff σ A hσ hA
  have hscell (i : ι) : s i ⊆ cell (a i) (b i) (c i) (d i) := by
    intro y hy
    exact ⟨hy.1,fun hc => hVB hy.2 (mem_iUnion.mpr ⟨i,hc⟩)⟩
  have hm (i : ι) : MapsTo P (s i) (cell (a i) (b i) (c i) (d i)) := by
    intro y hy
    exact coordinateMap_maps_cell σ A hσm hAm _ _ _ _ (hsfix i).1 (hsfix i).2
      (hafix i).1 (hafix i).2 y (hscell i hy)
  let D (i : ι) (y : ℝ × ℝ) :=
    (fderivWithin ℝ f (cell (a i) (b i) (c i) (d i)) (P y)).comp (fderiv ℝ P y)
  have hdF (i : ι) (y : ℝ × ℝ) (hy : y ∈ s i) :
      HasFDerivWithinAt f (fderivWithin ℝ f (cell (a i) (b i) (c i) (d i)) (P y))
        (cell (a i) (b i) (c i) (d i)) (P y) :=
    ((hf i).differentiableOn one_ne_zero (P y) (hm i hy)).hasFDerivWithinAt
  apply finite_matching_c1_glue s hs (f ∘ P) D
  · intro i
    exact ((hf i).continuousOn_fderivWithin (cell_uniqueDiff _ _ _ _ (hab i) (hcd i)) le_rfl).comp
      hP.continuous.continuousOn (hm i) |>.clm_comp (hP.continuous_fderiv one_ne_zero).continuousOn
  · intro i y hy
    exact (hdF i y hy).comp y (hP.differentiable one_ne_zero y).hasFDerivAt.hasFDerivWithinAt (hm i)
  · intro i j y hy
    exact flattened_derivative_match f σ A hσ hA hσm hAm _ _ _ _ _ _ _ _
      ⟨(hsfix i).1,(hsfix i).2,(hsfix j).1,(hsfix j).2⟩
      ⟨(hafix i).1,(hafix i).2,(hafix j).1,(hafix j).2⟩
      ⟨(hsflat i).1,(hsflat i).2,(hsflat j).1,(hsflat j).2⟩
      ⟨(haflat i).1,(haflat i).2,(haflat j).1,(haflat j).2⟩ y
      (hscell i hy.1) (hscell j hy.2) _ _ (hdF i y hy.1) (hdF j y hy.2)
  · apply mem_of_superset (inter_mem hzcov hzV)
    rintro y ⟨hy,hV⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨i,hi,hV⟩

end PolarSeam462

-- Paid source: PolarGridApply

noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
namespace PolarSeam462

theorem finite_grid_cover (n : ℕ) (hn : 0 < n) (r : Fin (n+1) → ℝ)
    (hr : Monotone r) (x : ℝ) (hx : x ∈ Icc (r 0) (r (Fin.last n))) :
    ∃ i : Fin n,x ∈ Icc (r i.castSucc) (r i.succ) := by
  classical
  have hex : ∃ i : Fin (n+1),x ≤ r i := ⟨Fin.last n,hx.2⟩
  let j := Fin.find (fun i : Fin (n+1) => x ≤ r i) hex
  have hj : x ≤ r j := Fin.find_spec hex
  by_cases hj0 : j=0
  · let i : Fin n := ⟨0,hn⟩
    refine ⟨i,?_,?_⟩
    · exact hx.1
    · exact hj0 ▸ hj |>.trans (hr (Fin.zero_le i.succ))
  · obtain ⟨i,hi⟩ := Fin.exists_succ_eq_of_ne_zero hj0
    refine ⟨i,?_,?_⟩
    · have hlt : i.castSucc < j := by rw [← hi];change i.val < i.val+1;omega
      exact (lt_of_not_ge (Fin.find_min hex hlt)).le
    · simpa only [hi] using hj

def angularShift (k : Fin 3) : ℝ := ((k.val : ℤ)-1) • (2*Real.pi)

theorem angular_three_cover (m : ℕ) (hm : 0 < m) (t : Fin (m+1) → ℝ)
    (ht : Monotone t) (ht0 : t 0=0) (htp : t (Fin.last m)=2*Real.pi)
    (θ : ℝ) (hθ : θ ∈ Icc (-(2*Real.pi)) (2*(2*Real.pi))) :
    ∃ j : Fin m,∃ k : Fin 3,θ ∈ Icc (t j.castSucc+angularShift k) (t j.succ+angularShift k) := by
  by_cases hneg : θ ≤ 0
  · have hh : θ+2*Real.pi ∈ Icc (t 0) (t (Fin.last m)) := by rw [ht0,htp];constructor <;> linarith [hθ.1]
    obtain ⟨j,hj⟩ := finite_grid_cover m hm t ht _ hh
    refine ⟨j,0,?_,?_⟩ <;> norm_num [angularShift] <;> linarith [hj.1,hj.2]
  · by_cases hle : θ ≤ 2*Real.pi
    · obtain ⟨j,hj⟩ := finite_grid_cover m hm t ht θ (by rw [ht0,htp];exact ⟨(lt_of_not_ge hneg).le,hle⟩)
      refine ⟨j,1,?_⟩
      simpa [angularShift] using hj
    · have hh : θ-2*Real.pi ∈ Icc (t 0) (t (Fin.last m)) := by rw [ht0,htp];constructor <;> linarith [hθ.2]
      obtain ⟨j,hj⟩ := finite_grid_cover m hm t ht _ hh
      refine ⟨j,2,?_,?_⟩ <;> norm_num [angularShift] <;> linarith [hj.1,hj.2]

theorem cell_shift (a b c d s : ℝ) : MapsTo (fun z : ℝ × ℝ => (z.1,z.2-s))
    (cell a b (c+s) (d+s)) (cell a b c d) := by
  intro z hz
  refine ⟨⟨hz.1.1,⟨by linarith [hz.1.2.1],by linarith [hz.1.2.2]⟩⟩,?_⟩
  intro hc
  apply hz.2
  refine ⟨hc.1,?_⟩
  have hh : z.2-s=c ∨ z.2-s=d := by simpa [corners] using hc.2
  simpa [corners] using hh.imp (by intro h;linarith) (by intro h;linarith)

theorem polar_tile_shift (H : E2 → E2) (a b c d : ℝ) (k : ℤ)
    (h : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => H (z.1 • unitCircleParameter z.2)) (cell a b c d)) :
    ContDiffOn ℝ 1 (fun z : ℝ × ℝ => H (z.1 • unitCircleParameter z.2))
      (cell a b (c+k • (2*Real.pi)) (d+k • (2*Real.pi))) := by
  have hp : ContDiff ℝ 1 (fun z : ℝ × ℝ => (z.1,z.2-k • (2*Real.pi))) :=
    contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)
  have hc := h.comp hp.contDiffOn (cell_shift a b c d (k • (2*Real.pi)))
  apply hc.congr
  intro z hz
  dsimp [Function.comp_def]
  have he : unitCircleParameter (z.2-k • (2*Real.pi))=unitCircleParameter z.2 := by
    simpa only [neg_smul,sub_eq_add_neg] using unitCircle_period z.2 (-k)
  rw [he]

theorem periodic_flat_shift (A : ℝ → ℝ)
    (hp : ∀ θ (k : ℤ),A (θ+k • (2*Real.pi))=A θ+k • (2*Real.pi))
    (x : ℝ) (hx : HasDerivAt A 0 x) (k : ℤ) : HasDerivAt A 0 (x+k • (2*Real.pi)) := by
  let s := k • (2*Real.pi)
  have hd : HasDerivAt A 0 ((x+s)-s) := by simpa only [add_sub_cancel_right] using hx
  have h := (hd.comp (x+s) ((hasDerivAt_id (x+s)).sub_const s)).add_const s
  have he : (fun θ : ℝ => A (θ-s)+s)=A := by
    funext θ
    have hh := hp (θ-s) k
    dsimp [s] at hh ⊢
    simpa only [sub_add_cancel] using hh.symm
  simp only [Function.comp_def,id_eq,zero_mul] at h
  rw [he] at h
  exact h

theorem local_polar_argument_normalized (x : E2) (hx : x ≠ 0) :
    ∃ θ : E2 → ℝ,ContDiffAt ℝ 1 θ x ∧
      (∀ y,‖y‖ • unitCircleParameter (θ y)=y) ∧ θ x ∈ Ico 0 (2*Real.pi) := by
  obtain ⟨ψ,hψ,hrec⟩ := local_polar_argument x hx
  let k := toIcoDiv Real.two_pi_pos 0 (ψ x)
  let θ : E2 → ℝ := fun y => ψ y-k • (2*Real.pi)
  refine ⟨θ,hψ.sub contDiffAt_const,?_,?_⟩
  · intro y
    have he : unitCircleParameter (θ y)=unitCircleParameter (ψ y) := by
      simpa only [θ,neg_smul,sub_eq_add_neg] using unitCircle_period (ψ y) (-k)
    rw [he,hrec]
  · simpa only [θ,k,zero_add] using sub_toIcoDiv_zsmul_mem_Ico Real.two_pi_pos 0 (ψ x)


def polarVertices {n m : ℕ} (r : Fin (n+1) → ℝ) (t : Fin (m+1) → ℝ) : Finset E2 :=
  insert 0 (Finset.univ.image (fun z : Fin (n+1) × Fin (m+1) => r z.1 • unitCircleParameter (t z.2)))

theorem flat_polar_grid_contDiffAt (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (r : Fin (n+1) → ℝ) (t : Fin (m+1) → ℝ) (hr : StrictMono r) (ht : StrictMono t)
    (hr0 : r 0=0) (ht0 : t 0=0) (htp : t (Fin.last m)=2*Real.pi)
    (H : E2 → E2)
    (hgrid : ∀ (i : Fin n) (j : Fin m),ContDiffOn ℝ 1
      (fun z : ℝ × ℝ => H (z.1 • unitCircleParameter z.2))
      (cell (r i.castSucc) (r i.succ) (t j.castSucc) (t j.succ)))
    (σ A : ℝ → ℝ) (hσ : ContDiff ℝ 1 σ) (hA : ContDiff ℝ 1 A)
    (hσm : StrictMono σ) (hAm : StrictMono A)
    (hsnodes : ∀ i,σ (r i)=r i ∧ HasDerivAt σ 0 (r i))
    (hanodes : ∀ j,A (t j)=t j ∧ HasDerivAt A 0 (t j))
    (haper : ∀ θ (k : ℤ),A (θ+k • (2*Real.pi))=A θ+k • (2*Real.pi))
    (x : E2) (hx : x ∉ polarVertices r t) (hxR : ‖x‖ < r (Fin.last n)) :
    ContDiffAt ℝ 1 (H ∘ polarMap σ (fun _ θ => A θ)) x := by
  classical
  have hx0 : x ≠ 0 := by intro he;subst x;exact hx (Finset.mem_insert_self _ _)
  obtain ⟨θ,hθ,hrec,hθrange⟩ := local_polar_argument_normalized x hx0
  let z : ℝ × ℝ := (‖x‖,θ x)
  let I := Fin n × Fin m × Fin 3
  let a (i : I) := r i.1.castSucc
  let b (i : I) := r i.1.succ
  let c (i : I) := t i.2.1.castSucc+angularShift i.2.2
  let d (i : I) := t i.2.1.succ+angularShift i.2.2
  let f : (ℝ × ℝ) → E2 := fun z => H (z.1 • unitCircleParameter z.2)
  have hab (i : I) : a i < b i := hr (by change i.1.val < i.1.val+1;omega)
  have hcd (i : I) : c i < d i := by
    dsimp [c,d]
    have hh := ht (show i.2.1.castSucc < i.2.1.succ by change i.2.1.val < i.2.1.val+1;omega)
    linarith
  have hf (i : I) : ContDiffOn ℝ 1 f (cell (a i) (b i) (c i) (d i)) :=
    polar_tile_shift H _ _ _ _ ((i.2.2.val:ℤ)-1) (hgrid i.1 i.2.1)
  have hsfix (i : I) : σ (a i)=a i ∧ σ (b i)=b i := ⟨(hsnodes _).1,(hsnodes _).1⟩
  have hafix (i : I) : A (c i)=c i ∧ A (d i)=d i := by
    dsimp [c,d,angularShift]
    constructor <;> rw [haper,(hanodes _).1]
  have hsflat (i : I) : HasDerivAt σ 0 (a i) ∧ HasDerivAt σ 0 (b i) := ⟨(hsnodes _).2,(hsnodes _).2⟩
  have haflat (i : I) : HasDerivAt A 0 (c i) ∧ HasDerivAt A 0 (d i) :=
    ⟨periodic_flat_shift A haper _ (hanodes _).2 _,periodic_flat_shift A haper _ (hanodes _).2 _⟩
  have hcov : (⋃ i : I,rectangle (a i) (b i) (c i) (d i)) ∈ 𝓝 z := by
    have hzopen : z ∈ Ioo 0 (r (Fin.last n)) ×ˢ Ioo (-(2*Real.pi)) (2*(2*Real.pi)) := by
      refine ⟨⟨norm_pos_iff.mpr hx0,hxR⟩,?_,?_⟩
      · dsimp [z];linarith [hθrange.1,Real.two_pi_pos]
      · dsimp [z];linarith [hθrange.2,Real.two_pi_pos]
    apply mem_of_superset ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hzopen)
    intro w hw
    obtain ⟨i,hi⟩ := finite_grid_cover n hn r hr.monotone w.1 (by rw [hr0];exact ⟨hw.1.1.le,hw.1.2.le⟩)
    obtain ⟨j,k,hjk⟩ := angular_three_cover m hm t ht.monotone ht0 htp w.2 ⟨hw.2.1.le,hw.2.2.le⟩
    exact mem_iUnion.mpr ⟨(i,j,k),hi,hjk⟩
  have hbad (i : I) : z ∉ corners (a i) (b i) (c i) (d i) := by
    intro hz
    have hrad : ‖x‖=r i.1.castSucc ∨ ‖x‖=r i.1.succ := by simpa [corners,a,b,z] using hz.1
    have hang : θ x=t i.2.1.castSucc+angularShift i.2.2 ∨ θ x=t i.2.1.succ+angularShift i.2.2 := by
      simpa [corners,c,d,z] using hz.2
    obtain ⟨ir,hir⟩ : ∃ ir : Fin (n+1),‖x‖=r ir :=
      hrad.elim (fun h => ⟨i.1.castSucc,h⟩) (fun h => ⟨i.1.succ,h⟩)
    obtain ⟨ja,hja⟩ : ∃ ja : Fin (m+1),θ x=t ja+angularShift i.2.2 :=
      hang.elim (fun h => ⟨i.2.1.castSucc,h⟩) (fun h => ⟨i.2.1.succ,h⟩)
    apply hx
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨(ir,ja),Finset.mem_univ _,?_⟩
    have hh := hrec x
    rw [hir,hja] at hh
    dsimp [angularShift] at hh
    rw [unitCircle_period] at hh
    exact hh
  have hc := finite_rectangle_flatten a b c d hab hcd f hf σ A hσ hA hσm hAm
    hsfix hafix hsflat haflat z hcov hbad
  have hn : ContDiffAt ℝ 1 (fun y : E2 => ‖y‖) x := contDiffAt_norm ℝ hx0
  have hcom := hc.comp x (hn.prodMk hθ)
  apply hcom.congr_of_eventuallyEq
  filter_upwards [isOpen_compl_singleton.mem_nhds hx0] with y hy
  change H (polarMap σ (fun _ θ => A θ) y)=H (σ ‖y‖ • unitCircleParameter (A (θ y)))
  exact congrArg H (polarMap_representation σ (fun _ θ => A θ)
    (fun _ θ k => haper θ k) y hy (θ y) (hrec y))

end PolarSeam462

-- Paid source: PolarSeamProducer
noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
-- Read-only independent producer contract, no new original hypothesis.

namespace SeifertSurfaces.SharpCapProducers
theorem finite_polar_seam_producer :
∀ (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
  (r : Fin (n+1) → ℝ) (t : Fin (m+1) → ℝ)
  (hr : StrictMono r) (ht : StrictMono t),
  r 0=0 → 0 < r (Fin.last n) → r (Fin.last n) < 1 →
  t 0=0 → t (Fin.last m)=2*Real.pi →
  ∀ (H : E2 → E2), (∃ L : NNReal, LipschitzWith L H) →
  (∀ x, r (Fin.last n) ≤ ‖x‖ → ContDiffAt ℝ 1 H x) →
  (∀ (i : Fin n) (j : Fin m),
    ContDiffOn ℝ 1 (fun z : ℝ×ℝ => H (z.1 • unitCircleParameter z.2))
      ((Icc (r i.castSucc) (r i.succ) ×ˢ Icc (t j.castSucc) (t j.succ)) \
        (({r i.castSucc,r i.succ}:Set ℝ) ×ˢ ({t j.castSucc,t j.succ}:Set ℝ)))) →
  ∃ (T : E2 → E2) (b : ℝ), r (Fin.last n) < b ∧ b < 1 ∧
    Bijective T ∧ ContDiff ℝ 1 T ∧ (∃ L : NNReal, LipschitzWith L T) ∧
    EqOn T id {x | b ≤ ‖x‖} ∧ T '' ball 0 1=ball 0 1 ∧
    ContDiff ℝ 1 (H ∘ T) ∧ (∃ L : NNReal, LipschitzWith L (H ∘ T)) := by
  intro n m hn hm r t hr ht hr0 hrpos hr1 ht0 htp H hHLip hHout hgrid
  classical
  let R := r (Fin.last n)
  let b := (R+1)/2
  have hRb : R < b := by dsimp [b,R];linarith
  have hb1 : b < 1 := by dsimp [b,R];linarith
  have hb0 : 0 < b := hrpos.trans hRb
  obtain ⟨σ,hσ,hσm,hσs,hσL,hσ0,hσd0,hsnodes,hσout,hσimages⟩ :=
    PolarSeam462.radial_flat_grid n hn r hr hr0 hr1
  obtain ⟨A,hA,hAm,hAs,hAL,hA0,hAp,haper,hanodes,hAimages⟩ :=
    PolarSeam462.periodic_angular_grid m hm t ht ht0 htp
  let B : ℝ → ℝ → ℝ := fun ρ θ => PolarSeam462.angleBlend A (PolarSeam462.radialCutoff R b ρ) θ
  let T0 := PolarSeam462.polarMap σ B
  have hBp : ∀ ρ θ (k : ℤ),B ρ (θ+k • (2*Real.pi))=B ρ θ+k • (2*Real.pi) :=
    fun ρ θ k => PolarSeam462.angleBlend_period A haper _ θ k
  have hBc : ContDiff ℝ 1 (fun z : ℝ × ℝ => B z.1 z.2) :=
    PolarSeam462.supported_angle_contDiff A hA R b
  have hT0b : Bijective T0 :=
    ⟨PolarSeam462.polarMap_injective σ B hσm hσ0 hBp
      (fun ρ => (PolarSeam462.angleBlend_strictMono A hAm _ (PolarSeam462.radialCutoff_range R b ρ)).injective),
     PolarSeam462.polarMap_surjective σ B hσm hσs hσ0 hBp
      (fun ρ => PolarSeam462.angleBlend_surjective A hA.continuous hA0 hAp haper _)⟩
  have hT0c (x : E2) (hx : x ≠ 0) : ContDiffAt ℝ 1 T0 x :=
    PolarSeam462.polarMap_contDiffAt σ B hσ hBc hBp x hx
  have hT0L : ∃ K : NNReal,LipschitzWith K T0 :=
    PolarSeam462.supported_polar_lipschitz σ A R b hrpos hRb hσ hσm hσ0 hσL hσout hA haper
  have hT0out (x : E2) (hx : b ≤ ‖x‖) : T0 x=x := by
    exact PolarSeam462.polarMap_eqOn σ B b hσout
      (fun ρ θ hρ => by simp only [B,PolarSeam462.radialCutoff_zero R b ρ hRb hρ,
        PolarSeam462.angleBlend,sub_zero,one_mul,zero_mul,add_zero]) hx
  let S := PolarSeam462.polarVertices r t
  have hSb : (S : Set E2) ⊆ ball 0 b := by
    intro y hy
    rcases Finset.mem_insert.mp hy with hy | hy
    · subst y;simpa only [Metric.mem_ball,dist_self] using hb0
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
      have hri : 0 ≤ r z.1 := by simpa only [hr0] using hr.monotone (Fin.zero_le z.1)
      have hir := hr.monotone (Fin.le_last z.1)
      simp only [Metric.mem_ball,dist_zero_right,PolarSeam462.polar_norm _ _ hri]
      exact hir.trans_lt hRb
  have hcomp (x : E2) (hx : x ∉ (S : Set E2)) : ContDiffAt ℝ 1 (H ∘ T0) x := by
    have hx0 : x ≠ 0 := by intro he;subst x;exact hx (Finset.mem_insert_self _ _)
    by_cases hxR : R ≤ ‖x‖
    · have hTxR : R ≤ ‖T0 x‖ := by
        change R ≤ ‖PolarSeam462.polarMap σ B x‖
        rw [PolarSeam462.polarMap_norm σ B hσm hσ0]
        have hh := hσm.monotone hxR
        dsimp [R] at hh ⊢
        rw [(hsnodes (Fin.last n)).1] at hh
        exact hh
      exact (hHout (T0 x) hTxR).comp x (hT0c x hx0)
    · have hc : ContDiffAt ℝ 1 (H ∘ PolarSeam462.polarMap σ (fun _ θ => A θ)) x :=
        PolarSeam462.flat_polar_grid_contDiffAt n m hn hm r t hr ht hr0 ht0 htp H
          hgrid σ A hσ hA hσm hAm hsnodes hanodes haper x hx (lt_of_not_ge hxR)
      apply hc.congr_of_eventuallyEq
      filter_upwards [continuous_norm.continuousAt.preimage_mem_nhds (Iio_mem_nhds (lt_of_not_ge hxR))] with y hy
      change H (PolarSeam462.polarMap σ B y)=H (PolarSeam462.polarMap σ (fun _ θ => A θ) y)
      simp only [PolarSeam462.polarMap,B,PolarSeam462.radialCutoff_one R b ‖y‖ hRb hy.le,
        PolarSeam462.angleBlend,sub_self,zero_mul,one_mul,zero_add]
  obtain ⟨T,hTb,hTc,hTL,hTout,hTball,hHTc,hHTL⟩ :=
    PolarSeam462.finish_polar_finite_vertices H T0 b hb0 hb1 hHLip hT0b hT0L hT0out hT0c S hSb hcomp
  exact ⟨T,b,hRb,hb1,hTb,hTc,hTL,hTout,hTball,hHTc,hHTL⟩
end SeifertSurfaces.SharpCapProducers

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CountGeometry
private theorem original_qdq_complete
    (R : ℝ) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2) (hM : Continuous M) :
    ∃ q : E2 → E2, ∃ dq : Fin 2 → E2 → E2,
      MetricAdmissible Ω q dq ∧ ContDiffOn ℝ 1 q (closedDisc 1) ∧
      q '' disc 1=Ω.domain ∧ InjOn q (closedDisc 1) ∧
      (∀ i j,(fun x => dq i x j) =ᵐ[volume.restrict (disc 1)]
        (fun x => jacobianWithin q (closedDisc 1) x i j)) ∧
      metricArea M q dq=∫ y in Ω.domain,Real.sqrt (Matrix.det (M y)) := by
  exact original_qdq_of_polar_producer SeifertSurfaces.SharpCapProducers.finite_polar_seam_producer R Ω M hM
end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CountGeometry

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CountGeometry
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
-- UNPAID LOWER GOAL: actual_full_class_planar_competitor
theorem actual_full_class_planar_competitor (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (u : E2 → E2) (same_map : u =ᵐ[volume.restrict (disc 1)] f)
    (forward_C1 : ContDiffOn ℝ 1 u (closedDisc 1))
    (forward_holder : ∀ i j, ∃ C : ℝ≥0,
      HolderOnWith C G.alpha (fun z => jacobianWithin u (closedDisc 1) z i j) (closedDisc 1)) :
    ∃ v : E2 → E2, ∃ dv : Fin 2 → E2 → E2,
      MetricAdmissible Ω v dv ∧
      ENNReal.ofReal (metricArea M v dv) ≤
        ∫⁻ x, ENNReal.ofReal (Real.sqrt (Matrix.det (M x))) *
          Ω.domain.indicator (fun _ => (1 : ℝ≥0∞)) x := by
  have hM : Continuous M := continuous_pi_iff.mpr fun i => continuous_pi_iff.mpr fun j => by
    obtain ⟨C, hC⟩ := holder i j
    exact hC.continuous G.alpha_pos
  obtain ⟨q, dq, hqa, hqc, hqi, hqin, hder, harea⟩ := original_qdq_complete R Ω M hM
  refine ⟨q, dq, hqa, le_of_eq ?_⟩
  have hint : IntegrableOn (fun x => Real.sqrt (Matrix.det (M x))) Ω.domain :=
    (ContinuousOn.integrableOn_compact Ω.bounded_domain.isCompact_closure
      hM.matrix_det.sqrt.continuousOn).mono_set subset_closure
  rw [harea, ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _)]
  rw [← lintegral_indicator Ω.open_domain.measurableSet]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ Ω.domain <;> simp [hx]


end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CountGeometry
