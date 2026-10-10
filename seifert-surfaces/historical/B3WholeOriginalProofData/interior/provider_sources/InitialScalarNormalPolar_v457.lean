import InitialGreenProduct_v411

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

private theorem original_scalar_normal_polar_v457
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (H1 : ∀ i,H1On (disc 1) (fun z=>f z i) (d i))
    (psi : E2 → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (p : E2) (a z : ℝ) (ha : 0<a) (haz : a<z) (hz : z<1)
    (i j : Fin 2) :
    let F : ℝ → ℝ := fun r=>r*∫ t in Ioo (-Real.pi) Real.pi,
      (disc 1).indicator (fun x=>f x i*psi x) (p+r•unitCircleParameter t)*unitCircleParameter t j
    IntegrableOn F (Ioo a z) ∧
      ∀ h : ℝ → ℝ,ContDiff ℝ ∞ h→HasCompactSupport h→
        tsupport h ⊆ Ioo (a^2) (z^2)→
      IntegrableOn (fun x=>f x i*psi x*(x j-p j)*h (‖x-p‖^2)) (disc 1) ∧
      IntegrableOn (fun r=>r*h (r^2)*F r) (Ioo a z) ∧
      (∫ x in disc 1,f x i*psi x*(x j-p j)*h (‖x-p‖^2))=
        ∫ r in Ioo a z,r*h (r^2)*F r := by
  classical
  dsimp only
  let F : ℝ → ℝ := fun r=>r*∫ t in Ioo (-Real.pi) Real.pi,
    (disc 1).indicator (fun x=>f x i*psi x) (p+r•unitCircleParameter t)*unitCircleParameter t j
  let v : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-(coordinateVector 2 j) 1,(coordinateVector 2 j) 0]
  let rows : Fin 2 → E2 → E2 := fun _ x=>(f x i*psi x)•v
  have hb : MemLp psi ∞ (volume.restrict (disc 1)) := by
    obtain ⟨K,hK⟩ := (isCompact_closedBall (0:E2) 1).exists_bound_of_continuousOn hpsi.continuous.continuousOn
    apply memLp_top_of_bound hpsi.continuous.aestronglyMeasurable.restrict K
    filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet (disc 1))] with x hx
    exact hK x (Metric.ball_subset_closedBall hx)
  have hr : ∀ k,MemLp (rows k) 2 (volume.restrict (disc 1)) := by
    intro k
    have hfpsi : MemLp (fun x=>f x i*psi x) 2 (volume.restrict (disc 1)) := (H1 i).2.1.mul hb
    exact hfpsi.continuousLinearMap_comp (ContinuousLinearMap.toSpanSingleton ℝ v)
  have hp := CourantAnalyticB.native_translated_polar_rows rows
    (fun k=>(hr k).aestronglyMeasurable) hr p a z ha haz hz
  dsimp only at hp
  have hpoint (r t : ℝ) :
      inner ℝ ((disc 1).indicator (rows 0) (p+r•unitCircleParameter t))
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![-(unitCircleParameter t) 1,(unitCircleParameter t) 0])=
      (disc 1).indicator (fun x=>f x i*psi x) (p+r•unitCircleParameter t)*unitCircleParameter t j := by
    by_cases hx:p+r•unitCircleParameter t∈disc 1
    · simp only [indicator_of_mem hx]
      fin_cases j <;>
        simp [rows,v,coordinateVector,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two] <;> ring
    · simp only [indicator_of_notMem hx,inner_zero_left,zero_mul]
  have hflux : (fun r=>r*∫ t in Ioo (-Real.pi) Real.pi,
      inner ℝ ((disc 1).indicator (rows 0) (p+r•unitCircleParameter t))
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![-(unitCircleParameter t) 1,(unitCircleParameter t) 0]))=F := by
    funext r
    simp only [F,hpoint]
  refine ⟨?_,?_⟩
  · simpa only [hflux] using (hp.2.2.2.2.2.2.2.1 0).2
  · intro h hh hhc hhs
    have ht := hp.2.2.2.2.2.2.2.2 h hh hhc hhs 0
    have hbulk (x : E2) :
        rows 0 x 0*(-(x 1-p 1)*h ((x 0-p 0)^2+(x 1-p 1)^2))+
        rows 0 x 1*((x 0-p 0)*h ((x 0-p 0)^2+(x 1-p 1)^2))=
        f x i*psi x*(x j-p j)*h (‖x-p‖^2) := by
      have hn : ‖x-p‖^2=(x 0-p 0)^2+(x 1-p 1)^2 := by
        rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
        rfl
      rw [hn]
      fin_cases j <;> simp [rows,v,coordinateVector] <;> ring
    refine ⟨?_,?_,?_⟩
    · exact ht.1.congr (Eventually.of_forall hbulk)
    · simpa only [hpoint,F] using ht.2.1
    · exact (integral_congr_ae (Eventually.of_forall fun x=>(hbulk x).symm)).trans
        (ht.2.2.trans (by simp only [hpoint]))

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
