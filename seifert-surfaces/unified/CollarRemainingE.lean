import Foundations
import Mathlib.Geometry.Manifold.PartitionOfUnity
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric

set_option maxSynthPendingDepth 3
set_option autoImplicit false
open scoped Manifold ContDiff BigOperators
open Set Topology
namespace SeifertSurfaces.LongitudeProducers.CollarCutHelpers.Remaining
open Foundations
universe u v
noncomputable section

structure PositiveRectangle {E : Type u} [TopologicalSpace E]
    (U : Set (ℝ × E)) (z : E) where
  T : ℝ
  T_pos : 0 < T
  W : Set E
  W_open : IsOpen W
  z_mem : z ∈ W
  positive_subset : Icc 0 T ×ˢ W ⊆ U
  r : ℝ
  r_pos : 0 < r
  r_lt : r < T
  W₀ : Set E
  W₀_open : IsOpen W₀
  z_mem₀ : z ∈ W₀
  smaller : W₀ ⊆ W
  rectangle_subset : Ioo (-r) r ×ˢ W₀ ⊆ U


theorem E1_positive_rectangle {E : Type u} [TopologicalSpace E]
    (U : Set (ℝ × E)) (hU : IsOpen U) (z : E) (hz : (0,z) ∈ U) :
    Nonempty (PositiveRectangle U z) := by
  obtain ⟨A, B, hA, hB, h0, hzB, hAB⟩ := isOpen_prod_iff.mp hU 0 z hz
  obtain ⟨e, he, hball⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds h0)
  refine ⟨{ T := e / 2
            T_pos := by positivity
            W := B
            W_open := hB
            z_mem := hzB
            positive_subset := ?_
            r := e / 4
            r_pos := by positivity
            r_lt := by linarith
            W₀ := B
            W₀_open := hB
            z_mem₀ := hzB
            smaller := Set.Subset.rfl
            rectangle_subset := ?_ }⟩
  · rintro ⟨t,w⟩ ⟨ht,hw⟩
    apply hAB
    refine ⟨hball ?_, hw⟩
    change dist t 0 < e
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    linarith [ht.2]
  · rintro ⟨t,w⟩ ⟨ht,hw⟩
    apply hAB
    refine ⟨hball ?_, hw⟩
    change dist t 0 < e
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [ht.1, ht.2]

structure RectangleExtension {E : Type u} {G : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U : Set (ℝ × E)} {z : E} (R : PositiveRectangle U z) (h : ℝ × E → G) where
  W : Set E
  W_open : IsOpen W
  z_mem : z ∈ W
  W_subset : W ⊆ R.W₀
  r : ℝ
  r_pos : 0 < r
  r_le : r ≤ R.r
  extended : ℝ × E → G
  smooth : ContDiffOn ℝ ∞ extended (Ioo (-r) r ×ˢ W)
  agrees : EqOn extended h ((Ioo (-r) r ×ˢ W) ∩ (Ici 0 ×ˢ univ))


theorem E2_interval_extension {E : Type u} {G : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (U : Set (ℝ × E)) (hU : IsOpen U) (z : E) (hz : (0,z) ∈ U)
    (h : ℝ × E → G) (hh : ContDiffOn ℝ ∞ h (U ∩ (Ici 0 ×ˢ univ)))
    (R : PositiveRectangle U z) : Nonempty (RectangleExtension R h) := by
  let g : ℝ → E → G := fun t w => h (t,w)
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g) (Icc 0 R.T ×ˢ R.W) :=
    hh.mono (fun p hp => ⟨R.positive_subset hp, hp.1.1, mem_univ _⟩)
  obtain ⟨gext, V, hV, hs, heq⟩ := DifferentialGeometry.Analysis.borel_interval_extend_param
    g R.T R.T_pos R.W z (by rw [IsOpen.interior_eq R.W_open]; exact R.z_mem) hg
  let W := interior V ∩ R.W₀
  have hW : IsOpen W := isOpen_interior.inter R.W₀_open
  have hzW : z ∈ W := ⟨mem_interior_iff_mem_nhds.mpr hV, R.z_mem₀⟩
  refine ⟨{ W := W
            W_open := hW
            z_mem := hzW
            W_subset := inter_subset_right
            r := R.r
            r_pos := R.r_pos
            r_le := le_rfl
            extended := Function.uncurry gext
            smooth := hs.mono (fun p hp => ⟨mem_univ _, interior_subset hp.2.1⟩)
            agrees := ?_ }⟩
  intro p hp
  exact heq p.1 ⟨hp.2.1, hp.1.1.2.le.trans R.r_lt.le⟩ p.2 (interior_subset hp.1.2.1)


structure CircleExtensionData (a : ℝ) (h : Circle × ℝ → ℝ) where
  count : ℕ
  chart : Fin count → OpenPartialHomeomorph Circle (Euc 1)
  chart_atlas : ∀ i, chart i ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle
  domain : Fin count → Set Circle
  domain_open : ∀ i, IsOpen (domain i)
  domain_subset : ∀ i, domain i ⊆ (chart i).source
  covers : ∀ z, ∃ i, z ∈ domain i
  width : Fin count → ℝ
  width_pos : ∀ i, 0 < width i
  width_lt : ∀ i, width i < a
  extended : Fin count → ℝ × Euc 1 → ℝ
  extended_smooth : ∀ i, ContDiffOn ℝ ∞ (extended i)
    (Ioo (-(width i)) (width i) ×ˢ ((chart i) '' domain i))
  extended_agrees : ∀ i z s, z ∈ domain i → 0 ≤ s → s < width i →
    extended i (s, chart i z) = h (z,s)
  weights : SmoothPartitionOfUnity (Fin count) (𝓡 1) Circle
  supported : ∀ i, tsupport (weights i) ⊆ domain i
  a' : ℝ
  a'_pos : 0 < a'
  a'_lt : a' < a
  uniform_width : ∀ i, a' < width i


theorem E4_circle_extension_data (a : ℝ) (ha : 0 < a) (h : Circle × ℝ → ℝ)
    (hh : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞ h
      {p | 0 ≤ p.2 ∧ p.2 < a}) : Nonempty (CircleExtensionData a h) := by
  classical
  have hlocal : ∀ z : Circle, ∃ c : OpenPartialHomeomorph Circle (Euc 1),
      ∃ O : Set Circle, ∃ w : ℝ, ∃ H : ℝ × Euc 1 → ℝ,
        c ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle ∧ IsOpen O ∧
        z ∈ O ∧ O ⊆ c.source ∧ 0 < w ∧ w < a ∧
        ContDiffOn ℝ ∞ H (Ioo (-w) w ×ˢ (c '' O)) ∧
        ∀ z' s, z' ∈ O → 0 ≤ s → s < w → H (s,c z') = h (z',s) := by
    intro z
    let c := chartAt (Euc 1) z
    let g : ℝ → Euc 1 → ℝ := fun t y => h (c.symm y,t)
    let B := Icc (0 : ℝ) (a/2) ×ˢ c.target
    have hswap : ContMDiffOn 𝓘(ℝ, ℝ × Euc 1) ((𝓡 1).prod 𝓘(ℝ,ℝ)) ∞
        (fun p : ℝ × Euc 1 => (c.symm p.2,p.1)) B := by
      have hc : ContMDiffOn 𝓘(ℝ, Euc 1) (𝓡 1) ∞ c.symm c.target :=
        contMDiffOn_chart_symm
      have hc' : ContMDiffOn 𝓘(ℝ, ℝ × Euc 1) (𝓡 1) ∞ (fun p => c.symm p.2) B :=
        hc.comp contDiff_snd.contMDiff.contMDiffOn (fun p hp => hp.2)
      exact hc'.prodMk contDiff_fst.contMDiff.contMDiffOn
    have hg : ContDiffOn ℝ ∞ (Function.uncurry g) B := by
      exact (hh.comp hswap (fun p hp => ⟨hp.1.1, by linarith [hp.1.2]⟩)).contDiffOn
    obtain ⟨gext,W,hW,hs,heq⟩ := DifferentialGeometry.Analysis.borel_interval_extend_param
      g (a/2) (by positivity) c.target (c z)
      (by rw [c.open_target.interior_eq]; exact c.map_source (mem_chart_source _ _)) hg
    let O := c.source ∩ c ⁻¹' interior W
    have hO : IsOpen O := c.isOpen_inter_preimage isOpen_interior
    have hzO : z ∈ O := ⟨mem_chart_source _ _,mem_interior_iff_mem_nhds.mpr hW⟩
    refine ⟨c,O,a/4,Function.uncurry gext,IsManifold.chart_mem_maximalAtlas z,hO,hzO,
      inter_subset_left,by positivity,by linarith,?_,?_⟩
    · apply hs.mono
      rintro ⟨t,y⟩ ⟨ht,hy⟩
      obtain ⟨z',hz',rfl⟩ := hy
      exact ⟨mem_univ _,interior_subset hz'.2⟩
    · intro z' s hz' hs0 hsw
      exact (heq s ⟨hs0,by linarith⟩ (c z') (interior_subset hz'.2)).trans
        (by change h (c.symm (c z'),s) = h (z',s); rw [c.left_inv hz'.1])
  choose c O w H hc hO hzO hOc hw hwa hH hHa using hlocal
  obtain ⟨cover,hcover⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun z _ => mem_iUnion.mpr ⟨z,hzO z⟩)
  let count := Fintype.card cover
  let index : Fin count → Circle := fun i => ((Fintype.equivFin cover).symm i).val
  have hfinite_cover : ∀ z, ∃ i : Fin count, z ∈ O (index i) := by
    intro z
    have hzcover : ∃ z', ∃ _hz' : z' ∈ cover, z ∈ O z' := by
      simpa only [mem_iUnion] using hcover (mem_univ z)
    obtain ⟨z',hz',hzO'⟩ := hzcover
    refine ⟨Fintype.equivFin cover ⟨z',hz'⟩,?_⟩
    simpa only [index,Equiv.symm_apply_apply] using hzO'
  obtain ⟨weights,hweights⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡 1)
    isClosed_univ (fun i : Fin count => O (index i)) (fun i => hO (index i))
    (fun z _ => mem_iUnion.mpr (hfinite_cover z))
  have hwidth : ∃ b : ℝ, 0 < b ∧ b < a ∧ ∀ i : Fin count, b < w (index i) := by
    have hex : ∀ s : Finset (Fin count), ∃ b : ℝ, 0 < b ∧ b < a ∧ ∀ i ∈ s, b < w (index i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨a/2,by positivity,by linarith,by simp⟩
      | @insert i s hi ih =>
        obtain ⟨b,hb,hba,hbw⟩ := ih
        have hwi := hw (index i)
        refine ⟨min b (w (index i)) / 2,by positivity,?_,?_⟩
        · exact (by linarith [min_le_left b (w (index i))] : min b (w (index i))/2 < b).trans hba
        · intro j hj
          rcases Finset.mem_insert.mp hj with hji | hj
          · subst j
            linarith [min_le_right b (w (index i)), hw (index i)]
          · exact (by linarith [min_le_left b (w (index i))] : min b (w (index i))/2 < b).trans (hbw j hj)
    obtain ⟨b,hb,hba,hbw⟩ := hex Finset.univ
    exact ⟨b,hb,hba,fun i => hbw i (Finset.mem_univ i)⟩
  obtain ⟨b,hb,hba,hbw⟩ := hwidth
  exact ⟨{ count := count
           chart := fun i => c (index i)
           chart_atlas := fun i => hc (index i)
           domain := fun i => O (index i)
           domain_open := fun i => hO (index i)
           domain_subset := fun i => hOc (index i)
           covers := hfinite_cover
           width := fun i => w (index i)
           width_pos := fun i => hw (index i)
           width_lt := fun i => hwa (index i)
           extended := fun i => H (index i)
           extended_smooth := fun i => hH (index i)
           extended_agrees := fun i => hHa (index i)
           weights := weights
           supported := hweights
           a' := b
           a'_pos := hb
           a'_lt := hba
           uniform_width := hbw }⟩

def circleWeightedExtension {a : ℝ} {h : Circle × ℝ → ℝ}
    (D : CircleExtensionData a h) (p : Circle × ℝ) : ℝ :=
  ∑ i : Fin D.count, @ite ℝ (p.1 ∈ D.domain i) (Classical.propDecidable _)
    ((D.weights i p.1) * D.extended i (p.2, D.chart i p.1)) 0


theorem E5_circle_weighted_extension {a : ℝ} {h : Circle × ℝ → ℝ}
    (hh : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞ h
      {p | 0 ≤ p.2 ∧ p.2 < a}) (D : CircleExtensionData a h) :
    ContMDiffOn ((𝓡 1).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞ (circleWeightedExtension D)
      {p | |p.2| < D.a'} ∧
    EqOn (circleWeightedExtension D) h {p | 0 ≤ p.2 ∧ p.2 < D.a'} ∧
    ∀ z, circleWeightedExtension D (z,0) = h (z,0) ∧
      deriv (fun s => circleWeightedExtension D (z,s)) 0 =
        derivWithin (fun s => h (z,s)) (Ici 0) 0 := by
  classical
  let term (i : Fin D.count) (p : Circle × ℝ) : ℝ :=
    if p.1 ∈ D.domain i then D.weights i p.1 * D.extended i (p.2,D.chart i p.1) else 0
  have hterm (i : Fin D.count) (p : Circle × ℝ) (hp : |p.2| < D.a') :
      ContMDiffAt ((𝓡 1).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞ (term i) p := by
    by_cases hin : p.1 ∈ D.domain i
    · have hc : ContMDiffAt (𝓡 1) 𝓘(ℝ,Euc 1) ∞ (D.chart i) p.1 :=
        contMDiffAt_of_mem_maximalAtlas (D.chart_atlas i) (D.domain_subset i hin)
      have hcoord : ContMDiffAt ((𝓡 1).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ × Euc 1) ∞
          (fun p : Circle × ℝ => (p.2,D.chart i p.1)) p :=
        contMDiff_snd.contMDiffAt.prodMk_space (hc.comp p contMDiff_fst.contMDiffAt)
      have hchartopen : IsOpen ((D.chart i) '' D.domain i) := by
        have heq : (D.chart i).source ∩ D.domain i = D.domain i :=
          inter_eq_right.mpr (D.domain_subset i)
        simpa only [heq] using (D.chart i).isOpen_image_source_inter (D.domain_open i)
      have ht : (p.2,D.chart i p.1) ∈ Ioo (-(D.width i)) (D.width i) ×ˢ ((D.chart i) '' D.domain i) :=
        ⟨abs_lt.mp (hp.trans (D.uniform_width i)),⟨p.1,hin,rfl⟩⟩
      have hE : ContMDiffAt 𝓘(ℝ,ℝ × Euc 1) 𝓘(ℝ,ℝ) ∞ (D.extended i)
          (p.2,D.chart i p.1) :=
        ((D.extended_smooth i).contDiffAt ((isOpen_Ioo.prod hchartopen).mem_nhds ht)).contMDiffAt
      have hprod := ((D.weights i).contMDiff.contMDiffAt.comp p contMDiff_fst.contMDiffAt).mul
        (hE.comp p hcoord)
      apply hprod.congr_of_eventuallyEq
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
        ((D.domain_open i).mem_nhds hin)] with q hq
      exact if_pos hq
    · have hsupp : p.1 ∉ tsupport (D.weights i) := fun h => hin (D.supported i h)
      apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hN := (isClosed_tsupport (D.weights i)).isOpen_compl.mem_nhds hsupp
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hN] with q hq
      have hz : D.weights i q.1 = 0 := by
        by_contra hn
        exact hq (subset_closure (Function.mem_support.mpr hn))
      simp only [term,hz,zero_mul,ite_self]
  have hsmooth : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞
      (circleWeightedExtension D) {p | |p.2| < D.a'} := by
    intro p hp
    exact (ContMDiffAt.sum (fun i _ => hterm i p hp)).contMDiffWithinAt
  have heq : EqOn (circleWeightedExtension D) h {p | 0 ≤ p.2 ∧ p.2 < D.a'} := by
    intro p hp
    have hsum : ∑ i : Fin D.count, D.weights i p.1 = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using D.weights.sum_eq_one (mem_univ p.1)
    calc
      circleWeightedExtension D p = ∑ i : Fin D.count, D.weights i p.1 * h p := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hin : p.1 ∈ D.domain i
        · simp only [circleWeightedExtension,if_pos hin]
          rw [D.extended_agrees i p.1 p.2 hin hp.1 (hp.2.trans (D.uniform_width i))]
        · have hz : D.weights i p.1 = 0 := by
            by_contra hn
            exact hin (D.supported i (subset_closure (Function.mem_support.mpr hn)))
          simp only [if_neg hin,hz,zero_mul]
      _ = h p := by rw [← Finset.sum_mul,hsum,one_mul]
  refine ⟨hsmooth,heq,?_⟩
  intro z
  have hzero : circleWeightedExtension D (z,0) = h (z,0) := heq ⟨le_rfl,D.a'_pos⟩
  have hslice : ContDiffAt ℝ ∞ (fun s => circleWeightedExtension D (z,s)) 0 := by
    have hs : ContMDiffAt ((𝓡 1).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞ (circleWeightedExtension D) (z,0) :=
      hsmooth.contMDiffAt ((isOpen_lt (continuous_abs.comp continuous_snd) continuous_const).mem_nhds
        (by simpa using D.a'_pos))
    exact (hs.comp 0 (contMDiff_const.prodMk contMDiff_id).contMDiffAt).contDiffAt
  have hnear : (fun s => circleWeightedExtension D (z,s)) =ᶠ[nhdsWithin (0 : ℝ) (Ici 0)]
      (fun s => h (z,s)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds D.a'_pos)] with s hs hsa
    exact heq ⟨hs,hsa⟩
  exact ⟨hzero, (hslice.differentiableAt (by simp)).derivWithin (uniqueDiffOn_Ici 0 0 (by simp)) |>.symm.trans
    (hnear.derivWithin_eq hzero)⟩

end
end SeifertSurfaces.LongitudeProducers.CollarCutHelpers.Remaining
