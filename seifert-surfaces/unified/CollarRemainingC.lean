import DifferentialGeometry.Analysis.Calculus.SmoothExtension.HalfSpace
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Closed
import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import CollarRemainingI
import CollarRemainingP
import SuppliedChartHelpers
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Icc

set_option maxSynthPendingDepth 3
set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Bundle Filter
namespace SeifertSurfaces.LongitudeProducers.CollarCutHelpers.Remaining
open Foundations MetricFoundations DifferentialGeometry.Analysis.ODE
noncomputable section

structure C3InwardField {K : OrientedKnot} (F : SphereSpanningSurface.{0} K) where
  field : (x : F.surface) → TangentSpace (𝓡∂ 2) x
  smooth : ContMDiff (𝓡∂ 2) (𝓡∂ 2).tangent ∞
    (fun x => (⟨x,field x⟩ : TangentBundle (𝓡∂ 2) F.surface))
  positive : ∀ z, 0 < inwardCoordinate (F.boundary.toFun z) (field (F.boundary.toFun z))
  lower : ℝ
  lower_pos : 0 < lower
  count : ℕ
  chart : Fin count → OpenPartialHomeomorph F.surface (EuclideanHalfSpace 2)
  atlas : ∀ i, chart i ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ F.surface
  domain : Fin count → Set F.surface
  domain_open : ∀ i, IsOpen (domain i)
  closure_subset : ∀ i, closure (domain i) ⊆ (chart i).source
  boundary_cover : ∀ z, ∃ i, F.boundary.toFun z ∈ domain i
  localField : (i : Fin count) → (x : F.surface) → TangentSpace (𝓡∂ 2) x
  local_smooth : ∀ i, ContMDiffOn (𝓡∂ 2) (𝓡∂ 2).tangent ∞
    (fun x => (⟨x,localField i x⟩ : TangentBundle (𝓡∂ 2) F.surface)) (chart i).source
  local_normal : ∀ i x, x ∈ (chart i).source →
    tangentSpaceCastModel 𝓘(ℝ,Euc 2) ((chart i).extend (𝓡∂ 2) x)
      (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) ((chart i).extend (𝓡∂ 2)) x (localField i x)) =
        EuclideanSpace.single 0 1
  weights : SmoothPartitionOfUnity (Fin count) (𝓡∂ 2) F.surface F.surface.boundary
  supports : ∀ i, tsupport (weights i) ⊆ domain i
  weighted : ∀ x, field x = ∑ i : Fin count, weights i x • localField i x
  lower_bound : ∀ i z, F.boundary.toFun z ∈ closure (domain i) →
    lower ≤ (tangentSpaceCastModel 𝓘(ℝ,Euc 2) ((chart i).extend (𝓡∂ 2) (F.boundary.toFun z))
      (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) ((chart i).extend (𝓡∂ 2))
        (F.boundary.toFun z) (field (F.boundary.toFun z)))) 0
theorem C3_inward_field {K : OrientedKnot} (F : SphereSpanningSurface.{0} K) : Nonempty (C3InwardField F) := by
  have hdata {K : OrientedKnot} (F : SphereSpanningSurface.{0} K) :
      ∃ count : ℕ, ∃ a : Fin count → F.surface, ∃ U : Fin count → Set F.surface,
        ∃ v : (i : Fin count) → (x : F.surface) → TangentSpace (𝓡∂ 2) x,
        ∃ ρ : SmoothPartitionOfUnity (Fin count) (𝓡∂ 2) F.surface F.surface.boundary,
        (∀ i, IsOpen (U i)) ∧
        (∀ i, closure (U i) ⊆ (chartAt (EuclideanHalfSpace 2) (a i)).source) ∧
        (∀ z, ∃ i, F.boundary.toFun z∈U i) ∧
        (∀ i, tsupport (ρ i)⊆U i) ∧
        (∀ i, ContMDiffOn (𝓡∂ 2) (𝓡∂ 2).tangent ∞
          (fun x => (⟨x,v i x⟩ : TangentBundle (𝓡∂ 2) F.surface)) (chartAt (EuclideanHalfSpace 2) (a i)).source) ∧
        (∀ i x, x∈(chartAt (EuclideanHalfSpace 2) (a i)).source →
          tangentSpaceCastModel 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) (a i) x)
            (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) (a i)) x (v i x))=
              EuclideanSpace.single 0 1) ∧
        ContMDiff (𝓡∂ 2) (𝓡∂ 2).tangent ∞
          (fun x => (⟨x,∑ i, ρ i x • v i x⟩ : TangentBundle (𝓡∂ 2) F.surface)) ∧
        ∀ z, 0 < inwardCoordinate (F.boundary.toFun z) (∑ i, ρ i (F.boundary.toFun z) • v i (F.boundary.toFun z)) := by
    have hlocal {K : OrientedKnot} (F : SphereSpanningSurface.{0} K) (a : F.surface) :
        ∃ v : (x : F.surface) → TangentSpace (𝓡∂ 2) x,
          ContMDiffOn (𝓡∂ 2) (𝓡∂ 2).tangent ∞
            (fun x => (⟨x,v x⟩ : TangentBundle (𝓡∂ 2) F.surface)) (chartAt (EuclideanHalfSpace 2) a).source ∧
          ∀ x, x∈(chartAt (EuclideanHalfSpace 2) a).source →
            tangentSpaceCastModel 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) a x)
              (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) a) x (v x))=
                EuclideanSpace.single 0 1 := by
      let e := trivializationAt (Euc 2) (TangentSpace (𝓡∂ 2)) a
      let w : Euc 2 := EuclideanSpace.single 0 1
      let v : (x : F.surface) → TangentSpace (𝓡∂ 2) x := fun x => e.symmL ℝ x w
      have hs : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2).tangent ∞
          (fun x => (⟨x,v x⟩ : TangentBundle (𝓡∂ 2) F.surface)) e.baseSet := by
        rw [e.contMDiffOn_section_baseSet_iff]
        apply (contMDiffOn_const (c:=w)).congr
        intro x hx
        rw [←e.continuousLinearMapAt_apply_of_mem (R:=ℝ) hx]
        change e.continuousLinearMapAt ℝ x (e.symmL ℝ x w)=w
        exact e.continuousLinearMapAt_symmL hx w
      have hbase : e.baseSet=(chartAt (EuclideanHalfSpace 2) a).source :=
        TangentBundle.trivializationAt_baseSet (I:=𝓡∂ 2) a
      refine ⟨v,hbase ▸ hs,?_⟩
      intro x hx
      have hc := TangentBundle.continuousLinearMapAt_trivializationAt (I:=𝓡∂ 2) (x₀:=a) (x:=x) hx
      change mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) a) x (v x)=w
      rw [←hc]
      exact e.continuousLinearMapAt_symmL (hbase.symm ▸ hx) w
    classical
    have hshrink (z : Circle) : ∃ U : Set F.surface, IsOpen U ∧ F.boundary.toFun z∈U ∧
        closure U⊆(chartAt (EuclideanHalfSpace 2) (F.boundary.toFun z)).source := by
      obtain ⟨U,hU,hz,hsub⟩ := isCompact_singleton.exists_isOpen_closure_subset
        ((chartAt (EuclideanHalfSpace 2) (F.boundary.toFun z)).open_source.mem_nhdsSet.mpr
          (singleton_subset_iff.mpr (mem_chart_source _ _)))
      exact ⟨U,hU,hz (mem_singleton _),hsub⟩
    choose U hU hUm hUc using hshrink
    have hbd : IsCompact F.surface.boundary := by
      rw [←F.boundary_covers]
      exact isCompact_range F.boundary.smoothEmbedding.isEmbedding.continuous
    have hcov : F.surface.boundary⊆⋃ z : Circle, U z := by
      rintro x hx
      rw [←F.boundary_covers] at hx
      obtain ⟨z,rfl⟩ := hx
      exact mem_iUnion.mpr ⟨z,hUm z⟩
    obtain ⟨sf,hsf⟩ := hbd.elim_finite_subcover U hU hcov
    let count := Fintype.card ↥sf
    let en : Fin count ≃ ↥sf := (Fintype.equivFin ↥sf).symm
    let a : Fin count → F.surface := fun i => F.boundary.toFun (en i).val
    let V : Fin count → Set F.surface := fun i => U (en i).val
    have hVo (i : Fin count) : IsOpen (V i) := hU _
    have hVc (i : Fin count) : closure (V i)⊆(chartAt (EuclideanHalfSpace 2) (a i)).source := hUc _
    have hcover : F.surface.boundary⊆⋃ i, V i := by
      intro x hx
      obtain ⟨z,hz,hxz⟩ := mem_iUnion₂.mp (hsf hx)
      let i := en.symm ⟨z,hz⟩
      apply mem_iUnion.mpr
      refine ⟨i,?_⟩
      change x∈U (en (en.symm ⟨z,hz⟩)).val
      rw [en.apply_symm_apply]
      exact hxz
    obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡∂ 2)
      ((𝓡∂ 2).isClosed_boundary (n:=∞) (by simp)) V hVo hcover
    choose v hv hn using fun i => hlocal F (a i)
    let field : (x : F.surface) → TangentSpace (𝓡∂ 2) x := fun x => ∑ i,ρ i x • v i x
    have hs : ContMDiff (𝓡∂ 2) (𝓡∂ 2).tangent ∞
        (fun x => (⟨x,field x⟩ : TangentBundle (𝓡∂ 2) F.surface)) := by
      apply ContMDiff.sum_section
      intro i _
      exact (ρ i).contMDiff.contMDiffOn.smul_section_of_tsupport
        (chartAt (EuclideanHalfSpace 2) (a i)).open_source
        ((hρ i).trans ((subset_closure).trans (hVc i))) (hv i)
    have hpos (z : Circle) : 0 < inwardCoordinate (F.boundary.toFun z) (field (F.boundary.toFun z)) := by
      let x := F.boundary.toFun z
      have hxb : x∈F.surface.boundary := by rw [←F.boundary_covers]; exact mem_range_self z
      have hp (i : Fin count) (hi : 0<ρ i x) : 0 < inwardCoordinate x (v i x) := by
        have hx : x∈(chartAt (EuclideanHalfSpace 2) (a i)).source :=
          hVc i (subset_closure (hρ i (subset_tsupport _ (ne_of_gt hi))))
        obtain ⟨r,hr,hreq⟩ := inward_coordinate_change_positive x hxb
          (chartAt (EuclideanHalfSpace 2) (a i)) (IsManifold.chart_mem_maximalAtlas _) hx
        have hh := hreq (v i x)
        change (tangentSpaceCastModel 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) (a i) x)
          (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) (a i)) x (v i x))) 0=_ at hh
        rw [hn i x hx] at hh
        have hh' : 1=r*inwardCoordinate x (v i x) := by simpa using hh
        nlinarith
      have hnn (i : Fin count) : 0≤ρ i x * inwardCoordinate x (v i x) := by
        by_cases hi : ρ i x=0
        · rw [hi,zero_mul]
        · exact mul_nonneg (ρ.nonneg i x) (hp i (lt_of_le_of_ne (ρ.nonneg i x) (Ne.symm hi))).le
      obtain ⟨i,hi⟩ := ρ.exists_pos_of_mem hxb
      have hsum : 0<∑ i,ρ i x * inwardCoordinate x (v i x) :=
        Finset.sum_pos' (fun i _ => hnn i) ⟨i,Finset.mem_univ _,mul_pos hi (hp i hi)⟩
      have hform : inwardCoordinate x (field x)=∑ i,ρ i x * inwardCoordinate x (v i x) := by
        let ell : TangentSpace (𝓡∂ 2) x →L[ℝ] ℝ := (EuclideanSpace.proj 0).comp
          ((tangentSpaceCastModel 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) x x)).toContinuousLinearMap.comp
            (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) x) x))
        change ell (∑ i,ρ i x • v i x)=∑ i,ρ i x * ell (v i x)
        rw [map_sum]
        simp only [map_smul,smul_eq_mul]
      change 0 < inwardCoordinate x (field x)
      rw [hform]
      exact hsum
    refine ⟨count,a,V,v,ρ,hVo,hVc,?_,hρ,hv,hn,hs,hpos⟩
    intro z
    have hz : F.boundary.toFun z∈F.surface.boundary := by rw [←F.boundary_covers]; exact mem_range_self z
    exact mem_iUnion.mp (hcover hz)
  have hlower {K : OrientedKnot} (F : SphereSpanningSurface.{0} K)
      (count : ℕ) (a : Fin count → F.surface) (U : Fin count → Set F.surface)
      (hUc : ∀ i, closure (U i)⊆(chartAt (EuclideanHalfSpace 2) (a i)).source)
      (field : (x : F.surface) → TangentSpace (𝓡∂ 2) x)
      (hs : ContMDiff (𝓡∂ 2) (𝓡∂ 2).tangent ∞
        (fun x => (⟨x,field x⟩ : TangentBundle (𝓡∂ 2) F.surface)))
      (hp : ∀ z, 0 < inwardCoordinate (F.boundary.toFun z) (field (F.boundary.toFun z))) :
      ∃ r : ℝ, 0<r ∧ ∀ i z, F.boundary.toFun z∈closure (U i) →
        r≤(tangentSpaceCastModel 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) (a i) (F.boundary.toFun z))
          (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) (a i))
            (F.boundary.toFun z) (field (F.boundary.toFun z)))) 0 := by
    classical
    have hi (i : Fin count) : ∃ r : ℝ, 0<r ∧ ∀ z, F.boundary.toFun z∈closure (U i) →
        r≤(tangentSpaceCastModel 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) (a i) (F.boundary.toFun z))
          (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) (a i))
            (F.boundary.toFun z) (field (F.boundary.toFun z)))) 0 := by
      let e := trivializationAt (Euc 2) (TangentSpace (𝓡∂ 2)) (a i)
      let f : F.surface → ℝ := fun x => ((e (⟨x,field x⟩ : TangentBundle (𝓡∂ 2) F.surface)).2) 0
      have hbase : e.baseSet=(chartAt (EuclideanHalfSpace 2) (a i)).source :=
        TangentBundle.trivializationAt_baseSet (I:=𝓡∂ 2) (a i)
      have hf : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,ℝ) ∞ f e.baseSet := by
        apply (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin 2)).contMDiff.comp_contMDiffOn
        exact e.contMDiffOn_section_baseSet_iff.mp hs.contMDiffOn
      have hformula (x : F.surface) (hx : x∈(chartAt (EuclideanHalfSpace 2) (a i)).source) :
          f x=(tangentSpaceCastModel 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) (a i) x)
            (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) (a i)) x (field x))) 0 := by
        have hc := TangentBundle.continuousLinearMapAt_trivializationAt (I:=𝓡∂ 2) (x₀:=a i) hx
        have he := e.continuousLinearMapAt_apply_of_mem ℝ (hbase.symm ▸ hx) (field x)
        change e.continuousLinearMapAt ℝ x (field x)=(e (⟨x,field x⟩ : TangentBundle (𝓡∂ 2) F.surface)).2 at he
        rw [hc] at he
        change f x=(show Euc 2 from mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) (a i)) x (field x)) 0
        exact congrArg (fun v : Euc 2 => v 0) he.symm
      let S := closure (U i) ∩ F.surface.boundary
      have hS : IsCompact S := isClosed_closure.isCompact.inter_right
        ((𝓡∂ 2).isClosed_boundary (n:=∞) (by simp))
      have hSe : S⊆e.baseSet := fun x hx => hbase.symm ▸ hUc i hx.1
      have hpos (x : F.surface) (hx : x∈S) : 0<f x := by
        obtain ⟨z,hz⟩ : x∈range F.boundary.toFun := by rw [F.boundary_covers]; exact hx.2
        have hxchart := hUc i hx.1
        obtain ⟨r,hr,hreq⟩ := inward_coordinate_change_positive x hx.2
          (chartAt (EuclideanHalfSpace 2) (a i)) (IsManifold.chart_mem_maximalAtlas _) hxchart
        rw [hformula x hxchart]
        have hreq := hreq (field x)
        change (tangentSpaceCastModel 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) (a i) x)
          (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) (a i)) x (field x))) 0=_ at hreq
        rw [hreq]
        exact mul_pos hr (hz ▸ hp z)
      by_cases hne : S.Nonempty
      · obtain ⟨x,hx,hmin⟩ := hS.exists_isMinOn hne (hf.continuousOn.mono hSe)
        refine ⟨f x,hpos x hx,?_⟩
        intro z hz
        have hb := F.boundary.lands_boundary z
        rw [←hformula _ (hUc i hz)]
        exact hmin ⟨hz,hb⟩
      · refine ⟨1,by norm_num,?_⟩
        intro z hz
        exact (hne ⟨F.boundary.toFun z,hz,F.boundary.lands_boundary z⟩).elim
    choose ri hri hbound using hi
    by_cases hn : Nonempty (Fin count)
    · letI := hn
      let r := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin count)).Nonempty) ri
      refine ⟨r,?_,?_⟩
      · exact (Finset.lt_inf'_iff (Finset.univ_nonempty : (Finset.univ : Finset (Fin count)).Nonempty)).mpr (fun i _ => hri i)
      · intro i z hz
        exact (Finset.inf'_le _ (Finset.mem_univ i)).trans (hbound i z hz)
    · refine ⟨1,by norm_num,?_⟩
      intro i
      exact (hn ⟨i⟩).elim
  obtain ⟨count,a,U,v,ρ,hU,hUc,hcov,hρ,hv,hn,hs,hp⟩ := hdata F
  let field : (x : F.surface) → TangentSpace (𝓡∂ 2) x := fun x => ∑ i,ρ i x • v i x
  obtain ⟨r,hr,hbound⟩ := hlower F count a U hUc field hs hp
  exact ⟨{ field := field
           smooth := hs
           positive := hp
           lower := r
           lower_pos := hr
           count := count
           chart := fun i => chartAt (EuclideanHalfSpace 2) (a i)
           atlas := fun i => IsManifold.chart_mem_maximalAtlas _
           domain := U
           domain_open := hU
           closure_subset := hUc
           boundary_cover := hcov
           localField := v
           local_smooth := hv
           local_normal := hn
           weights := ρ
           supports := hρ
           weighted := fun _ => rfl
           lower_bound := hbound }⟩

structure C4LocalFlow {K : OrientedKnot} {F : SphereSpanningSurface.{0} K} (X : C3InwardField F) where
  d : ℝ
  d_pos : 0 < d
  localDomain : Fin X.count → Set (Euc 2)
  local_open : ∀ i, IsOpen (localDomain i)
  local_contains : ∀ i z, F.boundary.toFun z ∈ X.domain i →
    (X.chart i).extend (𝓡∂ 2) (F.boundary.toFun z) ∈ localDomain i
  coordinateField : Fin X.count → Euc 2 → Euc 2
  coordinate_smooth : ∀ i, ContDiffOn ℝ ∞ (coordinateField i) (localDomain i)
  coordinate_agrees : ∀ i x, x ∈ X.domain i →
    coordinateField i ((X.chart i).extend (𝓡∂ 2) x) =
      tangentSpaceCastModel 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2) x)
        (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2)) x (X.field x))
  localFlow : Fin X.count → Euc 2 × ℝ → Euc 2
  local_smooth : ∀ i, ContDiffOn ℝ ∞ (localFlow i) (localDomain i ×ˢ Ioo (-d) d)
  local_zero : ∀ i q, q ∈ localDomain i → localFlow i (q,0)=q
  local_ode : ∀ i q t, q ∈ localDomain i → |t|<d →
    HasDerivAt (fun s => localFlow i (q,s))
      (coordinateField i (localFlow i (q,t))) t
  local_unique : ∀ i (q : Euc 2) (curve : ℝ → Euc 2), q ∈ localDomain i →
    curve 0=q → (∀ t ∈ Ioo (-d) d, curve t ∈ localDomain i) →
    (∀ t ∈ Ioo (-d) d, HasDerivAt curve (coordinateField i (curve t)) t) →
    EqOn curve (fun t => localFlow i (q,t)) (Ioo (-d) d)
  flow : Circle × ℝ → F.surface
  local_realization : ∀ i z t, F.boundary.toFun z ∈ X.domain i → 0≤t → t<d →
    flow (z,t) ∈ (X.chart i).source ∧
      (X.chart i).extend (𝓡∂ 2) (flow (z,t)) =
        localFlow i ((X.chart i).extend (𝓡∂ 2) (F.boundary.toFun z),t)
  normal_velocity : ∀ i z t, F.boundary.toFun z ∈ X.domain i → 0≤t → t<d →
    X.lower/2 ≤ (coordinateField i
      (localFlow i ((X.chart i).extend (𝓡∂ 2) (F.boundary.toFun z),t))) 0
  overlap : ∀ i j z t, F.boundary.toFun z ∈ X.domain i →
    F.boundary.toFun z ∈ X.domain j → 0≤t → t<d →
    (X.chart i).symm ((𝓡∂ 2).symm
      (localFlow i ((X.chart i).extend (𝓡∂ 2) (F.boundary.toFun z),t))) =
    (X.chart j).symm ((𝓡∂ 2).symm
      (localFlow j ((X.chart j).extend (𝓡∂ 2) (F.boundary.toFun z),t)))
  zero : ∀ z, flow (z,0) = F.boundary.toFun z
  interior : ∀ z t, 0 < t → t < d → flow (z,t) ∉ F.surface.boundary
  smooth : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 2) ∞ flow {p | 0 ≤ p.2 ∧ p.2 < d}
  tangent : ∀ z t, 0 ≤ t → t < d →
    mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 2) (fun s => flow (z,s)) (Ici 0) t
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) t).symm 1) = X.field (flow (z,t))
theorem C4_local_flow {K : OrientedKnot} {F : SphereSpanningSurface.{0} K}
    (X : C3InwardField F) : Nonempty (C4LocalFlow X) := by
  have hchart (i : Fin X.count) :
      ∃ L : Set F.surface, IsCompact L ∧ closure (X.domain i) ⊆ interior L ∧ L ⊆ (X.chart i).source ∧
      ∃ G : Euc 2 → Euc 2, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
        (∀ x ∈ L,G ((X.chart i).extend (𝓡∂ 2) x)=
          tangentSpaceCastModel 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2) x)
            (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2)) x (X.field x))) ∧
      ∃ Φ : Euc 2 × ℝ → Euc 2,ContDiff ℝ ∞ Φ ∧
        (∀ q,Φ (q,0)=q) ∧ (∀ q t,HasDerivAt (fun s => Φ (q,s)) (G (Φ (q,t))) t) ∧
        (∀ (q : Euc 2) (curve : ℝ → Euc 2) (d : ℝ),0 < d → curve 0=q →
          (∀ t ∈ Ioo (-d) d,HasDerivAt curve (G (curve t)) t) →
          EqOn curve (fun t => Φ (q,t)) (Ioo (-d) d)) ∧
      ∃ d : ℝ,0 < d ∧ ∀ x ∈ closure (X.domain i) ∩ F.surface.boundary,∀ t,0 ≤ t → t < d →
        Φ ((X.chart i).extend (𝓡∂ 2) x,t) ∈ ((X.chart i).extend (𝓡∂ 2)).target ∧
        ((X.chart i).extend (𝓡∂ 2)).symm (Φ ((X.chart i).extend (𝓡∂ 2) x,t)) ∈ interior L ∧
        X.lower/2 ≤ G (Φ ((X.chart i).extend (𝓡∂ 2) x,t)) 0 ∧
        (0 < t → 0 < Φ ((X.chart i).extend (𝓡∂ 2) x,t) 0) ∧
        HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 2)
          (fun s => ((X.chart i).extend (𝓡∂ 2)).symm (Φ ((X.chart i).extend (𝓡∂ 2) x,s))) (Ici 0) t
          ((1:ℝ →L[ℝ] ℝ).smulRight
            (X.field (((X.chart i).extend (𝓡∂ 2)).symm (Φ ((X.chart i).extend (𝓡∂ 2) x,t))))) := by
    have hext (i : Fin X.count) (S : Set F.surface) (hS : IsCompact S)
        (hSc : S ⊆ (X.chart i).source) :
        ∃ G : Euc 2 → Euc 2, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
          ∀ x ∈ S, G ((X.chart i).extend (𝓡∂ 2) x) =
            tangentSpaceCastModel 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2) x)
              (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2)) x (X.field x)) := by
      let c := X.chart i
      let e := c.extend (𝓡∂ 2)
      have he_source : e.source=c.source := c.extend_source
      let v : F.surface → Euc 2 := fun x => tangentSpaceCastModel 𝓘(ℝ,Euc 2) (e x)
        (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) e x (X.field x))
      have hv : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,Euc 2) ∞ v c.source := by
        have hf : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,Euc 2) ∞ e c.source := c.contMDiffOn_extend (X.atlas i)
        have hT : ContMDiffOn (𝓡∂ 2).tangent (𝓘(ℝ,Euc 2)).tangent ∞
            (tangentMapWithin (𝓡∂ 2) 𝓘(ℝ,Euc 2) e c.source)
            (Bundle.TotalSpace.proj ⁻¹' c.source) :=
          hf.contMDiffOn_tangentMapWithin (by simp) c.open_source.uniqueMDiffOn
        have hsection := hT.comp X.smooth.contMDiffOn (fun x hx => hx)
        have hread := (contMDiff_snd_tangentBundle_modelSpace (Euc 2) 𝓘(ℝ,Euc 2) (n:=∞)).comp_contMDiffOn hsection
        apply hread.congr
        intro x hx
        change (show Euc 2 from mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) e x (X.field x))=
          (show Euc 2 from mfderivWithin (𝓡∂ 2) 𝓘(ℝ,Euc 2) e c.source x (X.field x))
        rw [mfderivWithin_eq_mfderiv (c.open_source.uniqueMDiffWithinAt hx)
          ((c.contMDiffAt_extend (X.atlas i) hx).mdifferentiableAt (by simp))]
      have hes : ContMDiffOn 𝓘(ℝ,Euc 2) (𝓡∂ 2) ∞ e.symm e.target := by
        rw [c.extend_target']
        exact contMDiffOn_extend_symm (X.atlas i)
      have hvE : ContDiffOn ℝ ∞ (v ∘ e.symm) e.target :=
        (hv.comp hes (fun _ hx => he_source ▸ e.map_target hx)).contDiffOn
      let L : Euc 2 ≃L[ℝ] ℝ × ℝ := (EuclideanSpace.equiv (Fin 2) ℝ).trans
        (LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv
      have hL0 (q : Euc 2) : (L q).1=q 0 := rfl
      have hLi0 (q : ℝ × ℝ) : (L.symm q) 0=q.1 := by
        have hh := congrArg Prod.fst (L.apply_symm_apply q)
        exact hh
      let U : Set (ℝ × ℝ) := L.symm ⁻¹' ((𝓡∂ 2).symm ⁻¹' c.target)
      have hU : IsOpen U := (c.open_target.preimage (𝓡∂ 2).continuous_symm).preimage L.symm.continuous
      have heq : L.symm ⁻¹' e.target = (Ici 0 ×ˢ univ) ∩ U := by
        ext q
        rw [mem_preimage,c.extend_target,mem_inter_iff,range_modelWithCornersEuclideanHalfSpace]
        change ((_ ∈ c.target) ∧ 0 ≤ (L.symm q) 0) ↔ ((0 ≤ q.1 ∧ q.2 ∈ (univ:Set ℝ)) ∧ _)
        rw [hLi0]
        simp only [mem_univ,true_and,and_true,and_comm,U,mem_preimage]
      let vP : ℝ × ℝ → Euc 2 := (v ∘ e.symm) ∘ L.symm
      have hvP : ContDiffOn ℝ ∞ vP ((Ici 0 ×ˢ univ) ∩ U) := by
        rw [←heq]
        exact hvE.comp L.symm.contDiff.contDiffOn (fun _ hx => hx)
      have hloc (x : F.surface) (hx : x ∈ S) :
          ∃ W ∈ 𝓝 (e x), ∃ G : Euc 2 → Euc 2, ContDiffOn ℝ ∞ G W ∧
            ∀ y ∈ S, e y ∈ W → G (e y)=v y := by
        have hxt : e x ∈ e.target := e.map_source (he_source.symm ▸ hSc hx)
        have hpx : L (e x) ∈ U := by
          have h := congrArg (fun A : Set (ℝ × ℝ) => L (e x) ∈ A) heq
          have hh : L (e x) ∈ L.symm ⁻¹' e.target := by simpa using hxt
          exact (heq ▸ hh).2
        obtain ⟨G,hG,hGeq⟩ := hvP.exists_contDiff_extension_Ici_prod_nhdsWithin hU hpx
        obtain ⟨W,hW,hWeq⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hGeq
        refine ⟨L ⁻¹' W,L.continuous.continuousAt.preimage_mem_nhds hW,G ∘ L,
          (hG.comp L.contDiff).contDiffOn,?_⟩
        intro y hy hey
        have hyhalf : L (e y) ∈ Ici 0 ×ˢ univ := by
          have hyt := e.map_source (he_source.symm ▸ hSc hy)
          have hh : L (e y) ∈ L.symm ⁻¹' e.target := by simpa using hyt
          exact (heq ▸ hh).1
        have h := hWeq ⟨hey,hyhalf⟩
        change G (L (e y)) = v y
        change G (L (e y)) = (v ∘ e.symm) (L.symm (L (e y))) at h
        simpa only [L.symm_apply_apply,Function.comp_apply,e.left_inv (he_source.symm ▸ hSc hy)] using h
      have hecont : ContinuousOn e S := by
        apply c.continuousOn_extend.mono
        intro x hx
        exact he_source.symm ▸ hSc hx
      have himage : IsCompact (e '' S) := hS.image_of_continuousOn hecont
      obtain ⟨G,hG,hGeq⟩ := DifferentialGeometry.Analysis.exists_contDiff_extension_of_local himage.isClosed hloc
      obtain ⟨χ,hχ,hχcomp,hχone,_,_⟩ := DifferentialGeometry.Analysis.exists_bump_compact
        himage isOpen_univ (subset_univ _)
      refine ⟨fun q => χ q • G q,hχ.smul hG,hχcomp.smul_right,?_⟩
      intro x hx
      have hχx : χ (e x)=1 := (hχone.filter_mono (nhds_le_nhdsSet ⟨x,hx,rfl⟩)).self_of_nhds
      change χ (e x) • G (e x)=v x
      rw [hχx,one_smul]
      exact hGeq hx
    have hflow (G : Euc 2 → Euc 2) (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) :
        ∃ Φ : Euc 2 × ℝ → Euc 2, ContDiff ℝ ∞ Φ ∧
          (∀ q,Φ (q,0)=q) ∧
          (∀ q t,HasDerivAt (fun s => Φ (q,s)) (G (Φ (q,t))) t) ∧
          (∀ (q : Euc 2) (curve : ℝ → Euc 2) (d : ℝ),0 < d → curve 0=q →
            (∀ t ∈ Ioo (-d) d,HasDerivAt curve (G (curve t)) t) →
            EqOn curve (fun t => Φ (q,t)) (Ioo (-d) d)) := by
      let v : (x : Euc 2) → TangentSpace 𝓘(ℝ,Euc 2) x := G
      have hv : ContMDiff 𝓘(ℝ,Euc 2) (𝓘(ℝ,Euc 2)).tangent ∞
          (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,Euc 2) (Euc 2))) := by
        intro x
        exact contMDiffAt_vectorSpace_iff_contDiffAt.mpr hG.contDiffAt
      have hvc : IsCompact (tsupport v) := hGc
      let hc := exists_globalIntegralCurve_of_compactSupport v hv hvc
      let Φ : Euc 2 × ℝ → Euc 2 := fun p => curveAt v hc p.1 p.2
      have hΦ : ContDiff ℝ ∞ Φ := by
        have h := contMDiff_globalFlow_joint_of_compactSupport v hv hvc
        have hswap : ContMDiff ((𝓘(ℝ,Euc 2)).prod 𝓘(ℝ,ℝ))
            ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Euc 2)) ∞ (fun p : Euc 2 × ℝ => (p.2,p.1)) :=
          contMDiff_snd.prodMk contMDiff_fst
        have h' := h.comp hswap
        rw [←modelWithCornersSelf_prod] at h'
        rw [chartedSpaceSelf_prod] at h'
        exact h'.contDiff
      have hzero (q : Euc 2) : Φ (q,0)=q := curveAt_zero v hc q
      have hder (q : Euc 2) (t : ℝ) : HasDerivAt (fun s => Φ (q,s)) (G (Φ (q,t))) t := by
        have h := curveAt_integralCurve v hc q t
        have h' : HasFDerivAt (fun s => Φ (q,s)) ((1:ℝ →L[ℝ] ℝ).smulRight (G (Φ (q,t)))) t := h.hasFDerivAt
        simpa only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.one_apply,one_smul] using h'.hasDerivAt
      refine ⟨Φ,hΦ,hzero,hder,?_⟩
      intro q curve d hd hq hcurve
      have hγ : IsMIntegralCurveOn curve v (Ioo (-d) d) := by
        intro t ht
        exact (hcurve t ht).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
      have hγ' := (curveAt_integralCurve v hc q).isMIntegralCurveOn (Ioo (-d) d)
      exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        (t₀:=0) (by constructor <;> linarith) (hv.of_le (by simp)) hγ hγ'
        (hq.trans (hzero q).symm)
    have huniform (A : Set (Euc 2)) (hA : IsOpen A) (K : Set (Euc 2)) (hK : IsCompact K)
        (hKA : K ⊆ A) (G : Euc 2 → Euc 2) (hG : Continuous G)
        (lower : ℝ) (hlower : 0 < lower) (hbound : ∀ q ∈ K,lower ≤ G q 0)
        (Φ : Euc 2 × ℝ → Euc 2) (hΦ : Continuous Φ) (hzero : ∀ q,Φ (q,0)=q) :
        ∃ d : ℝ,0 < d ∧ ∀ q ∈ K,∀ t,|t| < d →
          Φ (q,t) ∈ A ∧ lower/2 ≤ G (Φ (q,t)) 0 := by
      have hΨ : Continuous (fun p : ℝ × Euc 2 => Φ (p.2,p.1)) :=
        hΦ.comp (continuous_snd.prodMk continuous_fst)
      have hv : Continuous (fun p : ℝ × Euc 2 => G (Φ (p.2,p.1)) 0) :=
        (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin 2)).continuous.comp (hG.comp hΨ)
      have hev : ∀ᶠ t in 𝓝 (0:ℝ),∀ q ∈ K,
          Φ (q,t) ∈ A ∧ lower/2 < G (Φ (q,t)) 0 :=
        hK.eventually_forall_of_forall_eventually (fun q hq => by
          have hm : Φ (q,0) ∈ A := (hzero q).symm ▸ hKA hq
          have hb : lower/2 < G (Φ (q,0)) 0 := by rw [hzero]; linarith [hbound q hq]
          have h1 : ∀ᶠ p : ℝ × Euc 2 in 𝓝 (0,q),Φ (p.2,p.1) ∈ A :=
            (hΨ.continuousAt (x:=(0,q))).preimage_mem_nhds (hA.mem_nhds hm)
          have h2 : ∀ᶠ p : ℝ × Euc 2 in 𝓝 (0,q),lower/2 < G (Φ (p.2,p.1)) 0 :=
            (hv.continuousAt (x:=(0,q))).eventually_const_lt hb
          exact h1.and h2)
      obtain ⟨d,hd,hds⟩ := Metric.mem_nhds_iff.mp hev
      refine ⟨d,hd,?_⟩
      intro q hq t ht
      have htmem : t ∈ Metric.ball (0:ℝ) d := by
        simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht
      exact ⟨(hds htmem q hq).1,(hds htmem q hq).2.le⟩
    have hpositive (G : Euc 2 → Euc 2) (Φ : Euc 2 × ℝ → Euc 2)
        (hzero : ∀ q,Φ (q,0)=q)
        (hder : ∀ q t,HasDerivAt (fun s => Φ (q,s)) (G (Φ (q,t))) t)
        (q : Euc 2) (hq : q 0=0) (d lower : ℝ) (hlower : 0 < lower)
        (hv : ∀ t,|t| < d → lower/2 ≤ G (Φ (q,t)) 0)
        (t : ℝ) (ht : 0 ≤ t) (htd : t < d) :
        lower/2*t ≤ Φ (q,t) 0 ∧ (0 < t → 0 < Φ (q,t) 0) := by
      let f : ℝ → ℝ := fun s => Φ (q,s) 0
      have hfder (s : ℝ) : HasDerivAt f (G (Φ (q,s)) 0) s :=
        (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin 2)).hasFDerivAt.comp_hasDerivAt s (hder q s)
      have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun s => (hfder s).continuousAt)
      have hdiff : Differentiable ℝ f := fun s => (hfder s).differentiableAt
      have hbound : ∀ s ∈ interior (Icc (0:ℝ) t),lower/2 ≤ deriv f s := by
        intro s hs
        have hs' : s ∈ Icc (0:ℝ) t := interior_subset hs
        rw [(hfder s).deriv]
        apply hv
        rw [abs_of_nonneg hs'.1]
        exact hs'.2.trans_lt htd
      have hh := (convex_Icc (0:ℝ) t).mul_sub_le_image_sub_of_le_deriv
        hcont.continuousOn hdiff.differentiableOn hbound 0 ⟨le_rfl,ht⟩ t ⟨ht,le_rfl⟩ ht
      have hzero' : f 0=0 := by change Φ (q,0) 0=0;rw[hzero,hq]
      have hh' : lower/2*t ≤ Φ (q,t) 0 := by simpa only [sub_zero,hzero',f] using hh
      exact ⟨hh',fun htpos => (mul_pos (half_pos hlower) htpos).trans_le hh'⟩
    have hdecode (i : Fin X.count) (γ : ℝ → Euc 2) (G : Euc 2 → Euc 2) (d : ℝ)
        (hγ : ∀ t,HasDerivAt γ (G (γ t)) t)
        (hmap : ∀ t,0 ≤ t → t < d → γ t ∈ ((X.chart i).extend (𝓡∂ 2)).target)
        (hagrees : ∀ t,0 ≤ t → t < d → G (γ t)=
          tangentSpaceCastModel 𝓘(ℝ,Euc 2) (γ t)
            (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2))
              (((X.chart i).extend (𝓡∂ 2)).symm (γ t))
              (X.field (((X.chart i).extend (𝓡∂ 2)).symm (γ t)))))
        (t : ℝ) (ht : 0 ≤ t) (htd : t < d) :
        HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 2)
          (fun s => ((X.chart i).extend (𝓡∂ 2)).symm (γ s)) (Ici 0) t
          ((1:ℝ →L[ℝ] ℝ).smulRight
            (X.field (((X.chart i).extend (𝓡∂ 2)).symm (γ t)))) := by
      have heval (i : Fin X.count) (γ : ℝ → Euc 2) (G : Euc 2 → Euc 2) (d : ℝ)
        (hγ : ∀ t,HasDerivAt γ (G (γ t)) t)
        (hmap : ∀ t,0 ≤ t → t < d → γ t ∈ ((X.chart i).extend (𝓡∂ 2)).target)
        (hagrees : ∀ t,0 ≤ t → t < d → G (γ t)=
          tangentSpaceCastModel 𝓘(ℝ,Euc 2) (γ t)
            (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2))
              (((X.chart i).extend (𝓡∂ 2)).symm (γ t))
              (X.field (((X.chart i).extend (𝓡∂ 2)).symm (γ t)))))
        (t : ℝ) (ht : 0 ≤ t) (htd : t < d) :
        mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 2)
          (fun s => ((X.chart i).extend (𝓡∂ 2)).symm (γ s)) (Ici 0) t
          ((tangentSpaceCastModel 𝓘(ℝ,ℝ) t).symm 1) =
            X.field (((X.chart i).extend (𝓡∂ 2)).symm (γ t))  := by
        let c := X.chart i
        let e := c.extend (𝓡∂ 2)
        have he : c ∈ IsManifold.maximalAtlas (𝓡∂ 2) 1 F.surface :=
          IsManifold.maximalAtlas_subset_of_le (by simp) (X.atlas i)
        have hs : MDifferentiableWithinAt 𝓘(ℝ,Euc 2) (𝓡∂ 2) e.symm (range (𝓡∂ 2)) (γ t) :=
          mdifferentiableWithinAt_extend_symm he (hmap t ht htd)
        have hγ' : HasMFDerivWithinAt 𝓘(ℝ,ℝ) 𝓘(ℝ,Euc 2) γ (Ici 0 ∩ Iio d) t
            ((1:ℝ →L[ℝ] ℝ).smulRight (G (γ t))) :=
          (hγ t).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
        have hc := hs.hasMFDerivWithinAt.comp t hγ' (fun s hs =>
          c.extend_target_subset_range (hmap s hs.1 hs.2))
        have hc' := (hasMFDerivWithinAt_inter (Iio_mem_nhds htd)).mp hc
        have huni := ((uniqueDiffOn_Ici (0:ℝ)) t ht).uniqueMDiffWithinAt
        have hh := hc'.mfderivWithin huni
        change (mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 2) (e.symm ∘ γ) (Ici 0) t)
          ((tangentSpaceCastModel 𝓘(ℝ,ℝ) t).symm 1) = X.field (e.symm (γ t))
        rw [hh]
        have heval :
            (mfderivWithin 𝓘(ℝ,Euc 2) (𝓡∂ 2) e.symm (range (𝓡∂ 2)) (γ t) ∘L
              ((1:ℝ →L[ℝ] ℝ).smulRight (G (γ t))))
              ((tangentSpaceCastModel 𝓘(ℝ,ℝ) t).symm 1) =
            mfderivWithin 𝓘(ℝ,Euc 2) (𝓡∂ 2) e.symm (range (𝓡∂ 2)) (γ t) (G (γ t)) := by
          change mfderivWithin 𝓘(ℝ,Euc 2) (𝓡∂ 2) e.symm (range (𝓡∂ 2)) (γ t)
            ((1:ℝ) • G (γ t)) = _
          rw [one_smul]
        erw [heval]
        rw [hagrees t ht htd]
        have hInv := mfderivWithin_extend_symm_comp_mfderiv_extend he (hmap t ht htd)
        have hv := congrArg (fun L => L (X.field (e.symm (γ t)))) hInv
        change mfderivWithin 𝓘(ℝ,Euc 2) (𝓡∂ 2) e.symm (range (𝓡∂ 2)) (γ t)
          (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) e (e.symm (γ t)) (X.field (e.symm (γ t)))) = _
        exact hv
      let c := X.chart i
      let e := c.extend (𝓡∂ 2)
      have he : c ∈ IsManifold.maximalAtlas (𝓡∂ 2) 1 F.surface :=
        IsManifold.maximalAtlas_subset_of_le (by simp) (X.atlas i)
      have hs := mdifferentiableWithinAt_extend_symm he (hmap t ht htd)
      have hγ' : HasMFDerivWithinAt 𝓘(ℝ,ℝ) 𝓘(ℝ,Euc 2) γ (Ici 0 ∩ Iio d) t
          ((1:ℝ →L[ℝ] ℝ).smulRight (G (γ t))) :=
        (hγ t).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
      have hc := hs.hasMFDerivWithinAt.comp t hγ' (fun s hs =>
        c.extend_target_subset_range (hmap s hs.1 hs.2))
      have hc' := (hasMFDerivWithinAt_inter (Iio_mem_nhds htd)).mp hc
      have huni := ((uniqueDiffOn_Ici (0:ℝ)) t ht).uniqueMDiffWithinAt
      have hdt := hc'.mdifferentiableWithinAt.hasMFDerivWithinAt
      apply hdt.congr_mfderiv
      apply ContinuousLinearMap.ext
      intro r
      let r0 : ℝ := r
      have hr : r = r0 • ((tangentSpaceCastModel 𝓘(ℝ,ℝ) t).symm 1) := by
        change r0=r0*(1:ℝ)
        exact (mul_one r0).symm
      calc
        mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 2) (e.symm ∘ γ) (Ici 0) t r =
            mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 2) (e.symm ∘ γ) (Ici 0) t
              (r0 • ((tangentSpaceCastModel 𝓘(ℝ,ℝ) t).symm 1)) := congrArg _ hr
        _ = r0 • mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 2) (e.symm ∘ γ) (Ici 0) t
              ((tangentSpaceCastModel 𝓘(ℝ,ℝ) t).symm 1) := map_smul _ _ _
        _ = r0 • X.field (e.symm (γ t)) := congrArg (fun v => r0 • v) (heval i γ G d hγ hmap hagrees t ht htd)
        _ = ((1:ℝ →L[ℝ] ℝ).smulRight (X.field (e.symm (γ t)))) r := rfl
    have hzeroChart (i : Fin X.count) (x : F.surface) (hx : x ∈ F.surface.boundary)
        (hxc : x ∈ (X.chart i).source) : ((X.chart i).extend (𝓡∂ 2) x) 0=0 := by
      let c := X.chart i
      let e' : PartialDiffeomorph (𝓡∂ 2) (𝓡∂ 2) F.surface (EuclideanHalfSpace 2) ∞ :=
        { __ := c.toPartialEquiv
          open_source := c.open_source
          open_target := c.open_target
          contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas (X.atlas i)
          contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas (X.atlas i) }
      have hd : IsLocalDiffeomorphAt (𝓡∂ 2) (𝓡∂ 2) ∞ c x :=
        ⟨e',hxc,fun _ _ => rfl⟩
      have hb := (hd.isBoundaryPoint_iff (by simp)).mp hx
      simpa [ModelWithCorners.IsBoundaryPoint,extChartAt,
        frontier_range_modelWithCornersEuclideanHalfSpace,eq_comm] using hb
    let c := X.chart i
    let e := c.extend (𝓡∂ 2)
    have hclos : IsCompact (closure (X.domain i)) := isClosed_closure.isCompact
    obtain ⟨L,hL,hDom,hLc⟩ := exists_compact_between hclos c.open_source (X.closure_subset i)
    obtain ⟨G,hG,hGc,hGeq⟩ := hext i L hL hLc
    obtain ⟨Φ,hΦ,hΦzero,hΦder,hΦunique⟩ := hflow G hG hGc
    let V := c '' interior L
    have hVo : IsOpen V := c.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hLc)
    let A : Set (Euc 2) := (𝓡∂ 2).symm ⁻¹' V
    have hAo : IsOpen A := hVo.preimage (𝓡∂ 2).continuous_symm
    let S := closure (X.domain i) ∩ F.surface.boundary
    have hS : IsCompact S := hclos.inter_right ((𝓡∂ 2).isClosed_boundary (n:=∞) (by simp))
    have he_source : e.source=c.source := c.extend_source
    have hecont : ContinuousOn e S := c.continuousOn_extend.mono
      (fun x hx => he_source.symm ▸ X.closure_subset i hx.1)
    have hSI : IsCompact (e '' S) := hS.image_of_continuousOn hecont
    have hSA : e '' S ⊆ A := by
      rintro q ⟨x,hx,rfl⟩
      change (𝓡∂ 2).symm ((𝓡∂ 2) (c x)) ∈ V
      rw [(𝓡∂ 2).left_inv]
      exact ⟨x,hDom hx.1,rfl⟩
    have hbound : ∀ q ∈ e '' S,X.lower ≤ G q 0 := by
      rintro q ⟨x,hx,rfl⟩
      rw [hGeq x (interior_subset (hDom hx.1))]
      obtain ⟨z,hz⟩ : x ∈ range F.boundary.toFun := by rw [F.boundary_covers];exact hx.2
      subst x
      exact X.lower_bound i z hx.1
    obtain ⟨d,hd,hdgood⟩ := huniform A hAo (e '' S) hSI hSA G hG.continuous X.lower X.lower_pos hbound Φ hΦ.continuous hΦzero
    have hgood (x : F.surface) (hx : x ∈ S) (t : ℝ) (ht : 0 ≤ t) (htd : t < d) :
        Φ (e x,t) ∈ e.target ∧ e.symm (Φ (e x,t)) ∈ interior L ∧
        X.lower/2 ≤ G (Φ (e x,t)) 0 ∧ (0 < t → 0 < Φ (e x,t) 0) := by
      have hv (s : ℝ) (hs : |s| < d) : X.lower/2 ≤ G (Φ (e x,s)) 0 := (hdgood (e x) ⟨x,hx,rfl⟩ s hs).2
      have hnormal := hpositive G Φ hΦzero hΦder (e x)
        (hzeroChart i x hx.2 (X.closure_subset i hx.1)) d X.lower X.lower_pos hv t ht htd
      have hrange : Φ (e x,t) ∈ range (𝓡∂ 2) := by
        rw [range_modelWithCornersEuclideanHalfSpace]
        exact (mul_nonneg (half_pos X.lower_pos).le ht).trans hnormal.1
      have hA := (hdgood (e x) ⟨x,hx,rfl⟩ t (by rw [abs_of_nonneg ht];exact htd)).1
      obtain ⟨y,hy,hyq⟩ := hA
      have hyt : y ∈ c.source := hLc (interior_subset hy)
      have htarget : Φ (e x,t) ∈ e.target := by
        rw [c.extend_target]
        refine ⟨?_,hrange⟩
        change (𝓡∂ 2).symm (Φ (e x,t)) ∈ c.target
        rw [←hyq]
        exact c.map_source hyt
      have hdecoder : e.symm (Φ (e x,t))=y := by
        change c.symm ((𝓡∂ 2).symm (Φ (e x,t)))=y
        rw [←hyq,c.left_inv hyt]
      exact ⟨htarget,hdecoder.symm ▸ hy,hv t (by rw [abs_of_nonneg ht];exact htd),hnormal.2⟩
    refine ⟨L,hL,hDom,hLc,G,hG,hGc,hGeq,Φ,hΦ,hΦzero,hΦder,hΦunique,d,hd,?_⟩
    intro x hx t ht htd
    have hgd := hgood x hx t ht htd
    refine ⟨hgd.1,hgd.2.1,hgd.2.2.1,hgd.2.2.2,?_⟩
    apply hdecode i (fun s => Φ (e x,s)) G d (hΦder (e x))
      (fun s hs hsd => (hgood x hx s hs hsd).1) ?_ t ht htd
    intro s hs hsd
    have hgs := hgood x hx s hs hsd
    have hh := hGeq (e.symm (Φ (e x,s))) (interior_subset hgs.2.1)
    erw [e.right_inv hgs.1] at hh
    exact hh
  have hboundaryUnique (i : Fin X.count) (L : Set F.surface) (hLc : L ⊆ (X.chart i).source)
      (x : F.surface) (hx : x ∈ interior L)
      (G : Euc 2 → Euc 2) (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G)
      (hGeq : ∀ y ∈ L,G ((X.chart i).extend (𝓡∂ 2) y)=
        tangentSpaceCastModel 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2) y)
          (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2)) y (X.field y)))
      (γ δ : ℝ → F.surface) (d : ℝ) (hd : 0 < d)
      (hγzero : γ 0=x) (hδzero : δ 0=x)
      (hγ : ∀ t,0 ≤ t → t < d → HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 2) γ (Ici 0) t
        ((1:ℝ →L[ℝ] ℝ).smulRight (X.field (γ t))))
      (hδ : ∀ t,0 ≤ t → t < d → HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 2) δ (Ici 0) t
        ((1:ℝ →L[ℝ] ℝ).smulRight (X.field (δ t))))
      (hγint : ∀ t,0 < t → t < d → γ t ∉ F.surface.boundary) :
      EqOn γ δ (Ici 0 ∩ Iio d) := by
    have hcoordinate (i : Fin X.count) (γ : ℝ → F.surface) (t : ℝ)
        (hγ : HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 2) γ (Ici 0) t
          ((1:ℝ →L[ℝ] ℝ).smulRight (X.field (γ t))))
        (hγc : γ t ∈ (X.chart i).source) :
        HasDerivWithinAt ((X.chart i).extend (𝓡∂ 2) ∘ γ)
          (tangentSpaceCastModel 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2) (γ t))
            (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2)) (γ t) (X.field (γ t))))
          (Ici 0) t := by
      let c := X.chart i
      let e := c.extend (𝓡∂ 2)
      have hc : HasMFDerivAt (𝓡∂ 2) 𝓘(ℝ,Euc 2) e (γ t)
          (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) e (γ t)) :=
        ((c.contMDiffAt_extend (X.atlas i) hγc).mdifferentiableAt (by simp)).hasMFDerivAt
      have hh := hc.comp_hasMFDerivWithinAt t hγ
      have hh' : HasFDerivWithinAt (e ∘ γ)
          ((1:ℝ →L[ℝ] ℝ).smulRight
            (tangentSpaceCastModel 𝓘(ℝ,Euc 2) (e (γ t))
              (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) e (γ t) (X.field (γ t))))) (Ici 0) t := by
        apply hh.hasFDerivWithinAt.congr_fderiv
        apply ContinuousLinearMap.ext
        intro r
        let r0 : ℝ := r
        change mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) e (γ t) (r0 • X.field (γ t)) =
          r0 • mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) e (γ t) (X.field (γ t))
        exact map_smul _ _ _
      simpa only [ContinuousLinearMap.smulRight_apply,one_apply_eq_self,one_smul] using hh'.hasDerivWithinAt
    let c := X.chart i
    let e := c.extend (𝓡∂ 2)
    have hγV : {t | γ t ∈ interior L} ∈ 𝓝[Ici 0] (0:ℝ) :=
      (hγ 0 le_rfl hd).continuousWithinAt.preimage_mem_nhdsWithin
        (isOpen_interior.mem_nhds (hγzero.symm ▸ hx))
    have hδV : {t | δ t ∈ interior L} ∈ 𝓝[Ici 0] (0:ℝ) :=
      (hδ 0 le_rfl hd).continuousWithinAt.preimage_mem_nhdsWithin
        (isOpen_interior.mem_nhds (hδzero.symm ▸ hx))
    obtain ⟨r,hr,hrs⟩ := Metric.mem_nhdsWithin_iff.mp (Filter.inter_mem hγV hδV)
    let b := min (d/2) (r/2)
    have hb : 0 < b := lt_min (half_pos hd) (half_pos hr)
    have hbd : b < d := (min_le_left _ _).trans_lt (by linarith)
    have hbr : b < r := (min_le_right _ _).trans_lt (by linarith)
    have hgood (t : ℝ) (ht : t ∈ Icc 0 b) : γ t ∈ interior L ∧ δ t ∈ interior L := by
      apply hrs
      refine ⟨?_,ht.1⟩
      change dist t 0 < r
      rw [Real.dist_eq,sub_zero,abs_of_nonneg ht.1]
      exact ht.2.trans_lt hbr
    have hγc (t : ℝ) (ht : t ∈ Icc 0 b) : γ t ∈ c.source := hLc (interior_subset (hgood t ht).1)
    have hδc (t : ℝ) (ht : t ∈ Icc 0 b) : δ t ∈ c.source := hLc (interior_subset (hgood t ht).2)
    have hcontγ : ContinuousOn (e ∘ γ) (Icc 0 b) := by
      intro t ht
      exact (c.continuousAt_extend (I:=𝓡∂ 2) (hγc t ht)).comp_continuousWithinAt
        ((hγ t ht.1 (ht.2.trans_lt hbd)).continuousWithinAt.mono (fun s hs => hs.1))
    have hcontδ : ContinuousOn (e ∘ δ) (Icc 0 b) := by
      intro t ht
      exact (c.continuousAt_extend (I:=𝓡∂ 2) (hδc t ht)).comp_continuousWithinAt
        ((hδ t ht.1 (ht.2.trans_lt hbd)).continuousWithinAt.mono (fun s hs => hs.1))
    have hderγ (t : ℝ) (ht : t ∈ Ico 0 b) :
        HasDerivWithinAt (e ∘ γ) (G ((e ∘ γ) t)) (Ici t) t := by
      have hh := hcoordinate i γ t (hγ t ht.1 (ht.2.trans hbd)) (hγc t ⟨ht.1,ht.2.le⟩)
      rw [←hGeq (γ t) (interior_subset (hgood t ⟨ht.1,ht.2.le⟩).1)] at hh
      exact hh.mono (fun s hs => ht.1.trans hs)
    have hderδ (t : ℝ) (ht : t ∈ Ico 0 b) :
        HasDerivWithinAt (e ∘ δ) (G ((e ∘ δ) t)) (Ici t) t := by
      have hh := hcoordinate i δ t (hδ t ht.1 (ht.2.trans hbd)) (hδc t ⟨ht.1,ht.2.le⟩)
      rw [←hGeq (δ t) (interior_subset (hgood t ⟨ht.1,ht.2.le⟩).2)] at hh
      exact hh.mono (fun s hs => ht.1.trans hs)
    obtain ⟨C,hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hGc hG (by simp)
    have heqcoord : EqOn (e ∘ γ) (e ∘ δ) (Icc 0 b) :=
      ODE_solution_unique (v:=fun _ => G) (fun _ => hC) hcontγ hderγ hcontδ hderδ
        (by simp only [Function.comp_apply,hγzero,hδzero])
    have ht0 : b/2 ∈ Icc (0:ℝ) b := ⟨(half_pos hb).le,by linarith⟩
    have heq0 : γ (b/2)=δ (b/2) := e.injOn
      (by simpa only [e,c.extend_source] using hγc (b/2) ht0)
      (by simpa only [e,c.extend_source] using hδc (b/2) ht0) (heqcoord ht0)
    have hγM : IsMIntegralCurveOn γ X.field (Ioo 0 d) := by
      intro t ht
      exact (hγ t ht.1.le ht.2).hasMFDerivAt (Ici_mem_nhds ht.1) |>.hasMFDerivWithinAt
    have hδM : IsMIntegralCurveOn δ X.field (Ioo 0 d) := by
      intro t ht
      exact (hδ t ht.1.le ht.2).hasMFDerivAt (Ici_mem_nhds ht.1) |>.hasMFDerivWithinAt
    have hi : ∀ t ∈ Ioo 0 d,(𝓡∂ 2).IsInteriorPoint (γ t) := fun t ht =>
      (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint (γ t)).mpr (hγint t ht.1 ht.2)
    have heqfull := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff
      (t₀:=b/2) ⟨half_pos hb,(by linarith)⟩ hi (X.smooth.of_le (by simp)) hγM hδM heq0
    intro t ht
    by_cases ht0 : t=0
    · subst t
      exact hγzero.trans hδzero.symm
    · exact heqfull ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),ht.2⟩
  have hzeroChart (i : Fin X.count) (x : F.surface) (hx : x ∈ F.surface.boundary)
      (hxc : x ∈ (X.chart i).source) : ((X.chart i).extend (𝓡∂ 2) x) 0=0 := by
    let c := X.chart i
    let e' : PartialDiffeomorph (𝓡∂ 2) (𝓡∂ 2) F.surface (EuclideanHalfSpace 2) ∞ :=
      { __ := c.toPartialEquiv
        open_source := c.open_source
        open_target := c.open_target
        contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas (X.atlas i)
        contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas (X.atlas i) }
    have hd : IsLocalDiffeomorphAt (𝓡∂ 2) (𝓡∂ 2) ∞ c x :=
      ⟨e',hxc,fun _ _ => rfl⟩
    have hb := (hd.isBoundaryPoint_iff (by simp)).mp hx
    simpa [ModelWithCorners.IsBoundaryPoint,extChartAt,
      frontier_range_modelWithCornersEuclideanHalfSpace,eq_comm] using hb
  classical
  choose L hL hmargin hLc G hG hGc hGeq Φ hΦ hΦzero hΦder hΦunique di hdi hgood using hchart
  choose pick hpick using X.boundary_cover
  letI : Nonempty (Fin X.count) := ⟨pick (1:Circle)⟩
  let d : ℝ := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin X.count)).Nonempty) di
  have hd : 0 < d := (Finset.lt_inf'_iff _).mpr (fun i _ => hdi i)
  have hdle (i : Fin X.count) : d ≤ di i := Finset.inf'_le _ (Finset.mem_univ i)
  let ψ : Fin X.count → Circle × ℝ → F.surface := fun i p =>
    ((X.chart i).extend (𝓡∂ 2)).symm (Φ i ((X.chart i).extend (𝓡∂ 2) (F.boundary.toFun p.1),p.2))
  have hψzero (i : Fin X.count) (z : Circle) (hz : F.boundary.toFun z ∈ X.domain i) : ψ i (z,0)=F.boundary.toFun z := by
    change ((X.chart i).extend (𝓡∂ 2)).symm (Φ i ((X.chart i).extend (𝓡∂ 2) (F.boundary.toFun z),0))=_
    rw [hΦzero]
    apply ((X.chart i).extend (𝓡∂ 2)).left_inv
    rw [(X.chart i).extend_source]
    exact X.closure_subset i (subset_closure hz)
  have hψgood (i : Fin X.count) (z : Circle) (hz : F.boundary.toFun z ∈ X.domain i)
      (t : ℝ) (ht : 0 ≤ t) (htd : t < d) :=
    hgood i (F.boundary.toFun z) ⟨subset_closure hz,F.boundary.lands_boundary z⟩ t ht (htd.trans_le (hdle i))
  have hψsource (i : Fin X.count) (z : Circle) (hz : F.boundary.toFun z ∈ X.domain i)
      (t : ℝ) (ht : 0 ≤ t) (htd : t < d) : ψ i (z,t) ∈ (X.chart i).source := by
    have h := ((X.chart i).extend (𝓡∂ 2)).map_target (hψgood i z hz t ht htd).1
    simpa only [(X.chart i).extend_source] using h
  have hψcoord (i : Fin X.count) (z : Circle) (hz : F.boundary.toFun z ∈ X.domain i)
      (t : ℝ) (ht : 0 ≤ t) (htd : t < d) :
      (X.chart i).extend (𝓡∂ 2) (ψ i (z,t)) = Φ i ((X.chart i).extend (𝓡∂ 2) (F.boundary.toFun z),t) :=
    ((X.chart i).extend (𝓡∂ 2)).right_inv (hψgood i z hz t ht htd).1
  have hψint (i : Fin X.count) (z : Circle) (hz : F.boundary.toFun z ∈ X.domain i)
      (t : ℝ) (ht : 0 < t) (htd : t < d) : ψ i (z,t) ∉ F.surface.boundary := by
    intro hb
    have hh := hzeroChart i (ψ i (z,t)) hb (hψsource i z hz t ht.le htd)
    rw [hψcoord i z hz t ht.le htd] at hh
    exact (ne_of_gt ((hψgood i z hz t ht.le htd).2.2.2.1 ht)) hh
  have hψder (i : Fin X.count) (z : Circle) (hz : F.boundary.toFun z ∈ X.domain i)
      (t : ℝ) (ht : 0 ≤ t) (htd : t < d) :
      HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 2) (fun s => ψ i (z,s)) (Ici 0) t
        ((1:ℝ →L[ℝ] ℝ).smulRight (X.field (ψ i (z,t)))) := (hψgood i z hz t ht htd).2.2.2.2
  have hoverlap (i j : Fin X.count) (z : Circle)
      (hi : F.boundary.toFun z ∈ X.domain i) (hj : F.boundary.toFun z ∈ X.domain j)
      (t : ℝ) (ht : 0 ≤ t) (htd : t < d) : ψ i (z,t)=ψ j (z,t) :=
    (hboundaryUnique i (L i) (hLc i) (F.boundary.toFun z) (hmargin i (subset_closure hi))
      (G i) (hG i) (hGc i) (hGeq i) (fun s => ψ i (z,s)) (fun s => ψ j (z,s)) d hd
      (hψzero i z hi) (hψzero j z hj) (hψder i z hi) (hψder j z hj) (hψint i z hi)) ⟨ht,htd⟩
  let flow : Circle × ℝ → F.surface := fun p => ψ (pick p.1) p
  have hfloweq (i : Fin X.count) (z : Circle) (hi : F.boundary.toFun z ∈ X.domain i)
      (t : ℝ) (ht : 0 ≤ t) (htd : t < d) : flow (z,t)=ψ i (z,t) :=
    hoverlap (pick z) i z (hpick z) hi t ht htd
  have hsmooth : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 2) ∞ flow {p | 0 ≤ p.2 ∧ p.2 < d} := by
    let S : Fin X.count → Set (Circle × ℝ) := fun i =>
      {p | F.boundary.toFun p.1 ∈ X.domain i ∧ 0 ≤ p.2 ∧ p.2 < d}
    have hψsmooth (i : Fin X.count) :
        ContMDiffOn ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 2) ∞ (ψ i) (S i) := by
      let e := (X.chart i).extend (𝓡∂ 2)
      have hb : ContMDiff ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 2) ∞
          (fun p : Circle × ℝ => F.boundary.toFun p.1) :=
        F.boundary.smoothEmbedding.contMDiff.comp contMDiff_fst
      have hθ : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,Euc 2) ∞
          (fun p : Circle × ℝ => e (F.boundary.toFun p.1)) (S i) :=
        ((X.chart i).contMDiffOn_extend (X.atlas i)).comp hb.contMDiffOn
          (fun p hp => X.closure_subset i (subset_closure hp.1))
      have hpair := hθ.prodMk_space (contMDiff_snd (I:=𝓡 1) (J:=𝓘(ℝ,ℝ))).contMDiffOn
      have hPhiS := (hΦ i).contMDiff.comp_contMDiffOn hpair
      have hes : ContMDiffOn 𝓘(ℝ,Euc 2) (𝓡∂ 2) ∞ e.symm e.target := by
        rw [(X.chart i).extend_target']
        exact contMDiffOn_extend_symm (X.atlas i)
      exact hes.comp hPhiS (fun p hp => (hψgood i p.1 hp.1 p.2 hp.2.1 hp.2.2).1)
    intro p hp
    let i := pick p.1
    have hopen : IsOpen {q : Circle × ℝ | F.boundary.toFun q.1 ∈ X.domain i} :=
      (X.domain_open i).preimage (F.boundary.smoothEmbedding.isEmbedding.continuous.comp continuous_fst)
    have hn : {q : Circle × ℝ | F.boundary.toFun q.1 ∈ X.domain i} ∈ 𝓝 p :=
      hopen.mem_nhds (hpick p.1)
    have hns : S i ∈ 𝓝[{q : Circle × ℝ | 0 ≤ q.2 ∧ q.2 < d}] p := by
      exact Filter.inter_mem (Filter.Eventually.filter_mono nhdsWithin_le_nhds hn) self_mem_nhdsWithin
    have hs := (hψsmooth i p ⟨hpick p.1,hp⟩).mono_of_mem_nhdsWithin hns
    have heq : flow =ᶠ[𝓝[{q : Circle × ℝ | 0 ≤ q.2 ∧ q.2 < d}] p] ψ i := by
      filter_upwards [self_mem_nhdsWithin,Filter.Eventually.filter_mono nhdsWithin_le_nhds hn] with q hq hqi
      exact hfloweq i q.1 hqi q.2 hq.1 hq.2
    exact hs.congr_of_eventuallyEq_of_mem heq hp
  refine ⟨{ d := d
            d_pos := hd
            localDomain := fun _ => univ
            local_open := fun _ => isOpen_univ
            local_contains := fun _ _ _ => mem_univ _
            coordinateField := G
            coordinate_smooth := fun i => (hG i).contDiffOn
            coordinate_agrees := ?_
            localFlow := Φ
            local_smooth := fun i => (hΦ i).contDiffOn
            local_zero := fun i q _ => hΦzero i q
            local_ode := fun i q t _ _ => hΦder i q t
            local_unique := fun i q curve _ hzero _ hder => hΦunique i q curve d hd hzero hder
            flow := flow
            local_realization := ?_
            normal_velocity := ?_
            overlap := ?_
            zero := fun z => hψzero (pick z) z (hpick z)
            interior := fun z t ht htd => hψint (pick z) z (hpick z) t ht htd
            smooth := hsmooth
            tangent := ?_ }⟩
  · intro i x hx
    exact hGeq i x (interior_subset (hmargin i (subset_closure hx)))
  · intro i z t hi ht htd
    rw [hfloweq i z hi t ht htd]
    exact ⟨hψsource i z hi t ht htd,hψcoord i z hi t ht htd⟩
  · intro i z t hi ht htd
    exact (hψgood i z hi t ht htd).2.2.1
  · intro i j z t hi hj ht htd
    exact hoverlap i j z hi hj t ht htd
  · intro z t ht htd
    have h := (hψder (pick z) z (hpick z) t ht htd).mfderivWithin
      (((uniqueDiffOn_Ici (0:ℝ)) t ht).uniqueMDiffWithinAt)
    change mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 2) (fun s => ψ (pick z) (z,s)) (Ici 0) t
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) t).symm 1) = X.field (ψ (pick z) (z,t))
    rw [h]
    change (1:ℝ) • X.field (ψ (pick z) (z,t))=X.field (ψ (pick z) (z,t))
    exact one_smul _ _

structure C5UniformFlow {K : OrientedKnot} {F : SphereSpanningSurface.{0} K} (X : C3InwardField F) (Y : C4LocalFlow X) where
  d : ℝ
  d_pos : 0 < d
  flow : Circle × ℝ → F.surface
  injective : Set.InjOn flow {p | 0 ≤ p.2 ∧ p.2 < d}
  d_le : d ≤ Y.d
  agrees : EqOn flow Y.flow {p | 0 ≤ p.2 ∧ p.2 < d}
  zero : ∀ z, flow (z,0) = F.boundary.toFun z
  positive : ∀ z t, 0 < t → t < d → flow (z,t) ∉ F.surface.boundary
  smooth : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 2) ∞ flow {p | 0 ≤ p.2 ∧ p.2 < d}
  lambda : ℝ
  lambda_pos : 0 < lambda
  lambda_lt : lambda < d
  time_deriv : ∀ z t, 0 ≤ t → t < d →
    mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 2) (fun s => flow (z,s)) (Ici 0) t
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) t).symm 1) = X.field (flow (z,t))
theorem C5_uniform_flow {K : OrientedKnot} {F : SphereSpanningSurface.{0} K}
    (X : C3InwardField F) (Y : C4LocalFlow X) : Nonempty (C5UniformFlow X Y) := by
  have hinj : Set.InjOn Y.flow {p | 0 ≤ p.2 ∧ p.2 < Y.d} := by
    have hder (z : Circle) (t : ℝ) (ht : 0 < t) (htd : t < Y.d) :
      HasMFDerivAt 𝓘(ℝ,ℝ) (𝓡∂ 2) (fun s => Y.flow (z,s)) t
            ((1:ℝ →L[ℝ] ℝ).smulRight (X.field (Y.flow (z,t))))
        := by
      have hs : ContMDiffOn 𝓘(ℝ,ℝ) (𝓡∂ 2) ∞ (fun s => Y.flow (z,s)) {s | 0 ≤ s ∧ s < Y.d} :=
        Y.smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun _ hs => hs)
      have hdt : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡∂ 2) (fun s => Y.flow (z,s)) t :=
        ((hs t ⟨ht.le,htd⟩).contMDiffAt
          (Filter.inter_mem (Ici_mem_nhds ht) (Iio_mem_nhds htd))).mdifferentiableAt (by simp)
      have hh := Y.tangent z t ht.le htd
      rw [mfderivWithin_eq_mfderiv ((uniqueDiffWithinAt_of_mem_nhds (𝕜:=ℝ) (Ici_mem_nhds ht)).uniqueMDiffWithinAt) hdt] at hh
      have heq : mfderiv 𝓘(ℝ,ℝ) (𝓡∂ 2) (fun s => Y.flow (z,s)) t=
          (1:ℝ →L[ℝ] ℝ).smulRight (X.field (Y.flow (z,t))) := by
        apply ContinuousLinearMap.ext
        intro r
        let r0 : ℝ := r
        let L := mfderiv 𝓘(ℝ,ℝ) (𝓡∂ 2) (fun s => Y.flow (z,s)) t
        have hr : r=r0 • (1:TangentSpace 𝓘(ℝ,ℝ) t) := by change r0=r0*(1:ℝ); ring
        change L (1:TangentSpace 𝓘(ℝ,ℝ) t)=X.field (Y.flow (z,t)) at hh
        change L r=r0 • X.field (Y.flow (z,t))
        calc
          L r=L (r0 • (1:TangentSpace 𝓘(ℝ,ℝ) t)) := congrArg L hr
          _=r0 • L (1:TangentSpace 𝓘(ℝ,ℝ) t) := L.map_smul r0 _
          _=r0 • X.field (Y.flow (z,t)) := congrArg (fun v => r0 • v) hh
      exact heq ▸ hdt.hasMFDerivAt
    have hcomp (z w : Circle) (t u : ℝ) (ht0 : 0 ≤ t) (htd : t < Y.d)
        (hu0 : 0 ≤ u) (hud : u < Y.d) (htu : t ≤ u)
        (heq : Y.flow (z,t)=Y.flow (w,u)) : t=u ∧ z=w := by
      by_cases ht : t=0
      · have hu : u=0 := by
          by_contra hune
          have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hune)
          have hbd : Y.flow (w,u) ∈ F.surface.boundary := by
            rw [←heq,ht,Y.zero]
            exact F.boundary.lands_boundary z
          exact Y.interior w u hup hud hbd
        refine ⟨ht.trans hu.symm,?_⟩
        rw [ht,hu,Y.zero,Y.zero] at heq
        exact F.boundary.smoothEmbedding.isEmbedding.injective heq
      · have htp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
        let b := (Y.d-u)/2
        have hb : 0 < b := by dsimp [b]; linarith
        let γ : ℝ → F.surface := fun s => Y.flow (z,t+s)
        let δ : ℝ → F.surface := fun s => Y.flow (w,u+s)
        have htime (s : ℝ) (hs : s ∈ Ioo (-t) b) :
            0 < t+s ∧ t+s < Y.d ∧ 0 < u+s ∧ u+s < Y.d := by
          dsimp [b] at hs
          constructor
          · linarith [hs.1]
          constructor
          · linarith [hs.2]
          constructor <;> linarith [hs.1,hs.2]
        have hγ : IsMIntegralCurveOn γ X.field (Ioo (-t) b) := by
          intro s hs
          have ht := htime s hs
          have hshift : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun s : ℝ => t+s) s (ContinuousLinearMap.id ℝ ℝ) :=
            ((hasFDerivAt_id s).const_add t).hasMFDerivAt
          have h := (hder z (t+s) ht.1 ht.2.1).comp s hshift
          have h' : HasMFDerivAt 𝓘(ℝ,ℝ) (𝓡∂ 2) γ s
              ((1:ℝ →L[ℝ] ℝ).smulRight (X.field (γ s))) :=
            h.congr_mfderiv (by apply ContinuousLinearMap.ext; intro r; rfl)
          exact h'.hasMFDerivWithinAt
        have hδ : IsMIntegralCurveOn δ X.field (Ioo (-t) b) := by
          intro s hs
          have ht := htime s hs
          have hshift : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun s : ℝ => u+s) s (ContinuousLinearMap.id ℝ ℝ) :=
            ((hasFDerivAt_id s).const_add u).hasMFDerivAt
          have h := (hder w (u+s) ht.2.2.1 ht.2.2.2).comp s hshift
          have h' : HasMFDerivAt 𝓘(ℝ,ℝ) (𝓡∂ 2) δ s
              ((1:ℝ →L[ℝ] ℝ).smulRight (X.field (δ s))) :=
            h.congr_mfderiv (by apply ContinuousLinearMap.ext; intro r; rfl)
          exact h'.hasMFDerivWithinAt
        have hi : ∀ s ∈ Ioo (-t) b, (𝓡∂ 2).IsInteriorPoint (γ s) := by
          intro s hs
          apply (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint (γ s)).mpr
          exact Y.interior z (t+s) (htime s hs).1 (htime s hs).2.1
        have he : EqOn γ δ (Ioo (-t) b) :=
          isMIntegralCurveOn_Ioo_eqOn_of_contMDiff ⟨by linarith,hb⟩ hi
            (X.smooth.of_le (by simp)) hγ hδ (by simpa [γ,δ] using heq)
        have hγc : ContinuousOn γ (Icc (-t) 0) := by
          apply Y.smooth.continuousOn.comp (continuous_const.prodMk (continuous_const.add continuous_id)).continuousOn
          intro s hs
          change 0 ≤ t+s ∧ t+s < Y.d
          exact ⟨by linarith [hs.1],by linarith [hs.2]⟩
        have hδc : ContinuousOn δ (Icc (-t) 0) := by
          apply Y.smooth.continuousOn.comp (continuous_const.prodMk (continuous_const.add continuous_id)).continuousOn
          intro s hs
          change 0 ≤ u+s ∧ u+s < Y.d
          exact ⟨by linarith [hs.1],by linarith [hs.2]⟩
        have he' : EqOn γ δ (Icc (-t) 0) := by
          apply (he.mono (show Ioo (-t) 0 ⊆ Ioo (-t) b from fun s hs => ⟨hs.1,hs.2.trans hb⟩)).of_subset_closure
            hγc hδc Ioo_subset_Icc_self
          rw [closure_Ioo (by linarith : -t ≠ (0:ℝ))]
        have hendpoint : F.boundary.toFun z=Y.flow (w,u-t) := by
          have h := he' (x:=-t) ⟨le_rfl,by linarith⟩
          simpa only [γ,δ,add_neg_cancel,Y.zero,←sub_eq_add_neg] using h
        have htu' : t=u := by
          by_contra hne
          have hup : 0 < u-t := sub_pos.mpr (lt_of_le_of_ne htu hne)
          have hbd : Y.flow (w,u-t) ∈ F.surface.boundary := hendpoint ▸ F.boundary.lands_boundary z
          exact Y.interior w (u-t) hup (by linarith) hbd
        refine ⟨htu',?_⟩
        rw [htu',sub_self,Y.zero] at hendpoint
        exact F.boundary.smoothEmbedding.isEmbedding.injective hendpoint
    intro p hp q hq heq
    rcases le_total p.2 q.2 with h | h
    · obtain ⟨ht,hz⟩ := hcomp p.1 q.1 p.2 q.2 hp.1 hp.2 hq.1 hq.2 h heq
      exact Prod.ext hz ht
    · obtain ⟨ht,hz⟩ := hcomp q.1 p.1 q.2 p.2 hq.1 hq.2 hp.1 hp.2 h heq.symm
      exact Prod.ext hz.symm ht.symm
  exact ⟨{ d := Y.d
           d_pos := Y.d_pos
           flow := Y.flow
           injective := hinj
           d_le := le_rfl
           agrees := fun _ _ => rfl
           zero := Y.zero
           positive := Y.interior
           smooth := Y.smooth
           lambda := Y.d/2
           lambda_pos := div_pos Y.d_pos (by norm_num)
           lambda_lt := by linarith [Y.d_pos]
           time_deriv := Y.tangent }⟩

structure C6FlowCharts {K : OrientedKnot} {F : SphereSpanningSurface.{0} K}
    (X : C3InwardField F) (Y : C4LocalFlow X) (Z : C5UniformFlow X Y) where
  charts : ∀ p : Circle × Time,
    ∃ source : OpenPartialHomeomorph (Circle × Time) (Euc 1 × EuclideanHalfSpace 1),
    ∃ target : OpenPartialHomeomorph F.surface (EuclideanHalfSpace 2),
    ∃ L : ((Euc 1 × Euc 1) × Euc 0) ≃L[ℝ] Euc 2,
      p ∈ source.source ∧ Z.flow (p.1,Z.lambda*(p.2:ℝ)) ∈ target.source ∧
      source ∈ IsManifold.maximalAtlas CollarModel ∞ (Circle × Time) ∧
      target ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ F.surface ∧
      source.source ⊆ (fun q : Circle × Time => Z.flow (q.1,Z.lambda*(q.2:ℝ))) ⁻¹' target.source ∧
      EqOn ((target.extend (𝓡∂ 2)) ∘ (fun q : Circle × Time => Z.flow (q.1,Z.lambda*(q.2:ℝ))) ∘
        (source.extend CollarModel).symm) (fun u => L (u,0)) (source.extend CollarModel).target
  open_image : IsOpen ((fun p : Circle × Time => Z.flow (p.1,Z.lambda*(p.2:ℝ))) ''
    {p | (p.2:ℝ)<1})
  positive_time_immersion : ∀ z t, 0<t → t<Z.d →
    Manifold.IsImmersionAt ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 2) ∞ Z.flow (z,t)
set_option maxHeartbeats 0 in
theorem C6_flow_charts {K : OrientedKnot} {F : SphereSpanningSurface.{0} K}
    (X : C3InwardField F) (Y : C4LocalFlow X) (Z : C5UniformFlow X Y) :
    Nonempty (C6FlowCharts X Y Z) := by
  have hdata (z : Circle) (t : ℝ) (ht : 0 ≤ t) (htd : t < Z.d) :
      ∃ i : Fin X.count, ∃ c : OpenPartialHomeomorph Circle (Euc 1),
        c ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle ∧ z ∈ c.source ∧
        ∃ B : Set (Euc 1), IsOpen B ∧ c z ∈ B ∧ B ⊆ c.target ∧
        ∃ T : ℝ,t < T ∧ T < Z.d ∧
        ∃ H : Euc 1 × ℝ → Euc 2,ContDiffOn ℝ ∞ H (B ×ˢ univ) ∧
          (∀ u ∈ B,∀ s,Function.Injective (fderiv ℝ H (u,s))) ∧
          (∀ u ∈ B,H (u,0) 0=0) ∧
          (∀ u ∈ B,0 < (fderiv ℝ H (u,0) (0,1)) 0) ∧
          ∀ u ∈ B,∀ s ∈ Icc 0 T,
            Z.flow (c.symm u,s) ∈ (X.chart i).source ∧
            H (u,s)=(X.chart i).extend (𝓡∂ 2) (Z.flow (c.symm u,s)) := by
    have htube (z : Circle) (t : ℝ) (ht : 0 ≤ t) (htd : t < Z.d) :
        ∃ i : Fin X.count, ∃ A : Set Circle, IsOpen A ∧ z ∈ A ∧
          ∃ T : ℝ, t < T ∧ T < Z.d ∧
          ∃ G : Euc 2 → Euc 2, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
            ∀ w ∈ A, ∀ s ∈ Icc 0 T,
              Z.flow (w,s) ∈ (X.chart i).source ∧
              G ((X.chart i).extend (𝓡∂ 2) (Z.flow (w,s))) =
                tangentSpaceCastModel 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2) (Z.flow (w,s)))
                  (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2))
                    (Z.flow (w,s)) (X.field (Z.flow (w,s)))) := by
      have hext (i : Fin X.count) (S : Set F.surface) (hS : IsCompact S)
          (hSc : S ⊆ (X.chart i).source) :
          ∃ G : Euc 2 → Euc 2, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
            ∀ x ∈ S, G ((X.chart i).extend (𝓡∂ 2) x) =
              tangentSpaceCastModel 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2) x)
                (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2)) x (X.field x)) := by
        let c := X.chart i
        let e := c.extend (𝓡∂ 2)
        have he_source : e.source=c.source := c.extend_source
        let v : F.surface → Euc 2 := fun x => tangentSpaceCastModel 𝓘(ℝ,Euc 2) (e x)
          (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) e x (X.field x))
        have hv : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,Euc 2) ∞ v c.source := by
          have hf : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,Euc 2) ∞ e c.source := c.contMDiffOn_extend (X.atlas i)
          have hT : ContMDiffOn (𝓡∂ 2).tangent (𝓘(ℝ,Euc 2)).tangent ∞
              (tangentMapWithin (𝓡∂ 2) 𝓘(ℝ,Euc 2) e c.source)
              (Bundle.TotalSpace.proj ⁻¹' c.source) :=
            hf.contMDiffOn_tangentMapWithin (by simp) c.open_source.uniqueMDiffOn
          have hsection := hT.comp X.smooth.contMDiffOn (fun x hx => hx)
          have hread := (contMDiff_snd_tangentBundle_modelSpace (Euc 2) 𝓘(ℝ,Euc 2) (n:=∞)).comp_contMDiffOn hsection
          apply hread.congr
          intro x hx
          change (show Euc 2 from mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) e x (X.field x))=
            (show Euc 2 from mfderivWithin (𝓡∂ 2) 𝓘(ℝ,Euc 2) e c.source x (X.field x))
          rw [mfderivWithin_eq_mfderiv (c.open_source.uniqueMDiffWithinAt hx)
            ((c.contMDiffAt_extend (X.atlas i) hx).mdifferentiableAt (by simp))]
        have hes : ContMDiffOn 𝓘(ℝ,Euc 2) (𝓡∂ 2) ∞ e.symm e.target := by
          rw [c.extend_target']
          exact contMDiffOn_extend_symm (X.atlas i)
        have hvE : ContDiffOn ℝ ∞ (v ∘ e.symm) e.target :=
          (hv.comp hes (fun _ hx => he_source ▸ e.map_target hx)).contDiffOn
        let L : Euc 2 ≃L[ℝ] ℝ × ℝ := (EuclideanSpace.equiv (Fin 2) ℝ).trans
          (LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv
        have hL0 (q : Euc 2) : (L q).1=q 0 := rfl
        have hLi0 (q : ℝ × ℝ) : (L.symm q) 0=q.1 := by
          have hh := congrArg Prod.fst (L.apply_symm_apply q)
          exact hh
        let U : Set (ℝ × ℝ) := L.symm ⁻¹' ((𝓡∂ 2).symm ⁻¹' c.target)
        have hU : IsOpen U := (c.open_target.preimage (𝓡∂ 2).continuous_symm).preimage L.symm.continuous
        have heq : L.symm ⁻¹' e.target = (Ici 0 ×ˢ univ) ∩ U := by
          ext q
          rw [mem_preimage,c.extend_target,mem_inter_iff,range_modelWithCornersEuclideanHalfSpace]
          change ((_ ∈ c.target) ∧ 0 ≤ (L.symm q) 0) ↔ ((0 ≤ q.1 ∧ q.2 ∈ (univ:Set ℝ)) ∧ _)
          rw [hLi0]
          simp only [mem_univ,true_and,and_true,and_comm,U,mem_preimage]
        let vP : ℝ × ℝ → Euc 2 := (v ∘ e.symm) ∘ L.symm
        have hvP : ContDiffOn ℝ ∞ vP ((Ici 0 ×ˢ univ) ∩ U) := by
          rw [←heq]
          exact hvE.comp L.symm.contDiff.contDiffOn (fun _ hx => hx)
        have hloc (x : F.surface) (hx : x ∈ S) :
            ∃ W ∈ 𝓝 (e x), ∃ G : Euc 2 → Euc 2, ContDiffOn ℝ ∞ G W ∧
              ∀ y ∈ S, e y ∈ W → G (e y)=v y := by
          have hxt : e x ∈ e.target := e.map_source (he_source.symm ▸ hSc hx)
          have hpx : L (e x) ∈ U := by
            have h := congrArg (fun A : Set (ℝ × ℝ) => L (e x) ∈ A) heq
            have hh : L (e x) ∈ L.symm ⁻¹' e.target := by simpa using hxt
            exact (heq ▸ hh).2
          obtain ⟨G,hG,hGeq⟩ := hvP.exists_contDiff_extension_Ici_prod_nhdsWithin hU hpx
          obtain ⟨W,hW,hWeq⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hGeq
          refine ⟨L ⁻¹' W,L.continuous.continuousAt.preimage_mem_nhds hW,G ∘ L,
            (hG.comp L.contDiff).contDiffOn,?_⟩
          intro y hy hey
          have hyhalf : L (e y) ∈ Ici 0 ×ˢ univ := by
            have hyt := e.map_source (he_source.symm ▸ hSc hy)
            have hh : L (e y) ∈ L.symm ⁻¹' e.target := by simpa using hyt
            exact (heq ▸ hh).1
          have h := hWeq ⟨hey,hyhalf⟩
          change G (L (e y)) = v y
          change G (L (e y)) = (v ∘ e.symm) (L.symm (L (e y))) at h
          simpa only [L.symm_apply_apply,Function.comp_apply,e.left_inv (he_source.symm ▸ hSc hy)] using h
        have hecont : ContinuousOn e S := by
          apply c.continuousOn_extend.mono
          intro x hx
          exact he_source.symm ▸ hSc hx
        have himage : IsCompact (e '' S) := hS.image_of_continuousOn hecont
        obtain ⟨G,hG,hGeq⟩ := DifferentialGeometry.Analysis.exists_contDiff_extension_of_local himage.isClosed hloc
        obtain ⟨χ,hχ,hχcomp,hχone,_,_⟩ := DifferentialGeometry.Analysis.exists_bump_compact
          himage isOpen_univ (subset_univ _)
        refine ⟨fun q => χ q • G q,hχ.smul hG,hχcomp.smul_right,?_⟩
        intro x hx
        have hχx : χ (e x)=1 := (hχone.filter_mono (nhds_le_nhdsSet ⟨x,hx,rfl⟩)).self_of_nhds
        change χ (e x) • G (e x)=v x
        rw [hχx,one_smul]
        exact hGeq hx
      obtain ⟨i,hi⟩ := X.boundary_cover z
      let V := F.boundary.toFun ⁻¹' X.domain i
      have hV : IsOpen V := (X.domain_open i).preimage F.boundary.smoothEmbedding.isEmbedding.continuous
      obtain ⟨A,hA,hAV,hAc⟩ := local_compact_nhds (hV.mem_nhds hi)
      let T := (t+Z.d)/2
      have htT : t < T := by dsimp [T]; linarith
      have hTd : T < Z.d := by dsimp [T]; linarith
      have hT : 0 < T := ht.trans_lt htT
      have hsmooth := Z.smooth.continuousOn
      have hcomp : IsCompact (A ×ˢ Icc 0 T) := hAc.prod isCompact_Icc
      let S := Z.flow '' (A ×ˢ Icc 0 T)
      have hS : IsCompact S := hcomp.image_of_continuousOn
        (hsmooth.mono (fun p hp => ⟨hp.2.1,hp.2.2.trans_lt hTd⟩))
      have hSc : S ⊆ (X.chart i).source := by
        rintro x ⟨p,hp,rfl⟩
        rw [Z.agrees ⟨hp.2.1,hp.2.2.trans_lt hTd⟩]
        exact (Y.local_realization i p.1 p.2 (hAV hp.1) hp.2.1
          ((hp.2.2.trans_lt hTd).trans_le Z.d_le)).1
      obtain ⟨G,hG,hGc,hGeq⟩ := hext i S hS hSc
      refine ⟨i,interior A,isOpen_interior,mem_interior_iff_mem_nhds.mpr hA,T,htT,hTd,G,hG,hGc,?_⟩
      intro w hw s hs
      have hsm : Z.flow (w,s) ∈ S := ⟨(w,s),⟨interior_subset hw,hs⟩,rfl⟩
      exact ⟨hSc hsm,hGeq _ hsm⟩
    have hagreement (i : Fin X.count) (A : Set Circle) (T : ℝ) (hT : 0 < T) (hTd : T < Z.d)
        (G : Euc 2 → Euc 2) (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G)
        (hgood : ∀ w ∈ A, ∀ s ∈ Icc 0 T,
          Z.flow (w,s) ∈ (X.chart i).source ∧
          G ((X.chart i).extend (𝓡∂ 2) (Z.flow (w,s))) =
            tangentSpaceCastModel 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2) (Z.flow (w,s)))
              (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2))
                (Z.flow (w,s)) (X.field (Z.flow (w,s))))) :
        ∃ Φ : Euc 2 × ℝ → Euc 2, ContDiff ℝ ∞ Φ ∧
          (∀ q,Φ (q,0)=q) ∧
          (∀ q s,HasDerivAt (fun r => Φ (q,r)) (G (Φ (q,s))) s) ∧
          (∀ q s r,Φ (q,s+r)=Φ (Φ (q,s),r)) ∧
          (∀ s,∃ d : Diffeomorph 𝓘(ℝ,Euc 2) 𝓘(ℝ,Euc 2) (Euc 2) (Euc 2) ∞,
            ∀ q,d q=Φ (q,s)) ∧
          ∀ w ∈ A, ∀ s ∈ Icc 0 T,
            (X.chart i).extend (𝓡∂ 2) (Z.flow (w,s)) =
              Φ ((X.chart i).extend (𝓡∂ 2) (F.boundary.toFun w),s) := by
      have hnative (z : Circle) (t : ℝ) (ht : 0 ≤ t) (htd : t < Z.d) :
          HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 2) (fun s => Z.flow (z,s)) (Ici 0) t
            ((1:ℝ →L[ℝ] ℝ).smulRight (X.field (Z.flow (z,t)))) := by
        have hs : ContMDiffOn 𝓘(ℝ,ℝ) (𝓡∂ 2) ∞ (fun s => Z.flow (z,s)) {s | 0 ≤ s ∧ s < Z.d} :=
          Z.smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun _ hs => hs)
        have hct : ContMDiffWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 2) ∞ (fun s => Z.flow (z,s)) (Ici 0) t :=
          (hs t ⟨ht,htd⟩).mono_of_mem_nhdsWithin
            (Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds htd)))
        have hmd := hct.mdifferentiableWithinAt (by simp)
        have hh := Z.time_deriv z t ht htd
        have heq : mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 2) (fun s => Z.flow (z,s)) (Ici 0) t=
            (1:ℝ →L[ℝ] ℝ).smulRight (X.field (Z.flow (z,t))) := by
          apply ContinuousLinearMap.ext
          intro r
          let r0 : ℝ := r
          let L := mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 2) (fun s => Z.flow (z,s)) (Ici 0) t
          have hr : r=r0 • (1:TangentSpace 𝓘(ℝ,ℝ) t) := by change r0=r0*(1:ℝ); ring
          change L (1:TangentSpace 𝓘(ℝ,ℝ) t)=X.field (Z.flow (z,t)) at hh
          change L r=r0 • X.field (Z.flow (z,t))
          calc
            L r=L (r0 • (1:TangentSpace 𝓘(ℝ,ℝ) t)) := congrArg L hr
            _=r0 • L (1:TangentSpace 𝓘(ℝ,ℝ) t) := L.map_smul r0 _
            _=r0 • X.field (Z.flow (z,t)) := congrArg (fun v => r0 • v) hh
        exact heq ▸ hmd.hasMFDerivWithinAt
      have hcoordinate (i : Fin X.count) (γ : ℝ → F.surface) (t : ℝ)
          (hγ : HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 2) γ (Ici 0) t
            ((1:ℝ →L[ℝ] ℝ).smulRight (X.field (γ t))))
          (hγc : γ t ∈ (X.chart i).source) :
          HasDerivWithinAt ((X.chart i).extend (𝓡∂ 2) ∘ γ)
            (tangentSpaceCastModel 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2) (γ t))
              (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) ((X.chart i).extend (𝓡∂ 2)) (γ t) (X.field (γ t))))
            (Ici 0) t := by
        let c := X.chart i
        let e := c.extend (𝓡∂ 2)
        have hc : HasMFDerivAt (𝓡∂ 2) 𝓘(ℝ,Euc 2) e (γ t)
            (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) e (γ t)) :=
          ((c.contMDiffAt_extend (X.atlas i) hγc).mdifferentiableAt (by simp)).hasMFDerivAt
        have hh := hc.comp_hasMFDerivWithinAt t hγ
        have hh' : HasFDerivWithinAt (e ∘ γ)
            ((1:ℝ →L[ℝ] ℝ).smulRight
              (tangentSpaceCastModel 𝓘(ℝ,Euc 2) (e (γ t))
                (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) e (γ t) (X.field (γ t))))) (Ici 0) t := by
          apply hh.hasFDerivWithinAt.congr_fderiv
          apply ContinuousLinearMap.ext
          intro r
          let r0 : ℝ := r
          change mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) e (γ t) (r0 • X.field (γ t)) =
            r0 • mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) e (γ t) (X.field (γ t))
          exact map_smul _ _ _
        simpa only [ContinuousLinearMap.smulRight_apply,one_apply_eq_self,one_smul] using hh'.hasDerivWithinAt
      let v : (x : Euc 2) → TangentSpace 𝓘(ℝ,Euc 2) x := G
      have hv : ContMDiff 𝓘(ℝ,Euc 2) (𝓘(ℝ,Euc 2)).tangent ∞
          (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,Euc 2) (Euc 2))) := by
        intro x
        exact contMDiffAt_vectorSpace_iff_contDiffAt.mpr hG.contDiffAt
      let hc := exists_globalIntegralCurve_of_compactSupport v hv hGc
      let Φ : Euc 2 × ℝ → Euc 2 := fun p => curveAt v hc p.1 p.2
      have hΦ : ContDiff ℝ ∞ Φ := by
        have h := contMDiff_globalFlow_joint_of_compactSupport v hv hGc
        have h' := h.comp (contMDiff_snd.prodMk contMDiff_fst)
        rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod] at h'
        exact h'.contDiff
      have hzero (q : Euc 2) : Φ (q,0)=q := curveAt_zero v hc q
      have hder (q : Euc 2) (s : ℝ) : HasDerivAt (fun r => Φ (q,r)) (G (Φ (q,s))) s := by
        have h' : HasFDerivAt (fun r => Φ (q,r)) ((1:ℝ →L[ℝ] ℝ).smulRight (G (Φ (q,s)))) s :=
          (curveAt_integralCurve v hc q s).hasFDerivAt
        simpa only [ContinuousLinearMap.smulRight_apply,one_apply_eq_self,one_smul] using h'.hasDerivAt
      have hadd (q : Euc 2) (s r : ℝ) : Φ (q,s+r)=Φ (Φ (q,s),r) :=
        curveAt_add v (hv.of_le (by simp)) hc q s r
      have hdiffeo (s : ℝ) : ∃ d : Diffeomorph 𝓘(ℝ,Euc 2) 𝓘(ℝ,Euc 2) (Euc 2) (Euc 2) ∞,
          ∀ q,d q=Φ (q,s) := by
        obtain ⟨d,hd,_⟩ := globalFlow_diffeomorph_of_complete v hv hc s
        exact ⟨d,hd⟩
      refine ⟨Φ,hΦ,hzero,hder,hadd,hdiffeo,?_⟩
      intro w hw
      let e := (X.chart i).extend (𝓡∂ 2)
      let γ : ℝ → Euc 2 := fun s => e (Z.flow (w,s))
      let δ : ℝ → Euc 2 := fun s => Φ (e (F.boundary.toFun w),s)
      have hγcont : ContinuousOn γ (Icc 0 T) := by
        intro s hs
        change ContinuousWithinAt (e ∘ (fun r => Z.flow (w,r))) (Icc 0 T) s
        exact ((X.chart i).continuousAt_extend (I:=𝓡∂ 2) (hgood w hw s hs).1).comp_continuousWithinAt
          (f:=fun r : ℝ => Z.flow (w,r)) (x:=s) (s:=Icc 0 T)
          ((hnative w s hs.1 (hs.2.trans_lt hTd)).continuousWithinAt.mono
            (fun (r : ℝ) (hr : r ∈ Icc 0 T) => hr.1))
      have hγder (s : ℝ) (hs : s ∈ Ico 0 T) : HasDerivWithinAt γ (G (γ s)) (Ici s) s := by
        have hh := hcoordinate i (fun r => Z.flow (w,r)) s
          (hnative w s hs.1 (hs.2.trans hTd)) (hgood w hw s ⟨hs.1,hs.2.le⟩).1
        rw [←(hgood w hw s ⟨hs.1,hs.2.le⟩).2] at hh
        exact hh.mono (fun r hr => hs.1.trans hr)
      have hδcont : ContinuousOn δ (Icc 0 T) :=
        continuous_iff_continuousAt.mpr (fun s => (hder _ s).continuousAt) |>.continuousOn
      have hδder (s : ℝ) (_hs : s ∈ Ico 0 T) : HasDerivWithinAt δ (G (δ s)) (Ici s) s :=
        (hder _ s).hasDerivWithinAt
      obtain ⟨C,hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hGc hG (by simp)
      exact ODE_solution_unique (v:=fun _ => G) (fun _ => hC) hγcont hγder hδcont hδder
        (by simp only [γ,δ,Z.zero,hzero])
    have hboundary (i : Fin X.count) (c : OpenPartialHomeomorph Circle (Euc 1))
        (hc : c ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle)
        (u : Euc 1) (hu : u ∈ c.target) (hue : F.boundary.toFun (c.symm u) ∈ (X.chart i).source) :
        let b : Euc 1 → Euc 2 := (X.chart i).extend (𝓡∂ 2) ∘ F.boundary.toFun ∘ c.symm
        ContDiffAt ℝ ∞ b u ∧ Function.Injective (fderiv ℝ b u) ∧
          ∀ v,(fderiv ℝ b u v) 0=0 := by
      let e := (X.chart i).extend (𝓡∂ 2)
      let b : Euc 1 → Euc 2 := e ∘ F.boundary.toFun ∘ c.symm
      have hcs : ContMDiffAt 𝓘(ℝ,Euc 1) (𝓡 1) ∞ c.symm u :=
        (contMDiffOn_symm_of_mem_maximalAtlas hc).contMDiffAt (c.open_target.mem_nhds hu)
      have hbs : ContMDiffAt (𝓡 1) (𝓡∂ 2) ∞ F.boundary.toFun (c.symm u) :=
        F.boundary.smoothEmbedding.contMDiff _
      have hes : ContMDiffAt (𝓡∂ 2) 𝓘(ℝ,Euc 2) ∞ e (F.boundary.toFun (c.symm u)) :=
        (X.chart i).contMDiffAt_extend (X.atlas i) hue
      have hb : ContDiffAt ℝ ∞ b u := (hes.comp u (hbs.comp u hcs)).contDiffAt
      have hd1 := mfderiv_comp u (hbs.mdifferentiableAt (by simp)) (hcs.mdifferentiableAt (by simp))
      have hd2 := mfderiv_comp u (hes.mdifferentiableAt (by simp))
        ((hbs.comp u hcs).mdifferentiableAt (by simp))
      have hcder : Function.Injective (mfderiv 𝓘(ℝ,Euc 1) (𝓡 1) c.symm u) := by
        have hcm : c.MDifferentiable (𝓡 1) 𝓘(ℝ,Euc 1) :=
          ⟨(contMDiffOn_of_mem_maximalAtlas hc).mdifferentiableOn (by simp),
            (contMDiffOn_symm_of_mem_maximalAtlas hc).mdifferentiableOn (by simp)⟩
        exact hcm.symm.mfderiv_injective hu
      have hbder : Function.Injective (mfderiv 𝓘(ℝ,Euc 1) 𝓘(ℝ,Euc 2) b u) := by
        change mfderiv 𝓘(ℝ,Euc 1) 𝓘(ℝ,Euc 2) (e ∘ (F.boundary.toFun ∘ c.symm)) u = _ at hd2
        rw [hd2,hd1]
        exact (isInvertible_mfderiv_extend (IsManifold.maximalAtlas_subset_of_le (by simp) (X.atlas i)) hue).injective.comp
          ((F.boundary.smoothEmbedding.isImmersion.mfderiv_injective (by simp) _).comp hcder)
      have hbder' : Function.Injective (fderiv ℝ b u) := by
        intro v w hvw
        have hv := congrArg (NormedSpace.fromTangentSpace (𝕜:=ℝ) (b u)).symm hvw
        apply (NormedSpace.fromTangentSpace (𝕜:=ℝ) u).symm.injective
        apply hbder
        simpa only [mfderiv_eq_fderiv,ContinuousLinearMap.coe_comp,Function.comp_apply,
          ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] using hv
      have hnormal : (fun v : Euc 1 => b v 0)=ᶠ[𝓝 u] (fun _ => (0:ℝ)) := by
        have hn : ∀ᶠ v in 𝓝 u, v ∈ c.target ∧ F.boundary.toFun (c.symm v) ∈ (X.chart i).source :=
          Filter.inter_mem (c.open_target.mem_nhds hu)
            ((F.boundary.smoothEmbedding.isEmbedding.continuous.continuousAt.comp hcs.continuousAt).preimage_mem_nhds
              ((X.chart i).open_source.mem_nhds hue))
        filter_upwards [hn] with v hv
        exact (halfspace_atlas_boundary_interior (X.chart i) (X.atlas i)
          (F.boundary.toFun (c.symm v)) hv.2).1.mp (F.boundary.lands_boundary _)
      have hnormalder : (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin 2)).comp (fderiv ℝ b u)=0 := by
        have h := (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin 2)).hasFDerivAt.comp u (hb.differentiableAt (by simp)).hasFDerivAt
        change HasFDerivAt (fun v : Euc 1 => b v 0) _ u at h
        have hzero := (hasFDerivAt_const (𝕜:=ℝ) (0:ℝ) u).congr_of_eventuallyEq hnormal
        exact h.unique hzero
      refine ⟨hb,hbder',?_⟩
      intro v
      exact congrArg (fun C : Euc 1 →L[ℝ] ℝ => C v) hnormalder
    have hrank (G : Euc 2 → Euc 2) (Φ : Euc 2 × ℝ → Euc 2) (hΦ : ContDiff ℝ ∞ Φ)
        (hzero : ∀ q,Φ (q,0)=q)
        (hder : ∀ q s,HasDerivAt (fun r => Φ (q,r)) (G (Φ (q,s))) s)
        (hadd : ∀ q s r,Φ (q,s+r)=Φ (Φ (q,s),r))
        (hdiffeo : ∀ s,∃ d : Diffeomorph 𝓘(ℝ,Euc 2) 𝓘(ℝ,Euc 2) (Euc 2) (Euc 2) ∞,∀ q,d q=Φ (q,s))
        (b : Euc 1 → Euc 2) (u : Euc 1) (t : ℝ)
        (hb : DifferentiableAt ℝ b u) (hbinj : Function.Injective (fderiv ℝ b u))
        (hbn : ∀ w, (fderiv ℝ b u w) 0 = 0) (hGn : 0 < G (b u) 0) :
        Function.Injective (fderiv ℝ (fun p : Euc 1 × ℝ => Φ (b p.1,p.2)) (u,t)) := by
      obtain ⟨d,hd⟩ := hdiffeo t
      have hdDiff : DifferentiableAt ℝ d (b u) := d.contDiff.differentiable (by simp) (b u)
      have hdInj : Function.Injective (fderiv ℝ d (b u)) := by
        have hdi : DifferentiableAt ℝ d.symm (d (b u)) := d.symm.contDiff.differentiable (by simp) _
        have h := hdi.hasFDerivAt.comp (b u) hdDiff.hasFDerivAt
        have heq : (fun x : Euc 2 => d.symm (d x))=id := funext d.symm_apply_apply
        change HasFDerivAt (fun x : Euc 2 => d.symm (d x)) _ (b u) at h
        rw [heq] at h
        have hid := h.unique (hasFDerivAt_id (b u))
        intro x y hxy
        have hx := congrArg (fun C : Euc 2 →L[ℝ] Euc 2 => C x) hid
        have hy := congrArg (fun C : Euc 2 →L[ℝ] Euc 2 => C y) hid
        exact hx.symm.trans ((congrArg (fderiv ℝ d.symm (d (b u))) hxy).trans hy)
      let A : Euc 1 × ℝ →L[ℝ] Euc 2 := (fderiv ℝ b u).coprod ((1:ℝ →L[ℝ] ℝ).smulRight (G (b u)))
      have hAinj : Function.Injective A := by
        suffices hk : ∀ p, A p=0 → p=0 by
          intro p q hpq
          exact sub_eq_zero.mp (hk (p-q) (by rw [map_sub,hpq,sub_self]))
        intro p hp
        have hn := congrArg (fun q : Euc 2 => q 0) hp
        change (fderiv ℝ b u p.1) 0+p.2*G (b u) 0=0 at hn
        rw [hbn] at hn
        have ht0 : p.2=0 := by nlinarith
        have hu0 : p.1=0 := by
          apply hbinj
          simpa [A,ht0] using hp
        exact Prod.ext hu0 ht0
      let D := fderiv ℝ Φ (b u,0)
      have hD : HasFDerivAt Φ D (b u,0) := (hΦ.differentiable (by simp) _).hasFDerivAt
      have hleft : D.comp (ContinuousLinearMap.inl ℝ (Euc 2) ℝ)=ContinuousLinearMap.id ℝ (Euc 2) := by
        have h := hD.comp (b u) (hasFDerivAt_prodMk_left (𝕜:=ℝ) (b u) (0:ℝ))
        have heq : (fun q : Euc 2 => Φ (q,0))=id := funext hzero
        change HasFDerivAt (fun q : Euc 2 => Φ (q,0)) _ (b u) at h
        rw [heq] at h
        exact h.unique (hasFDerivAt_id (b u))
      have hright : D.comp (ContinuousLinearMap.inr ℝ (Euc 2) ℝ)=
          (1:ℝ →L[ℝ] ℝ).smulRight (G (b u)) := by
        have h := hD.comp 0 (hasFDerivAt_prodMk_right (𝕜:=ℝ) (b u) (0:ℝ))
        have hg := (hder (b u) 0).hasFDerivAt
        rw [hzero] at hg
        exact h.unique hg
      have hR : HasFDerivAt (fun p : Euc 1 × ℝ => Φ (b p.1,p.2-t)) A (u,t) := by
        have hm := (hb.hasFDerivAt.comp (u,t) hasFDerivAt_fst).prodMk
          (HasFDerivAt.sub_const t (hasFDerivAt_snd (𝕜:=ℝ) (p:=(u,t))))
        have hD' : HasFDerivAt Φ D (b (u,t).1,(u,t).2-t) := by simpa using hD
        have hcomp := hD'.comp (u,t) hm
        have heq : D.comp (((fderiv ℝ b u).comp (ContinuousLinearMap.fst ℝ (Euc 1) ℝ)).prod
            (ContinuousLinearMap.snd ℝ (Euc 1) ℝ))=A := by
          apply ContinuousLinearMap.ext
          intro p
          have hp : (fderiv ℝ b u p.1,p.2)=(fderiv ℝ b u p.1,0)+(0,p.2) := by simp
          change D (fderiv ℝ b u p.1,p.2)=A p
          rw [hp,map_add]
          have hl := congrArg (fun C : Euc 2 →L[ℝ] Euc 2 => C (fderiv ℝ b u p.1)) hleft
          have hr := congrArg (fun C : ℝ →L[ℝ] Euc 2 => C p.2) hright
          exact congrArg₂ (·+·) hl hr
        change HasFDerivAt (fun p : Euc 1 × ℝ => Φ (b p.1,p.2-t)) _ (u,t) at hcomp
        rw [heq] at hcomp
        exact hcomp
      have hfull : HasFDerivAt (fun p : Euc 1 × ℝ => Φ (b p.1,p.2))
          ((fderiv ℝ d (b u)).comp A) (u,t) := by
        have hd' : HasFDerivAt d (fderiv ℝ d (b u)) (Φ (b (u,t).1,(u,t).2-t)) := by
          simpa only [Prod.fst,Prod.snd,sub_self,hzero] using hdDiff.hasFDerivAt
        have hc := hd'.comp (u,t) hR
        have heq : (fun p : Euc 1 × ℝ => d (Φ (b p.1,p.2-t)))=
            (fun p : Euc 1 × ℝ => Φ (b p.1,p.2)) := by
          funext p
          rw [hd]
          change Φ (Φ (b p.1,p.2-t),t)=Φ (b p.1,p.2)
          rw [←hadd]
          congr 1
          ring
        change HasFDerivAt (fun p : Euc 1 × ℝ => d (Φ (b p.1,p.2-t))) _ (u,t) at hc
        rw [heq] at hc
        exact hc
      rw [hfull.fderiv]
      exact hdInj.comp hAinj
    obtain ⟨i,A,hA,hzA,T,htT,hTd,G,hG,hGc,hgood⟩ := htube z t ht htd
    have hT : 0 < T := ht.trans_lt htT
    obtain ⟨Φ,hΦ,hzero,hder,hadd,hdiffeo,heq⟩ := hagreement i A T hT hTd G hG hGc hgood
    let c := chartAt (Euc 1) z
    have hc : c ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle := IsManifold.chart_mem_maximalAtlas _
    let B := c '' (c.source ∩ A)
    have hB : IsOpen B := c.isOpen_image_of_subset_source (c.open_source.inter hA) inter_subset_left
    have hz : z ∈ c.source := mem_chart_source _ _
    have hcz : c z ∈ B := ⟨z,⟨hz,hzA⟩,rfl⟩
    have hBtarget : B ⊆ c.target := by
      rintro u ⟨w,hw,rfl⟩
      exact c.map_source hw.1
    have hBback (u : Euc 1) (hu : u ∈ B) : c.symm u ∈ A := by
      obtain ⟨w,hw,rfl⟩ := hu
      rw [c.left_inv hw.1]
      exact hw.2
    let b : Euc 1 → Euc 2 := (X.chart i).extend (𝓡∂ 2) ∘ F.boundary.toFun ∘ c.symm
    have hboundarychart (u : Euc 1) (hu : u ∈ B) : F.boundary.toFun (c.symm u) ∈ (X.chart i).source := by
      have h := (hgood (c.symm u) (hBback u hu) 0 ⟨le_rfl,hT.le⟩).1
      rwa [Z.zero] at h
    have hb (u : Euc 1) (hu : u ∈ B) : ContDiffAt ℝ ∞ b u ∧
        Function.Injective (fderiv ℝ b u) ∧ ∀ v,(fderiv ℝ b u v) 0=0 :=
      hboundary i c hc u (hBtarget hu) (hboundarychart u hu)
    have hGpos (u : Euc 1) (hu : u ∈ B) : 0 < G (b u) 0 := by
      have h := (hgood (c.symm u) (hBback u hu) 0 ⟨le_rfl,hT.le⟩).2
      rw [Z.zero] at h
      change G (b u)=_ at h
      rw [h]
      obtain ⟨a,ha,he⟩ := inward_coordinate_change_positive (F.boundary.toFun (c.symm u))
        (F.boundary.lands_boundary _) (X.chart i) (X.atlas i) (hboundarychart u hu)
      rw [he]
      exact mul_pos ha (X.positive _)
    let H : Euc 1 × ℝ → Euc 2 := fun p => Φ (b p.1,p.2)
    have hH : ContDiffOn ℝ ∞ H (B ×ˢ univ) := by
      have hbs : ContDiffOn ℝ ∞ b B := fun u hu => (hb u hu).1.contDiffWithinAt
      exact hΦ.comp_contDiffOn ((hbs.comp contDiff_fst.contDiffOn (fun p hp => hp.1)).prodMk contDiff_snd.contDiffOn)
    refine ⟨i,c,hc,hz,B,hB,hcz,hBtarget,T,htT,hTd,H,hH,?_,?_,?_,?_⟩
    · intro u hu s
      exact hrank G Φ hΦ hzero hder hadd hdiffeo b u s
        ((hb u hu).1.differentiableAt (by simp)) (hb u hu).2.1 (hb u hu).2.2 (hGpos u hu)
    · intro u hu
      change Φ (b u,0) 0=0
      rw [hzero]
      exact (halfspace_atlas_boundary_interior (X.chart i) (X.atlas i)
        (F.boundary.toFun (c.symm u)) (hboundarychart u hu)).1.mp (F.boundary.lands_boundary _)
    · intro u hu
      have hd := ((hH (u,0) ⟨hu,mem_univ _⟩).contDiffAt
        ((hB.prod isOpen_univ).mem_nhds ⟨hu,mem_univ _⟩)).differentiableAt (by simp) |>.hasFDerivAt
      have hp := hd.comp 0 (hasFDerivAt_prodMk_right (𝕜:=ℝ) u (0:ℝ))
      have hp' : HasDerivAt (fun s => H (u,s)) (fderiv ℝ H (u,0) (0,1)) 0 := by
        change HasFDerivAt (fun s => H (u,s)) _ 0 at hp
        simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply] using hp.hasDerivAt
      have hh : HasDerivAt (fun s => H (u,s)) (G (b u)) 0 := by
        simpa only [H,hzero] using hder (b u) 0
      rw [hp'.unique hh]
      exact hGpos u hu
    · intro u hu s hs
      exact ⟨(hgood (c.symm u) (hBback u hu) s hs).1,(heq (c.symm u) (hBback u hu) s hs).symm⟩
  have hpositiveGiven (z : Circle) (t : ℝ) (ht : 0 < t)
      (i : Fin X.count) (c : OpenPartialHomeomorph Circle (Euc 1))
      (hc : c ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle) (hz : z ∈ c.source)
      (B : Set (Euc 1)) (hB : IsOpen B) (hcz : c z ∈ B) (hBt : B ⊆ c.target)
      (T : ℝ) (htT : t < T) (H : Euc 1 × ℝ → Euc 2)
      (hH : ContDiffOn ℝ ∞ H (B ×ˢ univ))
      (hHr : Function.Injective (fderiv ℝ H (c z,t)))
      (hHeq : ∀ u ∈ B,∀ s ∈ Icc 0 T,
        Z.flow (c.symm u,s) ∈ (X.chart i).source ∧
        H (u,s)=(X.chart i).extend (𝓡∂ 2) (Z.flow (c.symm u,s))) :
      ∃ Γ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 2) (Circle × ℝ) F.surface ∞,
        (z,t) ∈ Γ.source ∧ EqOn Γ Z.flow Γ.source := by
    let U := B ×ˢ Ioo 0 T
    have hU : IsOpen U := hB.prod isOpen_Ioo
    have hpU : (c z,t) ∈ U := ⟨hcz,ht,htT⟩
    let D : (Euc 1 × ℝ) ≃L[ℝ] Euc 2 :=
      ((fderiv ℝ H (c z,t)).toLinearMap.linearEquivOfInjective hHr (by simp [Module.finrank_prod])).toContinuousLinearEquiv
    have hD : (D : (Euc 1 × ℝ) →L[ℝ] Euc 2)=fderiv ℝ H (c z,t) := by rfl
    have hder : HasFDerivAt H (D : (Euc 1 × ℝ) →L[ℝ] Euc 2) (c z,t) := by
      rw [hD]
      exact ((hH.mono (fun p hp => ⟨hp.1,mem_univ _⟩)).contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp) |>.hasFDerivAt
    obtain ⟨β,hpβ,hβU,hβ,hβinv,hβeq⟩ := DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv
      (hH.mono (fun p hp => ⟨hp.1,mem_univ _⟩)) hU hpU hder
    let e := (X.chart i).extend (𝓡∂ 2)
    have hβtarget : β.target ⊆ e.target := by
      intro q hq
      have hr := hβU (β.map_target hq)
      have heq := (hHeq (β.symm q).1 hr.1 (β.symm q).2 ⟨hr.2.1.le,hr.2.2.le⟩).2
      have hsource := (hHeq (β.symm q).1 hr.1 (β.symm q).2 ⟨hr.2.1.le,hr.2.2.le⟩).1
      rw [←β.right_inv hq,hβeq,heq]
      exact e.map_source (by simpa only [e,OpenPartialHomeomorph.extend_source] using hsource)
    let targetChart : PartialDiffeomorph (𝓡∂ 2) 𝓘(ℝ,Euc 2) F.surface (Euc 2) ∞ :=
      { toPartialEquiv :=
          { toFun := e
            invFun := e.symm
            source := (X.chart i).source ∩ e ⁻¹' β.target
            target := β.target
            map_source' := fun x hx => hx.2
            map_target' := fun q hq => ⟨by simpa only [e,OpenPartialHomeomorph.extend_source] using e.map_target (hβtarget hq),by change e (e.symm q) ∈ β.target;rw [e.right_inv (hβtarget hq)];exact hq⟩
            left_inv' := fun x hx => e.left_inv (by simpa only [e,OpenPartialHomeomorph.extend_source] using hx.1)
            right_inv' := fun q hq => e.right_inv (hβtarget hq) }
        open_source := (X.chart i).isOpen_inter_preimage (β.open_target.preimage (𝓡∂ 2).continuous)
        open_target := β.open_target
        contMDiffOn_toFun := ((X.chart i).contMDiffOn_extend (X.atlas i)).mono inter_subset_left
        contMDiffOn_invFun := (by
          have hs := contMDiffOn_extend_symm (X.atlas i)
          rw [←(X.chart i).extend_target'] at hs
          exact hs.mono hβtarget) }
    let cp := c.prod (OpenPartialHomeomorph.refl ℝ)
    let sourceChart : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,Euc 1 × ℝ)
        (Circle × ℝ) (Euc 1 × ℝ) ∞ :=
      { toPartialEquiv := cp.toPartialEquiv
        open_source := cp.open_source
        open_target := cp.open_target
        contMDiffOn_toFun := by
          have h : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ,ℝ)) ((𝓡 1).prod 𝓘(ℝ,ℝ)) ∞ cp cp.source :=
            ((contMDiffOn_of_mem_maximalAtlas hc).comp contMDiff_fst.contMDiffOn (fun p hp => hp.1)).prodMk contMDiff_snd.contMDiffOn
          rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod] at h
          exact h
        contMDiffOn_invFun := by
          have h : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ,ℝ)) ((𝓡 1).prod 𝓘(ℝ,ℝ)) ∞ cp.symm cp.target :=
            ((contMDiffOn_symm_of_mem_maximalAtlas hc).comp contMDiff_fst.contMDiffOn (fun p hp => hp.1)).prodMk contMDiff_snd.contMDiffOn
          rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod] at h
          exact h }
    let βD : PartialDiffeomorph 𝓘(ℝ,Euc 1 × ℝ) 𝓘(ℝ,Euc 2) (Euc 1 × ℝ) (Euc 2) ∞ :=
      { toPartialEquiv := β.toPartialEquiv
        open_source := β.open_source
        open_target := β.open_target
        contMDiffOn_toFun := hβ.contMDiffOn
        contMDiffOn_invFun := hβinv.contMDiffOn }
    let Γ := (sourceChart.trans βD).trans targetChart.symm
    have hpΓ : (z,t) ∈ Γ.source := by
      change ((z ∈ c.source ∧ t ∈ (univ:Set ℝ)) ∧ (c z,t) ∈ β.source) ∧ β (c z,t) ∈ β.target
      exact ⟨⟨⟨hz,mem_univ _⟩,hpβ⟩,β.map_source hpβ⟩
    refine ⟨Γ,hpΓ,?_⟩
    intro p hp
    have hcsource : p.1 ∈ c.source := hp.1.1.1
    have hcoord : (c p.1,p.2) ∈ β.source := hp.1.2
    have hu := hβU hcoord
    have hmem := hHeq (c p.1) hu.1 p.2 ⟨hu.2.1.le,hu.2.2.le⟩
    rw [c.left_inv hcsource] at hmem
    change e.symm (β (c p.1,p.2))=Z.flow p
    rw [hβeq,hmem.2]
    exact e.left_inv (by simpa only [e,OpenPartialHomeomorph.extend_source] using hmem.1)
  have hlowerGiven (z : Circle)
      (i : Fin X.count) (c : OpenPartialHomeomorph Circle (Euc 1))
      (hc : c ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle) (hz : z ∈ c.source)
      (B : Set (Euc 1)) (hB : IsOpen B) (hcz : c z ∈ B) (hBt : B ⊆ c.target)
      (T : ℝ) (hT : 0 < T) (H : Euc 1 × ℝ → Euc 2)
      (hH : ContDiffOn ℝ ∞ H (B ×ˢ univ))
      (hHr : Function.Injective (fderiv ℝ H (c z,0)))
      (hHz : ∀ u ∈ B,H (u,0) 0=0)
      (hHp : 0 < (fderiv ℝ H (c z,0) (0,1)) 0)
      (hHeq : ∀ u ∈ B,∀ s ∈ Icc 0 T,
        Z.flow (c.symm u,s) ∈ (X.chart i).source ∧
        H (u,s)=(X.chart i).extend (𝓡∂ 2) (Z.flow (c.symm u,s))) :
      ∃ Δ : PartialDiffeomorph CollarModel (𝓡∂ 2) (Circle × Time) F.surface ∞,
        (z,0) ∈ Δ.source ∧ Δ.source ⊆ {p | (p.2:ℝ)<1} ∧
        EqOn Δ (fun p : Circle × Time => Z.flow (p.1,Z.lambda*(p.2:ℝ))) Δ.source := by
    have hsign (H : Euc 1 × ℝ → Euc 2) (B : Set (Euc 1)) (hB : IsOpen B)
        (u : Euc 1) (hu : u ∈ B) (T : ℝ) (hT : 0 < T)
        (hH : ContDiffOn ℝ ∞ H (B ×ˢ univ))
        (hz : ∀ w ∈ B,H (w,0) 0=0)
        (hp : 0 < (fderiv ℝ H (u,0) (0,1)) 0) :
        ∃ A : Set (Euc 1),IsOpen A ∧ u ∈ A ∧ A ⊆ B ∧
          ∃ r : ℝ,0 < r ∧ r < T ∧
            ∀ w ∈ A,∀ s ∈ Ioo (-r) r, (0 ≤ H (w,s) 0 ↔ 0 ≤ s) := by
      let g : Euc 1 × ℝ → ℝ := fun p => (fderiv ℝ H p (0,1)) 0
      have hD : IsOpen (B ×ˢ (univ:Set ℝ)) := hB.prod isOpen_univ
      have hg : ContinuousOn g (B ×ˢ univ) := by
        exact (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin 2)).continuous.comp_continuousOn
          ((hH.continuousOn_fderiv_of_isOpen hD (by simp)).clm_apply continuousOn_const)
      let V := (B ×ˢ (univ:Set ℝ)) ∩ g ⁻¹' Ioi 0
      have hV : IsOpen V := hg.isOpen_inter_preimage hD isOpen_Ioi
      have huV : (u,0) ∈ V := ⟨⟨hu,mem_univ _⟩,hp⟩
      obtain ⟨A,W,hA,hW,huA,h0W,hAW⟩ := isOpen_prod_iff.mp hV u 0 huV
      obtain ⟨a,ha,haW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h0W)
      let r := min (a/2) (T/2)
      have hr : 0 < r := lt_min (half_pos ha) (half_pos hT)
      have hra : r < a := (min_le_left _ _).trans_lt (by linarith)
      have hrT : r < T := (min_le_right _ _).trans_lt (by linarith)
      have hinterval (s : ℝ) (hs : s ∈ Ioo (-r) r) : s ∈ W := by
        apply haW
        change dist s 0 < a
        rw [Real.dist_eq,sub_zero,abs_lt]
        constructor <;> linarith [hs.1,hs.2]
      have hAB : A ⊆ B := fun w hw => (hAW (show (w,(0:ℝ)) ∈ A ×ˢ W from ⟨hw,h0W⟩)).1.1
      refine ⟨A,hA,huA,hAB,r,hr,hrT,?_⟩
      intro w hw
      let f : ℝ → ℝ := fun s => H (w,s) 0
      have hder (s : ℝ) (hs : s ∈ Ioo (-r) r) : HasDerivAt f (g (w,s)) s := by
        have hd := ((hH (w,s) ⟨hAB hw,mem_univ _⟩).contDiffAt
          (hD.mem_nhds ⟨hAB hw,mem_univ _⟩)).differentiableAt (by simp) |>.hasFDerivAt
        have hc := hd.comp s (hasFDerivAt_prodMk_right (𝕜:=ℝ) w s)
        have hc' : HasDerivAt (fun s => H (w,s)) (fderiv ℝ H (w,s) (0,1)) s := by
          change HasFDerivAt (fun s => H (w,s)) _ s at hc
          simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply] using hc.hasDerivAt
        exact (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin 2)).hasFDerivAt.comp_hasDerivAt s hc'
      have hmono : StrictMonoOn f (Ioo (-r) r) :=
        strictMonoOn_of_deriv_pos (convex_Ioo (-r) r)
          (fun s hs => (hder s hs).continuousAt.continuousWithinAt) (fun s hs => by
            have hs' : s ∈ Ioo (-r) r := interior_subset hs
            rw [(hder s hs').deriv]
            exact (hAW ⟨hw,hinterval s hs'⟩).2)
      have h0 : 0 ∈ Ioo (-r) r := ⟨neg_lt_zero.mpr hr,hr⟩
      have hf0 : f 0=0 := hz w (hAB hw)
      intro s hs
      change 0 ≤ f s ↔ 0 ≤ s
      constructor
      · intro hfs
        by_contra hneg
        have hlt := hmono hs h0 (lt_of_not_ge hneg)
        rw [hf0] at hlt
        linarith
      · intro hs0
        by_cases hse : s=0
        · rw [hse,hf0]
        · have hlt := hmono h0 hs (lt_of_le_of_ne hs0 (Ne.symm hse))
          rw [hf0] at hlt
          exact hlt.le
    have hinverse (β : OpenPartialHomeomorph (Euc 1 × ℝ) (Euc 2))
        (hβ : ContDiffOn ℝ ∞ β β.source) (hβinv : ContDiffOn ℝ ∞ β.symm β.target)
        (hsign : ∀ p ∈ β.source,0 ≤ β p 0 ↔ 0 ≤ p.2) :
        ∃ φ : PartialDiffeomorph CollarModel (𝓡∂ 2)
            (Euc 1 × EuclideanHalfSpace 1) (EuclideanHalfSpace 2) ∞,
          φ.source={p | (p.1,(p.2.val) 0) ∈ β.source} ∧
          φ.target={q | q.val ∈ β.target} ∧
          ∀ p ∈ φ.source,(𝓡∂ 2) (φ p)=β (p.1,(p.2.val) 0) := by
      let enc : Euc 1 × EuclideanHalfSpace 1 → Euc 1 × ℝ := fun p => (p.1,p.2.val 0)
      let dec : Euc 1 × ℝ → Euc 1 × EuclideanHalfSpace 1 :=
        fun p => (p.1,(𝓡∂ 1).symm (EuclideanSpace.single 0 p.2))
      have hencdec (p : Euc 1 × ℝ) (hp : 0 ≤ p.2) : enc (dec p)=p := by
        have hr : EuclideanSpace.single (0:Fin 1) p.2 ∈ range (𝓡∂ 1) := by
          rw [range_modelWithCornersEuclideanHalfSpace]
          simpa using hp
        apply Prod.ext
        · rfl
        · change ((𝓡∂ 1) ((𝓡∂ 1).symm (EuclideanSpace.single 0 p.2))) 0=p.2
          rw [(𝓡∂ 1).right_inv hr]
          simp
      have hdecenc (p : Euc 1 × EuclideanHalfSpace 1) : dec (enc p)=p := by
        apply Prod.ext
        · rfl
        · have h : EuclideanSpace.single (0:Fin 1) (p.2.val 0)=p.2.val := by ext i;fin_cases i;simp
          change (𝓡∂ 1).symm (EuclideanSpace.single 0 (p.2.val 0))=p.2
          rw [h]
          exact (𝓡∂ 1).left_inv p.2
      have henc : ContMDiff CollarModel 𝓘(ℝ,Euc 1 × ℝ) ∞ enc :=
        contMDiff_fst.prodMk_space
          ((EuclideanSpace.proj (𝕜:=ℝ) (0:Fin 1)).contMDiff.comp ((𝓡∂ 1).contMDiff.comp contMDiff_snd))
      have hencnn (p : Euc 1 × EuclideanHalfSpace 1) : 0 ≤ (enc p).2 := p.2.property
      have hβrange (p : Euc 1 × EuclideanHalfSpace 1) (hp : enc p ∈ β.source) : β (enc p) ∈ range (𝓡∂ 2) := by
        rw [range_modelWithCornersEuclideanHalfSpace]
        exact (hsign _ hp).mpr (hencnn p)
      have hβinvnn (q : EuclideanHalfSpace 2) (hq : q.val ∈ β.target) : 0 ≤ (β.symm q.val).2 := by
        apply (hsign _ (β.map_target hq)).mp
        rw [β.right_inv hq]
        exact q.property
      let source := {p : Euc 1 × EuclideanHalfSpace 1 | enc p ∈ β.source}
      let target := {q : EuclideanHalfSpace 2 | q.val ∈ β.target}
      let φeq : PartialEquiv (Euc 1 × EuclideanHalfSpace 1) (EuclideanHalfSpace 2) :=
        { toFun := fun p => (𝓡∂ 2).symm (β (enc p))
          invFun := fun q => dec (β.symm q.val)
          source := source
          target := target
          map_source' := by
            intro p hp
            change ((𝓡∂ 2) ((𝓡∂ 2).symm (β (enc p)))) ∈ β.target
            rw [(𝓡∂ 2).right_inv (hβrange p hp)]
            exact β.map_source hp
          map_target' := by
            intro q hq
            change enc (dec (β.symm q.val)) ∈ β.source
            rw [hencdec _ (hβinvnn q hq)]
            exact β.map_target hq
          left_inv' := by
            intro p hp
            change dec (β.symm ((𝓡∂ 2) ((𝓡∂ 2).symm (β (enc p)))))=p
            rw [(𝓡∂ 2).right_inv (hβrange p hp),β.left_inv hp,hdecenc]
          right_inv' := by
            intro q hq
            change (𝓡∂ 2).symm (β (enc (dec (β.symm q.val))))=q
            rw [hencdec _ (hβinvnn q hq),β.right_inv hq]
            exact (𝓡∂ 2).left_inv q }
      let φ : PartialDiffeomorph CollarModel (𝓡∂ 2)
          (Euc 1 × EuclideanHalfSpace 1) (EuclideanHalfSpace 2) ∞ :=
        { toPartialEquiv := φeq
          open_source := β.open_source.preimage henc.continuous
          open_target := β.open_target.preimage continuous_subtype_val
          contMDiffOn_toFun := (𝓡∂ 2).contMDiffOn_symm.comp
            (hβ.contMDiffOn.comp henc.contMDiffOn (fun p hp => hp)) hβrange
          contMDiffOn_invFun := by
            have hh : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,Euc 1 × ℝ) ∞
                (fun q : EuclideanHalfSpace 2 => β.symm q.val) target :=
              hβinv.contMDiffOn.comp (𝓡∂ 2).contMDiff.contMDiffOn (fun q hq => hq)
            have hhfst : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,Euc 1) ∞
                (fun q : EuclideanHalfSpace 2 => (β.symm q.val).1) target :=
              contDiff_fst.contMDiff.comp_contMDiffOn hh
            have hhsnd : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,ℝ) ∞
                (fun q : EuclideanHalfSpace 2 => (β.symm q.val).2) target :=
              contDiff_snd.contMDiff.comp_contMDiffOn hh
            let a : ℝ →L[ℝ] Euc 1 := (1:ℝ →L[ℝ] ℝ).smulRight (EuclideanSpace.single (0:Fin 1) 1)
            have ha : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,Euc 1) ∞
                (fun q : EuclideanHalfSpace 2 => EuclideanSpace.single (0:Fin 1) (β.symm q.val).2) target := by
              have h := a.contMDiff.comp_contMDiffOn hhsnd
              apply h.congr
              intro q hq
              ext i
              fin_cases i
              simp [a,ContinuousLinearMap.smulRight_apply]
            exact hhfst.prodMk ((𝓡∂ 1).contMDiffOn_symm.comp ha (by
              intro q hq
              rw [range_modelWithCornersEuclideanHalfSpace]
              simpa using hβinvnn q hq)) }
      refine ⟨φ,rfl,rfl,?_⟩
      intro p hp
      exact (𝓡∂ 2).right_inv (hβrange p hp)
    have hhalf (a : ℝ) (ha : 0<a) :
        ∃ d : Diffeomorph (𝓡∂ 1) (𝓡∂ 1) (EuclideanHalfSpace 1) (EuclideanHalfSpace 1) ∞,
          ∀ u, (𝓡∂ 1) (d u)=a⁻¹ • (𝓡∂ 1) u := by
      let f : EuclideanHalfSpace 1 → EuclideanHalfSpace 1 :=
        fun u => ⟨a⁻¹ • u.val,by
          change 0≤a⁻¹ * u.val 0
          exact mul_nonneg (inv_nonneg.mpr ha.le) u.property⟩
      let g : EuclideanHalfSpace 1 → EuclideanHalfSpace 1 :=
        fun u => ⟨a • u.val,by
          change 0≤a * u.val 0
          exact mul_nonneg ha.le u.property⟩
      have hfg : Function.LeftInverse f g := by
        intro u; apply Subtype.ext; simp [f,g,smul_smul,ne_of_gt ha]
      have hgf : Function.LeftInverse g f := by
        intro u; apply Subtype.ext; simp [f,g,smul_smul,ne_of_gt ha]
      have hf : (fun u => (𝓡∂ 1).symm (a⁻¹ • (𝓡∂ 1) u))=f := by
        funext u
        exact (𝓡∂ 1).left_inv (f u)
      have hg : (fun u => (𝓡∂ 1).symm (a • (𝓡∂ 1) u))=g := by
        funext u
        exact (𝓡∂ 1).left_inv (g u)
      have hfs : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ f := by
        rw [←hf]
        exact (𝓡∂ 1).contMDiffOn_symm.comp_contMDiff
          ((contMDiff_const (I:=𝓡∂ 1) (I':=𝓘(ℝ,ℝ)) (c:=a⁻¹)).smul (𝓡∂ 1).contMDiff) (fun u => mem_range_self (f u))
      have hgs : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ g := by
        rw [←hg]
        exact (𝓡∂ 1).contMDiffOn_symm.comp_contMDiff
          ((contMDiff_const (I:=𝓡∂ 1) (I':=𝓘(ℝ,ℝ)) (c:=a)).smul (𝓡∂ 1).contMDiff) (fun u => mem_range_self (g u))
      exact ⟨⟨⟨f,g,hgf,hfg⟩,hfs,hgs⟩,fun _ => rfl⟩
    obtain ⟨A,hA,hczA,hAB,r,hr,hrT,hsgn⟩ := hsign H B hB (c z) hcz T hT hH hHz hHp
    let U := A ×ˢ Ioo (-r) r
    have hU : IsOpen U := hA.prod isOpen_Ioo
    have hpU : (c z,(0:ℝ)) ∈ U := ⟨hczA,neg_lt_zero.mpr hr,hr⟩
    let D : (Euc 1 × ℝ) ≃L[ℝ] Euc 2 :=
      ((fderiv ℝ H (c z,0)).toLinearMap.linearEquivOfInjective hHr (by simp [Module.finrank_prod])).toContinuousLinearEquiv
    have hD : (D : (Euc 1 × ℝ) →L[ℝ] Euc 2)=fderiv ℝ H (c z,0) := rfl
    have hHU : ContDiffOn ℝ ∞ H U := hH.mono (fun p hp => ⟨hAB hp.1,mem_univ _⟩)
    have hder : HasFDerivAt H (D : (Euc 1 × ℝ) →L[ℝ] Euc 2) (c z,0) := by
      rw [hD]
      exact (hHU.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp) |>.hasFDerivAt
    obtain ⟨β,hpβ,hβU,hβ,hβinv,hβeq⟩ := DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv
      hHU hU hpU hder
    obtain ⟨φ,hφs,hφt,hφeq⟩ := hinverse β hβ hβinv (by
      intro p hp
      rw [hβeq]
      exact hsgn p.1 (hβU hp).1 p.2 (hβU hp).2)
    have hφtarget : φ.target ⊆ (X.chart i).target := by
      intro q hq
      have hqt : q.val ∈ β.target := by rwa [hφt] at hq
      have hbt := β.map_target hqt
      have hu := hβU hbt
      have hn : 0 ≤ (β.symm q.val).2 := by
        apply (hsgn _ hu.1 _ hu.2).mp
        rw [←hβeq,β.right_inv hqt]
        exact q.property
      have heq := hHeq (β.symm q.val).1 (hAB hu.1) (β.symm q.val).2 ⟨hn,hu.2.2.le.trans hrT.le⟩
      have hcq : (X.chart i) (Z.flow (c.symm (β.symm q.val).1,(β.symm q.val).2))=q := by
        apply (𝓡∂ 2).injective
        change (X.chart i).extend (𝓡∂ 2) (Z.flow (c.symm (β.symm q.val).1,(β.symm q.val).2))=q.val
        rw [←heq.2,←hβeq,β.right_inv hqt]
      rw [←hcq]
      exact (X.chart i).map_source heq.1
    have hleft : IccLeftChart 0 1 ∈ IsManifold.maximalAtlas (𝓡∂ 1) ∞ Time := by
      rw [←Icc_chartedSpaceChartAt_of_le_top (z:=(0:Time)) (by norm_num)]
      exact IsManifold.chart_mem_maximalAtlas _
    let dom := c.prod (IccLeftChart 0 1)
    let cd : PartialDiffeomorph CollarModel CollarModel (Circle × Time) (Euc 1 × EuclideanHalfSpace 1) ∞ :=
      { toPartialEquiv := dom.toPartialEquiv
        open_source := dom.open_source
        open_target := dom.open_target
        contMDiffOn_toFun :=
          ((contMDiffOn_of_mem_maximalAtlas hc).comp contMDiff_fst.contMDiffOn (fun p hp => hp.1)).prodMk
            ((contMDiffOn_of_mem_maximalAtlas hleft).comp contMDiff_snd.contMDiffOn (fun p hp => hp.2))
        contMDiffOn_invFun :=
          ((contMDiffOn_symm_of_mem_maximalAtlas hc).comp contMDiff_fst.contMDiffOn (fun p hp => hp.1)).prodMk
            ((contMDiffOn_symm_of_mem_maximalAtlas hleft).comp contMDiff_snd.contMDiffOn (fun p hp => hp.2)) }
    obtain ⟨dh,hdh⟩ := hhalf Z.lambda Z.lambda_pos
    let ds := ((Diffeomorph.refl (𝓡 1) (Euc 1) ∞).prodCongr dh.symm).toPartialDiffeomorph
    have hds (p : Circle × Time) :
        ((ds (cd p)).1,((ds (cd p)).2.val) 0)=(c p.1,Z.lambda*(p.2:ℝ)) := by
      apply Prod.ext
      · rfl
      · have hh := hdh (dh.symm (IccLeftChart 0 1 p.2))
        rw [dh.apply_symm_apply] at hh
        have he := congrArg (fun u : Euc 1 => u 0) hh
        change (p.2:ℝ)-0=Z.lambda⁻¹*((dh.symm (IccLeftChart 0 1 p.2)).val 0) at he
        change ((dh.symm (IccLeftChart 0 1 p.2)).val 0)=Z.lambda*(p.2:ℝ)
        simp only [sub_zero] at he
        rw [←div_eq_inv_mul] at he
        exact ((eq_div_iff (ne_of_gt Z.lambda_pos)).mp he).symm.trans (mul_comm _ _)
    let tc : PartialDiffeomorph (𝓡∂ 2) (𝓡∂ 2) F.surface (EuclideanHalfSpace 2) ∞ :=
      { toPartialEquiv := (X.chart i).toPartialEquiv
        open_source := (X.chart i).open_source
        open_target := (X.chart i).open_target
        contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas (X.atlas i)
        contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas (X.atlas i) }
    let Δ := ((cd.trans ds).trans φ).trans tc.symm
    have hcoord (p : Circle × Time) (hp : ds (cd p) ∈ φ.source) :
        (c p.1,Z.lambda*(p.2:ℝ)) ∈ β.source := by
      rw [hφs] at hp
      change ((ds (cd p)).1,((ds (cd p)).2.val) 0) ∈ β.source at hp
      rwa [hds] at hp
    have hpφ : ds (cd (z,(0:Time))) ∈ φ.source := by
      rw [hφs]
      change ((ds (cd (z,(0:Time)))).1,((ds (cd (z,(0:Time)))).2.val) 0) ∈ β.source
      rw [hds]
      simpa using hpβ
    have hpΔ : (z,(0:Time)) ∈ Δ.source := by
      change ((((z,(0:Time)) ∈ dom.source ∧ cd (z,0) ∈ (univ:Set (Euc 1 × EuclideanHalfSpace 1))) ∧
        ds (cd (z,0)) ∈ φ.source) ∧ φ (ds (cd (z,0))) ∈ (X.chart i).target)
      exact ⟨⟨⟨⟨hz,by change (0:ℝ)<1;norm_num⟩,mem_univ _⟩,hpφ⟩,hφtarget (φ.toPartialEquiv.map_source hpφ)⟩
    refine ⟨Δ,hpΔ,(fun p hp => hp.1.1.1.2),?_⟩
    intro p hp
    have hpc : p.1 ∈ c.source := hp.1.1.1.1
    have hpφ' : ds (cd p) ∈ φ.source := hp.1.2
    have hpcβ := hcoord p hpφ'
    have hu := hβU hpcβ
    have heq := hHeq (c p.1) (hAB hu.1) (Z.lambda*(p.2:ℝ))
      ⟨mul_nonneg Z.lambda_pos.le p.2.property.1,hu.2.2.le.trans hrT.le⟩
    rw [c.left_inv hpc] at heq
    have hchart : φ (ds (cd p))=(X.chart i) (Z.flow (p.1,Z.lambda*(p.2:ℝ))) := by
      apply (𝓡∂ 2).injective
      rw [hφeq _ hpφ',hds,hβeq]
      exact heq.2
    change (X.chart i).symm (φ (ds (cd p)))=Z.flow (p.1,Z.lambda*(p.2:ℝ))
    rw [hchart]
    exact (X.chart i).left_inv heq.1
  have hlowerCharts (f : Circle × Time → F.surface) (p : Circle × Time)
      (hp : (p.2:ℝ)<1)
      (Δ : PartialDiffeomorph CollarModel (𝓡∂ 2) (Circle × Time) F.surface ∞)
      (hpΔ : p ∈ Δ.source) (hΔeq : EqOn Δ f Δ.source) :
      ∃ source : OpenPartialHomeomorph (Circle × Time) (Euc 1 × EuclideanHalfSpace 1),
      ∃ target : OpenPartialHomeomorph F.surface (EuclideanHalfSpace 2),
      ∃ L : ((Euc 1 × Euc 1) × Euc 0) ≃L[ℝ] Euc 2,
        p ∈ source.source ∧ f p ∈ target.source ∧
        source ∈ IsManifold.maximalAtlas CollarModel ∞ (Circle × Time) ∧
        target ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ F.surface ∧
        source.source ⊆ f ⁻¹' target.source ∧
        EqOn (target.extend (𝓡∂ 2) ∘ f ∘ (source.extend CollarModel).symm)
          (fun u => L (u,0)) (source.extend CollarModel).target := by
    have hbridge (B : CollarModelBridge) :
        ContMDiff CollarModel (𝓡∂ 2) ∞ B.homeo ∧
          ContMDiff (𝓡∂ 2) CollarModel ∞ B.homeo.symm := by
      have hf : (fun p => (𝓡∂ 2).symm (B.linear (CollarModel p)))=B.homeo := by
        funext p
        rw [←B.compatible p]
        exact (𝓡∂ 2).left_inv _
      have hi : (fun p => CollarModel.symm (B.linear.symm ((𝓡∂ 2) p)))=B.homeo.symm := by
        funext p
        have he := B.compatible (B.homeo.symm p)
        rw [B.homeo.apply_symm_apply] at he
        rw [he,B.linear.symm_apply_apply]
        exact CollarModel.left_inv _
      have hc : ContMDiff CollarModel 𝓘(ℝ,Euc 1 × Euc 1) ∞
          (fun p : Euc 1 × EuclideanHalfSpace 1 => (p.1,(𝓡∂ 1) p.2)) := by
        rw [modelWithCornersSelf_prod,←chartedSpaceSelf_prod]
        exact contMDiff_fst.prodMk ((𝓡∂ 1).contMDiff.comp contMDiff_snd)
      constructor
      · rw [←hf]
        apply (𝓡∂ 2).contMDiffOn_symm.comp_contMDiff
          (B.linear.contDiff.contMDiff.comp hc)
        intro p
        change B.linear (CollarModel p) ∈ range (𝓡∂ 2)
        rw [←B.compatible p]
        exact mem_range_self _
      · rw [←hi]
        have hh := B.linear.symm.contDiff.contMDiff.comp (𝓡∂ 2).contMDiff (n:=∞)
        rw [modelWithCornersSelf_prod,←chartedSpaceSelf_prod] at hh
        exact hh.fst.prodMk ((𝓡∂ 1).contMDiffOn_symm.comp_contMDiff hh.snd (by
          intro p
          have he := B.compatible (B.homeo.symm p)
          rw [B.homeo.apply_symm_apply] at he
          rw [he,B.linear.symm_apply_apply]
          exact mem_range_self _))
    let l₂ : (Euc 1 × Euc 1) ≃ₗ[ℝ] Euc 2 :=
      { toFun := fun p => !₂[p.2 0, p.1 0]
        invFun := fun w => (!₂[w 1], !₂[w 0])
        left_inv := by
          intro p
          apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
        right_inv := by intro w; ext i; fin_cases i <;> rfl
        map_add' := by intro p q; ext i; fin_cases i <;> rfl
        map_smul' := by intro r p; ext i; fin_cases i <;> rfl }
    let L₂ := l₂.toContinuousLinearEquiv
    let e₂ : (Euc 1 × EuclideanHalfSpace 1) ≃ EuclideanHalfSpace 2 :=
      { toFun := fun p => ⟨L₂ (p.1, p.2.val), p.2.property⟩
        invFun := fun w => ((L₂.symm w.val).1, ⟨(L₂.symm w.val).2, w.property⟩)
        left_inv := by
          intro p
          refine Prod.ext ?_ ?_
          · ext i; fin_cases i; rfl
          · apply Subtype.ext; ext i; fin_cases i; rfl
        right_inv := by
          intro w
          apply Subtype.ext
          exact L₂.apply_symm_apply w.val }
    let h₂ : (Euc 1 × EuclideanHalfSpace 1) ≃ₜ EuclideanHalfSpace 2 :=
      { toEquiv := e₂
        continuous_toFun := (L₂.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
        continuous_invFun :=
          ((continuous_fst.comp (L₂.symm.continuous.comp continuous_subtype_val)).prodMk
            ((continuous_snd.comp (L₂.symm.continuous.comp continuous_subtype_val)).subtype_mk _)) }
    let B : CollarModelBridge :=
      { homeo := h₂
        linear := L₂
        formula := fun _ => rfl
        linear_formula := fun _ => rfl
        compatible := fun _ => rfl }
    let db : Diffeomorph CollarModel (𝓡∂ 2) (Euc 1 × EuclideanHalfSpace 1) (EuclideanHalfSpace 2) ∞ :=
      ⟨B.homeo.toEquiv,(hbridge B).1,(hbridge B).2⟩
    let cc := chartAt (Euc 1) p.1
    have hcc : cc ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle := IsManifold.chart_mem_maximalAtlas _
    have hleft : IccLeftChart 0 1 ∈ IsManifold.maximalAtlas (𝓡∂ 1) ∞ Time := by
      rw [←Icc_chartedSpaceChartAt_of_le_top (z:=(0:Time)) (by norm_num)]
      exact IsManifold.chart_mem_maximalAtlas _
    let dom0 := cc.prod (IccLeftChart 0 1)
    have hdom0 : dom0 ∈ IsManifold.maximalAtlas CollarModel ∞ (Circle × Time) :=
      IsManifold.mem_maximalAtlas_prod hcc hleft
    let dom := dom0.restr Δ.source
    have hdom : dom ∈ IsManifold.maximalAtlas CollarModel ∞ (Circle × Time) :=
      restr_mem_maximalAtlas _ hdom0 Δ.open_source
    have hdoms : dom.source=dom0.source ∩ Δ.source := dom0.restr_source' _ Δ.open_source
    let cd : PartialDiffeomorph CollarModel CollarModel (Circle × Time) (Euc 1 × EuclideanHalfSpace 1) ∞ :=
      { toPartialEquiv := dom0.toPartialEquiv
        open_source := dom0.open_source
        open_target := dom0.open_target
        contMDiffOn_toFun :=
          ((contMDiffOn_of_mem_maximalAtlas hcc).comp contMDiff_fst.contMDiffOn (fun p hp => hp.1)).prodMk
            ((contMDiffOn_of_mem_maximalAtlas hleft).comp contMDiff_snd.contMDiffOn (fun p hp => hp.2))
        contMDiffOn_invFun :=
          ((contMDiffOn_symm_of_mem_maximalAtlas hcc).comp contMDiff_fst.contMDiffOn (fun p hp => hp.1)).prodMk
            ((contMDiffOn_symm_of_mem_maximalAtlas hleft).comp contMDiff_snd.contMDiffOn (fun p hp => hp.2)) }
    let codD := (Δ.symm.trans cd).trans db.toPartialDiffeomorph
    let cod := codD.toOpenPartialHomeomorph
    have hcod : cod ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ F.surface :=
      cod.mem_maximalAtlas_of_contMDiffOn codD.contMDiffOn_toFun codD.contMDiffOn_invFun
    have hmem (q : Circle × Time) (hq : q ∈ dom.source) :
        f q ∈ cod.source ∧ cod (f q)=B.homeo (dom0 q) := by
      rw [hdoms] at hq
      have hcancel : Δ.symm (f q)=q := by rw [←hΔeq hq.2];exact Δ.toPartialEquiv.left_inv hq.2
      constructor
      · change ((f q ∈ Δ.target ∧ Δ.symm (f q) ∈ dom0.source) ∧
          cd (Δ.symm (f q)) ∈ (univ:Set (Euc 1 × EuclideanHalfSpace 1)))
        refine ⟨⟨?_,?_⟩,mem_univ _⟩
        · rw [←hΔeq hq.2];exact Δ.toPartialEquiv.map_source hq.2
        · rw [hcancel];exact hq.1
      · change B.homeo (dom0 (Δ.symm (f q)))=B.homeo (dom0 q)
        rw [hcancel]
    have hpdom : p ∈ dom.source := by rw [hdoms];exact ⟨⟨mem_chart_source _ _,hp⟩,hpΔ⟩
    let L := (ContinuousLinearEquiv.prodUnique ℝ (Euc 1 × Euc 1) (Euc 0)).trans B.linear
    refine ⟨dom,cod,L,hpdom,(hmem p hpdom).1,hdom,hcod,(fun q hq => (hmem q hq).1),?_⟩
    intro u hu
    let q := (dom.extend CollarModel).symm u
    have hq : q ∈ dom.source := by simpa only [OpenPartialHomeomorph.extend_source] using (dom.extend CollarModel).map_target hu
    change (𝓡∂ 2) (cod (f q))=L (u,0)
    rw [(hmem q hq).2,B.compatible]
    change B.linear ((dom.extend CollarModel) q)=B.linear u
    rw [(dom.extend CollarModel).right_inv hu]
  have hclosedPositiveCharts (l : ℝ) (hl : 0 < l) (f : Circle × Time → F.surface) (p : Circle × Time)
      (Γ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 2) (Circle × ℝ) F.surface ∞)
      (hpΓ : (p.1,l*(p.2:ℝ)) ∈ Γ.source)
      (hΓeq : ∀ q : Circle × Time,(q.1,l*(q.2:ℝ)) ∈ Γ.source → Γ (q.1,l*(q.2:ℝ))=f q)
      (ct : OpenPartialHomeomorph Time (EuclideanHalfSpace 1))
      (hct : ct ∈ IsManifold.maximalAtlas (𝓡∂ 1) ∞ Time) (hpct : p.2 ∈ ct.source)
      (a b : ℝ) (ha : a ≠ 0) (hcteq : ∀ t : Time,((ct t).val) 0=a*(l*(t:ℝ))+b) :
      ∃ source : OpenPartialHomeomorph (Circle × Time) (Euc 1 × EuclideanHalfSpace 1),
      ∃ target : OpenPartialHomeomorph F.surface (EuclideanHalfSpace 2),
      ∃ L : ((Euc 1 × Euc 1) × Euc 0) ≃L[ℝ] Euc 2,
        p ∈ source.source ∧ f p ∈ target.source ∧
        source ∈ IsManifold.maximalAtlas CollarModel ∞ (Circle × Time) ∧
        target ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ F.surface ∧
        source.source ⊆ f ⁻¹' target.source ∧
        EqOn (target.extend (𝓡∂ 2) ∘ f ∘ (source.extend CollarModel).symm)
          (fun u => L (u,0)) (source.extend CollarModel).target := by
    let cc := chartAt (Euc 1) p.1
    let v : Euc 1 := !₂[1-(cc p.1) 0]
    let dc : Diffeomorph (𝓡 1) (𝓡 1) (Euc 1) (Euc 1) ∞ :=
      ⟨(Homeomorph.addLeft v).toEquiv,contMDiff_const.add contMDiff_id,contMDiff_const.add contMDiff_id⟩
    let cs := cc.trans dc.toHomeomorph.toOpenPartialHomeomorph
    have hcs : cs ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle := by
      apply cs.mem_maximalAtlas_of_contMDiffOn
      · exact dc.contMDiff.comp_contMDiffOn
          ((contMDiffOn_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p.1)).mono inter_subset_left)
      · exact (contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p.1)).comp
          dc.symm.contMDiff.contMDiffOn (fun _ h => h.2)
    let O : Set Circle := cs.source ∩ cs ⁻¹' {u : Euc 1 | 0 < u 0}
    have hO : IsOpen O := cs.isOpen_inter_preimage (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous)
    let cp := cs.restr O
    have hcpSource : cp.source=O := by
      simp only [cp,OpenPartialHomeomorph.restr_source,hO.interior_eq]
      exact inter_eq_right.mpr inter_subset_left
    have hcp : cp ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle := restr_mem_maximalAtlas _ hcs hO
    have hpcc : p.1 ∈ cp.source := by
      rw [hcpSource]
      refine ⟨⟨mem_chart_source _ _,mem_univ _⟩,?_⟩
      change 0 < 1-(cc p.1) 0+(cc p.1) 0
      linarith
    let clock : Circle × Time → Circle × ℝ := fun q => (q.1,l*(q.2:ℝ))
    have hclock : Continuous clock := continuous_fst.prodMk (continuous_const.mul (continuous_subtype_val.comp continuous_snd))
    let OΓ := clock ⁻¹' Γ.source
    have hOΓ : IsOpen OΓ := Γ.open_source.preimage hclock
    let dom0 := cp.prod ct
    have hdom0 : dom0 ∈ IsManifold.maximalAtlas CollarModel ∞ (Circle × Time) :=
      IsManifold.mem_maximalAtlas_prod hcp hct
    let dom := dom0.restr OΓ
    have hdom : dom ∈ IsManifold.maximalAtlas CollarModel ∞ (Circle × Time) :=
      restr_mem_maximalAtlas _ hdom0 hOΓ
    have hdomSource : dom.source=dom0.source ∩ OΓ := dom0.restr_source' _ hOΓ
    let sourceChart : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,Euc 1 × ℝ)
        (Circle × ℝ) (Euc 1 × ℝ) ∞ :=
      { toPartialEquiv := (cp.prod (OpenPartialHomeomorph.refl ℝ)).toPartialEquiv
        open_source := (cp.prod (OpenPartialHomeomorph.refl ℝ)).open_source
        open_target := (cp.prod (OpenPartialHomeomorph.refl ℝ)).open_target
        contMDiffOn_toFun := by
          exact ((contMDiffOn_of_mem_maximalAtlas hcp).comp contMDiff_fst.contMDiffOn
            (fun p hp => hp.1)).prodMk_space contMDiff_snd.contMDiffOn
        contMDiffOn_invFun := by
          exact ((contMDiffOn_symm_of_mem_maximalAtlas hcp).comp contDiff_fst.contMDiff.contMDiffOn
            (fun p hp => hp.1)).prodMk contDiff_snd.contMDiff.contMDiffOn }
    let lin : (Euc 1 × ℝ) ≃ₗ[ℝ] Euc 2 :=
      { toFun := fun u => !₂[u.1 0,a*u.2]
        invFun := fun w => (!₂[w 0],w 1/a)
        left_inv := by
          intro u;apply Prod.ext
          · ext i;fin_cases i;rfl
          · change a*u.2/a=u.2;simp [ha]
        right_inv := by
          intro w;ext i;fin_cases i
          · rfl
          · change a*(w 1/a)=w 1;field_simp
        map_add' := by intro u w;ext i;fin_cases i <;> simp [mul_add]
        map_smul' := by intro r u;ext i;fin_cases i <;> simp [mul_left_comm] }
    let L := lin.toContinuousLinearEquiv
    let v2 : Euc 2 := !₂[0,b]
    let dx : Diffeomorph 𝓘(ℝ,Euc 1 × ℝ) (𝓡 2) (Euc 1 × ℝ) (Euc 2) ∞ :=
      (show Diffeomorph 𝓘(ℝ,Euc 1 × ℝ) (𝓡 2) (Euc 1 × ℝ) (Euc 2) ∞ from
        ⟨L.toEquiv,L.contDiff.contMDiff,L.symm.contDiff.contMDiff⟩).trans
        (show Diffeomorph (𝓡 2) (𝓡 2) (Euc 2) (Euc 2) ∞ from
          ⟨(Homeomorph.addLeft v2).toEquiv,contMDiff_const.add contMDiff_id,contMDiff_const.add contMDiff_id⟩)
    have hdx (u : Euc 1 × ℝ) : dx u=!₂[u.1 0,a*u.2+b] := by
      change v2+L u=!₂[u.1 0,a*u.2+b]
      ext i
      fin_cases i
      · change 0+u.1 0=u.1 0;ring
      · change b+a*u.2=a*u.2+b;ring
    let S : Set (Euc 2) := {u | 0 < u 0}
    have hS : S ⊆ range (𝓡∂ 2) := by
      intro u hu
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact (show 0 < u 0 from hu).le
    let j : OpenPartialHomeomorph (Euc 2) (EuclideanHalfSpace 2) :=
      { toFun := (𝓡∂ 2).symm
        invFun := (𝓡∂ 2)
        source := S
        target := {u | 0 < (Subtype.val u) 0}
        map_source' := by intro u hu;change 0 < (𝓡∂ 2) ((𝓡∂ 2).symm u) 0;rw [(𝓡∂ 2).right_inv (hS hu)];exact hu
        map_target' := fun _ hu => hu
        left_inv' := fun u hu => (𝓡∂ 2).right_inv (hS hu)
        right_inv' := fun u _ => (𝓡∂ 2).left_inv u
        open_source := isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous
        open_target := isOpen_lt continuous_const ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val)
        continuousOn_toFun := (𝓡∂ 2).continuous_symm.continuousOn
        continuousOn_invFun := (𝓡∂ 2).continuous.continuousOn }
    let jd : PartialDiffeomorph (𝓡 2) (𝓡∂ 2) (Euc 2) (EuclideanHalfSpace 2) ∞ :=
      { toPartialEquiv := j.toPartialEquiv
        open_source := j.open_source
        open_target := j.open_target
        contMDiffOn_toFun := (𝓡∂ 2).contMDiffOn_symm.mono hS
        contMDiffOn_invFun := (𝓡∂ 2).contMDiff.contMDiffOn }
    let codD := ((Γ.symm.trans sourceChart).trans dx.toPartialDiffeomorph).trans jd
    let cod := codD.toOpenPartialHomeomorph
    have hcod : cod ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ F.surface :=
      cod.mem_maximalAtlas_of_contMDiffOn codD.contMDiffOn_toFun codD.contMDiffOn_invFun
    have hmem (q : Circle × Time) (hq : q ∈ dom.source) :
        f q ∈ cod.source ∧ (𝓡∂ 2) (cod (f q))=!₂[(cp q.1) 0,((ct q.2).val) 0] := by
      rw [hdomSource] at hq
      have hcancel : Γ.symm (f q)=clock q := by rw [←hΓeq q hq.2];exact Γ.toPartialEquiv.left_inv hq.2
      have hn : 0 < (cp q.1) 0 := (hcpSource ▸ hq.1.1).2
      have hdxs : dx (sourceChart (clock q)) ∈ S := by rw [hdx];exact hn
      constructor
      · change (((f q ∈ Γ.target ∧ Γ.symm (f q) ∈ (cp.prod (OpenPartialHomeomorph.refl ℝ)).source) ∧
          sourceChart (Γ.symm (f q)) ∈ (univ:Set (Euc 1 × ℝ))) ∧
          dx (sourceChart (Γ.symm (f q))) ∈ S)
        refine ⟨⟨⟨?_,?_⟩,mem_univ _⟩,?_⟩
        · rw [←hΓeq q hq.2];exact Γ.toPartialEquiv.map_source hq.2
        · rw [hcancel];exact ⟨hq.1.1,mem_univ _⟩
        · rw [hcancel];exact hdxs
      · change (𝓡∂ 2) ((𝓡∂ 2).symm (dx (sourceChart (Γ.symm (f q)))))=_
        rw [hcancel,(𝓡∂ 2).right_inv (hS hdxs),hdx]
        change !₂[(cp q.1) 0,a*(l*(q.2:ℝ))+b]=!₂[(cp q.1) 0,((ct q.2).val) 0]
        rw [hcteq]
    have hpdom : p ∈ dom.source := by rw [hdomSource];exact ⟨⟨hpcc,hpct⟩,hpΓ⟩
    let ll : (Euc 1 × Euc 1) ≃ₗ[ℝ] Euc 2 :=
      { toFun := fun u => !₂[u.1 0,u.2 0]
        invFun := fun w => (!₂[w 0],!₂[w 1])
        left_inv := by intro u;apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
        right_inv := by intro w;ext i;fin_cases i <;> rfl
        map_add' := by intro u w;ext i;fin_cases i <;> rfl
        map_smul' := by intro r u;ext i;fin_cases i <;> rfl }
    let LL := (ContinuousLinearEquiv.prodUnique ℝ (Euc 1 × Euc 1) (Euc 0)).trans ll.toContinuousLinearEquiv
    refine ⟨dom,cod,LL,hpdom,(hmem p hpdom).1,hdom,hcod,(fun q hq => (hmem q hq).1),?_⟩
    intro u hu
    let q := (dom.extend CollarModel).symm u
    have hq : q ∈ dom.source := by simpa only [OpenPartialHomeomorph.extend_source] using (dom.extend CollarModel).map_target hu
    change (𝓡∂ 2) (cod (f q))=LL (u,0)
    rw [(hmem q hq).2]
    have heq := (dom.extend CollarModel).right_inv hu
    change (cp q.1,(𝓡∂ 1) (ct q.2))=u at heq
    rw [←heq]
    rfl
  have hnativePositiveCharts (f : Circle × ℝ → F.surface) (p : Circle × ℝ)
      (Γ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 2) (Circle × ℝ) F.surface ∞)
      (hpΓ : p ∈ Γ.source) (hΓeq : EqOn Γ f Γ.source) :
      Manifold.IsImmersionAt ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 2) ∞ f p := by
    let cc := chartAt (Euc 1) p.1
    let v : Euc 1 := !₂[1-(cc p.1) 0]
    let dc : Diffeomorph (𝓡 1) (𝓡 1) (Euc 1) (Euc 1) ∞ :=
      ⟨(Homeomorph.addLeft v).toEquiv,contMDiff_const.add contMDiff_id,contMDiff_const.add contMDiff_id⟩
    let cs := cc.trans dc.toHomeomorph.toOpenPartialHomeomorph
    have hcs : cs ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle := by
      apply cs.mem_maximalAtlas_of_contMDiffOn
      · exact dc.contMDiff.comp_contMDiffOn
          ((contMDiffOn_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p.1)).mono inter_subset_left)
      · exact (contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p.1)).comp
          dc.symm.contMDiff.contMDiffOn (fun _ h => h.2)
    let O : Set Circle := cs.source ∩ cs ⁻¹' {u : Euc 1 | 0 < u 0}
    have hO : IsOpen O := cs.isOpen_inter_preimage (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous)
    let cp := cs.restr O
    have hcpSource : cp.source=O := by
      simp only [cp,OpenPartialHomeomorph.restr_source,hO.interior_eq]
      exact inter_eq_right.mpr inter_subset_left
    have hcp : cp ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle := restr_mem_maximalAtlas _ hcs hO
    have hpcc : p.1 ∈ cp.source := by
      rw [hcpSource]
      refine ⟨⟨mem_chart_source _ _,mem_univ _⟩,?_⟩
      change 0 < 1-(cc p.1) 0+(cc p.1) 0
      linarith
    let dom0 := cp.prod (OpenPartialHomeomorph.refl ℝ)
    have hdom0 : dom0 ∈ IsManifold.maximalAtlas ((𝓡 1).prod 𝓘(ℝ,ℝ)) ∞ (Circle × ℝ) :=
      IsManifold.mem_maximalAtlas_prod hcp (by
        apply (OpenPartialHomeomorph.refl ℝ).mem_maximalAtlas_of_contMDiffOn <;> exact contMDiff_id.contMDiffOn)
    let dom := dom0.restr Γ.source
    have hdom : dom ∈ IsManifold.maximalAtlas ((𝓡 1).prod 𝓘(ℝ,ℝ)) ∞ (Circle × ℝ) :=
      restr_mem_maximalAtlas _ hdom0 Γ.open_source
    have hdomSource : dom.source=dom0.source ∩ Γ.source := dom0.restr_source' _ Γ.open_source
    let sourceChart : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,Euc 1 × ℝ)
        (Circle × ℝ) (Euc 1 × ℝ) ∞ :=
      { toPartialEquiv := dom0.toPartialEquiv
        open_source := dom0.open_source
        open_target := dom0.open_target
        contMDiffOn_toFun := by
          exact ((contMDiffOn_of_mem_maximalAtlas hcp).comp contMDiff_fst.contMDiffOn
            (fun p hp => hp.1)).prodMk_space contMDiff_snd.contMDiffOn
        contMDiffOn_invFun := by
          exact ((contMDiffOn_symm_of_mem_maximalAtlas hcp).comp contDiff_fst.contMDiff.contMDiffOn
            (fun p hp => hp.1)).prodMk contDiff_snd.contMDiff.contMDiffOn }
    let lin : (Euc 1 × ℝ) ≃ₗ[ℝ] Euc 2 :=
      { toFun := fun u => !₂[u.1 0,u.2]
        invFun := fun w => (!₂[w 0],w 1)
        left_inv := by intro u;apply Prod.ext <;> first | rfl | (ext i;fin_cases i;rfl)
        right_inv := by intro w;ext i;fin_cases i <;> rfl
        map_add' := by intro u w;ext i;fin_cases i <;> rfl
        map_smul' := by intro r u;ext i;fin_cases i <;> rfl }
    let L := lin.toContinuousLinearEquiv
    let ld : PartialDiffeomorph 𝓘(ℝ,Euc 1 × ℝ) (𝓡 2) (Euc 1 × ℝ) (Euc 2) ∞ :=
      (show Diffeomorph 𝓘(ℝ,Euc 1 × ℝ) (𝓡 2) (Euc 1 × ℝ) (Euc 2) ∞ from
        ⟨L.toEquiv,L.contDiff.contMDiff,L.symm.contDiff.contMDiff⟩).toPartialDiffeomorph
    let S : Set (Euc 2) := {u | 0 < u 0}
    have hS : S ⊆ range (𝓡∂ 2) := by
      intro u hu
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact (show 0 < u 0 from hu).le
    let j : OpenPartialHomeomorph (Euc 2) (EuclideanHalfSpace 2) :=
      { toFun := (𝓡∂ 2).symm
        invFun := (𝓡∂ 2)
        source := S
        target := {u | 0 < (Subtype.val u) 0}
        map_source' := by intro u hu;change 0 < (𝓡∂ 2) ((𝓡∂ 2).symm u) 0;rw [(𝓡∂ 2).right_inv (hS hu)];exact hu
        map_target' := fun _ hu => hu
        left_inv' := fun u hu => (𝓡∂ 2).right_inv (hS hu)
        right_inv' := fun u _ => (𝓡∂ 2).left_inv u
        open_source := isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous
        open_target := isOpen_lt continuous_const ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val)
        continuousOn_toFun := (𝓡∂ 2).continuous_symm.continuousOn
        continuousOn_invFun := (𝓡∂ 2).continuous.continuousOn }
    let jd : PartialDiffeomorph (𝓡 2) (𝓡∂ 2) (Euc 2) (EuclideanHalfSpace 2) ∞ :=
      { toPartialEquiv := j.toPartialEquiv
        open_source := j.open_source
        open_target := j.open_target
        contMDiffOn_toFun := (𝓡∂ 2).contMDiffOn_symm.mono hS
        contMDiffOn_invFun := (𝓡∂ 2).contMDiff.contMDiffOn }
    let codD := ((Γ.symm.trans sourceChart).trans ld).trans jd
    let cod := codD.toOpenPartialHomeomorph
    have hcod : cod ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ F.surface :=
      cod.mem_maximalAtlas_of_contMDiffOn codD.contMDiffOn_toFun codD.contMDiffOn_invFun
    have hmem (q : Circle × ℝ) (hq : q ∈ dom.source) :
        f q ∈ cod.source ∧ (𝓡∂ 2) (cod (f q))=L (dom0 q) := by
      rw [hdomSource] at hq
      have hcancel : Γ.symm (f q)=q := by rw [←hΓeq hq.2];exact Γ.toPartialEquiv.left_inv hq.2
      have hn : 0 < (cp q.1) 0 := (hcpSource ▸ hq.1.1).2
      have hLs : L (dom0 q) ∈ S := hn
      constructor
      · change (((f q ∈ Γ.target ∧ Γ.symm (f q) ∈ dom0.source) ∧
            sourceChart (Γ.symm (f q)) ∈ (univ:Set (Euc 1 × ℝ))) ∧
            L (sourceChart (Γ.symm (f q))) ∈ S)
        refine ⟨⟨⟨?_,?_⟩,mem_univ _⟩,?_⟩
        · rw [←hΓeq hq.2];exact Γ.toPartialEquiv.map_source hq.2
        · rw [hcancel];exact hq.1
        · rw [hcancel];exact hLs
      · change (𝓡∂ 2) ((𝓡∂ 2).symm (L (dom0 (Γ.symm (f q)))))=L (dom0 q)
        rw [hcancel,(𝓡∂ 2).right_inv (hS hLs)]
    have hpdom : p ∈ dom.source := by rw [hdomSource];exact ⟨⟨hpcc,mem_univ _⟩,hpΓ⟩
    let LL := (ContinuousLinearEquiv.prodUnique ℝ (Euc 1 × ℝ) (Euc 0)).trans L
    apply (Manifold.IsImmersionAtOfComplement.mk_of_charts (I:=((𝓡 1).prod 𝓘(ℝ,ℝ))) (J:=𝓡∂ 2) LL dom cod hpdom
      (hmem p hpdom).1 hdom hcod (fun q hq => (hmem q hq).1) ?_).isImmersionAt
    intro u hu
    let q := (dom.extend ((𝓡 1).prod 𝓘(ℝ,ℝ))).symm u
    have hq : q ∈ dom.source := by
      simpa only [OpenPartialHomeomorph.extend_source] using (dom.extend ((𝓡 1).prod 𝓘(ℝ,ℝ))).map_target hu
    change (𝓡∂ 2) (cod (f q))=LL (u,0)
    rw [(hmem q hq).2]
    have heq := (dom.extend ((𝓡 1).prod 𝓘(ℝ,ℝ))).right_inv hu
    change dom0 q=u at heq
    rw [heq]
    rfl
  have hopen
      (hlow : ∀ z : Circle,
        ∃ Δ : PartialDiffeomorph CollarModel (𝓡∂ 2) (Circle × Time) F.surface ∞,
          (z,0) ∈ Δ.source ∧ Δ.source ⊆ {p | (p.2:ℝ)<1} ∧
          EqOn Δ (fun p : Circle × Time => Z.flow (p.1,Z.lambda*(p.2:ℝ))) Δ.source)
      (hpos : ∀ z t,0<t → t<Z.d →
        ∃ Γ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 2) (Circle × ℝ) F.surface ∞,
          (z,t) ∈ Γ.source ∧ EqOn Γ Z.flow Γ.source) :
      IsOpen ((fun p : Circle × Time => Z.flow (p.1,Z.lambda*(p.2:ℝ))) '' {p | (p.2:ℝ)<1}) := by
    let f : Circle × Time → F.surface := fun p => Z.flow (p.1,Z.lambda*(p.2:ℝ))
    let S : Set (Circle × Time) := {p | (p.2:ℝ)<1}
    change IsOpen (f '' S)
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨p,hp,rfl⟩
    by_cases hp0 : (p.2:ℝ)=0
    · have hpe : p.2=(0:Time) := Subtype.ext hp0
      obtain ⟨Δ,hpΔ,hΔsub,hΔeq⟩ := hlow p.1
      change EqOn Δ f Δ.source at hΔeq
      have hpx : p ∈ Δ.source := by simpa only [←hpe,Prod.eta] using hpΔ
      have hfmem : f p ∈ Δ.target := by
        rw [←hΔeq hpx]
        exact Δ.toPartialEquiv.map_source hpx
      apply mem_of_superset (Δ.open_target.mem_nhds hfmem)
      intro q hq
      have hr : Δ.symm q ∈ Δ.source := Δ.toPartialEquiv.map_target hq
      refine ⟨Δ.symm q,hΔsub hr,?_⟩
      rw [←hΔeq hr]
      exact Δ.toPartialEquiv.right_inv hq
    · have ht0 : 0 < (p.2:ℝ) := lt_of_le_of_ne p.2.property.1 (Ne.symm hp0)
      have hs0 : 0 < Z.lambda*(p.2:ℝ) := mul_pos Z.lambda_pos ht0
      have hsbound : Z.lambda*(p.2:ℝ)<Z.lambda := by simpa only [mul_one] using mul_lt_mul_of_pos_left hp Z.lambda_pos
      obtain ⟨Γ,hpΓ,hΓeq⟩ := hpos p.1 _ hs0 (hsbound.trans Z.lambda_lt)
      let U := Γ.source ∩ {q : Circle × ℝ | 0<q.2 ∧ q.2<Z.lambda}
      have hU : IsOpen U := Γ.open_source.inter
        ((isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const))
      have hpU : (p.1,Z.lambda*(p.2:ℝ)) ∈ U := ⟨hpΓ,hs0,hsbound⟩
      have himage : IsOpen (Γ.toOpenPartialHomeomorph '' U) :=
        Γ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hU inter_subset_left
      have hfimage : f p ∈ Γ.toOpenPartialHomeomorph '' U :=
        ⟨(p.1,Z.lambda*(p.2:ℝ)),hpU,hΓeq hpΓ⟩
      apply mem_of_superset (himage.mem_nhds hfimage)
      rintro q ⟨r,hr,rfl⟩
      let time : Time := ⟨r.2/Z.lambda,⟨(div_pos hr.2.1 Z.lambda_pos).le,
        ((div_lt_one Z.lambda_pos).mpr hr.2.2).le⟩⟩
      refine ⟨(r.1,time),(div_lt_one Z.lambda_pos).mpr hr.2.2,?_⟩
      change Z.flow (r.1,Z.lambda*(r.2/Z.lambda))=Γ r
      rw [mul_div_cancel₀ _ (ne_of_gt Z.lambda_pos)]
      exact (hΓeq hr.1).symm
  have hpositive (z : Circle) (t : ℝ) (ht : 0<t) (htd : t<Z.d) :
      ∃ Γ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 2) (Circle × ℝ) F.surface ∞,
        (z,t) ∈ Γ.source ∧ EqOn Γ Z.flow Γ.source := by
    obtain ⟨i,c,hc,hz,B,hB,hcz,hBt,T,htT,hTd,H,hH,hHr,hHz,hHp,hHeq⟩ := hdata z t ht.le htd
    exact hpositiveGiven z t ht i c hc hz B hB hcz hBt T htT H hH (hHr (c z) hcz t) hHeq
  have hlower (z : Circle) :
      ∃ Δ : PartialDiffeomorph CollarModel (𝓡∂ 2) (Circle × Time) F.surface ∞,
        (z,0) ∈ Δ.source ∧ Δ.source ⊆ {p | (p.2:ℝ)<1} ∧
        EqOn Δ (fun p : Circle × Time => Z.flow (p.1,Z.lambda*(p.2:ℝ))) Δ.source := by
    obtain ⟨i,c,hc,hz,B,hB,hcz,hBt,T,htT,hTd,H,hH,hHr,hHz,hHp,hHeq⟩ := hdata z 0 le_rfl Z.d_pos
    exact hlowerGiven z i c hc hz B hB hcz hBt T htT H hH (hHr (c z) hcz 0) hHz (hHp (c z) hcz) hHeq
  refine ⟨{ charts := ?_,open_image := hopen hlower hpositive,positive_time_immersion := ?_ }⟩
  · intro p
    let f : Circle × Time → F.surface := fun q => Z.flow (q.1,Z.lambda*(q.2:ℝ))
    by_cases hp0 : (p.2:ℝ)=0
    · have hpe : p.2=(0:Time) := Subtype.ext hp0
      obtain ⟨Δ,hpΔ,hΔsub,hΔeq⟩ := hlower p.1
      have hpx : p ∈ Δ.source := by simpa only [←hpe,Prod.eta] using hpΔ
      exact hlowerCharts f p (by rw [hp0];norm_num) Δ hpx hΔeq
    · have ht0 : 0 < (p.2:ℝ) := lt_of_le_of_ne p.2.property.1 (Ne.symm hp0)
      have hs0 : 0 < Z.lambda*(p.2:ℝ) := mul_pos Z.lambda_pos ht0
      have hsd : Z.lambda*(p.2:ℝ)<Z.d :=
        (mul_le_of_le_one_right Z.lambda_pos.le p.2.property.2).trans_lt Z.lambda_lt
      obtain ⟨Γ,hpΓ,hΓeq⟩ := hpositive p.1 _ hs0 hsd
      have hΓf (q : Circle × Time) (hq : (q.1,Z.lambda*(q.2:ℝ)) ∈ Γ.source) :
          Γ (q.1,Z.lambda*(q.2:ℝ))=f q := hΓeq hq
      by_cases hp1 : (p.2:ℝ)<1
      · have hleft : IccLeftChart 0 1 ∈ IsManifold.maximalAtlas (𝓡∂ 1) ∞ Time := by
          rw [←Icc_chartedSpaceChartAt_of_le_top (z:=(0:Time)) (by norm_num)]
          exact IsManifold.chart_mem_maximalAtlas _
        exact hclosedPositiveCharts Z.lambda Z.lambda_pos f p Γ hpΓ hΓf (IccLeftChart 0 1) hleft hp1
          Z.lambda⁻¹ 0 (inv_ne_zero (ne_of_gt Z.lambda_pos)) (by
            intro t
            change (t:ℝ)-0=Z.lambda⁻¹*(Z.lambda*(t:ℝ))+0
            simp [ne_of_gt Z.lambda_pos])
      · have hright : IccRightChart 0 1 ∈ IsManifold.maximalAtlas (𝓡∂ 1) ∞ Time := by
          rw [←Icc_chartedSpaceChartAt_of_top_le (z:=(1:Time)) (by norm_num)]
          exact IsManifold.chart_mem_maximalAtlas _
        exact hclosedPositiveCharts Z.lambda Z.lambda_pos f p Γ hpΓ hΓf (IccRightChart 0 1) hright ht0
          (-Z.lambda⁻¹) 1 (neg_ne_zero.mpr (inv_ne_zero (ne_of_gt Z.lambda_pos))) (by
            intro t
            change 1-(t:ℝ)=(-Z.lambda⁻¹)*(Z.lambda*(t:ℝ))+1
            simp [ne_of_gt Z.lambda_pos]
            ring)
  · intro z t ht htd
    obtain ⟨Γ,hpΓ,hΓeq⟩ := hpositive z t ht htd
    exact hnativePositiveCharts Z.flow (z,t) Γ hpΓ hΓeq


structure C7UpperCollar {K : OrientedKnot} {F : SphereSpanningSurface.{0} K} (c : SourceCollar F) where
  extension : UpperExtendedCollar c
  width_gt_one : 1 < extension.width
  endpoint_immersion : ∀ z, Manifold.IsImmersionAt ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 2) ∞ extension.map (z,1)
structure C8RescaledCollar {K : OrientedKnot} {F : SphereSpanningSurface.{0} K}
    (c : SourceCollar F) (scale : ℝ) (hscale : 0 < scale) (hscale1 : scale < 1) where
  rescaled : SourceCollar F
  boundary : ∀ z, rescaled.toFun (z,0) = c.toFun (z,0)
  interior : ∀ z (t : Time), 0 < (t:ℝ) → rescaled.toFun (z,t) ∉ F.surface.boundary
  equation : ∀ z (t : Time), rescaled.toFun (z,t) = c.toFun (z,scaleTime scale hscale.le hscale1.le t)
theorem C8_rescale {K : OrientedKnot} {F : SphereSpanningSurface.{0} K}
    (c : SourceCollar F) (scale : ℝ) (hscale : 0 < scale) (hscale1 : scale < 1) :
    Nonempty (C8RescaledCollar c scale hscale hscale1) := by
  let a := scale
  have ha : 0<a := hscale
  have ha1 : a<1 := hscale1
  have hlower (p : Circle × Time) (hp : (p.2:ℝ)<1) :
      Manifold.IsImmersionAtOfComplement (Euc 0) CollarModel (𝓡∂ 2) ∞
        (fun q : Circle × Time => c.toFun (q.1,scaleTime a ha.le ha1.le q.2)) p := by
    have hbridge (B : CollarModelBridge) :
        ContMDiff CollarModel (𝓡∂ 2) ∞ B.homeo ∧
          ContMDiff (𝓡∂ 2) CollarModel ∞ B.homeo.symm := by
      have hf : (fun p => (𝓡∂ 2).symm (B.linear (CollarModel p)))=B.homeo := by
        funext p
        rw [←B.compatible p]
        exact (𝓡∂ 2).left_inv _
      have hi : (fun p => CollarModel.symm (B.linear.symm ((𝓡∂ 2) p)))=B.homeo.symm := by
        funext p
        have he := B.compatible (B.homeo.symm p)
        rw [B.homeo.apply_symm_apply] at he
        rw [he,B.linear.symm_apply_apply]
        exact CollarModel.left_inv _
      have hc : ContMDiff CollarModel 𝓘(ℝ,Euc 1 × Euc 1) ∞
          (fun p : Euc 1 × EuclideanHalfSpace 1 => (p.1,(𝓡∂ 1) p.2)) := by
        rw [modelWithCornersSelf_prod,←chartedSpaceSelf_prod]
        exact contMDiff_fst.prodMk ((𝓡∂ 1).contMDiff.comp contMDiff_snd)
      constructor
      · rw [←hf]
        apply (𝓡∂ 2).contMDiffOn_symm.comp_contMDiff
          (B.linear.contDiff.contMDiff.comp hc)
        intro p
        change B.linear (CollarModel p) ∈ range (𝓡∂ 2)
        rw [←B.compatible p]
        exact mem_range_self _
      · rw [←hi]
        have hh := B.linear.symm.contDiff.contMDiff.comp (𝓡∂ 2).contMDiff (n:=∞)
        rw [modelWithCornersSelf_prod,←chartedSpaceSelf_prod] at hh
        exact hh.fst.prodMk ((𝓡∂ 1).contMDiffOn_symm.comp_contMDiff hh.snd (by
          intro p
          have he := B.compatible (B.homeo.symm p)
          rw [B.homeo.apply_symm_apply] at he
          rw [he,B.linear.symm_apply_apply]
          exact mem_range_self _))
    have hhalf (a : ℝ) (ha : 0<a) :
        ∃ d : Diffeomorph (𝓡∂ 1) (𝓡∂ 1) (EuclideanHalfSpace 1) (EuclideanHalfSpace 1) ∞,
          ∀ u, (𝓡∂ 1) (d u)=a⁻¹ • (𝓡∂ 1) u := by
      let f : EuclideanHalfSpace 1 → EuclideanHalfSpace 1 :=
        fun u => ⟨a⁻¹ • u.val,by
          change 0≤a⁻¹ * u.val 0
          exact mul_nonneg (inv_nonneg.mpr ha.le) u.property⟩
      let g : EuclideanHalfSpace 1 → EuclideanHalfSpace 1 :=
        fun u => ⟨a • u.val,by
          change 0≤a * u.val 0
          exact mul_nonneg ha.le u.property⟩
      have hfg : Function.LeftInverse f g := by
        intro u; apply Subtype.ext; simp [f,g,smul_smul,ne_of_gt ha]
      have hgf : Function.LeftInverse g f := by
        intro u; apply Subtype.ext; simp [f,g,smul_smul,ne_of_gt ha]
      have hf : (fun u => (𝓡∂ 1).symm (a⁻¹ • (𝓡∂ 1) u))=f := by
        funext u
        exact (𝓡∂ 1).left_inv (f u)
      have hg : (fun u => (𝓡∂ 1).symm (a • (𝓡∂ 1) u))=g := by
        funext u
        exact (𝓡∂ 1).left_inv (g u)
      have hfs : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ f := by
        rw [←hf]
        exact (𝓡∂ 1).contMDiffOn_symm.comp_contMDiff
          ((contMDiff_const (I:=𝓡∂ 1) (I':=𝓘(ℝ,ℝ)) (c:=a⁻¹)).smul (𝓡∂ 1).contMDiff) (fun u => mem_range_self (f u))
      have hgs : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ g := by
        rw [←hg]
        exact (𝓡∂ 1).contMDiffOn_symm.comp_contMDiff
          ((contMDiff_const (I:=𝓡∂ 1) (I':=𝓘(ℝ,ℝ)) (c:=a)).smul (𝓡∂ 1).contMDiff) (fun u => mem_range_self (g u))
      exact ⟨⟨⟨f,g,hgf,hfg⟩,hfs,hgs⟩,fun _ => rfl⟩
    
    have hinc {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
        {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
        {M : Type} [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] (U : TopologicalSpace.Opens M) (hne : Nonempty U) :
        ∃ d : PartialDiffeomorph I I U M ∞,
          (∀ x, d x=x.val) ∧ d.source=univ ∧ d.target=(U:Set M) := by
      let e := U.openPartialHomeomorphSubtypeCoe hne
      have hi : ContMDiffOn I I ∞ e.symm e.target := by
        intro x hx
        apply (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target x).mp
        have heq : EqOn (Subtype.val ∘ e.symm) id e.target :=
          fun y hy => e.right_inv hy
        exact (contMDiffOn_id.congr (fun y hy => heq hy)) x hx
      exact ⟨{ toPartialEquiv := e.toPartialEquiv
               open_source := e.open_source
               open_target := e.open_target
               contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
               contMDiffOn_invFun := hi },fun _ => rfl,rfl,
        U.openPartialHomeomorphSubtypeCoe_target hne⟩
    let l₂ : (Euc 1 × Euc 1) ≃ₗ[ℝ] Euc 2 :=
      { toFun := fun p => !₂[p.2 0, p.1 0]
        invFun := fun w => (!₂[w 1], !₂[w 0])
        left_inv := by
          intro p
          apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
        right_inv := by intro w; ext i; fin_cases i <;> rfl
        map_add' := by intro p q; ext i; fin_cases i <;> rfl
        map_smul' := by intro r p; ext i; fin_cases i <;> rfl }
    let L₂ := l₂.toContinuousLinearEquiv
    let e₂ : (Euc 1 × EuclideanHalfSpace 1) ≃ EuclideanHalfSpace 2 :=
      { toFun := fun p => ⟨L₂ (p.1, p.2.val), p.2.property⟩
        invFun := fun w => ((L₂.symm w.val).1, ⟨(L₂.symm w.val).2, w.property⟩)
        left_inv := by
          intro p
          refine Prod.ext ?_ ?_
          · ext i; fin_cases i; rfl
          · apply Subtype.ext; ext i; fin_cases i; rfl
        right_inv := by
          intro w
          apply Subtype.ext
          exact L₂.apply_symm_apply w.val }
    let h₂ : (Euc 1 × EuclideanHalfSpace 1) ≃ₜ EuclideanHalfSpace 2 :=
      { toEquiv := e₂
        continuous_toFun := (L₂.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
        continuous_invFun :=
          ((continuous_fst.comp (L₂.symm.continuous.comp continuous_subtype_val)).prodMk
            ((continuous_snd.comp (L₂.symm.continuous.comp continuous_subtype_val)).subtype_mk _)) }
    let B : CollarModelBridge :=
      { homeo := h₂
        linear := L₂
        formula := fun _ => rfl
        linear_formula := fun _ => rfl
        compatible := fun _ => rfl }
    obtain ⟨dh,hdh⟩ := hhalf a ha
    let ds := (Diffeomorph.refl (𝓡 1) (Euc 1) ∞).prodCongr dh
    let db : Diffeomorph CollarModel (𝓡∂ 2) (Euc 1 × EuclideanHalfSpace 1) (EuclideanHalfSpace 2) ∞ :=
      ⟨B.homeo.toEquiv,(hbridge B).1,(hbridge B).2⟩
    let b := (a+1)/2
    let b' := (b+1)/2
    have hb : a<b := by dsimp [b]; linarith
    have hbpos : 0<b := ha.trans hb
    have hbb' : b<b' := by dsimp [b,b']; linarith
    have hb' : b'<1 := by dsimp [b,b']; linarith
    obtain ⟨A⟩ := source_collar_substrip_coordinates c b b' hbpos hbb' hb'
    let ps : openTimeStrip b := ⟨(p.1,0),by change (0:ℝ)<b; exact hbpos⟩
    obtain ⟨incA,hincA,hincAs,hincAt⟩ := hinc (I:=𝓡∂ 2) A.image ⟨A.coordinates ps⟩
    obtain ⟨incS,hincS,hincSs,hincSt⟩ := hinc (I:=CollarModel) (openTimeStrip b) ⟨ps⟩
    let cc := chartAt (Euc 1) p.1
    have hcc : cc ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle := IsManifold.chart_mem_maximalAtlas _
    have hct : IccLeftChart 0 1 ∈ IsManifold.maximalAtlas (𝓡∂ 1) ∞ Time := by
      rw [←Icc_chartedSpaceChartAt_of_le_top (z:=(0:Time)) (by norm_num)]
      exact IsManifold.chart_mem_maximalAtlas _
    let dom := cc.prod (IccLeftChart 0 1)
    have hdom : dom ∈ IsManifold.maximalAtlas CollarModel ∞ (Circle × Time) :=
      IsManifold.mem_maximalAtlas_prod hcc hct
    let cd : PartialDiffeomorph CollarModel CollarModel (Circle × Time) (Euc 1 × EuclideanHalfSpace 1) ∞ :=
      { toPartialEquiv := dom.toPartialEquiv
        open_source := dom.open_source
        open_target := dom.open_target
        contMDiffOn_toFun := by
          exact ((contMDiffOn_of_mem_maximalAtlas hcc).comp contMDiff_fst.contMDiffOn (fun _ h => h.1)).prodMk
            ((contMDiffOn_of_mem_maximalAtlas hct).comp contMDiff_snd.contMDiffOn (fun _ h => h.2))
        contMDiffOn_invFun := by
          exact ((contMDiffOn_symm_of_mem_maximalAtlas hcc).comp contMDiff_fst.contMDiffOn (fun _ h => h.1)).prodMk
            ((contMDiffOn_symm_of_mem_maximalAtlas hct).comp contMDiff_snd.contMDiffOn (fun _ h => h.2)) }
    let codD := ((((incA.symm.trans A.coordinates.symm.toPartialDiffeomorph).trans incS).trans cd).trans
      ds.toPartialDiffeomorph).trans db.toPartialDiffeomorph
    let cod := codD.toOpenPartialHomeomorph
    have hcod : cod ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ F.surface :=
      cod.mem_maximalAtlas_of_contMDiffOn codD.contMDiffOn_toFun codD.contMDiffOn_invFun
    let f : Circle × Time → F.surface := fun q => c.toFun (q.1,scaleTime a ha.le ha1.le q.2)
    have hn (t : Time) : dh (IccLeftChart 0 1 (scaleTime a ha.le ha1.le t))=IccLeftChart 0 1 t := by
      apply (𝓡∂ 1).injective
      rw [hdh]
      ext i
      fin_cases i
      simp only [IccLeftChart_apply]
      change a⁻¹*(a*(t:ℝ)-0)=(t:ℝ)-0
      simp only [sub_zero]
      field_simp [ne_of_gt ha]
    have hsmem (q : Circle × Time) : (scaleTime a ha.le ha1.le q.2:ℝ)<b :=
      (mul_le_of_le_one_right ha.le q.2.property.2).trans_lt hb
    have hmem (q : Circle × Time) (hq : q ∈ dom.source) :
        f q ∈ cod.source ∧ cod (f q)=B.homeo (dom q) := by
      let q' : openTimeStrip b := ⟨(q.1,scaleTime a ha.le ha1.le q.2),hsmem q⟩
      have hfq : incA (A.coordinates q')=f q := (hincA _).trans (A.equation q')
      have hqin : A.coordinates q' ∈ incA.source := by rw [hincAs]; trivial
      have hinv : incA.symm (f q)=A.coordinates q' := by
        rw [←hfq]
        exact incA.toOpenPartialHomeomorph.left_inv hqin
      have hcomp : A.coordinates.symm (incA.symm (f q))=q' := by rw [hinv,A.coordinates.symm_apply_apply]
      have hval : incS (A.coordinates.symm (incA.symm (f q)))=q'.val := by rw [hcomp,hincS]
      have hqd : q'.val ∈ dom.source := by
        exact ⟨hq.1,by change a*(q.2:ℝ)<1; exact (hsmem q).trans (hbb'.trans hb')⟩
      constructor
      · change (((((f q ∈ incA.target ∧ incA.symm (f q) ∈ univ) ∧
          A.coordinates.symm (incA.symm (f q)) ∈ incS.source) ∧
          incS (A.coordinates.symm (incA.symm (f q))) ∈ cd.source) ∧
          cd (incS (A.coordinates.symm (incA.symm (f q)))) ∈ univ) ∧
          ds (cd (incS (A.coordinates.symm (incA.symm (f q))))) ∈ univ)
        refine ⟨⟨⟨⟨⟨?_,mem_univ _⟩,?_⟩,?_⟩,mem_univ _⟩,mem_univ _⟩
        · rw [hincAt,←hfq,hincA]
          exact (A.coordinates q').property
        · rw [hincSs]; trivial
        · change incS (A.coordinates.symm (incA.symm (f q))) ∈ dom.source
          rw [hval]; exact hqd
      · change B.homeo (ds (dom (incS (A.coordinates.symm (incA.symm (f q))))))=B.homeo (dom q)
        rw [hval]
        congr 1
        change (cc q.1,dh (IccLeftChart 0 1 (scaleTime a ha.le ha1.le q.2)))=_
        rw [hn]
        rfl
    have hpdom : p ∈ dom.source := ⟨mem_chart_source _ _,hp⟩
    let L := (ContinuousLinearEquiv.prodUnique ℝ (Euc 1 × Euc 1) (Euc 0)).trans B.linear
    apply Manifold.IsImmersionAtOfComplement.mk_of_charts (I:=CollarModel) (J:=𝓡∂ 2) L dom cod hpdom (hmem p hpdom).1 hdom hcod
    · exact fun q hq => (hmem q hq).1
    · intro u hu
      let q := (dom.extend CollarModel).symm u
      have hq : q ∈ dom.source := by simpa only [OpenPartialHomeomorph.extend_source] using (dom.extend CollarModel).map_target hu
      change (𝓡∂ 2) (cod (f q))=L (u,0)
      rw [(hmem q hq).2,B.compatible]
      change B.linear ((dom.extend CollarModel) q)=B.linear u
      rw [(dom.extend CollarModel).right_inv hu]
  have hupper (p : Circle × Time) (hp : (p.2:ℝ)=1) :
      Manifold.IsImmersionAtOfComplement (Euc 0) CollarModel (𝓡∂ 2) ∞
        (fun q : Circle × Time => c.toFun (q.1,scaleTime a ha.le ha1.le q.2)) p := by
    have hflat (n : ℕ) [NeZero n] :
        ∃ j : OpenPartialHomeomorph (Euc n) (EuclideanHalfSpace n),
          j.source={u | 0<u 0} ∧ j.target={u | 0<(Subtype.val u) 0} ∧
          (∀ u, j u=(𝓡∂ n).symm u) ∧ (∀ u, j.symm u=(𝓡∂ n) u) ∧
          ContMDiffOn (𝓡 n) (𝓡∂ n) ∞ j j.source ∧
          ContMDiffOn (𝓡∂ n) (𝓡 n) ∞ j.symm j.target := by
      let S : Set (Euc n) := {u | 0<u 0}
      let V : Set (EuclideanHalfSpace n) := {u | 0<(Subtype.val u) 0}
      have hS : S ⊆ range (𝓡∂ n) := by
        intro u hu
        change 0<u 0 at hu
        rw [range_modelWithCornersEuclideanHalfSpace]
        exact hu.le
      let j : OpenPartialHomeomorph (Euc n) (EuclideanHalfSpace n) :=
        { toFun := (𝓡∂ n).symm
          invFun := (𝓡∂ n)
          source := S
          target := V
          map_source' := by
            intro u hu
            change 0<(𝓡∂ n) ((𝓡∂ n).symm u) 0
            rw [(𝓡∂ n).right_inv (hS hu)]
            exact hu
          map_target' := by intro u hu; exact hu
          left_inv' := fun u hu => (𝓡∂ n).right_inv (hS hu)
          right_inv' := fun u _ => (𝓡∂ n).left_inv u
          open_source := isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous
          open_target := isOpen_lt continuous_const ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val)
          continuousOn_toFun := (𝓡∂ n).continuous_symm.continuousOn
          continuousOn_invFun := (𝓡∂ n).continuous.continuousOn }
      exact ⟨j,rfl,rfl,fun _ => rfl,fun _ => rfl,
        (𝓡∂ n).contMDiffOn_symm.mono hS,(𝓡∂ n).contMDiff.contMDiffOn⟩
    
    have hinc {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
        {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
        {M : Type} [TopologicalSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] (U : TopologicalSpace.Opens M) (hne : Nonempty U) :
        ∃ d : PartialDiffeomorph I I U M ∞,
          (∀ x, d x=x.val) ∧ d.source=univ ∧ d.target=(U:Set M) := by
      let e := U.openPartialHomeomorphSubtypeCoe hne
      have hi : ContMDiffOn I I ∞ e.symm e.target := by
        intro x hx
        apply (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target x).mp
        have heq : EqOn (Subtype.val ∘ e.symm) id e.target :=
          fun y hy => e.right_inv hy
        exact (contMDiffOn_id.congr (fun y hy => heq hy)) x hx
      exact ⟨{ toPartialEquiv := e.toPartialEquiv
               open_source := e.open_source
               open_target := e.open_target
               contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
               contMDiffOn_invFun := hi },fun _ => rfl,rfl,
        U.openPartialHomeomorphSubtypeCoe_target hne⟩
    obtain ⟨j1,hj1s,hj1t,hj1,hj1inv,hj1smooth,hj1invsmooth⟩ := hflat 1
    obtain ⟨j2,hj2s,hj2t,hj2,hj2inv,hj2smooth,hj2invsmooth⟩ := hflat 2
    let jd1 : PartialDiffeomorph (𝓡 1) (𝓡∂ 1) (Euc 1) (EuclideanHalfSpace 1) ∞ :=
      { toPartialEquiv := j1.toPartialEquiv
        open_source := j1.open_source
        open_target := j1.open_target
        contMDiffOn_toFun := hj1smooth
        contMDiffOn_invFun := hj1invsmooth }
    let jd2 : PartialDiffeomorph (𝓡 2) (𝓡∂ 2) (Euc 2) (EuclideanHalfSpace 2) ∞ :=
      { toPartialEquiv := j2.toPartialEquiv
        open_source := j2.open_source
        open_target := j2.open_target
        contMDiffOn_toFun := hj2smooth
        contMDiffOn_invFun := hj2invsmooth }
    have hleft : IccLeftChart 0 1 ∈ IsManifold.maximalAtlas (𝓡∂ 1) ∞ Time := by
      rw [←Icc_chartedSpaceChartAt_of_le_top (z:=(0:Time)) (by norm_num)]
      exact IsManifold.chart_mem_maximalAtlas _
    have hright : IccRightChart 0 1 ∈ IsManifold.maximalAtlas (𝓡∂ 1) ∞ Time := by
      rw [←Icc_chartedSpaceChartAt_of_top_le (z:=(1:Time)) (by norm_num)]
      exact IsManifold.chart_mem_maximalAtlas _
    let td : PartialDiffeomorph (𝓡∂ 1) (𝓡∂ 1) Time (EuclideanHalfSpace 1) ∞ :=
      { toPartialEquiv := (IccLeftChart 0 1).toPartialEquiv
        open_source := (IccLeftChart 0 1).open_source
        open_target := (IccLeftChart 0 1).open_target
        contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hleft
        contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hleft }
    let tf := td.trans jd1.symm
    let cc := chartAt (Euc 1) p.1
    let v : Euc 1 := !₂[1-(cc p.1) 0]
    let dc : Diffeomorph (𝓡 1) (𝓡 1) (Euc 1) (Euc 1) ∞ :=
      ⟨(Homeomorph.addLeft v).toEquiv,contMDiff_const.add contMDiff_id,contMDiff_const.add contMDiff_id⟩
    let cs := cc.trans dc.toHomeomorph.toOpenPartialHomeomorph
    have hcs : cs ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle := by
      apply cs.mem_maximalAtlas_of_contMDiffOn
      · exact dc.contMDiff.comp_contMDiffOn
          ((contMDiffOn_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p.1)).mono inter_subset_left)
      · exact (contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p.1)).comp
          dc.symm.contMDiff.contMDiffOn (fun _ h => h.2)
    let O : Set Circle := cs.source ∩ cs ⁻¹' {u : Euc 1 | 0<u 0}
    have hO : IsOpen O := cs.isOpen_inter_preimage (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous)
    let cp := cs.restr O
    have hcpSource : cp.source=O := by
      simp only [cp,OpenPartialHomeomorph.restr_source,hO.interior_eq]
      exact inter_eq_right.mpr inter_subset_left
    have hcp : cp ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Circle := restr_mem_maximalAtlas _ hcs hO
    have hpcc : p.1 ∈ cp.source := by
      rw [hcpSource]
      refine ⟨⟨mem_chart_source _ _,mem_univ _⟩,?_⟩
      change 0 < (v + cc p.1) 0
      change 0 < 1-(cc p.1) 0+(cc p.1) 0
      linarith
    let dom := cp.prod (IccRightChart 0 1)
    have hdom : dom ∈ IsManifold.maximalAtlas CollarModel ∞ (Circle × Time) :=
      IsManifold.mem_maximalAtlas_prod hcp hright
    let cd : PartialDiffeomorph CollarModel ((𝓡 1).prod (𝓡 1)) (Circle × Time) (Euc 1 × Euc 1) ∞ :=
      { toPartialEquiv := (cp.prod tf.toOpenPartialHomeomorph).toPartialEquiv
        open_source := (cp.prod tf.toOpenPartialHomeomorph).open_source
        open_target := (cp.prod tf.toOpenPartialHomeomorph).open_target
        contMDiffOn_toFun := by
          exact ((contMDiffOn_of_mem_maximalAtlas hcp).comp contMDiff_fst.contMDiffOn (fun _ h => h.1)).prodMk
            (tf.contMDiffOn_toFun.comp contMDiff_snd.contMDiffOn (fun _ h => h.2))
        contMDiffOn_invFun := by
          exact ((contMDiffOn_symm_of_mem_maximalAtlas hcp).comp contMDiff_fst.contMDiffOn (fun _ h => h.1)).prodMk
            (tf.contMDiffOn_invFun.comp contMDiff_snd.contMDiffOn (fun _ h => h.2)) }
    let ell : (Euc 1 × Euc 1) ≃ₗ[ℝ] Euc 2 :=
      { toFun := fun u => !₂[u.1 0,-a⁻¹*u.2 0]
        invFun := fun w => (!₂[w 0],!₂[-a*w 1])
        left_inv := by
          intro u
          apply Prod.ext <;> ext i <;> fin_cases i
          · rfl
          · change -a*(-a⁻¹*u.2 0)=u.2 0
            field_simp [ne_of_gt ha]
        right_inv := by
          intro w
          ext i
          fin_cases i
          · rfl
          · change -a⁻¹*(-a*w 1)=w 1
            field_simp [ne_of_gt ha]
        map_add' := by intro u w; ext i; fin_cases i <;> simp <;> ring
        map_smul' := by intro r u; ext i; fin_cases i <;> simp <;> ring }
    let el := ell.toContinuousLinearEquiv
    let dl : Diffeomorph ((𝓡 1).prod (𝓡 1)) (𝓡 2) (Euc 1 × Euc 1) (Euc 2) ∞ :=
      ⟨el.toEquiv,by
        rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod]
        exact el.contDiff.contMDiff,by
        rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod]
        exact el.symm.contDiff.contMDiff⟩
    let dt : Diffeomorph (𝓡 2) (𝓡 2) (Euc 2) (Euc 2) ∞ :=
      ⟨(Homeomorph.addLeft (!₂[0,1]:Euc 2)).toEquiv,
        contMDiff_const.add contMDiff_id,contMDiff_const.add contMDiff_id⟩
    let dx := dl.trans dt
    have hdx (u : Euc 1 × Euc 1) : dx u = !₂[u.1 0,1-a⁻¹*u.2 0] := by
      ext i
      fin_cases i
      · change 0 + u.1 0=u.1 0
        simp
      · change 1 + -a⁻¹*u.2 0=1-a⁻¹*u.2 0
        ring
    let b := (a+1)/2
    let b' := (b+1)/2
    have hb : a<b := by dsimp [b]; linarith
    have hbpos : 0<b := ha.trans hb
    have hbb' : b<b' := by dsimp [b,b']; linarith
    have hb' : b'<1 := by dsimp [b,b']; linarith
    obtain ⟨A⟩ := source_collar_substrip_coordinates c b b' hbpos hbb' hb'
    let ps : openTimeStrip b := ⟨(p.1,0),by change (0:ℝ)<b; exact hbpos⟩
    obtain ⟨incA,hincA,hincAs,hincAt⟩ := hinc (I:=𝓡∂ 2) A.image ⟨A.coordinates ps⟩
    obtain ⟨incS,hincS,hincSs,hincSt⟩ := hinc (I:=CollarModel) (openTimeStrip b) ⟨ps⟩
    let codD := ((((incA.symm.trans A.coordinates.symm.toPartialDiffeomorph).trans incS).trans cd).trans
      dx.toPartialDiffeomorph).trans jd2
    let cod := codD.toOpenPartialHomeomorph
    have hcod : cod ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ F.surface :=
      cod.mem_maximalAtlas_of_contMDiffOn codD.contMDiffOn_toFun codD.contMDiffOn_invFun
    let f : Circle × Time → F.surface := fun q => c.toFun (q.1,scaleTime a ha.le ha1.le q.2)
    have hsmem (q : Circle × Time) : (scaleTime a ha.le ha1.le q.2:ℝ)<b :=
      (mul_le_of_le_one_right ha.le q.2.property.2).trans_lt hb
    have htime (q : Circle × Time) (hq : q ∈ dom.source) :
        scaleTime a ha.le ha1.le q.2 ∈ tf.source := by
      change (scaleTime a ha.le ha1.le q.2:ℝ)<1 ∧ IccLeftChart 0 1 (scaleTime a ha.le ha1.le q.2) ∈ j1.target
      refine ⟨(hsmem q).trans (hbb'.trans hb'),?_⟩
      rw [hj1t]
      change 0<a*(q.2:ℝ)-0
      rw [sub_zero]
      exact mul_pos ha hq.2
    have hxsource (q : Circle × Time) (hq : q ∈ dom.source) :
        dx (cp q.1,tf (scaleTime a ha.le ha1.le q.2)) ∈ j2.source := by
      rw [hj2s]
      rw [hdx]
      change 0<(cp q.1) 0
      exact (hcpSource ▸ hq.1).2
    have hmem (q : Circle × Time) (hq : q ∈ dom.source) :
        f q ∈ cod.source ∧
        (𝓡∂ 2) (cod (f q))= !₂[(cp q.1) 0,1-(q.2:ℝ)] := by
      let q' : openTimeStrip b := ⟨(q.1,scaleTime a ha.le ha1.le q.2),hsmem q⟩
      have hfq : incA (A.coordinates q')=f q := (hincA _).trans (A.equation q')
      have hqin : A.coordinates q' ∈ incA.source := by rw [hincAs]; trivial
      have hinv : incA.symm (f q)=A.coordinates q' := by
        rw [←hfq]
        exact incA.toOpenPartialHomeomorph.left_inv hqin
      have hcomp : A.coordinates.symm (incA.symm (f q))=q' := by rw [hinv,A.coordinates.symm_apply_apply]
      have hval : incS (A.coordinates.symm (incA.symm (f q)))=q'.val := by rw [hcomp,hincS]
      have hqd : q'.val ∈ cd.source := ⟨hq.1,htime q hq⟩
      constructor
      · change (((((f q ∈ incA.target ∧ incA.symm (f q) ∈ univ) ∧
          A.coordinates.symm (incA.symm (f q)) ∈ incS.source) ∧
          incS (A.coordinates.symm (incA.symm (f q))) ∈ cd.source) ∧
          cd (incS (A.coordinates.symm (incA.symm (f q)))) ∈ univ) ∧
          dx (cd (incS (A.coordinates.symm (incA.symm (f q))))) ∈ j2.source)
        refine ⟨⟨⟨⟨⟨?_,mem_univ _⟩,?_⟩,?_⟩,mem_univ _⟩,?_⟩
        · rw [hincAt,←hfq,hincA]; exact (A.coordinates q').property
        · rw [hincSs]; trivial
        · rw [hval]; exact hqd
        · rw [hval]; exact hxsource q hq
      · change (𝓡∂ 2) (j2 (dx (cd (incS (A.coordinates.symm (incA.symm (f q)))))))=_
        rw [hval]
        rw [hj2]
        rw [(𝓡∂ 2).right_inv (by
          rw [range_modelWithCornersEuclideanHalfSpace]
          have hx := hxsource q hq
          rw [hj2s] at hx
          exact (show 0<(dx (cp q.1,tf (scaleTime a ha.le ha1.le q.2))) 0 from hx).le)]
        change dx (cp q.1,j1.symm (IccLeftChart 0 1 (scaleTime a ha.le ha1.le q.2)))=_
        rw [hj1inv,hdx]
        ext i
        fin_cases i
        · rfl
        · change 1 - a⁻¹*(a*(q.2:ℝ)-0)=1-(q.2:ℝ)
          field_simp [ne_of_gt ha]
          ring
    have hpdom : p ∈ dom.source := ⟨hpcc,by change (0:ℝ)<(p.2:ℝ); rw [hp]; norm_num⟩
    let lin : (Euc 1 × Euc 1) ≃ₗ[ℝ] Euc 2 :=
      { toFun := fun u => !₂[u.1 0,u.2 0]
        invFun := fun w => (!₂[w 0],!₂[w 1])
        left_inv := by intro u; apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
        right_inv := by intro w; ext i; fin_cases i <;> rfl
        map_add' := by intro u w; ext i; fin_cases i <;> rfl
        map_smul' := by intro r u; ext i; fin_cases i <;> rfl }
    let L := (ContinuousLinearEquiv.prodUnique ℝ (Euc 1 × Euc 1) (Euc 0)).trans lin.toContinuousLinearEquiv
    apply Manifold.IsImmersionAtOfComplement.mk_of_charts (I:=CollarModel) (J:=𝓡∂ 2) L dom cod hpdom (hmem p hpdom).1 hdom hcod
    · exact fun q hq => (hmem q hq).1
    · intro u hu
      let q := (dom.extend CollarModel).symm u
      have hq : q ∈ dom.source := by simpa only [OpenPartialHomeomorph.extend_source] using (dom.extend CollarModel).map_target hu
      change (𝓡∂ 2) (cod (f q))=L (u,0)
      rw [(hmem q hq).2]
      have heq := (dom.extend CollarModel).right_inv hu
      change (cp q.1,(𝓡∂ 1) (IccRightChart 0 1 q.2))=u at heq
      rw [←heq]
      ext i
      fin_cases i
      · rfl
      · rfl
  have hinward : ∀ z, ∃ w : TangentSpace (𝓡∂ 1) (0:Time),
      0 < inwardCoordinate (F.boundary.toFun z)
        (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => c.toFun (z,scaleTime a ha.le ha1.le t)) 0 w) := by
    let s := scaleTime a ha.le ha1.le
    have hs : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ s := by
      apply contMDiff_iff_comp_subtypeVal_Icc.mpr
      exact ⟨(continuous_const.mul continuous_subtype_val).subtype_mk _,
        contMDiff_const.mul contMDiff_subtypeVal_Icc⟩
    have hs0 : s 0=0 := by apply Subtype.ext; simp [s,scaleTime]
    let d := mfderiv (𝓡∂ 1) 𝓘(ℝ,ℝ) (Subtype.val : Time → ℝ) (0:Time)
    have hdi : Function.Injective d :=
      (isSmoothEmbedding_subtypeVal_Icc (n:=∞)).isImmersion.mfderiv_injective (by simp) (0:Time)
    let A : ℝ →L[ℝ] ℝ := a • ContinuousLinearMap.id ℝ ℝ
    have he : (Subtype.val ∘ s : Time → ℝ)=A ∘ Subtype.val := rfl
    have h1 := mfderiv_comp (0:Time)
      ((contMDiff_subtypeVal_Icc (n:=∞)).mdifferentiableAt (by simp) (x:=s 0))
      (hs.mdifferentiableAt (by simp))
    have h2 := mfderiv_comp (0:Time) A.differentiableAt.mdifferentiableAt
      ((contMDiff_subtypeVal_Icc (n:=∞)).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv,ContinuousLinearMap.fderiv] at h2
    rw [he] at h1
    rw [hs0] at h1
    have hscale (w : TangentSpace (𝓡∂ 1) (0:Time)) :
        mfderiv (𝓡∂ 1) (𝓡∂ 1) s (0:Time) w=a • w := by
      apply hdi
      have hh := congrArg (fun L => L w) (h1.symm.trans h2)
      change d (mfderiv (𝓡∂ 1) (𝓡∂ 1) s (0:Time) w)=a • d w at hh
      simpa only [map_smul] using hh
    intro z
    obtain ⟨w,hw⟩ := c.inward z
    let u : TangentSpace (𝓡∂ 1) (0:Time) := a⁻¹ • w
    have hc : ContMDiff (𝓡∂ 1) (𝓡∂ 2) ∞ (fun t => c.toFun (z,t)) :=
      c.embedding.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)
    have hchain := mfderiv_comp (0:Time)
      (hc.mdifferentiableAt (by simp) (x:=s 0)) (hs.mdifferentiableAt (by simp))
    have hv := congrArg (fun L => L u) hchain
    change (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => c.toFun (z,s t)) (0:Time) u:Euc 2)=
        (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => c.toFun (z,t)) (s 0)
          (mfderiv (𝓡∂ 1) (𝓡∂ 1) s (0:Time) u):Euc 2) at hv
    rw [hscale] at hv
    change (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => c.toFun (z,s t)) (0:Time) u:Euc 2)=
      (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => c.toFun (z,t)) (s 0) (a • u):Euc 2) at hv
    have hau : (a • u:Euc 1)=(w:Euc 1) := by simp [u,smul_smul,ne_of_gt ha]
    rw [hau] at hv
    have hzero := congrArg (fun t : Time =>
      (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => c.toFun (z,t)) t (w:Euc 1):Euc 2)) hs0
    have hv2 := hv.trans hzero
    change (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => c.toFun (z,s t)) (0:Time) u:Euc 2)=
      (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => c.toFun (z,t)) 0 w:Euc 2) at hv2
    exact ⟨u,hv2 ▸ hw⟩
  let f : Circle × Time → F.surface := fun q => c.toFun (q.1,scaleTime a ha.le ha1.le q.2)
  have himm : Manifold.IsImmersionOfComplement (Euc 0) CollarModel (𝓡∂ 2) ∞ f := by
    intro p
    by_cases hp : (p.2:ℝ)<1
    · exact hlower p hp
    · exact hupper p (le_antisymm p.2.property.2 (le_of_not_gt hp))
  have hinj : Function.Injective f := by
    intro p q heq
    have h := c.embedding.isEmbedding.injective heq
    have hz := congrArg (@Prod.fst Circle Time) h
    refine Prod.ext hz ?_
    apply Subtype.ext
    exact mul_left_cancel₀ (ne_of_gt ha) (congrArg (fun u : Circle × Time => (u.2:ℝ)) h)
  let b := (a+1)/2
  have hab : a<b := by dsimp [b]; linarith
  have hb : b<1 := by dsimp [b]; linarith
  obtain ⟨A⟩ := source_collar_substrip_coordinates c a b ha hab hb
  have himage : f '' {p | (p.2:ℝ)<1}=c.toFun '' {p | (p.2:ℝ)<a} := by
    ext y
    constructor
    · rintro ⟨p,hp,rfl⟩
      refine ⟨(p.1,scaleTime a ha.le ha1.le p.2),?_,rfl⟩
      change a*(p.2:ℝ)<a
      exact (mul_lt_mul_of_pos_left hp ha).trans_eq (mul_one a)
    · rintro ⟨p,hp,rfl⟩
      let t : Time := ⟨(p.2:ℝ)/a,div_nonneg p.2.property.1 ha.le,
        (div_lt_one ha).mpr hp |>.le⟩
      refine ⟨(p.1,t),(div_lt_one ha).mpr hp,?_⟩
      change c.toFun (p.1,scaleTime a ha.le ha1.le t)=c.toFun p
      congr 1
      refine Prod.ext rfl ?_
      apply Subtype.ext
      change a*((p.2:ℝ)/a)=(p.2:ℝ)
      field_simp [ne_of_gt ha]
  have hboundary (z : Circle) : f (z,0)=c.toFun (z,0) := by
    change c.toFun (z,scaleTime a ha.le ha1.le 0)=_
    congr 1
    refine Prod.ext rfl ?_
    apply Subtype.ext
    simp [scaleTime]
  have hinterior (z : Circle) (t : Time) (ht : 0<(t:ℝ)) : f (z,t) ∉ F.surface.boundary :=
    c.interior z (scaleTime a ha.le ha1.le t) (mul_pos ha ht)
  let d : SourceCollar F :=
    { toFun := f
      embedding := ⟨himm.isImmersion,(himm.contMDiff.continuous.isClosedEmbedding hinj).isEmbedding⟩
      boundary := fun z => (hboundary z).trans (c.boundary z)
      neighborhood := by rw [himage,←A.image_eq]; exact A.image.isOpen
      inward := hinward
      interior := hinterior }
  exact ⟨{ rescaled := d
           boundary := hboundary
           interior := hinterior
           equation := fun _ _ => rfl }⟩

theorem C1_open_substrip {K : OrientedKnot} {F : SphereSpanningSurface.{0} K}
    (c : SourceCollar F) (a b : ℝ) (ha : 0<a) (hab : a<b) (hb : b<1) :
    ∃ image : TopologicalSpace.Opens F.surface,
      (image : Set F.surface)=c.toFun '' {p | (p.2:ℝ)<a} ∧
      ∃ d : Diffeomorph CollarModel (𝓡∂ 2) (openTimeStrip a) image ∞,
        ∀ p, (d p : F.surface)=c.toFun p.val := by
  rcases source_collar_substrip_coordinates c a b ha hab hb with ⟨A⟩
  exact ⟨A.image,A.image_eq,A.coordinates,A.equation⟩


theorem C2_compact_remainder {K : OrientedKnot} {F : SphereSpanningSurface.{0} K}
    (c : SourceCollar F) (a b : ℝ) (ha : 0<a) (hab : a<b) (hb : b<1)
    (image : TopologicalSpace.Opens F.surface)
    (hi : (image : Set F.surface)=c.toFun '' {p | (p.2:ℝ)<a}) :
    IsCompact (c.toFun '' {p : Circle × Time | (p.2:ℝ)≤b}) ∧
      IsCompact ((image : Set F.surface)ᶜ) ∧
      Disjoint ((image : Set F.surface)ᶜ) (Set.range F.boundary.toFun) := by
  refine ⟨?_,image.isOpen.isClosed_compl.isCompact,?_⟩
  · apply (IsClosed.isCompact ?_).image c.embedding.isEmbedding.continuous
    exact isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const
  · apply Set.disjoint_left.mpr
    intro x hx hboundary
    rcases hboundary with ⟨z,rfl⟩
    apply hx
    rw [hi]
    exact ⟨(z,0),by simpa using ha,c.boundary z⟩


theorem C7_upper_collar {K : OrientedKnot} {F : SphereSpanningSurface.{0} K}
    (X : C3InwardField F) (Y : C4LocalFlow X) (Z : C5UniformFlow X Y)
    (J : C6FlowCharts X Y Z) :
    ∃ c : SourceCollar F, (∀ p, c.toFun p=Z.flow (p.1,Z.lambda*(p.2:ℝ))) ∧
      ∃ A : C7UpperCollar c, (∀ z t, A.extension.map (z,t)=Z.flow (z,Z.lambda*t)) ∧
        Z.lambda*A.extension.width<Z.d := by
  let f : Circle × Time → F.surface := fun p => Z.flow (p.1,Z.lambda*(p.2:ℝ))
  have himm : Manifold.IsImmersionOfComplement (Euc 0) CollarModel (𝓡∂ 2) ∞ f := by
    intro p
    obtain ⟨source,target,L,hp,hf,hs,ht,hsub,heq⟩ := J.charts p
    exact Manifold.IsImmersionAtOfComplement.mk_of_charts L source target hp hf hs ht hsub heq
  have hinj : Function.Injective f := by
    intro p q hpq
    have heq := Z.injective
      (by exact ⟨mul_nonneg Z.lambda_pos.le p.2.property.1,
        (mul_le_of_le_one_right Z.lambda_pos.le p.2.property.2).trans_lt Z.lambda_lt⟩)
      (by exact ⟨mul_nonneg Z.lambda_pos.le q.2.property.1,
        (mul_le_of_le_one_right Z.lambda_pos.le q.2.property.2).trans_lt Z.lambda_lt⟩) hpq
    refine Prod.ext (congrArg (@Prod.fst Circle ℝ) heq) ?_
    apply Subtype.ext
    exact mul_left_cancel₀ (ne_of_gt Z.lambda_pos) (congrArg (@Prod.snd Circle ℝ) heq)
  have hboundary (z : Circle) : f (z,0)=F.boundary.toFun z := by simpa [f] using Z.zero z
  have hinward (z : Circle) : ∃ w : TangentSpace (𝓡∂ 1) (0:Time),
      0 < inwardCoordinate (F.boundary.toFun z)
        (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => f (z,t)) 0 w) := by
    let g : ℝ → F.surface := fun t => Z.flow (z,t)
    let a : Time → ℝ := fun t => Z.lambda*(t:ℝ)
    let B : ℝ →L[ℝ] ℝ := Z.lambda • ContinuousLinearMap.id ℝ ℝ
    have hg : ContMDiffOn 𝓘(ℝ,ℝ) (𝓡∂ 2) ∞ g {t | 0≤t ∧ t<Z.d} :=
      Z.smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun _ ht => ht)
    have hg0 : MDifferentiableWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 2) g (Ici 0) 0 := by
      have hc : ContMDiffWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 2) ∞ g (Ici 0) 0 :=
        (hg 0 ⟨le_rfl,Z.d_pos⟩).mono_of_mem_nhdsWithin
          (Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds Z.d_pos)))
      exact hc.mdifferentiableWithinAt (by simp)
    have ha : ContMDiff (𝓡∂ 1) 𝓘(ℝ,ℝ) ∞ a := contMDiff_const.mul contMDiff_subtypeVal_Icc
    have hader : mfderiv (𝓡∂ 1) 𝓘(ℝ,ℝ) a (0:Time)=B.comp
        (mfderiv (𝓡∂ 1) 𝓘(ℝ,ℝ) (Subtype.val : Time → ℝ) 0) := by
      have h := mfderiv_comp (0:Time) B.differentiableAt.mdifferentiableAt
        ((contMDiff_subtypeVal_Icc (n:=∞)).mdifferentiableAt (by simp))
      rw [mfderiv_eq_fderiv,ContinuousLinearMap.fderiv] at h
      exact h
    have hc := mfderivWithin_comp_of_eq (s:=univ) (u:=Ici 0)
      hg0 (ha.mdifferentiableAt (by simp)).mdifferentiableWithinAt
      (fun t _ => mul_nonneg Z.lambda_pos.le t.property.1)
      (uniqueMDiffWithinAt_univ (𝓡∂ 1)) (show a (0:Time)=0 by simp [a])
    rw [mfderivWithin_univ,mfderivWithin_univ,hader] at hc
    have hvalue : mfderiv (𝓡∂ 1) 𝓘(ℝ,ℝ) (Subtype.val : Time → ℝ) (0:Time)
        (1:TangentSpace (𝓡∂ 1) (0:Time))=1 := mfderiv_subtypeVal_Icc_one (0:Time)
    have hder : mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => f (z,t)) (0:Time) (1:TangentSpace (𝓡∂ 1) (0:Time))=
        Z.lambda • X.field (F.boundary.toFun z) := by
      have h := congrArg (fun L => L (1:TangentSpace (𝓡∂ 1) (0:Time))) hc
      change mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => f (z,t)) (0:Time) (1:TangentSpace (𝓡∂ 1) (0:Time))=
        mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 2) g (Ici 0) 0
          (B (mfderiv (𝓡∂ 1) 𝓘(ℝ,ℝ) (Subtype.val : Time → ℝ) 0 (1:TangentSpace (𝓡∂ 1) (0:Time)))) at h
      rw [hvalue] at h
      change _=mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 2) g (Ici 0) 0 (Z.lambda • (1:ℝ)) at h
      have hsm := (mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 2) g (Ici 0) 0).map_smul Z.lambda (1:ℝ)
      have h' := h.trans hsm
      have hz := Z.time_deriv z 0 le_rfl Z.d_pos
      change mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 2) g (Ici 0) 0 (1:ℝ)=X.field (Z.flow (z,0)) at hz
      change (mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 2) g (Ici 0) 0 (1:ℝ) : Euc 2)=(X.field (Z.flow (z,0)) : Euc 2) at hz
      rw [hz] at h'
      change _=(Z.lambda • X.field (F.boundary.toFun z) : Euc 2)
      change ((mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => f (z,t)) (0:Time)
        (1:TangentSpace (𝓡∂ 1) (0:Time))):Euc 2)=
          (Z.lambda • X.field (Z.flow (z,0)):Euc 2) at h'
      rw [Z.zero z] at h'
      exact h'
    refine ⟨(1:TangentSpace (𝓡∂ 1) (0:Time)),?_⟩
    rw [hder]
    change 0 < (tangentSpaceCastModel 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) (F.boundary.toFun z) (F.boundary.toFun z))
      ((mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 2) (extChartAt (𝓡∂ 2) (F.boundary.toFun z))
      (F.boundary.toFun z) (Z.lambda • X.field (F.boundary.toFun z)))) 0)
    rw [map_smul]
    exact mul_pos Z.lambda_pos (X.positive z)
  let c : SourceCollar F :=
    { toFun := f
      embedding := ⟨himm.isImmersion,(himm.contMDiff.continuous.isClosedEmbedding hinj).isEmbedding⟩
      boundary := hboundary
      neighborhood := J.open_image
      inward := hinward
      interior := fun z t ht => Z.positive z (Z.lambda*(t:ℝ)) (mul_pos Z.lambda_pos ht)
        ((mul_le_of_le_one_right Z.lambda_pos.le t.property.2).trans_lt Z.lambda_lt) }
  let w := (1+Z.d/Z.lambda)/2
  have hw : 1<w := by
    have h : (1:ℝ)<Z.d/Z.lambda := (lt_div_iff₀ Z.lambda_pos).mpr (by simpa using Z.lambda_lt)
    dsimp [w]; linarith
  have hwd : Z.lambda*w<Z.d := by
    have h := div_mul_cancel₀ Z.d (ne_of_gt Z.lambda_pos)
    dsimp [w]
    nlinarith [Z.lambda_lt]
  let fext : Circle × ℝ → F.surface := fun p => Z.flow (p.1,Z.lambda*p.2)
  have hext : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 2) ∞ fext {p | 0≤p.2 ∧ p.2<w} := by
    exact Z.smooth.comp (contMDiff_fst.prodMk (contMDiff_const.mul contMDiff_snd)).contMDiffOn
      (fun p hp => ⟨mul_nonneg Z.lambda_pos.le hp.1,
        (mul_lt_mul_of_pos_left hp.2 Z.lambda_pos).trans hwd⟩)
  let dl : Diffeomorph 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ℝ ℝ ∞ :=
    ⟨(Homeomorph.mulLeft₀ Z.lambda (ne_of_gt Z.lambda_pos)).toEquiv,
      contMDiff_const.mul contMDiff_id,contMDiff_const.mul contMDiff_id⟩
  let e := (Diffeomorph.refl (𝓡 1) Circle ∞).prodCongr dl
  have hie : ∀ z, Manifold.IsImmersionAt ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 2) ∞ fext (z,1) := by
    intro z
    let h := J.positive_time_immersion z Z.lambda Z.lambda_pos Z.lambda_lt
    let H := h.isImmersionAtOfComplement_complement
    let dom := e.toHomeomorph.toOpenPartialHomeomorph.trans H.domChart
    have hsource : (z,(1:ℝ)) ∈ dom.source := ⟨mem_univ _,by change (z,Z.lambda*(1:ℝ)) ∈ H.domChart.source; simpa only [mul_one] using H.mem_domChart_source⟩
    have hdom : dom ∈ IsManifold.maximalAtlas ((𝓡 1).prod 𝓘(ℝ,ℝ)) ∞ (Circle × ℝ) := by
      apply dom.mem_maximalAtlas_of_contMDiffOn
      · exact (contMDiffOn_of_mem_maximalAtlas H.domChart_mem_maximalAtlas).comp
          e.contMDiff.contMDiffOn (fun _ hp => hp.2)
      · exact e.symm.contMDiff.comp_contMDiffOn
          ((contMDiffOn_symm_of_mem_maximalAtlas H.domChart_mem_maximalAtlas).mono (fun _ hp => hp.1))
    apply Manifold.IsImmersionAtOfComplement.isImmersionAt (F:=h.complement)
    apply Manifold.IsImmersionAtOfComplement.mk_of_charts H.equiv dom H.codChart hsource
    · change Z.flow (z,Z.lambda*(1:ℝ)) ∈ H.codChart.source
      simpa only [mul_one] using H.mem_codChart_source
    · exact hdom
    · exact H.codChart_mem_maximalAtlas
    · intro p hp
      exact H.source_subset_preimage_source hp.2
    · intro u hu
      have hut : u ∈ (H.domChart.extend ((𝓡 1).prod 𝓘(ℝ,ℝ))).target := by
        rw [dom.extend_target (I:=((𝓡 1).prod 𝓘(ℝ,ℝ)))] at hu
        rcases hu with ⟨hum,hur⟩
        rw [H.domChart.extend_target (I:=((𝓡 1).prod 𝓘(ℝ,ℝ)))]
        exact ⟨hum.1,hur⟩
      have heq := H.writtenInCharts hut
      change (H.codChart.extend (𝓡∂ 2)) (Z.flow
        (e (e.symm ((H.domChart.extend ((𝓡 1).prod 𝓘(ℝ,ℝ))).symm u))))=H.equiv (u,0)
      rw [e.apply_symm_apply]
      exact heq
  let extension : UpperExtendedCollar c :=
    { width := w
      width_gt_one := hw
      map := fext
      agrees := fun _ => rfl
      smooth := hext
      upper_immersion := hie }
  exact ⟨c,fun _ => rfl,{ extension := extension,width_gt_one := hw,endpoint_immersion := hie },
    fun _ _ => rfl,hwd⟩



end
end SeifertSurfaces.LongitudeProducers.CollarCutHelpers.Remaining
