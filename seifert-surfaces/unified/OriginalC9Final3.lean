import C9BoundaryHelpers

noncomputable section
open Bundle
open scoped Manifold ContDiff Topology

namespace SeifertSurfaces.AppendixC.Original

universe u v
variable (S : Type u) [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]
  (D : Type v) [TopologicalSpace D] [ChartedSpace Plane D]
  [IsManifold (𝓡 2) ∞ D]

-- Preserve the frozen declarations' compiler-generated instance-binder names.
-- Restore the exporting module before serializing; imports remain acyclic.
run_cmd Lean.modifyEnv fun env => env.setMainModule `OriginalC9

/-- Recover the genuine half-disk boundary charts from the full C.8 charts
and the raw GIVEN diffeomorphism, in its same atlas. -/
theorem raw_L2doubleprime_boundary_interface
    [T2Space S] [SecondCountableTopology S] [CompactSpace S]
    [T2Space D] [SecondCountableTopology D] [CompactSpace D]
    (t : InteriorConformalField (𝓡∂ 2) S) (j : S → D)
    (d : SmoothDouble S D j)
    (c : RawL2DoublePrime S D t d.swap.toHomeomorph)
    (r : ∀ q : D, c.involution q = q →
      Nonempty (DiskReflectionChart D c.atlas c.involution q)) :
    Nonempty (AnalyticBoundaryPullback S D t d.swap.toHomeomorph c) := by
  have hboundary := given_diffeomorphism_boundary_fixed S D t j d c r
  exact reflection_component_half_disk_pullback S D t j d c r hboundary

/-- The residual component/subsurface interface for L2″. C.7 constructs the
metric; C.8 and conjugacy construct the boundary and separating-component
properties. The supplied parametrization and its inverse are preserved. -/
theorem raw_L2doubleprime_support_interface
    [T2Space S] [SecondCountableTopology S] [CompactSpace S]
    [T2Space D] [SecondCountableTopology D] [CompactSpace D]
    (t : InteriorConformalField (𝓡∂ 2) S) (j : S → D)
    (d : SmoothDouble S D j)
    (c : RawL2DoublePrime S D t d.swap.toHomeomorph) :
    ∃ h : L2DoublePrimeCompatibility (𝓡∂ 2) (𝓡 2) S D t d.swap.toHomeomorph,
      PointwiseConformal (𝓡 2) D h.double_metric.inner c.double_class.representative ∧
      h.conformal_atlas = c.atlas ∧ h.involution = c.involution ∧
      h.conjugacy = c.conjugacy ∧ h.component = c.component ∧
      HEq h.parametrization c.diffeomorph.homeomorph := by
  classical
  obtain ⟨g, hg⟩ := c7_smooth_metric_representative (𝓡 2) D c.double_class
  let U : Set D := j '' (𝓡∂ 2).interior S
  let V : Set D := d.swap '' U
  let A : Set D := c.conjugacy '' U
  let B : Set D := c.conjugacy '' V
  have hU : U = interior (Set.range j) := by
    dsimp only [U]
    rw [← (𝓡∂ 2).compl_boundary, Set.image_compl_eq_range_sdiff_image d.inclusion.embedding.injective,
      d.inclusion.boundary_image, self_sdiff_frontier]
  have hUo : IsOpen U := hU ▸ isOpen_interior
  have hUc : IsConnected U := d.interior_connected
  have hVo : IsOpen V := d.swap.toHomeomorph.isOpenMap _ hUo
  have hVc : IsConnected V := hUc.image d.swap d.swap.contMDiff.continuous.continuousOn
  have hUfixed : ∀ x ∈ U, d.swap x ≠ x := by
    intro x hx heq
    have hxb : x ∈ j '' (𝓡∂ 2).boundary S := by
      rw [← d.fixed_boundary]
      exact heq
    rcases hx with ⟨p, hp, rfl⟩
    rcases hxb with ⟨q, hq, hjq⟩
    have : q = p := d.inclusion.embedding.injective hjq
    subst q
    exact Set.disjoint_left.mp (𝓡∂ 2).disjoint_interior_boundary hp hq
  have hVfixed : ∀ x ∈ V, d.swap x ≠ x := by
    rintro x ⟨y, hy, rfl⟩ heq
    apply hUfixed y hy
    simpa only [d.involutive y] using heq.symm
  have hUV : Disjoint U V := by
    rw [Set.disjoint_left]
    rintro x hx ⟨y, hy, hxy⟩
    have hboth : x ∈ Set.range j ∩ d.swap '' Set.range j := by
      exact ⟨by rcases hx with ⟨p, hp, rfl⟩; exact ⟨p, rfl⟩,
        ⟨y, by rcases hy with ⟨p, hp, rfl⟩; exact ⟨p, rfl⟩, hxy⟩⟩
    rw [d.overlap, ← d.fixed_boundary] at hboth
    exact hUfixed x hx hboth
  have hcover : U ∪ V = {x | d.swap x ≠ x} := by
    apply Set.Subset.antisymm
    · rintro x (hx | hx)
      · exact hUfixed x hx
      · exact hVfixed x hx
    · intro x hx
      have hxu : x ∈ Set.range j ∪ d.swap '' Set.range j := by rw [d.cover]; exact Set.mem_univ x
      have hleft : ∀ y ∈ Set.range j, d.swap y ≠ y → y ∈ U := by
        rintro y ⟨p, rfl⟩ hy
        rcases (𝓡∂ 2).isInteriorPoint_or_isBoundaryPoint p with hp | hp
        · exact ⟨p, hp, rfl⟩
        · apply False.elim
          apply hy
          have : j p ∈ j '' (𝓡∂ 2).boundary S := ⟨p, hp, rfl⟩
          rwa [← d.fixed_boundary] at this
      rcases hxu with h | ⟨y, hy, rfl⟩
      · exact Or.inl (hleft x h hx)
      · refine Or.inr ⟨y, hleft y hy ?_, rfl⟩
        intro heq
        apply hx
        rw [d.involutive y, heq]
  have hAo : IsOpen A := c.conjugacy.isOpenMap _ hUo
  have hBo : IsOpen B := c.conjugacy.isOpenMap _ hVo
  have hAc : IsConnected A := hUc.image c.conjugacy c.conjugacy.continuous.continuousOn
  have hBc : IsConnected B := hVc.image c.conjugacy c.conjugacy.continuous.continuousOn
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro x ⟨y, hy, rfl⟩ ⟨z, hz, heq⟩
    have : z = y := c.conjugacy.injective heq
    subst z
    exact Set.disjoint_left.mp hUV hy hz
  have hconjfixed (x : D) : c.involution (c.conjugacy x) ≠ c.conjugacy x ↔ d.swap x ≠ x := by
    rw [c.conjugate_swap]
    exact not_congr c.conjugacy.injective.eq_iff
  have hABcover : A ∪ B = {x | c.involution x ≠ x} := by
    rw [← Set.image_union, hcover]
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact (hconjfixed y).2 hy
    · intro x hx
      refine ⟨c.conjugacy.symm x, (hconjfixed _).1 ?_, c.conjugacy.apply_symm_apply x⟩
      simpa only [c.conjugacy.apply_symm_apply x, Set.mem_setOf_eq] using hx
  have havoid : c.component ⊆ {x | c.involution x ≠ x} := by
    rw [c.component_eq]
    exact connectedComponentIn_subset _ _
  have hcconnected : IsConnected c.component := by
    rw [c.component_eq]
    exact isConnected_connectedComponentIn_iff.mpr c.point_not_fixed
  have hcmem : c.component_point ∈ c.component := by
    rw [c.component_eq]
    exact mem_connectedComponentIn c.point_not_fixed
  have hcomponent : c.component = A ∨ c.component = B := by
    have hsub : c.component ⊆ A ∪ B := by rw [hABcover]; exact havoid
    rcases hcconnected.isPreconnected.subset_or_subset hAo hBo hAB hsub with ha | hb
    · left
      apply Set.Subset.antisymm ha
      rw [c.component_eq]
      apply hAc.isPreconnected.subset_connectedComponentIn (ha hcmem)
      intro x hx
      rw [← hABcover]
      exact Or.inl hx
    · right
      apply Set.Subset.antisymm hb
      rw [c.component_eq]
      apply hBc.isPreconnected.subset_connectedComponentIn (hb hcmem)
      intro x hx
      rw [← hABcover]
      exact Or.inr hx
  have hswapV : d.swap '' V = U := by
    dsimp only [V]
    rw [Set.image_image]
    have heq : (fun x => d.swap (d.swap x)) = id := funext d.involutive
    rw [heq, Set.image_id]
  have hIA : c.involution '' A = B := by
    change c.involution '' (c.conjugacy '' U) = c.conjugacy '' (d.swap '' U)
    have heq : (fun x => c.involution (c.conjugacy x)) =
        (fun x => c.conjugacy (d.swap x)) := funext c.conjugate_swap
    calc
      c.involution '' (c.conjugacy '' U) = (fun x => c.involution (c.conjugacy x)) '' U :=
        Set.image_image _ _ U
      _ = (fun x => c.conjugacy (d.swap x)) '' U := congrArg (fun f => f '' U) heq
      _ = c.conjugacy '' (d.swap '' U) := (Set.image_image _ _ U).symm
  have hIB : c.involution '' B = A := by
    rw [← hIA, Set.image_image]
    have heq : (fun x => c.involution (c.involution x)) = id := funext c.involutive
    rw [heq, Set.image_id]
  have hco : IsOpen c.component := by
    rcases hcomponent with ha | hb
    · rwa [ha]
    · rwa [hb]
  have hmax : ∀ C : Set D, IsPreconnected C → C ⊆ {x | c.involution x ≠ x} →
      (C ∩ c.component).Nonempty → C ⊆ c.component := by
    intro C hC hCsub hCm
    obtain ⟨x, hxC, hxc⟩ := hCm
    rw [c.component_eq] at hxc ⊢
    rw [connectedComponentIn_eq hxc]
    exact hC.subset_connectedComponentIn hxC hCsub
  have hexchange : c.involution '' c.component = {x | c.involution x ≠ x} \ c.component := by
    rw [← hABcover]
    rcases hcomponent with ha | hb
    · rw [ha, hIA]
      ext x
      constructor
      · intro hx
        exact ⟨Or.inr hx, fun hxa => Set.disjoint_left.mp hAB hxa hx⟩
      · rintro ⟨hx | hx, hxa⟩
        · exact False.elim (hxa hx)
        · exact hx
    · rw [hb, hIB]
      ext x
      constructor
      · intro hx
        exact ⟨Or.inl hx, fun hxb => Set.disjoint_left.mp hAB hx hxb⟩
      · rintro ⟨hx | hx, hxb⟩
        · exact hx
        · exact False.elim (hxb hx)
  refine ⟨{
    double_compact := isCompact_univ
    double_boundaryless := inferInstance
    double_metric := g
    conformal_atlas := c.atlas
    metric_in_atlas := ?_
    involution := c.involution
    involutive := c.involutive
    anti_conformal := c.anti_conformal
    conjugacy := c.conjugacy
    conjugate_swap := c.conjugate_swap
    component := c.component
    component_open := hco
    component_connected := hcconnected
    component_maximal := hmax
    component_avoids_fixed := havoid
    exchanges_components := hexchange
    parametrization := c.diffeomorph.homeomorph
    inclusion_smooth := c.diffeomorph.smooth
    inclusion_immersion := c.diffeomorph.immersion
    boundary_fixed := ?_
    pullback_conformal := ?_ }, hg, rfl, rfl, rfl, rfl, HEq.rfl⟩
  · intro p q hq
    obtain ⟨a, ha, hea⟩ := hg q
    obtain ⟨b, hb, heb⟩ := c.class_in_atlas p q hq
    refine ⟨a * b, mul_pos ha hb, ?_⟩
    intro v w
    rw [hea, heb, mul_assoc]
  · obtain ⟨b⟩ := raw_L2doubleprime_boundary_interface S D t j d c
      (paper_C8 D c.atlas c.involution c.involutive c.anti_conformal)
    exact b.boundary_fixed
  · intro p hp
    obtain ⟨a, ha, hea⟩ := hg (c.diffeomorph.homeomorph p : D)
    obtain ⟨b, hb, heb⟩ := c.class_pullback p
    refine ⟨a * b, mul_pos ha hb, ?_⟩
    intro v w
    rw [hea, heb, mul_assoc]

/-- The full original Proposition C.9. The caller supplies one of the two
literal compatibilities; neither one is asserted to exist. The metric is
smooth on all S and represents the SAME t, including its prescribed boundary
values. For the supplied L2″ witness the same atlas/diffeomorphism/inverse
furnishes real-analytic boundary charts. -/
theorem paper_C9
    [T2Space S] [SecondCountableTopology S] [CompactSpace S]
    [T2Space D] [SecondCountableTopology D] [CompactSpace D]
    (t : InteriorConformalField (𝓡∂ 2) S) (j : S → D)
    (d : SmoothDouble S D j)
    (compatibility : RawL2Prime S D t j ⊕
      RawL2DoublePrime S D t d.swap.toHomeomorph) :
    (∃ g : ContMDiffRiemannianMetric (𝓡∂ 2) ∞ Plane
        (fun p : S => TangentSpace (𝓡∂ 2) p),
      PointwiseConformal (𝓡∂ 2) S g.inner t.representative) ∧
    ∀ c : RawL2DoublePrime S D t d.swap.toHomeomorph,
      compatibility = Sum.inr c →
      Nonempty (AnalyticBoundaryPullback S D t d.swap.toHomeomorph c) := by
  constructor
  · cases compatibility with
    | inl c =>
      obtain ⟨h, hh, hΦeq⟩ := raw_L2prime_support_interface S D t j d c
      let Φ := c.diffeomorph
      have hΦ : ∀ q, Function.Injective (mfderiv (𝓡 2) (𝓡 2) Φ q) := by
        intro q
        have hi : Function.Injective (mfderiv (𝓡 2) (𝓡 2) (Φ.symm ∘ Φ) q) := by
          have heq : (Φ.symm ∘ Φ : D → D) = id := by
            funext x
            exact Φ.symm_apply_apply x
          rw [heq, mfderiv_id]
          exact Function.injective_id
        rw [mfderiv_comp q (Φ.symm.contMDiff.mdifferentiableAt (by simp))
          (Φ.contMDiff.mdifferentiableAt (by simp))] at hi
        exact Function.Injective.of_comp hi
      have hj : ContMDiff (𝓡∂ 2) (𝓡 2) ∞ (Φ ∘ j) :=
        Φ.contMDiff.comp d.inclusion.smooth
      have him : ∀ p, Function.Injective (mfderiv (𝓡∂ 2) (𝓡 2) (Φ ∘ j) p) := by
        intro p
        rw [mfderiv_comp p (Φ.contMDiff.mdifferentiableAt (by simp))
          (d.inclusion.smooth.mdifferentiableAt (by simp))]
        exact (hΦ (j p)).comp (d.inclusion.immersion p)
      obtain ⟨g, hg⟩ := c7_restrict_metric_smooth_up_to_boundary
        (𝓡 2) D (𝓡∂ 2) S (Φ ∘ j) hj him h.double_metric
      refine ⟨g, ?_⟩
      intro p
      obtain ⟨a, ha, hea⟩ := hh (Φ (j p))
      obtain ⟨b, hb, heb⟩ := c.class_pullback p
      refine ⟨a * b, mul_pos ha hb, ?_⟩
      intro v w
      rw [hg]
      simp only [Function.comp_apply, mfderiv_comp p
        (Φ.contMDiff.mdifferentiableAt (by simp))
        (d.inclusion.smooth.mdifferentiableAt (by simp)), ContinuousLinearMap.comp_apply]
      rw [hea, heb, mul_assoc]
    | inr c =>
      obtain ⟨gd, hgd⟩ := c7_smooth_metric_representative (𝓡 2) D c.double_class
      obtain ⟨g, hg⟩ := c7_restrict_metric_smooth_up_to_boundary
        (𝓡 2) D (𝓡∂ 2) S (fun q => (c.diffeomorph.homeomorph q : D))
        c.diffeomorph.smooth c.diffeomorph.immersion gd
      refine ⟨g, ?_⟩
      intro p
      obtain ⟨a, ha, hea⟩ := hgd (c.diffeomorph.homeomorph p : D)
      obtain ⟨b, hb, heb⟩ := c.class_pullback p
      refine ⟨a * b, mul_pos ha hb, ?_⟩
      intro v w
      rw [hg, hea, heb, mul_assoc]
  · intro c hc
    apply raw_L2doubleprime_boundary_interface S D t j d c
    exact paper_C8 D c.atlas c.involution c.involutive c.anti_conformal

run_cmd Lean.modifyEnv fun env => env.setMainModule `OriginalC9Final3

end SeifertSurfaces.AppendixC.Original
