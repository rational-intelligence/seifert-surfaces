import CurveComplexGenusTwo.Topology.StarConeChart

set_option linter.style.haveILetI false

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set

variable {V : Type*} [DecidableEq V]

/-- A quotient-topology identification of the actual realized star with the
cone on its actual realized link turns link contractibility into the required
local strong deformation retract. The quotient-map premise is the remaining
topological chart theorem; it is strictly weaker than assuming an SDR. -/
theorem closedStar_local_sdr_of_quotient_chart
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u})
    (hfull : HasRealizedStarFaces K intersect v)
    [ContractibleSpace (RealizedSeparatingLink K intersect separating v)]
    (hquot : Topology.IsQuotientMap
      (closedStarConeMap K intersect separating v hfull)) :
    IsStrongDeformationRetract
      {x : ClosedStarLocus K intersect v |
        (x : RealizationPoint K) ∈
          RealizedSeparatingLink K intersect separating v} := by
  let f := closedStarConeMap K intersect separating v hfull
  have hfi : Function.Injective f :=
    closedStarConeMap_injective K intersect separating v hfull
  have hne : Nonempty (RealizedSeparatingLink K intersect separating v) := by
    obtain ⟨he⟩ := ContractibleSpace.hequiv_unit
      (RealizedSeparatingLink K intersect separating v)
    exact ⟨he.invFun ()⟩
  have hfs : Function.Surjective f :=
    closedStarConeMap_surjective K intersect separating hsep v hfull
      hne
  let e : TopologicalCone (RealizedSeparatingLink K intersect separating v) ≃ₜ
      ClosedStarLocus K intersect v :=
    (Equiv.ofBijective f ⟨hfi, hfs⟩).toHomeomorphOfContinuousOpen
      hquot.continuous (hquot.isCoinducing.isOpenMap_of_injective hfi)
  let s := Classical.choice
    (topologicalConeBase_sdr (X := RealizedSeparatingLink K intersect separating v))
  let H : C(ClosedStarLocus K intersect v × Interval,
      ClosedStarLocus K intersect v) :=
    ⟨fun p => e (s.homotopy (p.2, e.symm p.1)), by
      exact e.continuous.comp
        (s.homotopy.continuous.comp
          (continuous_snd.prodMk (e.symm.continuous.comp continuous_fst)))⟩
  have hbase (l : RealizedSeparatingLink K intersect separating v) :
      e (topologicalConeBase l) = ⟨l.1, l.property.1⟩ := by
    change f (topologicalConeBase l) = _
    exact closedStarConeMap_base K intersect separating v hfull l
  refine ⟨H, ?_, ?_, ?_⟩
  · intro x
    change e (s.homotopy (0, e.symm x)) = x
    have h0 : s.homotopy (0, e.symm x) = e.symm x :=
      s.homotopy.map_zero_left _
    rw [h0]
    exact e.apply_symm_apply x
  · intro x
    change (e (s.homotopy (1, e.symm x))).1 ∈
      RealizedSeparatingLink K intersect separating v
    have h1 : s.homotopy (1, e.symm x) =
        topologicalConeBase (s.retraction (e.symm x)) :=
      s.homotopy.map_one_left _
    rw [h1]
    rw [hbase]
    exact (s.retraction (e.symm x)).property
  · intro x hx t
    let l : RealizedSeparatingLink K intersect separating v := ⟨x.1, hx⟩
    have hxe : x = ⟨l.1, l.property.1⟩ := by
      apply Subtype.ext
      rfl
    have hex : e.symm x = topologicalConeBase l := by
      rw [hxe, ← hbase]
      exact e.symm_apply_apply _
    change e (s.homotopy (t, e.symm x)) = x
    rw [hex]
    have hfix := s.homotopy_base_fixed t l
    rw [hfix, hbase]

/-- The source-facing realization assembly after the geometric link
contractibility and actual star quotient-chart lemmas have been supplied.
The infinite cover and cylinder weak topology are discharged internally. -/
theorem realization_star_deletion_of_contractible_links_and_quotient_charts
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (hfull : ∀ v : {u : V // separating u},
      HasRealizedStarFaces K intersect v)
    (hlinks : ∀ v : {u : V // separating u},
      ContractibleSpace (RealizedSeparatingLink K intersect separating v))
    (hcharts : ∀ v : {u : V // separating u},
      Topology.IsQuotientMap
        (closedStarConeMap K intersect separating v (hfull v))) :
    IsStrongDeformationRetract (NonseparatingWeightLocus K separating) := by
  apply realization_simultaneous_separating_star_deletion K intersect separating
    hcurve hsep
  intro v
  haveI : ContractibleSpace (RealizedSeparatingLink K intersect separating v) :=
    hlinks v
  exact closedStar_local_sdr_of_quotient_chart K intersect separating hsep
    v (hfull v) (hcharts v)

end CurveComplexGenusTwo.Topology
