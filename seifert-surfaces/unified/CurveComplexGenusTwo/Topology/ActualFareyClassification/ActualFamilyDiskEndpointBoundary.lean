import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSourceClosedFamilyDisk

open Set Topology Schoenflies Metric

/-- Actual compact interval contact forces both source endpoints onto the
boundary of the actual disk. No endpoint-boundary certificate is supplied. -/
theorem actual_line_interval_disk_endpoints_on_boundary
    (G : C(ℝ,Plane)) (hG : Function.Injective G) (a b : ℝ) (hab : a<b)
    (Phi : Plane ≃ₜ Plane)
    (hcontact : (Phi '' Plane.closedSquare 0 1)∩range G=G '' Icc a b) :
    Phi.symm (G a)∈modelCurve ∧ Phi.symm (G b)∈modelCurve := by
  let U := Phi '' Plane.openSquare 0 1
  have hU : IsOpen U := Phi.isOpenMap _ (Plane.isOpen_openSquare 0 1)
  have hUD : U⊆Phi '' Plane.closedSquare 0 1 := image_mono (by
    intro z hz
    rw [mem_openSquare_zero_one] at hz
    exact mem_closedSquare_zero_one.mpr hz.le)
  have hboundary (t : ℝ) (ht : t=a ∨ t=b) : G t∉U := by
    intro hGt
    have ho : IsOpen (G ⁻¹' U) := hU.preimage G.continuous
    obtain ⟨epsilon,hepsilon,he⟩ := Metric.isOpen_iff.mp ho t hGt
    rcases ht with ht|ht
    · subst t
      have hu : a-epsilon/2∈G ⁻¹' U := he (by
        rw [mem_ball,Real.dist_eq]
        have hh : a-epsilon/2-a= -epsilon/2 := by ring
        rw [hh,abs_div,abs_neg,abs_of_pos hepsilon]
        linarith)
      have hh : G (a-epsilon/2)∈G '' Icc a b := hcontact ▸
        (show G (a-epsilon/2)∈(Phi '' Plane.closedSquare 0 1)∩range G from ⟨hUD hu,mem_range_self _⟩)
      obtain ⟨v,hv,hvG⟩ := hh
      have hv0 := hG hvG
      linarith [hv.1]
    · subst t
      have hu : b+epsilon/2∈G ⁻¹' U := he (by
        rw [mem_ball,Real.dist_eq]
        have hh : b+epsilon/2-b=epsilon/2 := by ring
        rw [hh,abs_div,abs_of_pos hepsilon]
        linarith)
      have hh : G (b+epsilon/2)∈G '' Icc a b := hcontact ▸
        (show G (b+epsilon/2)∈(Phi '' Plane.closedSquare 0 1)∩range G from ⟨hUD hu,mem_range_self _⟩)
      obtain ⟨v,hv,hvG⟩ := hh
      have hv0 := hG hvG
      linarith [hv.2]
  have hend (t : ℝ) (ht : t=a ∨ t=b) : Phi.symm (G t)∈modelCurve := by
    have htI : t∈Icc a b := by rcases ht with rfl|rfl <;> exact ⟨by linarith,by linarith⟩
    have hGtD : G t∈Phi '' Plane.closedSquare 0 1 :=
      (show G t∈(Phi '' Plane.closedSquare 0 1)∩range G from hcontact.symm ▸ mem_image_of_mem G htI).1
    obtain ⟨z,hz,hzG⟩ := hGtD
    have hpt : Phi.symm (G t)∈Plane.closedSquare 0 1 := by rw [←hzG,Phi.symm_apply_apply]; exact hz
    have hn := mem_closedSquare_zero_one.mp hpt
    change Plane.supNorm (Phi.symm (G t))=1
    apply le_antisymm hn
    by_contra hh
    have hlt : Plane.supNorm (Phi.symm (G t))<1 := lt_of_not_ge hh
    exact hboundary t ht ⟨Phi.symm (G t),mem_openSquare_zero_one.mpr hlt,Phi.apply_symm_apply _⟩
  exact ⟨hend a (Or.inl rfl),hend b (Or.inr rfl)⟩

#print axioms actual_line_interval_disk_endpoints_on_boundary
