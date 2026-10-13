import HolomorphicAnosov.Ghys.CurveJetAffineData

/-! Local holomorphic sections of jet truncation with zero quadratic coefficient. (Ghys, §3
pp.591–592) -/
noncomputable section
open Set Filter
open scoped Topology _root_.Topology Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u

/-- Over each holomorphic curve chart, jet truncation admits a holomorphic section with zero
quadratic coefficient that commutes with nonzero scalar source changes. (Ghys, §3 pp.591–592) -/
theorem curve_jet_local_zero_section
    (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]
    [IsManifold 𝓘(ℂ) ∞ L] [T2Space L] [SecondCountableTopology L]
    (A1 : ChartedSpace (ℂ × ℂ) (CurveJet1 L))
    (A2 : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L))
    (hAtlases : CurveJetCoefficientAtlases L A1 A2) (c : LeafChart L) :
    letI := A1
    letI := A2
    ∃ σ : CurveJet1 L → CurveJet2 L,
      ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ σ
        ((curveJet1Base L) ⁻¹' c.1.source) ∧
      (∀ j, curveJet1Base L j ∈ c.1.source →
        curveJetTruncation L (σ j) = j ∧
        curveJet2Coeff L c (σ j) = (curveJet1Coeff L c j, 0)) ∧
      ∀ (omega : ℂˣ) j, curveJet1Base L j ∈ c.1.source →
        σ (curveJet1Scale L omega j) = curveJet2Reparametrize L (.scale omega) (σ j) := by
  let := A1
  let := A2
  obtain ⟨e1, e2, _, _, hs1, hs2, ht1, ht2, he1, he2,
    he1smooth, _, _, he2inv⟩ := hAtlases.2.2.1 c
  let σ : CurveJet1 L → CurveJet2 L := fun j ↦ e2.symm (e1 j, 0)
  have htarget (j : CurveJet1 L) (hj : curveJet1Base L j ∈ c.1.source) :
      (e1 j, (0 : ℂ)) ∈ e2.target := by
    rw [ht2]
    have h := e1.map_source (show j ∈ e1.source by rwa [hs1])
    rw [ht1] at h
    exact h
  have hsource (j : CurveJet1 L) (hj : curveJet1Base L j ∈ c.1.source) :
      curveJet2Base L (σ j) ∈ c.1.source := by
    have h := e2.map_target (htarget j hj)
    rwa [hs2] at h
  have hcoeff (j : CurveJet1 L) (hj : curveJet1Base L j ∈ c.1.source) :
      curveJet2Coeff L c (σ j) = (curveJet1Coeff L c j, 0) := by
    rw [← he2 (e2.map_target (htarget j hj))]
    rw [e2.right_inv (htarget j hj), he1 (show j ∈ e1.source by rwa [hs1])]
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro j hj
    have h1 := he1smooth.contMDiffAt
      (e1.open_source.mem_nhds (show j ∈ e1.source by rwa [hs1]))
    have h2 := he2inv.contMDiffAt (e2.open_target.mem_nhds (htarget j hj))
    have hembed : ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞
        (fun w : ℂ × ℂ ↦ (w, (0 : ℂ))) :=
      contMDiff_id.prodMk_space contMDiff_const
    exact (h2.comp j (hembed.contMDiffAt.comp j h1)).contMDiffWithinAt
  · intro j hj
    refine ⟨?_, hcoeff j hj⟩
    have ht := ((leaf_jet_complex_manifold L).2.2.2.1 c).2.2 (σ j) (hsource j hj)
    apply ((leaf_jet_complex_manifold L).2.2.2.1 c).1.injOn
      (show curveJet1Base L (curveJetTruncation L (σ j)) ∈ c.1.source from
        ht.1 ▸ hsource j hj) hj
    exact ht.2.trans (congrArg Prod.fst (hcoeff j hj))
  · intro omega j hj
    have hscale1 := (curve_jet_reparametrization L).2.2.2.1 omega j
    have hscale2 := (curve_jet_reparametrization L).2.2.1 (.scale omega) (σ j)
    have hjscale : curveJet1Base L (curveJet1Scale L omega j) ∈ c.1.source :=
      hscale1.1 ▸ hj
    apply ((leaf_jet_complex_manifold L).2.2.2.1 c).2.1.injOn
      (hsource _ hjscale)
      (show curveJet2Base L (curveJet2Reparametrize L (.scale omega) (σ j)) ∈ c.1.source
        from hscale2.1 ▸ hsource j hj)
    rw [hcoeff _ hjscale, hscale2.2.2 c (hsource j hj), hcoeff j hj, hscale1.2 c hj]
    simp only [CurveJetReparametrization.scale, mul_zero, zero_mul, sub_zero]

end HolomorphicAnosov.Ghys
