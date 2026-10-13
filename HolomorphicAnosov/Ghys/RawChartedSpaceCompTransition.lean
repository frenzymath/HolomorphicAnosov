import HolomorphicAnosov.Ghys.CurveJetAffineData
noncomputable section
open Set Filter Topology _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
/-- Every chart in the `Homeomorph.piUnique` pushed-forward atlas agrees on its source with the inverse continuous-linear equivalence. (Mathlib, chartedSpaceOfRightInverse) -/
theorem atlas_chart_eq_piUnique_inv :
    ∀ (q : OpenPartialHomeomorph ℂ (ComplexModel 1)),
      q ∈ (Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).chartedSpace.atlas →
      EqOn q (ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)).symm q.source := by
  intro q hq
  change q ∈ ((Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).isLocalHomeomorph.chartedSpace
    (Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).surjective).atlas at hq
  change q ∈ {((Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).isLocalHomeomorph.localInverseAt
    ((Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).surjective.hasRightInverse.choose x)).trans
      (chartAt (ComplexModel 1) ((Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).surjective.hasRightInverse.choose x)) | x : ℂ} at hq
  rcases hq with ⟨x, rfl⟩
  intro z hz
  let E : ComplexModel 1 ≃L[ℂ] ℂ := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
  have hz' : z ∈ ((Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).isLocalHomeomorph.localInverseAt
      ((Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).surjective.hasRightInverse.choose x)).source := by
    exact hz.1
  apply E.injective
  rw [E.apply_symm_apply]
  change (Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ))
    ((Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).isLocalHomeomorph.localInverseAt
      ((Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).surjective.hasRightInverse.choose x) z) = _
  exact (Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).isLocalHomeomorph.apply_localInverseAt_of_mem hz'

example (q : OpenPartialHomeomorph ℂ (ComplexModel 1))
    (hq : q ∈ (Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).chartedSpace.atlas) :
    ContDiffOn ℂ ∞ q q.source := by
  let E : ComplexModel 1 ≃L[ℂ] ℂ := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
  apply E.symm.contDiff.contDiffOn.congr
  exact (by
    intro z hz
    exact atlas_chart_eq_piUnique_inv q hq hz)


/-- The inverse of every pushed-forward `Homeomorph.piUnique` chart agrees on its target with the continuous-linear equivalence. (Mathlib, chartedSpaceOfRightInverse) -/
theorem atlas_chart_inv_eq_piUnique (q : OpenPartialHomeomorph ℂ (ComplexModel 1))
    (hq : q ∈ (Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).chartedSpace.atlas) :
    EqOn q.symm (ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)) q.target := by
  change q ∈ ((Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).isLocalHomeomorph.chartedSpace
    (Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).surjective).atlas at hq
  change q ∈ {((Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).isLocalHomeomorph.localInverseAt
    ((Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).surjective.hasRightInverse.choose x)).trans
      (chartAt (ComplexModel 1) ((Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).surjective.hasRightInverse.choose x)) | x : ℂ} at hq
  rcases hq with ⟨x, rfl⟩
  intro z hz
  let E : ComplexModel 1 ≃L[ℂ] ℂ := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
  change _ = E z
  simp only [OpenPartialHomeomorph.coe_trans_symm,
    IsLocalHomeomorph.localInverseAt_symm]
  rfl


/-- Chart transitions in the canonical product-model atlas are complex smooth. (Mathlib, chartedSpaceOfRightInverse) -/
theorem raw_chartedSpace_comp_transition
    {L : Type*} [TopologicalSpace L] [ChartedSpace ℂ L]
    [IsManifold 𝓘(ℂ) ∞ L]
    (e e' : OpenPartialHomeomorph L (ComplexModel 1))
    (he : e ∈ @ChartedSpace.atlas (ComplexModel 1) _ L _ (curveScalarToProductChartedSpace L))
    (he' : e' ∈ @ChartedSpace.atlas (ComplexModel 1) _ L _ (curveScalarToProductChartedSpace L)) :
    ContDiffOn ℂ ∞
      ((complexModel 1) ∘ (e.symm.trans e') ∘ (complexModel 1).symm)
      ((complexModel 1).symm ⁻¹' (e.symm.trans e').source ∩ Set.range (complexModel 1)) := by
  rcases he with ⟨c, hc, q, hq, rfl⟩
  rcases he' with ⟨c', hc', q', hq', rfl⟩
  let E : ComplexModel 1 ≃L[ℂ] ℂ := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
  have hqf : EqOn q E.symm q.source := by
    exact atlas_chart_eq_piUnique_inv q hq
  have hqfi : EqOn q.symm E q.target := by
    exact atlas_chart_inv_eq_piUnique q hq
  have hq_smooth : ContDiffOn ℂ ∞ q q.source := by
    apply E.symm.contDiff.contDiffOn.congr
    exact fun z hz => hqf hz
  have hq_inv_smooth : ContDiffOn ℂ ∞ q.symm q.target := by
    apply E.contDiff.contDiffOn.congr
    exact fun z hz => hqfi hz
  have hq'f : EqOn q' E.symm q'.source := by
    exact atlas_chart_eq_piUnique_inv q' hq'
  have hq'fi : EqOn q'.symm E q'.target := by
    exact atlas_chart_inv_eq_piUnique q' hq'
  have hq'_smooth : ContDiffOn ℂ ∞ q' q'.source := by
    apply E.symm.contDiff.contDiffOn.congr
    exact fun z hz => hq'f hz
  have hq'_inv_smooth : ContDiffOn ℂ ∞ q'.symm q'.target := by
    apply E.contDiff.contDiffOn.congr
    exact fun z hz => hq'fi hz
  have hcc : ContDiffOn ℂ ∞ (c.symm.trans c') (c.symm.trans c').source := by
    have hcomp := (contDiffGroupoid ∞ (𝓘(ℂ, ℂ))).compatible hc hc'
    have h := (mem_groupoid_of_pregroupoid.mp hcomp).1
    change ContDiffOn ℂ ∞ ((𝓘(ℂ, ℂ)) ∘ (c.symm.trans c') ∘ (𝓘(ℂ, ℂ)).symm)
      ((𝓘(ℂ, ℂ)).symm ⁻¹' (c.symm.trans c').source ∩ Set.range (𝓘(ℂ, ℂ))) at h
    simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, Set.range_id, Set.preimage_id, Set.inter_univ] using h
  simp only [complexModel, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.range_id, Set.preimage_id, Set.inter_univ]
  let t := (c.trans q).symm.trans (c'.trans q')
  change ContDiffOn ℂ ∞ t t.source
  let u := c.symm.trans c'
  have hu : ContDiffOn ℂ ∞ u u.source := hcc
  have hmap1 : MapsTo q.symm t.source u.source := by
    intro z hz
    change q.symm z ∈ (c.symm.trans c').source
    rw [OpenPartialHomeomorph.trans_source]
    rcases hz with ⟨hz1, hz2⟩
    simp only [OpenPartialHomeomorph.symm_symm] at hz1
    rw [OpenPartialHomeomorph.trans_target] at hz1
    exact ⟨hz1.2, by
      change (c.trans q).symm z ∈ (c'.trans q').source at hz2
      rw [OpenPartialHomeomorph.trans_source] at hz2
      have hz2a := hz2.1
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] at hz2a
      change c.symm (q.symm z) ∈ c'.source
      simpa only [OpenPartialHomeomorph.trans_apply] using hz2a⟩
  have hmap2 : MapsTo (u ∘ q.symm) t.source q'.source := by
    intro z hz
    change c' (c.symm (q.symm z)) ∈ q'.source
    rcases hz with ⟨hz1, hz2⟩
    change (c.trans q).symm z ∈ (c'.trans q').source at hz2
    rw [OpenPartialHomeomorph.trans_source] at hz2
    have hz2a := hz2.2
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] at hz2a
    change c' (c.symm (q.symm z)) ∈ q'.source at hz2a
    exact hz2a
  have htq : t.source ⊆ q.target := by
    intro z hz
    rcases hz with ⟨hz1, hz2⟩
    simp only [OpenPartialHomeomorph.symm_symm] at hz1
    rw [OpenPartialHomeomorph.trans_target] at hz1
    exact hz1.1
  have hcomp : ContDiffOn ℂ ∞ (q' ∘ u ∘ q.symm) t.source := by
    exact hq'_smooth.comp (hu.comp (hq_inv_smooth.mono htq) hmap1) hmap2
  apply hcomp.congr
  intro z hz
  change (c'.trans q') ((c.trans q).symm z) = t z
  rfl
end HolomorphicAnosov.Ghys
