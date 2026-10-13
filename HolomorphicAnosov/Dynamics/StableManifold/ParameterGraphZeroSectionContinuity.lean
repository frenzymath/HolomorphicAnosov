import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity

noncomputable section
open Set _root_.Topology

namespace HolomorphicAnosov

/-! This file proves continuity of the zero sections in the native dependent fibre topologies (HPS, pp.8, 61–62). -/
theorem parameter_graph_zero_section_continuity
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    [TopologicalSpace (Sigma E₁)] [TopologicalSpace (Sigma E₂)]
    [TopologicalSpace (Sigma (fun p ↦ E₁ p × E₂ p))]
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) :
    Continuous (fun p : A ↦ (⟨p, 0⟩ : Sigma E₁)) ∧
    Continuous (fun p : A ↦ (⟨p, 0⟩ : Sigma E₂)) := by
  constructor
  · apply continuous_iff_continuousAt.2
    intro p
    let c := e.first.chart p
    have hp : p ∈ c.baseSet := e.first.mem_baseSet p
    have hc : ContinuousAt c.toOpenPartialHomeomorph.symm
        (p, (0 : FiniteFiberModel (e.first.rank p))) :=
      c.toOpenPartialHomeomorph.continuousAt_symm
        (show (p, (0 : FiniteFiberModel (e.first.rank p))) ∈ c.target from c.mem_target.mpr hp)
    have hprod : ContinuousAt (fun q : A ↦ (q, (0 : FiniteFiberModel (e.first.rank p)))) p :=
      continuousAt_id.prodMk continuousAt_const
    have hlocal : ContinuousAt (fun q : A ↦ c.toOpenPartialHomeomorph.symm
        (q, (0 : FiniteFiberModel (e.first.rank p)))) p := by
      exact ContinuousAt.comp (f := fun q : A ↦ (q, (0 : FiniteFiberModel (e.first.rank p))))
        (g := c.toOpenPartialHomeomorph.symm) hc hprod
    have hpoint : ∀ q : A, q ∈ c.baseSet →
        c.toOpenPartialHomeomorph.symm
            (q, (0 : FiniteFiberModel (e.first.rank p))) = (⟨q, 0⟩ : Sigma E₁) := by
      intro q hq
      have hzero : c (⟨q, 0⟩ : Sigma E₁) =
            (q, (0 : FiniteFiberModel (e.first.rank p))) := by
          rw [e.first.chart_apply p q hq 0]
          simp
      have hsrc : (⟨q, 0⟩ : Sigma E₁) ∈ c.toOpenPartialHomeomorph.source := by
        exact c.mem_source.mpr hq
      have htar : (q, (0 : FiniteFiberModel (e.first.rank p))) ∈
          c.toOpenPartialHomeomorph.target := c.mem_target.mpr hq
      have hinvsrc := c.toOpenPartialHomeomorph.map_target htar
      apply c.toOpenPartialHomeomorph.injOn hinvsrc hsrc
      calc
        c.toOpenPartialHomeomorph (c.toOpenPartialHomeomorph.symm
            (q, (0 : FiniteFiberModel (e.first.rank p)))) =
            (q, (0 : FiniteFiberModel (e.first.rank p))) :=
          c.apply_symm_apply' hq
        _ = c.toOpenPartialHomeomorph (⟨q, 0⟩ : Sigma E₁) := hzero.symm
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [c.open_baseSet.mem_nhds hp] with q hq
    exact (hpoint q hq).symm

  · apply continuous_iff_continuousAt.2
    intro p
    let c := e.second.chart p
    have hp : p ∈ c.baseSet := e.second.mem_baseSet p
    have hc : ContinuousAt c.toOpenPartialHomeomorph.symm
        (p, (0 : FiniteFiberModel (e.second.rank p))) :=
      c.toOpenPartialHomeomorph.continuousAt_symm
        (show (p, (0 : FiniteFiberModel (e.second.rank p))) ∈ c.target from c.mem_target.mpr hp)
    have hprod : ContinuousAt (fun q : A ↦ (q, (0 : FiniteFiberModel (e.second.rank p)))) p :=
      continuousAt_id.prodMk continuousAt_const
    have hlocal : ContinuousAt (fun q : A ↦ c.toOpenPartialHomeomorph.symm
        (q, (0 : FiniteFiberModel (e.second.rank p)))) p := by
      exact ContinuousAt.comp (f := fun q : A ↦ (q, (0 : FiniteFiberModel (e.second.rank p))))
        (g := c.toOpenPartialHomeomorph.symm) hc hprod
    have hpoint : ∀ q : A, q ∈ c.baseSet →
        c.toOpenPartialHomeomorph.symm
            (q, (0 : FiniteFiberModel (e.second.rank p))) = (⟨q, 0⟩ : Sigma E₂) := by
      intro q hq
      have hzero : c (⟨q, 0⟩ : Sigma E₂) =
            (q, (0 : FiniteFiberModel (e.second.rank p))) := by
          rw [e.second.chart_apply p q hq 0]
          simp
      have hsrc : (⟨q, 0⟩ : Sigma E₂) ∈ c.toOpenPartialHomeomorph.source := by
        exact c.mem_source.mpr hq
      have htar : (q, (0 : FiniteFiberModel (e.second.rank p))) ∈
          c.toOpenPartialHomeomorph.target := c.mem_target.mpr hq
      have hinvsrc := c.toOpenPartialHomeomorph.map_target htar
      apply c.toOpenPartialHomeomorph.injOn hinvsrc hsrc
      calc
        c.toOpenPartialHomeomorph (c.toOpenPartialHomeomorph.symm
            (q, (0 : FiniteFiberModel (e.second.rank p)))) =
            (q, (0 : FiniteFiberModel (e.second.rank p))) :=
          c.apply_symm_apply' hq
        _ = c.toOpenPartialHomeomorph (⟨q, 0⟩ : Sigma E₂) := hzero.symm
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [c.open_baseSet.mem_nhds hp] with q hq
    exact (hpoint q hq).symm

end HolomorphicAnosov
