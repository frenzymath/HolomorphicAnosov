import HolomorphicAnosov.Dynamics.Bowen.CompactProductDataOnInvariantSubtype
import HolomorphicAnosov.Dynamics.HirschPughHyperbolicSetFactOne

noncomputable section

namespace HolomorphicAnosov.BowenBasicSetCoding

open Set Filter Manifold Bundle
open scoped Topology _root_.Topology ContDiff Bundle

/-- Apply the published original hyperbolic-set Fact 1 theorem and construct
its compact product data with the adapted distance, while definitionally
preserving the original topology. The underlying invariant map remains the
given restriction. This inherits exactly the current Fact 1 admission; the
metric, bracket, scales and product-chart adapters add no new admission.
Source: Hirsch–Pugh (1969), Theorem 3.1; Bowen (1970), Fact 1 and Lemmas 5–8. -/
theorem original_factOne_gives_compact_product_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [tM : TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (Λ : Set M)
    (H : HyperbolicSetFactOneDatum f Λ)
    (hΛ : ∀ x, x ∈ Λ ↔ f x ∈ Λ) :
    ∃ d : MetricSpace M, ∃ ht : d.toUniformSpace.toTopologicalSpace = tM,
      letI : MetricSpace M := d.replaceTopology ht.symm
      letI : CompactSpace Λ := isCompact_iff_compactSpace.mp H.compact
      ∃ κ γ : ℝ, Nonempty (Dynamics.Bowen.CompactLocalProductData
        (f.toHomeomorph.subtype hΛ) γ κ) := by
  obtain ⟨h, a, d, κ, γ, ε, _, _, _, ht, _, hκ, hκ1, hγ, hε, hs, hu,
    b, hb, hbsingleton⟩ := hirschPughHyperbolicSetFactOne f Λ H
  refine ⟨d, ht, ?_⟩
  let : MetricSpace M := d.replaceTopology ht.symm
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp H.compact
  refine ⟨κ, γ, ?_⟩
  refine compact_product_data_on_invariant_subtype f.toHomeomorph Λ hΛ
    H.compact H.nonempty γ κ ε hγ hκ hκ1 hε ?_ ?_ b hb ?_ ?_
  · intro x hx y hy z hz hxy hxz n
    exact hs x hx y ⟨hy, hxy⟩ z ⟨hz, hxz⟩ n
  · intro x hx y hy z hz hxy hxz n
    exact hu x hx y ⟨hy, hxy⟩ z ⟨hz, hxz⟩ n
  · intro p
    have hm : (b p).val ∈ hyperbolicClosedStablePlaque f Λ d γ p.val.1 ∩
        hyperbolicClosedUnstablePlaque f Λ d γ p.val.2 := by
      rw [hbsingleton p]
      exact mem_singleton _
    exact ⟨hm.1.2, hm.2.2⟩
  · intro p z hzS hzU
    apply Subtype.ext
    have hm : z.val ∈ hyperbolicClosedStablePlaque f Λ d γ p.val.1 ∩
        hyperbolicClosedUnstablePlaque f Λ d γ p.val.2 :=
      ⟨⟨z.property, hzS⟩, ⟨z.property, hzU⟩⟩
    rw [hbsingleton p] at hm
    exact hm



end HolomorphicAnosov.BowenBasicSetCoding
