import HolomorphicAnosov.Dynamics.Anosov.DistanceLeafRange
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.NativeAsymptoticDatumOfLeaf

/-! # Native intrinsic structures on metric asymptotic carriers
Source: HPS, *Invariant Manifolds* (1977), §6B–7, pp.111–116;
Shub, *Global Stability of Dynamical Systems* (1987), Definition 2.1, pp.8–9.
-/

open scoped ContDiff Manifold Topology _root_.Topology
namespace HolomorphicAnosov.HPS
universe u

/-- A metric-distance identification transports each selected source leaf to
its literal original asymptotic carrier, preserving dimension and ambient points.

Source: HPS (1977), §6B–7, pp.111–116, and Shub (1987), Definition 2.1,
pp.8–9. The centre is asymptotic to itself, so the stored range identity
provides its preimage in the selected leaf. Apply the existing
`DistanceLeafIdentification.range_eq_forwardAsymptotic` at that preimage.
This is precisely the range equality required
by `native_asymptotic_datum_of_leaf_g15`. Apply that theorem to the selected
leaf; it transports the intrinsic topology, smooth atlas, immersion and
point-preserving diffeomorphism without using the ambient subtype topology. -/
theorem DistanceLeafIdentification.nativeDatum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type u} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
    {D : RealTangentDistribution 𝓘(ℝ, E) M} {F : LeafPartition D ι L r}
    {f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞}
    (A : DistanceLeafIdentification F f edist) (x : M) :
    ∃ N : NativeAsymptoticLeafDatum 𝓘(ℝ, E) f.toHomeomorph D x,
      N.rank = r (A.label x) ∧
      (letI := N.topology; letI := N.charts
       ∃ e : Diffeomorph 𝓘(ℝ, Fin (r (A.label x)) → ℝ) 𝓘(ℝ, Fin N.rank → ℝ)
          (L (A.label x)) (StableAsymptoticLeaf f.toHomeomorph x) ∞,
          ∀ z, (e z).val = (F.leaf (A.label x)).inclusion z) := by
  apply native_asymptotic_datum_of_leaf_g15 D (F.leaf (A.label x)) f.toHomeomorph x
  have hx : x ∈ Set.range (F.leaf (A.label x)).inclusion := by
    rw [A.equality]
    simp only [Set.mem_ofPred_eq, edist_self]
    exact tendsto_const_nhds
  obtain ⟨z, hz⟩ := hx
  simpa only [hz, Diffeomorph.coe_toHomeomorph] using
    A.range_eq_forwardAsymptotic (A.label x) z

end HolomorphicAnosov.HPS
