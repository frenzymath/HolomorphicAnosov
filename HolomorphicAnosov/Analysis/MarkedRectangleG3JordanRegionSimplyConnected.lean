import HolomorphicAnosov.Topology.MarkedRectangleG3JordanSeparationSchoenflies
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The bounded complementary region of a Jordan curve

Statement formalization of
`analysis.marked_rectangle_g3_jordan_region_simply_connected`.
The circle is Mathlib's unit circle in the complex plane. The region is an actual
connected component of the complement, with its ordinary subtype topology.

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem*,
Proc. AMS 2 (1951), pp. 860–867, through the named Jordan-Schoenflies provider
`topo.marked_rectangle_g3_jordan_separation_schoenflies`. No regularity or
finite-length hypothesis on the embedded circle is used.
-/

namespace HolomorphicAnosov

/--
The bounded component of the complement of a topologically embedded circle is
a nonempty bounded open connected Jordan region with the entire curve as its
frontier, and is simply connected in its inherited topology.

Source: Cairns (1951), main theorem p. 860, Theorem 4.1 pp. 864–865,
Lemmas 5.1–5.2 p. 866, and final amalgamation p. 867, via
`topo.marked_rectangle_g3_jordan_separation_schoenflies`.

Natural-language proof: Put C = range γ. The topological embedding identifies
the circle homeomorphically with C, so C is compact and nonempty. The named
Jordan-Schoenflies theorem gives exactly two nonempty complementary connected
components: one bounded and open, the other unbounded and open, both with
frontier C. Since z is outside C, connectedComponentIn selects a genuine
nonempty component; its boundedness identifies it with the inside component.
This proves the domain and frontier conclusions.

The same provider gives a plane homeomorphism taking C onto the unit circle.
Homeomorphisms carry complementary components onto complementary components.
Contain the bounded component in a closed ball. The continuous image of that
compact ball is compact and bounded, so its image component cannot be the
unbounded outside of the unit circle. It is therefore the open unit disk.
Alternatively, the provider's prescribed boundary homeomorphism extends over
the closed inside disk and restricts, with its inverse, to a homeomorphism from
the region onto the open unit disk. This uses its original subtype topology,
without assuming a smooth boundary or a conformal parametrization.

The open unit disk is homeomorphic to ℂ by w ↦ w / (1 - ‖w‖), with inverse
v ↦ v / (1 + ‖v‖). Both denominators are positive on their stated domains;
norm homogeneity proves the inverse identities and membership in the disk,
and continuity proves the homeomorphism. The real-vector-space contraction
v ↦ (1 - t) • v then pulls back to an actual contraction of the region to the
preimage of zero. SimplyConnectedSpace.ofContractible gives the final
conclusion. The implemented proof uses the provider's exact two-component
image and unbounded exterior to identify the given component, then transports
the convex open-disk contraction directly by the supplied plane homeomorphism.
The named Jordan-Schoenflies provider remains a lower proof obligation; this
conditional deduction does not certify that provider.
-/
theorem markedRectangleG3JordanRegionSimplyConnected
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ) (z : ℂ)
    (hz : z ∉ Set.range γ)
    (hbounded : Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z)) :
    let Q : Set ℂ := connectedComponentIn (Set.range γ)ᶜ z
    Q.Nonempty ∧ Bornology.IsBounded Q ∧ IsOpen Q ∧ IsConnected Q ∧
      frontier Q = Set.range γ ∧ SimplyConnectedSpace Q := by
  obtain ⟨H, Q, E, _hcurve, hinside, _houtside, hQne, _hEne, _hne,
    _hunion, _hdisjoint, hcomponents, hQopen, _hEopen, hQconn, _hEconn,
    hQbounded, hEunbounded, hQfrontier, _hEfrontier, _hclosure, _hextension,
    _hcrosscut⟩ := markedRectangleG3JordanSeparationSchoenflies γ hγ
  have hcomponent : connectedComponentIn (Set.range γ)ᶜ z = Q ∨
      connectedComponentIn (Set.range γ)ᶜ z = E := by
    have hmem := Set.mem_image_of_mem
      (fun w : ℂ ↦ connectedComponentIn (Set.range γ)ᶜ w)
      (show z ∈ (Set.range γ)ᶜ from hz)
    simpa only [hcomponents, Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have heq : connectedComponentIn (Set.range γ)ᶜ z = Q := by
    rcases hcomponent with hQ | hE
    · exact hQ
    · exact False.elim (hEunbounded (hE ▸ hbounded))
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  rw [heq]
  refine ⟨hQne, hQbounded, hQopen, hQconn, hQfrontier, ?_⟩
  have : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
    Metric.contractibleSpace_ball (by norm_num)
  have hdisk : IsSimplyConnected (Metric.ball (0 : ℂ) 1) :=
    SimplyConnectedSpace.ofContractible _
  have hQsimple : IsSimplyConnected Q := H.isSimplyConnected_image.mp (hinside ▸ hdisk)
  exact hQsimple.simplyConnectedSpace


end HolomorphicAnosov
