import HolomorphicAnosov.Topology.BasedHomotopyUniqueness
import HolomorphicAnosov.Topology.Franks.PointedMapComposition

/-!
# An inverse on fundamental groups gives a composite homotopic to the identity

Source: Hatcher, *Algebraic Topology*, Theorem 1B.8, the deduction from Proposition
1B.9 on p.90. This is one of the two composite homotopies in that deduction.
DAG node: `topo.cw_aspherical_composite_homotopy_g18`.
-/

universe u v w

namespace HolomorphicAnosov.Topology

set_option backward.isDefEq.respectTransparency false in
/-- If based maps out of and back into a connected CW complex induce a composite
identity on its fundamental group, their composite is homotopic to the identity
through maps fixing the basepoint, provided the complex has a contractible cover.
The intermediate space has no CW, separation, or connectivity assumption.

Source: Hatcher, *Algebraic Topology*, Theorem 1B.8 and Proposition 1B.9, p.90.

Proof: the endpoint-aware composition formula identifies the induced homomorphism
of g composed with f with the composite of their induced homomorphisms, hence with
the identity. The identity continuous map induces the identity homomorphism, as can
be checked on a representative loop. The based uniqueness theorem applied to the
composite and the identity on K supplies the homotopy fixing k₀. Its source is the
original CW complex and its target uses the supplied surjective contractible cover;
no cover, CW structure, or local hypotheses on the intermediate space are used. -/
theorem cw_aspherical_composite_homotopy
    {K : Type u} {Y : Type v} {E : Type w}
    [TopologicalSpace K] [TopologicalSpace Y] [TopologicalSpace E]
    [T2Space K] [ConnectedSpace K] [_root_.Topology.CWComplex (Set.univ : Set K)]
    [ContractibleSpace E]
    (k₀ : K) (y₀ : Y) (p : E → K)
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (f : C(K, Y)) (g : C(Y, K)) (hf : f k₀ = y₀) (hg : g y₀ = k₀)
    (hπ : (FundamentalGroup.mapOfEq g hg).comp (FundamentalGroup.mapOfEq f hf) =
      MonoidHom.id (FundamentalGroup K k₀)) :
    Nonempty (ContinuousMap.HomotopyRel (g.comp f) (ContinuousMap.id K) {k₀}) := by
  apply cw_map_based_homotopy_uniqueness k₀ k₀ p hp hsurj
    (g.comp f) (ContinuousMap.id K) ((congrArg g hf).trans hg) rfl
  rw [← FranksPointedTransport.mapOfEq_comp f g hf hg, hπ]
  ext γ
  change γ = FundamentalGroup.mapOfEq (ContinuousMap.id K) rfl γ
  rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
  induction γ using Quotient.inductionOn with
  | h γ => rfl


end HolomorphicAnosov.Topology
