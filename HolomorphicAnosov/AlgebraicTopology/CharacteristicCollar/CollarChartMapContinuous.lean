import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarChartMap

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The collar-chart map into the characteristic attachment source is continuous.

Proof: On the lower-skeleton summand use the continuous sum injection. On every disk summand compose the continuous collar subtype inclusion with sigma and sum injections. The sum and sigma continuity criteria complete the proof.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem collarChartMap_continuous (m : ℕ) : Continuous (collarChartMap X m) :=
  continuous_inl.sumElim (continuous_sigma fun _i ↦
    continuous_inr.comp (continuous_sigmaMk.comp continuous_subtype_val))

end HolomorphicAnosov.CharacteristicCellComparison
