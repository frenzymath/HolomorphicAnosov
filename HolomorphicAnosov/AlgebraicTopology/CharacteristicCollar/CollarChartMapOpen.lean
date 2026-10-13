import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarChartMap

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The collar-chart map into the characteristic attachment source is open.

Proof: The disk collar is defined by a strict continuous norm inequality and is open. Its subtype inclusion is open, as are sigma and sum injections. Apply openness on each summand and combine by the sum criterion.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem collarChartMap_open (m : ℕ) : IsOpenMap (collarChartMap X m) := by
  apply isOpenMap_inl.sumElim
  apply isOpenMap_sigma.mpr
  intro i
  exact isOpenMap_inr.comp (isOpenMap_sigmaMk.comp
    ((isOpen_lt continuous_const
      ((continuous_subtype_val.comp continuous_uliftDown).norm)).isOpenMap_subtype_val))

end HolomorphicAnosov.CharacteristicCellComparison
