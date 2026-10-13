import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.AttachmentSource
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarCharts

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The collar-chart map sends lower-skeleton points to their attachment summand and forgets the collar bound on disk points in their attachment summand.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
def collarChartMap (m : ℕ) : CollarCharts X m → AttachmentSource X m :=
  Sum.elim Sum.inl (fun z ↦ Sum.inr ⟨z.1, z.2.1⟩)

end HolomorphicAnosov.CharacteristicCellComparison
