import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformation
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCollarFiber
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarImage
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DescendedCollar

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- Evaluating the descended collar formula at a characteristic collar image agrees with deforming that collar representative and applying its characteristic map.

Proof: The chosen representative and the specified one have the same characteristic image. Fibre compatibility makes their deformed characteristic images equal.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem descendedCollar_characteristic (m : ℕ) (t : unitInterval)
    (i : RelCWComplex.cell (univ : Set X) m) (z : DiskCollar.{u} m) :
    descendedCollar X m t ⟨characteristicCell X m i z.1, ⟨⟨i, z⟩, rfl⟩⟩ =
      characteristicCell X m i (collarDeformation m (t, z)).1 := by
  exact characteristic_collar_fiber X m t _ _ _ _ (Classical.choose_spec
    (show characteristicCell X m i z.1 ∈ collarImage X m from ⟨⟨i, z⟩, rfl⟩))

end HolomorphicAnosov.CharacteristicCellComparison
