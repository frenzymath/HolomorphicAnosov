import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.InnerBallImage

/-! The actual restricted characteristic map in Hatcher, Algebraic Topology,
Proposition 3.17 p.217. Source and target carry the original subtype topologies. -/

open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison

/-- Restrict the characteristic sum to the open inner disks and their image.
Source: Hatcher p.217. Continuity is that of the characteristic maps on the
disjoint union, followed by restriction of domain and codomain. -/
def innerBallCharacteristic (X : Type u) [TopologicalSpace X] [T2Space X]
    [CWComplex (univ : Set X)] (m : ℕ) :
    C(↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m |
        ‖z.2.down.1‖ < (3 / 4 : ℝ)}, ↥(innerBallImage X m)) where
  toFun z := ⟨characteristicCell X m z.1.1 z.1.2, ⟨z.1.1, z.1.2, z.2, rfl⟩⟩
  continuous_toFun := by
    have h : Continuous (fun z : Σ _i : RelCWComplex.cell (univ : Set X) m,
        CellDisk.{u} m ↦ characteristicCell X m z.1 z.2) :=
      continuous_sigma fun i ↦ (characteristicCell X m i).continuous
    exact (h.comp continuous_subtype_val).subtype_mk _

end HolomorphicAnosov.CharacteristicCellComparison
