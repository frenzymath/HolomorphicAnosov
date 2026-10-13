import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell

/-! Inner characteristic balls for Hatcher, Algebraic Topology, p.217 and Appendix A.2 p.521. -/

open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- Hatcher p.217: images of the open balls of radius three quarters in the
characteristic disks, inside the original skeleton topology. -/
def innerBallImage (m : ℕ) : Set (Skeleton X m) :=
  {x | ∃ (i : RelCWComplex.cell (univ : Set X) m) (z : CellDisk.{u} m),
    ‖z.down.1‖ < (3 / 4 : ℝ) ∧ characteristicCell X m i z = x}

end HolomorphicAnosov.CharacteristicCellComparison
