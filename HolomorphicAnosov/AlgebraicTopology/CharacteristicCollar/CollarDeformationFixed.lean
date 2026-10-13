import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellBoundary
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarRadialBoundaryFixed
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformation

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The continuous disk-collar deformation fixes the disk boundary pointwise for every time.

Proof: Apply subtype extensionality twice and use that the underlying radial vector fixes unit-norm boundary points.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem collarDeformation_fixed (m : ℕ) (t : unitInterval) (z : DiskCollar.{u} m)
    (hz : z.1 ∈ cellBoundary m) : collarDeformation m (t, z) = z := by
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  exact collarRadial_boundary_fixed m t z hz

end HolomorphicAnosov.CharacteristicCellComparison
